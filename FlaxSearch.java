/*
 * Flax Search - a complete search engine in one Java file (JDK 17+, no dependencies).
 *
 *   Run:   java FlaxSearch.java
 *   Open:  http://localhost:8080
 *
 * Parts:
 *   1. Crawler  - multi-threaded (virtual threads), respects robots.txt, per-host politeness,
 *                 follows links so the index keeps growing toward your target size.
 *   2. Index    - inverted index with BM25 ranking, field boosts (title/url/description/body),
 *                 phrase search ("..."), exclusion (-word) and site:domain filters.
 *   3. Server   - Google-style UI: home page, results page, autocomplete, "I'm Feeling Lucky",
 *                 pagination, dark mode.
 *
 * Useful settings (add as  -Dname=value  before FlaxSearch.java):
 *   port=8080          bind=127.0.0.1        data=flax-data
 *   crawl=true         workers=64            max=10000000     perHost=500
 *   delayMs=1000       seeds=seeds.txt       allow.private=false    public.submit=false
 */

import com.sun.net.httpserver.Headers;
import com.sun.net.httpserver.HttpExchange;
import com.sun.net.httpserver.HttpHandler;
import com.sun.net.httpserver.HttpServer;

import java.io.*;
import java.net.*;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.text.NumberFormat;
import java.time.Duration;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.locks.ReentrantReadWriteLock;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class FlaxSearch {

    // ------------------------------------------------------------------ settings
    static final int PORT = Integer.getInteger("port", 8080);
    static final String BIND = System.getProperty("bind", "127.0.0.1");
    static final Path DATA = Path.of(System.getProperty("data", "flax-data"));
    static final boolean CRAWL = Boolean.parseBoolean(System.getProperty("crawl", "true"));
    static final int WORKERS = Integer.getInteger("workers", 64);
    static final int MAX_PAGES = Integer.getInteger("max", 10_000_000);
    static final int PER_HOST = Integer.getInteger("perHost", 500);
    static final long DELAY_MS = Long.getLong("delayMs", 1000L);
    static final boolean ALLOW_PRIVATE = Boolean.getBoolean("allow.private");
    static final boolean PUBLIC_SUBMIT = Boolean.getBoolean("public.submit");
    static final String USER_AGENT = "FlaxBot/1.0 (+http://localhost:" + PORT + "/about)";
    static final int PAGE_SIZE = 10;

    // ------------------------------------------------------------------ data model
    record Doc(String url, String title, String desc, String text, long time) {}

    record Hit(Doc doc, double score) {}

    record Result(int total, List<Hit> hits, Pattern highlight, List<String> terms) {}

    // ================================================================== INDEX
    static final class Index {
        static final double K1 = 1.2, B = 0.75;
        static final Pattern TOKEN = Pattern.compile("[\\p{L}\\p{N}]+");
        static final Pattern QUERY_PART = Pattern.compile("\"([^\"]+)\"|(\\S+)");

        final ReentrantReadWriteLock lock = new ReentrantReadWriteLock();
        final ArrayList<Doc> docs = new ArrayList<>();
        final ArrayList<Integer> lens = new ArrayList<>();
        final HashMap<String, Integer> byUrl = new HashMap<>();
        final TreeMap<String, HashMap<Integer, Integer>> inv = new TreeMap<>();
        long totalLen = 0;
        volatile boolean dirty = false;

        static String stem(String t) {
            if (t.length() > 3 && t.endsWith("s") && !t.endsWith("ss")) return t.substring(0, t.length() - 1);
            return t;
        }

        static List<String> tokens(String s) {
            List<String> out = new ArrayList<>();
            if (s == null) return out;
            Matcher m = TOKEN.matcher(s.toLowerCase(Locale.ROOT));
            while (m.find()) {
                String t = m.group();
                if (t.length() > 40) continue;
                if (t.length() == 1 && !Character.isDigit(t.charAt(0))) continue;
                out.add(stem(t));
            }
            return out;
        }

        int size() {
            lock.readLock().lock();
            try { return docs.size(); } finally { lock.readLock().unlock(); }
        }

        int hostCount() {
            lock.readLock().lock();
            try {
                Set<String> hosts = new HashSet<>();
                for (Doc d : docs) hosts.add(hostOf(d.url));
                return hosts.size();
            } finally { lock.readLock().unlock(); }
        }

        private static int count(Map<String, Integer> tf, String text, int weight) {
            int n = 0;
            for (String t : tokens(text)) { tf.merge(t, weight, Integer::sum); n += weight; }
            return n;
        }

        boolean add(Doc d) {
            lock.writeLock().lock();
            try {
                if (byUrl.containsKey(d.url())) return false;
                int id = docs.size();
                docs.add(d);
                byUrl.put(d.url(), id);
                Map<String, Integer> tf = new HashMap<>();
                int len = 0;
                len += count(tf, d.title(), 3);
                len += count(tf, urlWords(d.url()), 2);
                len += count(tf, d.desc(), 2);
                len += count(tf, d.text(), 1);
                lens.add(Math.max(len, 1));
                totalLen += Math.max(len, 1);
                for (var e : tf.entrySet())
                    inv.computeIfAbsent(e.getKey(), k -> new HashMap<>()).put(id, e.getValue());
                dirty = true;
                return true;
            } finally { lock.writeLock().unlock(); }
        }

        static String urlWords(String url) {
            try {
                URI u = URI.create(url);
                return (u.getHost() == null ? "" : u.getHost()) + " " + (u.getPath() == null ? "" : u.getPath());
            } catch (Exception e) { return ""; }
        }

        // ---- query parsing
        static final class Parsed {
            final LinkedHashSet<String> terms = new LinkedHashSet<>();
            final Set<String> exclude = new HashSet<>();
            final List<String> phrases = new ArrayList<>();
            String site = null;
        }

        static Parsed parse(String q) {
            Parsed p = new Parsed();
            Matcher m = QUERY_PART.matcher(q);
            while (m.find()) {
                if (m.group(1) != null) {
                    List<String> ts = tokens(m.group(1));
                    p.terms.addAll(ts);
                    if (!ts.isEmpty()) p.phrases.add(m.group(1).toLowerCase(Locale.ROOT).trim());
                    continue;
                }
                String w = m.group(2);
                if (w.length() > 1 && w.startsWith("-")) p.exclude.addAll(tokens(w.substring(1)));
                else if (w.toLowerCase(Locale.ROOT).startsWith("site:") && w.length() > 5)
                    p.site = w.substring(5).toLowerCase(Locale.ROOT);
                else p.terms.addAll(tokens(w));
            }
            return p;
        }

        // ---- search (BM25 + boosts)
        Result search(String query, int offset, int limit) {
            Parsed p = parse(query);
            List<Hit> ranked = new ArrayList<>();
            lock.readLock().lock();
            try {
                int n = docs.size();
                if (n == 0 || (p.terms.isEmpty() && p.site == null))
                    return new Result(0, List.of(), null, new ArrayList<>(p.terms));
                double avg = (double) totalLen / n;
                Map<Integer, double[]> acc = new HashMap<>();
                if (p.terms.isEmpty()) {
                    for (int id = 0; id < n && acc.size() < 5000; id++)
                        if (siteMatches(docs.get(id), p.site)) acc.put(id, new double[]{1, 1});
                } else {
                    for (String t : p.terms) {
                        HashMap<Integer, Integer> post = inv.get(t);
                        if (post == null) continue;
                        double idf = Math.log(1 + (n - post.size() + 0.5) / (post.size() + 0.5));
                        for (var e : post.entrySet()) {
                            double tf = e.getValue();
                            double len = lens.get(e.getKey());
                            double s = idf * tf * (K1 + 1) / (tf + K1 * (1 - B + B * len / avg));
                            double[] a = acc.computeIfAbsent(e.getKey(), k -> new double[2]);
                            a[0] += s;
                            a[1]++;
                        }
                    }
                }
                final int wanted = Math.max(p.terms.size(), 1);
                boolean anyFull = acc.values().stream().anyMatch(a -> a[1] >= wanted);
                int need = anyFull ? wanted : 1;

                List<Hit> cands = new ArrayList<>();
                for (var e : acc.entrySet()) {
                    double[] a = e.getValue();
                    if (a[1] < need) continue;
                    int id = e.getKey();
                    boolean bad = false;
                    for (String x : p.exclude) {
                        HashMap<Integer, Integer> post = inv.get(x);
                        if (post != null && post.containsKey(id)) { bad = true; break; }
                    }
                    if (bad) continue;
                    Doc d = docs.get(id);
                    if (p.site != null && !siteMatches(d, p.site)) continue;
                    if (!p.phrases.isEmpty()) {
                        String hay = (d.title() + " " + d.desc() + " " + d.text()).toLowerCase(Locale.ROOT);
                        boolean all = true;
                        for (String ph : p.phrases) if (!hay.contains(ph)) { all = false; break; }
                        if (!all) continue;
                    }
                    double frac = p.terms.isEmpty() ? 1 : a[1] / p.terms.size();
                    cands.add(new Hit(d, a[0] * frac * frac));
                }
                cands.sort((x, y) -> Double.compare(y.score(), x.score()));

                // boosts on the head of the list only (keeps big result sets fast)
                String plain = String.join(" ", p.terms);
                int head = Math.min(cands.size(), 300);
                List<Hit> boosted = new ArrayList<>(head);
                for (int i = 0; i < head; i++) {
                    Hit h = cands.get(i);
                    double s = h.score();
                    String titleLower = h.doc().title().toLowerCase(Locale.ROOT);
                    List<String> tt = tokens(h.doc().title());
                    if (!p.terms.isEmpty() && tt.containsAll(p.terms)) s *= 1.3;
                    if (!plain.isEmpty() && String.join(" ", tt).contains(plain)) s *= 1.5;
                    if (titleLower.equals(query.toLowerCase(Locale.ROOT).trim())) s *= 1.5;
                    if (isHome(h.doc().url())) s *= 1.15;
                    boosted.add(new Hit(h.doc(), s));
                }
                boosted.sort((x, y) -> Double.compare(y.score(), x.score()));
                ranked.addAll(boosted);
                if (cands.size() > head) ranked.addAll(cands.subList(head, cands.size()));
            } finally { lock.readLock().unlock(); }

            int from = Math.min(offset, ranked.size());
            int to = Math.min(from + limit, ranked.size());
            Pattern hl = highlightPattern(p.terms);
            return new Result(ranked.size(), new ArrayList<>(ranked.subList(from, to)), hl, new ArrayList<>(p.terms));
        }

        static boolean siteMatches(Doc d, String site) {
            if (site == null) return true;
            String h = hostOf(d.url());
            return h.equals(site) || h.endsWith("." + site);
        }

        static boolean isHome(String url) {
            try {
                String path = URI.create(url).getPath();
                return path == null || path.isEmpty() || path.equals("/");
            } catch (Exception e) { return false; }
        }

        static Pattern highlightPattern(Collection<String> terms) {
            if (terms.isEmpty()) return null;
            StringBuilder sb = new StringBuilder("\\b(?:");
            boolean first = true;
            for (String t : terms) {
                if (!first) sb.append('|');
                sb.append(Pattern.quote(t));
                first = false;
            }
            sb.append(")\\p{L}*");
            return Pattern.compile(sb.toString(),
                    Pattern.CASE_INSENSITIVE | Pattern.UNICODE_CASE | Pattern.UNICODE_CHARACTER_CLASS);
        }

        // ---- autocomplete: complete the last word from index vocabulary, ranked by document frequency
        List<String> suggest(String input) {
            String s = input.toLowerCase(Locale.ROOT);
            int cut = Math.max(s.lastIndexOf(' '), -1);
            String head = cut >= 0 ? s.substring(0, cut + 1) : "";
            String prefix = stem(s.substring(cut + 1));
            if (prefix.isEmpty() || prefix.length() > 30) return List.of();
            List<Map.Entry<String, Integer>> found = new ArrayList<>();
            lock.readLock().lock();
            try {
                int seen = 0;
                for (var e : inv.subMap(prefix, true, prefix + '\uffff', true).entrySet()) {
                    found.add(Map.entry(e.getKey(), e.getValue().size()));
                    if (++seen >= 2000) break;
                }
            } finally { lock.readLock().unlock(); }
            found.sort((a, b) -> b.getValue() - a.getValue());
            List<String> out = new ArrayList<>();
            for (var e : found) {
                out.add(head + e.getKey());
                if (out.size() >= 8) break;
            }
            return out;
        }

        // ---- persistence
        static final int MAGIC = 0xF1A5C0DE;

        void save(Path file) throws IOException {
            List<Doc> snap;
            lock.readLock().lock();
            try { snap = new ArrayList<>(docs); dirty = false; } finally { lock.readLock().unlock(); }
            Path tmp = file.resolveSibling(file.getFileName() + ".tmp");
            try (DataOutputStream out = new DataOutputStream(new BufferedOutputStream(Files.newOutputStream(tmp)))) {
                out.writeInt(MAGIC);
                out.writeInt(snap.size());
                for (Doc d : snap) {
                    out.writeUTF(d.url());
                    out.writeUTF(d.title());
                    out.writeUTF(d.desc());
                    out.writeUTF(d.text());
                    out.writeLong(d.time());
                }
            }
            Files.move(tmp, file, StandardCopyOption.REPLACE_EXISTING);
        }

        void load(Path file) {
            if (!Files.exists(file)) return;
            try (DataInputStream in = new DataInputStream(new BufferedInputStream(Files.newInputStream(file)))) {
                if (in.readInt() != MAGIC) return;
                int n = in.readInt();
                for (int i = 0; i < n; i++)
                    add(new Doc(in.readUTF(), in.readUTF(), in.readUTF(), in.readUTF(), in.readLong()));
            } catch (Exception e) {
                System.err.println("Index load stopped early: " + e);
            }
            dirty = false;
        }
    }

    static String hostOf(String url) {
        try {
            String h = URI.create(url).getHost();
            return h == null ? "" : h.toLowerCase(Locale.ROOT);
        } catch (Exception e) { return ""; }
    }

    // ================================================================== HTML PARSING
    record Parsed(String title, String desc, String text, List<String> links, boolean noindex, boolean nofollow) {}

    static final class Html {
        static final Pattern TITLE = Pattern.compile("<title[^>]*>(.*?)</title>", Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
        static final Pattern META = Pattern.compile("<meta\\s[^>]*>", Pattern.CASE_INSENSITIVE);
        static final Pattern ANCHOR = Pattern.compile("<a\\s[^>]*>", Pattern.CASE_INSENSITIVE);
        static final Pattern JUNK = Pattern.compile("<(script|style|noscript|svg|template|head)[^>]*>.*?</\\1>", Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
        static final Pattern COMMENT = Pattern.compile("<!--.*?-->", Pattern.DOTALL);
        static final Pattern TAG = Pattern.compile("<[^>]+>");
        static final Pattern ENTITY = Pattern.compile("&(#\\d+|#x[0-9a-fA-F]+|[a-zA-Z]+);");
        static final Pattern SPACE = Pattern.compile("\\s+");

        static String attr(String tag, String name) {
            Matcher m = Pattern.compile("\\b" + name + "\\s*=\\s*(?:\"([^\"]*)\"|'([^']*)'|([^\\s>]+))", Pattern.CASE_INSENSITIVE).matcher(tag);
            if (!m.find()) return null;
            return m.group(1) != null ? m.group(1) : m.group(2) != null ? m.group(2) : m.group(3);
        }

        static String decode(String s) {
            if (s.indexOf('&') < 0) return s;
            Matcher m = ENTITY.matcher(s);
            StringBuilder sb = new StringBuilder();
            while (m.find()) {
                String e = m.group(1), r;
                switch (e) {
                    case "amp" -> r = "&";
                    case "lt" -> r = "<";
                    case "gt" -> r = ">";
                    case "quot" -> r = "\"";
                    case "apos" -> r = "'";
                    case "nbsp" -> r = " ";
                    default -> {
                        r = " ";
                        try {
                            int cp = e.startsWith("#x") ? Integer.parseInt(e.substring(2), 16)
                                    : e.startsWith("#") ? Integer.parseInt(e.substring(1)) : -1;
                            if (cp > 0 && cp < 0x110000) r = new String(Character.toChars(cp));
                        } catch (Exception ignored) { }
                    }
                }
                m.appendReplacement(sb, Matcher.quoteReplacement(r));
            }
            m.appendTail(sb);
            return sb.toString();
        }

        static String clean(String s) {
            return SPACE.matcher(decode(s)).replaceAll(" ").trim();
        }

        static Parsed parse(String html, URI base) {
            String title = "";
            Matcher tm = TITLE.matcher(html);
            if (tm.find()) title = clean(TAG.matcher(tm.group(1)).replaceAll(" "));

            String desc = "";
            boolean noindex = false, nofollow = false;
            Matcher mm = META.matcher(html);
            while (mm.find()) {
                String tag = mm.group();
                String name = attr(tag, "name");
                String prop = attr(tag, "property");
                String content = attr(tag, "content");
                if (content == null) continue;
                if (name != null && name.equalsIgnoreCase("description") && desc.isEmpty()) desc = clean(content);
                if (prop != null && prop.equalsIgnoreCase("og:description") && desc.isEmpty()) desc = clean(content);
                if (name != null && name.equalsIgnoreCase("robots")) {
                    String c = content.toLowerCase(Locale.ROOT);
                    if (c.contains("noindex") || c.contains("none")) noindex = true;
                    if (c.contains("nofollow") || c.contains("none")) nofollow = true;
                }
            }

            List<String> links = new ArrayList<>();
            Matcher am = ANCHOR.matcher(html);
            while (am.find() && links.size() < 500) {
                String tag = am.group();
                String rel = attr(tag, "rel");
                if (rel != null && rel.toLowerCase(Locale.ROOT).contains("nofollow")) continue;
                String href = attr(tag, "href");
                if (href == null) continue;
                String n = normalize(base, decode(href));
                if (n != null) links.add(n);
            }

            String body = JUNK.matcher(html).replaceAll(" ");
            body = COMMENT.matcher(body).replaceAll(" ");
            body = TAG.matcher(body).replaceAll(" ");
            String text = clean(body);
            if (text.length() > 8000) text = text.substring(0, 8000);
            if (desc.length() > 400) desc = desc.substring(0, 400);
            if (title.length() > 200) title = title.substring(0, 200);
            if (desc.isEmpty()) desc = text.length() > 200 ? text.substring(0, 200) : text;
            return new Parsed(title, desc, text, links, noindex, nofollow);
        }
    }

    static final Pattern SKIP_EXT = Pattern.compile(
            ".*\\.(jpg|jpeg|png|gif|webp|svg|ico|bmp|pdf|zip|gz|tar|rar|7z|exe|dmg|iso|mp3|mp4|avi|mov|mkv|wav|css|js|json|xml|woff2?|ttf|eot|apk|doc|docx|xls|xlsx|ppt|pptx)$",
            Pattern.CASE_INSENSITIVE);

    /** Turns any href into a canonical http(s) URL, or null if it should not be crawled. */
    static String normalize(URI base, String href) {
        try {
            href = href.trim();
            if (href.isEmpty() || href.startsWith("#")) return null;
            String lower = href.toLowerCase(Locale.ROOT);
            if (lower.startsWith("javascript:") || lower.startsWith("mailto:") || lower.startsWith("tel:") || lower.startsWith("data:"))
                return null;
            URI u = (base == null ? new URI(href) : base.resolve(href)).normalize();
            String scheme = u.getScheme() == null ? "" : u.getScheme().toLowerCase(Locale.ROOT);
            if (!scheme.equals("http") && !scheme.equals("https")) return null;
            String host = u.getHost();
            if (host == null || host.isEmpty()) return null;
            host = host.toLowerCase(Locale.ROOT);
            int port = u.getPort();
            if ((port == 80 && scheme.equals("http")) || (port == 443 && scheme.equals("https"))) port = -1;
            String path = u.getRawPath();
            if (path == null || path.isEmpty()) path = "/";
            if (SKIP_EXT.matcher(path).matches()) return null;
            String query = u.getRawQuery();
            if (query != null && query.length() > 100) return null;
            String out = scheme + "://" + host + (port > 0 ? ":" + port : "") + path + (query != null ? "?" + query : "");
            return out.length() > 1000 ? null : out;
        } catch (Exception e) {
            return null;
        }
    }

    // ================================================================== CRAWLER
    static final class Crawler {
        final Index index;
        final LinkedBlockingDeque<String> frontier = new LinkedBlockingDeque<>();
        final Set<String> seen = ConcurrentHashMap.newKeySet();
        final ConcurrentHashMap<String, AtomicLong> hostNext = new ConcurrentHashMap<>();
        final ConcurrentHashMap<String, AtomicInteger> hostPages = new ConcurrentHashMap<>();
        final ConcurrentHashMap<String, List<String>> robots = new ConcurrentHashMap<>();
        final AtomicInteger fetched = new AtomicInteger(), failed = new AtomicInteger();
        final HttpClient http = HttpClient.newBuilder()
                .connectTimeout(Duration.ofSeconds(8))
                .followRedirects(HttpClient.Redirect.NEVER)
                .build();
        volatile boolean running = false;

        Crawler(Index index) { this.index = index; }

        boolean enqueue(String rawUrl, boolean front) {
            String u = normalize(null, rawUrl);
            if (u == null || !seen.add(u)) return false;
            if (front) frontier.addFirst(u);
            else if (frontier.size() < 5_000_000) frontier.addLast(u);
            return true;
        }

        void start(List<String> seeds) {
            running = true;
            for (String s : seeds) enqueue(s, false);
            for (int i = 0; i < WORKERS; i++) Thread.ofVirtual().name("crawler-" + i).start(this::loop);
        }

        void loop() {
            while (running) {
                try {
                    if (index.size() >= MAX_PAGES) { Thread.sleep(5000); continue; }
                    String url = frontier.poll(2, TimeUnit.SECONDS);
                    if (url == null) continue;
                    String host = hostOf(url);
                    AtomicLong next = hostNext.computeIfAbsent(host, h -> new AtomicLong(0));
                    long now = System.currentTimeMillis();
                    long v = next.get();
                    if (v > now || !next.compareAndSet(v, now + DELAY_MS)) {
                        frontier.addLast(url);          // host is busy: come back later
                        Thread.sleep(40);
                        continue;
                    }
                    crawl(url, host);
                } catch (InterruptedException e) {
                    return;
                } catch (Exception e) {
                    failed.incrementAndGet();
                }
            }
        }

        void crawl(String url, String host) {
            try {
                if (hostPages.computeIfAbsent(host, h -> new AtomicInteger()).incrementAndGet() > PER_HOST) return;
                URI u = URI.create(url);
                if (!robotsAllowed(u)) return;
                Object[] res = fetch(u);
                if (res == null) { failed.incrementAndGet(); return; }
                URI finalUri = (URI) res[0];
                Parsed p = Html.parse((String) res[1], finalUri);
                fetched.incrementAndGet();
                String canon = normalize(null, finalUri.toString());
                if (canon == null) canon = finalUri.toString();
                if (!p.noindex()) {
                    String title = p.title().isBlank() ? hostOf(canon) : p.title();
                    index.add(new Doc(canon, title, p.desc(), p.text(), System.currentTimeMillis()));
                }
                if (!p.nofollow()) for (String l : p.links()) enqueue(l, false);
            } catch (Exception e) {
                failed.incrementAndGet();
            }
        }

        static void checkPublic(URI u) throws IOException {
            String scheme = u.getScheme();
            if (scheme == null || !(scheme.equals("http") || scheme.equals("https")))
                throw new IOException("bad scheme");
            if (u.getHost() == null) throw new IOException("no host");
            if (ALLOW_PRIVATE) return;
            for (InetAddress a : InetAddress.getAllByName(u.getHost())) {
                if (a.isAnyLocalAddress() || a.isLoopbackAddress() || a.isLinkLocalAddress()
                        || a.isSiteLocalAddress() || a.isMulticastAddress())
                    throw new IOException("private address blocked");
            }
        }

        /** Returns {finalUri, html} or null. Redirects are followed by hand so each hop is checked. */
        Object[] fetch(URI start) throws Exception {
            URI cur = start;
            for (int hop = 0; hop < 5; hop++) {
                checkPublic(cur);
                HttpRequest req = HttpRequest.newBuilder(cur).timeout(Duration.ofSeconds(12))
                        .header("User-Agent", USER_AGENT)
                        .header("Accept", "text/html,application/xhtml+xml")
                        .GET().build();
                HttpResponse<InputStream> r = http.send(req, HttpResponse.BodyHandlers.ofInputStream());
                try (InputStream in = r.body()) {
                    int sc = r.statusCode();
                    if (sc >= 300 && sc < 400) {
                        Optional<String> loc = r.headers().firstValue("location");
                        if (loc.isEmpty()) return null;
                        cur = cur.resolve(loc.get());
                        continue;
                    }
                    if (sc != 200) return null;
                    String ct = r.headers().firstValue("content-type").orElse("");
                    String ctl = ct.toLowerCase(Locale.ROOT);
                    if (!ctl.contains("text/html") && !ctl.contains("xhtml")) return null;
                    byte[] data = in.readNBytes(1_000_000);
                    Charset cs = StandardCharsets.UTF_8;
                    Matcher m = Pattern.compile("charset=([\\w-]+)", Pattern.CASE_INSENSITIVE).matcher(ct);
                    if (m.find()) {
                        try { cs = Charset.forName(m.group(1)); } catch (Exception ignored) { }
                    }
                    return new Object[]{cur, new String(data, cs)};
                }
            }
            return null;
        }

        // ---- robots.txt (User-agent: * and FlaxBot; Disallow rules)
        boolean robotsAllowed(URI u) {
            String key = u.getScheme() + "://" + u.getAuthority();
            List<String> rules = robots.get(key);
            if (rules == null) {
                rules = loadRobots(key);
                robots.put(key, rules);
            }
            String p = u.getRawPath() == null || u.getRawPath().isEmpty() ? "/" : u.getRawPath();
            if (u.getRawQuery() != null) p += "?" + u.getRawQuery();
            for (String r : rules) if (ruleMatches(r, p)) return false;
            return true;
        }

        List<String> loadRobots(String origin) {
            try {
                URI r = URI.create(origin + "/robots.txt");
                checkPublic(r);
                HttpResponse<InputStream> resp = http.send(
                        HttpRequest.newBuilder(r).timeout(Duration.ofSeconds(8)).header("User-Agent", USER_AGENT).GET().build(),
                        HttpResponse.BodyHandlers.ofInputStream());
                try (InputStream in = resp.body()) {
                    if (resp.statusCode() != 200) return List.of();
                    String txt = new String(in.readNBytes(512_000), StandardCharsets.UTF_8);
                    List<String> out = new ArrayList<>();
                    boolean applies = false, lastUa = false;
                    for (String line : txt.split("\\r?\\n")) {
                        int hash = line.indexOf('#');
                        if (hash >= 0) line = line.substring(0, hash);
                        int c = line.indexOf(':');
                        if (c < 0) continue;
                        String k = line.substring(0, c).trim().toLowerCase(Locale.ROOT);
                        String v = line.substring(c + 1).trim();
                        if (k.equals("user-agent")) {
                            if (!lastUa) applies = false;
                            String a = v.toLowerCase(Locale.ROOT);
                            if (a.equals("*") || a.contains("flaxbot")) applies = true;
                            lastUa = true;
                        } else {
                            lastUa = false;
                            if (k.equals("disallow") && applies && !v.isEmpty()) out.add(v);
                        }
                    }
                    return out;
                }
            } catch (Exception e) {
                return List.of();
            }
        }

        static boolean ruleMatches(String rule, String path) {
            if (rule.indexOf('*') < 0 && !rule.endsWith("$")) return path.startsWith(rule);
            boolean end = rule.endsWith("$");
            if (end) rule = rule.substring(0, rule.length() - 1);
            StringBuilder re = new StringBuilder("^");
            String[] parts = rule.split("\\*", -1);
            for (int i = 0; i < parts.length; i++) {
                if (i > 0) re.append(".*");
                re.append(Pattern.quote(parts[i]));
            }
            if (end) re.append("$");
            return Pattern.compile(re.toString()).matcher(path).find();
        }
    }

    // ================================================================== BUILT-IN STARTER INDEX
    // Lets the engine return results immediately, even before (or without) crawling.
    static final String[][] STARTER = {
            {"https://en.wikipedia.org/", "Wikipedia, the free encyclopedia", "Free online encyclopedia written and maintained by volunteers, with millions of articles in hundreds of languages."},
            {"https://www.britannica.com/", "Encyclopaedia Britannica", "Reference articles, biographies, and fact-checked knowledge on history, science, geography, and the arts."},
            {"https://github.com/", "GitHub: where software is built", "Host and review code, manage projects, and build software alongside millions of developers."},
            {"https://stackoverflow.com/", "Stack Overflow", "Question and answer site where programmers ask, answer, and learn about coding problems."},
            {"https://developer.mozilla.org/", "MDN Web Docs", "Documentation for HTML, CSS, JavaScript and web APIs, with guides and tutorials for web developers."},
            {"https://openjdk.org/", "OpenJDK", "The open-source reference implementation of the Java platform, with downloads, projects, and JDK enhancement proposals."},
            {"https://docs.oracle.com/en/java/", "Java Documentation", "Official Java documentation: tutorials, API reference, language specification, and release notes."},
            {"https://www.python.org/", "Python.org", "The official home of the Python programming language: downloads, documentation, and community news."},
            {"https://www.rust-lang.org/", "Rust Programming Language", "A language empowering everyone to build reliable and efficient software."},
            {"https://go.dev/", "The Go Programming Language", "Go is an open source language that makes it simple to build secure, scalable systems."},
            {"https://nodejs.org/", "Node.js", "Node.js is a JavaScript runtime built on the V8 engine for building fast network applications."},
            {"https://kotlinlang.org/", "Kotlin Programming Language", "A modern, concise language that runs on the JVM, Android, and the web."},
            {"https://spring.io/", "Spring | Home", "Spring makes Java simple, modern, productive, and reactive, from web apps to cloud services."},
            {"https://www.apache.org/", "The Apache Software Foundation", "Open source projects including Lucene, Kafka, Tomcat, Maven, Hadoop, and Spark."},
            {"https://lucene.apache.org/", "Apache Lucene", "High-performance full-text search library for Java, the engine behind Solr and Elasticsearch."},
            {"https://arxiv.org/", "arXiv.org", "Free distribution service and open archive of scholarly articles in physics, mathematics, and computer science."},
            {"https://www.nature.com/", "Nature", "International journal of science publishing peer-reviewed research and news across all fields."},
            {"https://www.nasa.gov/", "NASA", "News, images, missions, and research from the National Aeronautics and Space Administration."},
            {"https://www.who.int/", "World Health Organization", "Global health guidance, data, and news on diseases, vaccines, and public health emergencies."},
            {"https://www.un.org/", "United Nations", "Information on the work of the UN on peace, development, human rights, and international law."},
            {"https://www.bbc.com/", "BBC Home", "Breaking news, sport, business, culture, and analysis from around the world."},
            {"https://www.reuters.com/", "Reuters", "Global news agency covering business, markets, politics, and technology."},
            {"https://www.khanacademy.org/", "Khan Academy", "Free lessons in math, science, computing, economics, and more for learners of every age."},
            {"https://www.gutenberg.org/", "Project Gutenberg", "Over seventy thousand free ebooks, including classic literature in the public domain."},
            {"https://archive.org/", "Internet Archive", "Digital library of free books, movies, music, and the Wayback Machine archive of web pages."},
            {"https://news.ycombinator.com/", "Hacker News", "Social news site focused on computer science, startups, and entrepreneurship."},
            {"https://www.mit.edu/", "Massachusetts Institute of Technology", "MIT research, education, admissions, and news from one of the leading universities in science and engineering."},
            {"https://www.stanford.edu/", "Stanford University", "Stanford research, programs, admissions, and campus news."},
    };

    static void loadStarter(Index idx) {
        for (String[] s : STARTER)
            idx.add(new Doc(s[0], s[1], s[2], s[2], System.currentTimeMillis()));
    }

    static List<String> loadSeeds() {
        List<String> seeds = new ArrayList<>();
        Path f = Path.of(System.getProperty("seeds", "seeds.txt"));
        if (Files.exists(f)) {
            try {
                for (String l : Files.readAllLines(f))
                    if (!l.isBlank() && !l.startsWith("#")) seeds.add(l.trim());
            } catch (IOException ignored) { }
        }
        for (String[] s : STARTER) seeds.add(s[0]);
        return seeds;
    }

    // ================================================================== WEB UI
    static final String CSS = """
:root{--bg:#fff;--fg:#202124;--muted:#5f6368;--link:#1a0dab;--visited:#681da8;--line:#dfe1e5;--hover:#f8f9fa;--snip:#4d5156;--url:#202124;--foot:#f2f2f2;--shadow:0 1px 6px rgba(32,33,36,.28);--c1:#3b5bdb;--c2:#e8590c;--c3:#f08c00;--c4:#2b8a3e;--c5:#7048e8}
@media (prefers-color-scheme:dark){:root{--bg:#202124;--fg:#e8eaed;--muted:#9aa0a6;--link:#8ab4f8;--visited:#c58af9;--line:#5f6368;--hover:#303134;--snip:#bdc1c6;--url:#dadce0;--foot:#171717;--shadow:0 1px 6px rgba(0,0,0,.7)}}
*{box-sizing:border-box}
html,body{margin:0;height:100%}
body{background:var(--bg);color:var(--fg);font:14px/1.58 system-ui,-apple-system,"Segoe UI",Roboto,Arial,sans-serif}
a{color:inherit;text-decoration:none}
.top{display:flex;justify-content:flex-end;gap:20px;padding:18px 24px;font-size:13px}
.top a:hover{text-decoration:underline}
.home{display:flex;flex-direction:column;min-height:100%}
.center{flex:1;display:flex;flex-direction:column;align-items:center;justify-content:center;padding:0 16px 120px}
.logo{font-weight:500;letter-spacing:-.06em;line-height:1;margin:0}
.logo.big{font-size:clamp(64px,16vw,96px);margin-bottom:26px}
.logo.small{font-size:30px;margin-right:6px}
.logo span:nth-child(1){color:var(--c1)}.logo span:nth-child(2){color:var(--c2)}.logo span:nth-child(3){color:var(--c3)}.logo span:nth-child(4){color:var(--c4)}
.sf{width:100%;display:flex;flex-direction:column;align-items:center}
.sbox{position:relative;display:flex;align-items:center;width:min(584px,100%);height:46px;padding:0 12px 0 16px;border:1px solid var(--line);border-radius:24px;background:var(--bg)}
.sbox:hover,.sbox:focus-within{box-shadow:var(--shadow);border-color:transparent}
.sbox.open{border-radius:24px 24px 0 0;box-shadow:var(--shadow);border-color:transparent}
.sbox svg{flex:none;width:20px;height:20px;fill:var(--muted)}
.sbox input{flex:1;min-width:0;height:100%;margin:0 10px;border:0;outline:0;background:transparent;color:var(--fg);font:16px system-ui,Arial,sans-serif}
.clr{border:0;background:none;color:var(--muted);font-size:24px;line-height:1;cursor:pointer;padding:4px 6px}
.clr:focus-visible,.btns button:focus-visible,.pg a:focus-visible,.top a:focus-visible{outline:2px solid var(--link);outline-offset:2px}
#sug{position:absolute;left:-1px;right:-1px;top:100%;margin:0;padding:4px 0 12px;list-style:none;background:var(--bg);border:1px solid transparent;border-top:1px solid var(--line);border-radius:0 0 24px 24px;box-shadow:var(--shadow);z-index:20;clip-path:inset(0 -8px -8px -8px)}
#sug li{padding:6px 18px 6px 48px;cursor:pointer;font-size:16px}
#sug li.on{background:var(--hover)}
.btns{margin-top:28px;display:flex;gap:12px}
.btns button{height:36px;padding:0 16px;border:1px solid var(--hover);border-radius:4px;background:var(--hover);color:var(--fg);font:14px system-ui,Arial,sans-serif;cursor:pointer}
.btns button:hover{border-color:var(--line);box-shadow:0 1px 1px rgba(0,0,0,.1)}
.foot{background:var(--foot);border-top:1px solid var(--line);color:var(--muted);font-size:14px;padding:14px 24px;display:flex;flex-wrap:wrap;gap:8px 24px;justify-content:space-between}
.foot a:hover{text-decoration:underline}
.rh{display:flex;align-items:center;gap:24px;padding:18px 24px 14px;border-bottom:1px solid var(--line);position:sticky;top:0;background:var(--bg);z-index:10}
.rh .sf{width:auto;flex:1}
.rh .sbox{width:min(690px,100%)}
.rh nav{margin-left:auto;display:flex;gap:18px;font-size:13px;color:var(--muted)}
.wrap{max-width:652px;margin:0 0 0 180px;padding:0 16px 40px}
.stats{color:var(--muted);font-size:14px;margin:16px 0 20px}
.res{margin-bottom:28px}
.res .url{display:flex;align-items:center;gap:12px;line-height:1.3;margin-bottom:4px}
.fav{flex:none;width:28px;height:28px;border-radius:50%;background:var(--hover);border:1px solid var(--line);display:grid;place-items:center;font-size:13px;font-weight:600;color:var(--c1)}
.host{color:var(--url);font-size:14px}
.path{color:var(--muted);font-size:12px}
.res .title{display:block;color:var(--link);font-size:20px;line-height:1.3;margin:2px 0 3px;overflow-wrap:anywhere}
.res .title:visited{color:var(--visited)}
.res .title:hover{text-decoration:underline}
.snip{margin:0;color:var(--snip);max-width:600px}
.snip b{color:var(--fg);font-weight:600}
.none{margin-top:24px;max-width:600px}
.none ul{color:var(--snip);padding-left:20px}
.pg{display:flex;flex-wrap:wrap;gap:4px;margin:12px 0 0;align-items:center}
.pg a,.pg span{min-width:38px;padding:8px 10px;text-align:center;border-radius:4px;color:var(--link)}
.pg a:hover{background:var(--hover)}
.pg .cur{color:var(--fg);font-weight:600}
.page{max-width:680px;margin:40px auto;padding:0 20px}
.page h1{font-weight:500;font-size:28px}
.page p,.page li{color:var(--snip);font-size:15px;line-height:1.65}
.page form{display:flex;gap:10px;margin:18px 0}
.page input[type=text]{flex:1;height:42px;padding:0 14px;border:1px solid var(--line);border-radius:8px;background:var(--bg);color:var(--fg);font-size:15px}
.page button{height:42px;padding:0 20px;border:0;border-radius:8px;background:var(--c1);color:#fff;font-size:14px;cursor:pointer}
.note{padding:10px 14px;border-radius:8px;background:var(--hover);border:1px solid var(--line)}
code{background:var(--hover);padding:1px 6px;border-radius:4px}
@media (max-width:900px){.wrap{margin:0 auto}.rh{flex-wrap:wrap;gap:12px}.rh nav{display:none}.rh .sf{flex-basis:100%}}
""";

    static final String JS = """
(function(){
  var box=document.querySelector('.sbox'); if(!box) return;
  var inp=box.querySelector('input'), ul=document.getElementById('sug'), clr=box.querySelector('.clr');
  var items=[], idx=-1, timer=null, seq=0;
  function close(){ ul.hidden=true; box.classList.remove('open'); idx=-1; }
  function mark(){ Array.prototype.forEach.call(ul.children,function(li,i){ li.classList.toggle('on',i===idx); }); }
  function go(text){ inp.value=text; close(); inp.form.submit(); }
  function render(list){
    ul.textContent=''; items=list;
    if(!list.length){ close(); return; }
    list.forEach(function(s){
      var li=document.createElement('li'); li.setAttribute('role','option'); li.textContent=s;
      li.addEventListener('mousedown',function(e){ e.preventDefault(); go(s); });
      ul.appendChild(li);
    });
    ul.hidden=false; box.classList.add('open'); idx=-1;
  }
  function toggleClear(){ clr.hidden = inp.value.length===0; }
  inp.addEventListener('input',function(){
    toggleClear();
    clearTimeout(timer);
    var v=inp.value;
    if(!v.trim()){ close(); return; }
    var my=++seq;
    timer=setTimeout(function(){
      fetch('/suggest?q='+encodeURIComponent(v)).then(function(r){return r.json();}).then(function(d){
        if(my===seq) render(d[1]||[]);
      }).catch(function(){});
    },120);
  });
  inp.addEventListener('keydown',function(e){
    if(ul.hidden) return;
    if(e.key==='ArrowDown'){ e.preventDefault(); idx=(idx+1)%items.length; inp.value=items[idx]; mark(); }
    else if(e.key==='ArrowUp'){ e.preventDefault(); idx=(idx<=0?items.length:idx)-1; inp.value=items[idx]; mark(); }
    else if(e.key==='Escape'){ close(); }
  });
  inp.addEventListener('blur',function(){ setTimeout(close,100); });
  clr.addEventListener('click',function(){ inp.value=''; toggleClear(); close(); inp.focus(); });
  document.addEventListener('keydown',function(e){
    if(e.key==='/' && document.activeElement!==inp){ e.preventDefault(); inp.focus(); }
  });
  toggleClear();
  if(!inp.value) inp.focus();
})();
""";

    static final String FAVICON = "<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 32 32'><rect width='32' height='32' rx='8' fill='#3b5bdb'/><text x='16' y='23' font-size='20' font-family='Arial' font-weight='700' text-anchor='middle' fill='#fff'>F</text></svg>";

    static String esc(String s) {
        if (s == null) return "";
        StringBuilder sb = new StringBuilder(s.length() + 16);
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            switch (c) {
                case '&' -> sb.append("&amp;");
                case '<' -> sb.append("&lt;");
                case '>' -> sb.append("&gt;");
                case '"' -> sb.append("&quot;");
                case '\'' -> sb.append("&#39;");
                default -> sb.append(c);
            }
        }
        return sb.toString();
    }

    static String jsonStr(String s) {
        StringBuilder sb = new StringBuilder("\"");
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c == '"' || c == '\\') sb.append('\\').append(c);
            else if (c < 0x20) sb.append(String.format("\\u%04x", (int) c));
            else sb.append(c);
        }
        return sb.append('"').toString();
    }

    static String logo(boolean big, boolean link) {
        String inner = "<span>F</span><span>l</span><span>a</span><span>x</span>";
        return link ? "<a href=\"/\" class=\"logo small\" aria-label=\"Flax Search home\">" + inner + "</a>"
                : "<h1 class=\"logo big\" aria-label=\"Flax\">" + inner + "</h1>";
    }

    static String searchBox(String q, boolean withButtons) {
        StringBuilder sb = new StringBuilder();
        sb.append("<form class=\"sf\" action=\"/search\" method=\"get\" role=\"search\" autocomplete=\"off\">");
        sb.append("<div class=\"sbox\">");
        sb.append("<svg viewBox=\"0 0 24 24\" aria-hidden=\"true\"><path d=\"M15.5 14h-.79l-.28-.27A6.47 6.47 0 0 0 16 9.5 6.5 6.5 0 1 0 9.5 16c1.61 0 3.09-.59 4.23-1.57l.27.28v.79l5 4.99L20.49 19l-4.99-5zm-6 0C7.01 14 5 11.99 5 9.5S7.01 5 9.5 5 14 7.01 14 9.5 11.99 14 9.5 14z\"/></svg>");
        sb.append("<input type=\"text\" name=\"q\" value=\"").append(esc(q)).append("\" maxlength=\"200\" aria-label=\"Search\" role=\"combobox\" aria-autocomplete=\"list\" spellcheck=\"false\">");
        sb.append("<button type=\"button\" class=\"clr\" aria-label=\"Clear\" hidden>&times;</button>");
        sb.append("<ul id=\"sug\" role=\"listbox\" hidden></ul></div>");
        if (withButtons) {
            sb.append("<div class=\"btns\"><button type=\"submit\">Flax Search</button>");
            sb.append("<button type=\"submit\" formaction=\"/lucky\">I'm Feeling Lucky</button></div>");
        }
        return sb.append("</form>").toString();
    }

    static String shell(String title, String bodyClass, String body) {
        return "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">"
                + "<meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">"
                + "<title>" + esc(title) + "</title>"
                + "<link rel=\"icon\" href=\"/favicon.svg\" type=\"image/svg+xml\">"
                + "<link rel=\"stylesheet\" href=\"/static/flax.css\"></head>"
                + "<body class=\"" + bodyClass + "\">" + body
                + "<script src=\"/static/flax.js\"></script></body></html>";
    }

    static String footer(Index idx) {
        NumberFormat nf = NumberFormat.getIntegerInstance(Locale.US);
        return "<footer class=\"foot\"><span>" + nf.format(idx.size()) + " pages indexed</span>"
                + "<span><a href=\"/about\">About</a> &nbsp; <a href=\"/submit\">Submit a site</a> &nbsp; <a href=\"/status\">Status</a></span></footer>";
    }

    static String homePage(Index idx) {
        String body = "<div class=\"top\"><a href=\"/about\">About</a><a href=\"/submit\">Submit a site</a></div>"
                + "<main class=\"center\">" + logo(true, false) + searchBox("", true) + "</main>" + footer(idx);
        return shell("Flax Search", "home", body);
    }

    static String snippet(Doc d, Pattern hl) {
        String best = null;
        int pos = -1;
        if (hl != null) {
            for (String cand : new String[]{d.desc(), d.text()}) {
                if (cand == null || cand.isEmpty()) continue;
                Matcher m = hl.matcher(cand);
                if (m.find()) { best = cand; pos = m.start(); break; }
            }
        }
        if (best == null) best = d.desc() != null && !d.desc().isEmpty() ? d.desc() : d.text();
        if (best == null) best = "";
        int start = 0;
        if (pos > 70) {
            start = pos - 60;
            int sp = best.indexOf(' ', start);
            if (sp > 0 && sp < pos) start = sp + 1;
        }
        int end = Math.min(best.length(), start + 210);
        String s = best.substring(start, end);
        String prefix = start > 0 ? "\u2026 " : "";
        String suffix = end < best.length() ? " \u2026" : "";
        if (hl == null) return esc(prefix + s + suffix);
        Matcher m = hl.matcher(s);
        StringBuilder sb = new StringBuilder(esc(prefix));
        int last = 0;
        while (m.find()) {
            sb.append(esc(s.substring(last, m.start()))).append("<b>").append(esc(m.group())).append("</b>");
            last = m.end();
        }
        sb.append(esc(s.substring(last))).append(esc(suffix));
        return sb.toString();
    }

    static String crumb(String url) {
        try {
            URI u = URI.create(url);
            String p = u.getRawPath() == null ? "" : u.getRawPath();
            StringBuilder sb = new StringBuilder();
            int n = 0;
            for (String seg : p.split("/")) {
                if (seg.isEmpty()) continue;
                if (++n > 3) { sb.append(" \u203a \u2026"); break; }
                sb.append(" \u203a ").append(seg.length() > 30 ? seg.substring(0, 30) + "\u2026" : seg);
            }
            return sb.toString();
        } catch (Exception e) { return ""; }
    }

    static String resultsPage(Index idx, String q, int page, Result r, double seconds) {
        NumberFormat nf = NumberFormat.getIntegerInstance(Locale.US);
        StringBuilder sb = new StringBuilder();
        sb.append("<header class=\"rh\">").append(logo(false, true)).append(searchBox(q, false));
        sb.append("<nav><a href=\"/about\">About</a><a href=\"/submit\">Submit a site</a></nav></header>");
        sb.append("<main class=\"wrap\">");
        if (r.total() == 0) {
            sb.append("<div class=\"none\"><p>Your search &ndash; <b>").append(esc(q)).append("</b> &ndash; did not match any pages.</p>")
              .append("<p>Suggestions:</p><ul><li>Make sure all words are spelled correctly.</li>")
              .append("<li>Try different or more general keywords.</li>")
              .append("<li>Use <code>\"quotes\"</code> for exact phrases, <code>-word</code> to exclude, or <code>site:example.com</code>.</li></ul></div>");
        } else {
            sb.append("<div class=\"stats\">About ").append(nf.format(r.total())).append(" results (")
              .append(String.format(Locale.US, "%.2f", seconds)).append(" seconds)</div>");
            for (Hit h : r.hits()) {
                Doc d = h.doc();
                String host = hostOf(d.url());
                String shown = host.startsWith("www.") ? host.substring(4) : host;
                sb.append("<div class=\"res\"><div class=\"url\"><span class=\"fav\">")
                  .append(esc(shown.isEmpty() ? "?" : shown.substring(0, 1).toUpperCase(Locale.ROOT))).append("</span><div><span class=\"host\">")
                  .append(esc(shown)).append("</span><div class=\"path\">").append(esc(d.url().startsWith("https") ? "https://" : "http://"))
                  .append(esc(host)).append(esc(crumb(d.url()))).append("</div></div></div>")
                  .append("<a class=\"title\" href=\"").append(esc(d.url())).append("\" rel=\"noopener\">")
                  .append(esc(d.title().isBlank() ? d.url() : d.title())).append("</a>")
                  .append("<p class=\"snip\">").append(snippet(d, r.highlight())).append("</p></div>");
            }
            int pages = Math.min((r.total() + PAGE_SIZE - 1) / PAGE_SIZE, 100);
            if (pages > 1) {
                int from = Math.max(1, page - 4), to = Math.min(pages, from + 9);
                from = Math.max(1, to - 9);
                String base = "/search?q=" + URLEncoder.encode(q, StandardCharsets.UTF_8) + "&p=";
                sb.append("<nav class=\"pg\" aria-label=\"Pages\">");
                if (page > 1) sb.append("<a href=\"").append(base).append(page - 1).append("\">Previous</a>");
                for (int i = from; i <= to; i++) {
                    if (i == page) sb.append("<span class=\"cur\" aria-current=\"page\">").append(i).append("</span>");
                    else sb.append("<a href=\"").append(base).append(i).append("\">").append(i).append("</a>");
                }
                if (page < pages) sb.append("<a href=\"").append(base).append(page + 1).append("\">Next</a>");
                sb.append("</nav>");
            }
        }
        sb.append("</main>").append(footer(idx));
        return shell(q + " - Flax Search", "results", sb.toString());
    }

    static String infoPage(String title, String inner) {
        return shell(title + " - Flax Search",
                "info", "<header class=\"rh\">" + logo(false, true) + "<nav><a href=\"/about\">About</a><a href=\"/submit\">Submit a site</a></nav></header>"
                        + "<main class=\"page\">" + inner + "</main>");
    }

    // ================================================================== HTTP SERVER
    static final class Router implements HttpHandler {
        final Index idx;
        final Crawler crawler;
        final long started = System.currentTimeMillis();

        Router(Index idx, Crawler crawler) { this.idx = idx; this.crawler = crawler; }

        static Map<String, String> params(String raw) {
            Map<String, String> m = new HashMap<>();
            if (raw == null || raw.isEmpty()) return m;
            for (String pair : raw.split("&")) {
                int i = pair.indexOf('=');
                try {
                    String k = URLDecoder.decode(i < 0 ? pair : pair.substring(0, i), StandardCharsets.UTF_8);
                    String v = i < 0 ? "" : URLDecoder.decode(pair.substring(i + 1), StandardCharsets.UTF_8);
                    m.putIfAbsent(k, v);
                } catch (Exception ignored) { }
            }
            return m;
        }

        static void send(HttpExchange ex, int code, String type, byte[] body, String cache) throws IOException {
            Headers h = ex.getResponseHeaders();
            h.set("Content-Type", type);
            h.set("Cache-Control", cache);
            h.set("X-Content-Type-Options", "nosniff");
            h.set("X-Frame-Options", "DENY");
            h.set("Referrer-Policy", "strict-origin-when-cross-origin");
            h.set("Content-Security-Policy", "default-src 'none'; style-src 'self'; script-src 'self'; connect-src 'self'; img-src 'self' data:; form-action 'self'; base-uri 'none'; frame-ancestors 'none'");
            boolean head = ex.getRequestMethod().equalsIgnoreCase("HEAD");
            ex.sendResponseHeaders(code, head || body.length == 0 ? -1 : body.length);
            if (!head && body.length > 0) try (OutputStream os = ex.getResponseBody()) { os.write(body); }
        }

        static void html(HttpExchange ex, int code, String s) throws IOException {
            send(ex, code, "text/html; charset=utf-8", s.getBytes(StandardCharsets.UTF_8), "no-cache");
        }

        static void redirect(HttpExchange ex, int code, String to) throws IOException {
            ex.getResponseHeaders().set("Location", to);
            send(ex, code, "text/plain; charset=utf-8", new byte[0], "no-cache");
        }

        @Override
        public void handle(HttpExchange ex) throws IOException {
            try {
                String path = ex.getRequestURI().getPath();
                String method = ex.getRequestMethod().toUpperCase(Locale.ROOT);
                Map<String, String> q = params(ex.getRequestURI().getRawQuery());
                boolean read = method.equals("GET") || method.equals("HEAD");
                if (!read && !(method.equals("POST") && path.equals("/submit"))) {
                    send(ex, 405, "text/plain; charset=utf-8", "Method not allowed".getBytes(), "no-cache");
                    return;
                }
                switch (path) {
                    case "/" -> html(ex, 200, homePage(idx));
                    case "/search" -> search(ex, q);
                    case "/lucky" -> lucky(ex, q);
                    case "/suggest" -> suggest(ex, q);
                    case "/about" -> html(ex, 200, aboutPage());
                    case "/submit" -> submit(ex, method, q);
                    case "/status" -> status(ex);
                    case "/static/flax.css" -> send(ex, 200, "text/css; charset=utf-8", CSS.getBytes(StandardCharsets.UTF_8), "public, max-age=3600");
                    case "/static/flax.js" -> send(ex, 200, "text/javascript; charset=utf-8", JS.getBytes(StandardCharsets.UTF_8), "public, max-age=3600");
                    case "/favicon.svg", "/favicon.ico" -> send(ex, 200, "image/svg+xml", FAVICON.getBytes(StandardCharsets.UTF_8), "public, max-age=86400");
                    default -> html(ex, 404, infoPage("Not found",
                            "<h1>404. That&rsquo;s an error.</h1><p>The page you asked for does not exist. <a href=\"/\">Go to the Flax Search home page.</a></p>"));
                }
            } catch (Exception e) {
                e.printStackTrace();
                try { send(ex, 500, "text/plain; charset=utf-8", "Server error".getBytes(), "no-cache"); } catch (Exception ignored) { }
            } finally {
                ex.close();
            }
        }

        static String clampQuery(String q) {
            q = q == null ? "" : q.strip();
            return q.length() > 200 ? q.substring(0, 200) : q;
        }

        void search(HttpExchange ex, Map<String, String> params) throws IOException {
            String q = clampQuery(params.get("q"));
            if (q.isEmpty()) { redirect(ex, 302, "/"); return; }
            int page = 1;
            try { page = Math.max(1, Math.min(100, Integer.parseInt(params.getOrDefault("p", "1")))); } catch (Exception ignored) { }
            long t0 = System.nanoTime();
            Result r = idx.search(q, (page - 1) * PAGE_SIZE, PAGE_SIZE);
            double secs = (System.nanoTime() - t0) / 1e9;
            html(ex, 200, resultsPage(idx, q, page, r, secs));
        }

        void lucky(HttpExchange ex, Map<String, String> params) throws IOException {
            String q = clampQuery(params.get("q"));
            if (q.isEmpty()) { redirect(ex, 302, "/"); return; }
            Result r = idx.search(q, 0, 1);
            if (r.hits().isEmpty()) redirect(ex, 302, "/search?q=" + URLEncoder.encode(q, StandardCharsets.UTF_8));
            else redirect(ex, 302, r.hits().get(0).doc().url());
        }

        void suggest(HttpExchange ex, Map<String, String> params) throws IOException {
            String q = clampQuery(params.get("q"));
            StringBuilder sb = new StringBuilder("[").append(jsonStr(q)).append(",[");
            List<String> s = idx.suggest(q);
            for (int i = 0; i < s.size(); i++) {
                if (i > 0) sb.append(',');
                sb.append(jsonStr(s.get(i)));
            }
            sb.append("]]");
            send(ex, 200, "application/json; charset=utf-8", sb.toString().getBytes(StandardCharsets.UTF_8), "no-cache");
        }

        void status(HttpExchange ex) throws IOException {
            String json = "{\"indexed\":" + idx.size() + ",\"hosts\":" + idx.hostCount()
                    + ",\"crawled\":" + crawler.fetched.get() + ",\"failed\":" + crawler.failed.get()
                    + ",\"queued\":" + crawler.frontier.size() + ",\"known_urls\":" + crawler.seen.size()
                    + ",\"crawling\":" + crawler.running + ",\"target\":" + MAX_PAGES
                    + ",\"uptime_seconds\":" + (System.currentTimeMillis() - started) / 1000 + "}";
            send(ex, 200, "application/json; charset=utf-8", json.getBytes(StandardCharsets.UTF_8), "no-cache");
        }

        String aboutPage() {
            return infoPage("About", "<h1>About Flax Search</h1>"
                    + "<p>Flax Search is a search engine written in Java. It crawls public web pages, builds an inverted index, and ranks results with BM25 plus title, URL, and description boosts.</p>"
                    + "<p><b>Search tips</b></p><ul><li><code>\"exact phrase\"</code> matches the words together.</li>"
                    + "<li><code>-word</code> leaves out pages containing that word.</li>"
                    + "<li><code>site:wikipedia.org</code> limits results to one site.</li></ul>"
                    + "<p><b>Crawler</b></p><p>FlaxBot obeys <code>robots.txt</code>, <code>noindex</code>, and <code>nofollow</code>, and waits between requests to the same host. "
                    + "Site owners can block it with <code>User-agent: FlaxBot</code> in robots.txt.</p>");
        }

        void submit(HttpExchange ex, String method, Map<String, String> params) throws IOException {
            boolean local = ex.getRemoteAddress().getAddress().isLoopbackAddress();
            String msg = "";
            if (method.equals("POST")) {
                if (!local && !PUBLIC_SUBMIT) {
                    html(ex, 403, infoPage("Submit a site", "<h1>Submit a site</h1><p class=\"note\">Submissions are only accepted from the machine running Flax Search.</p>"));
                    return;
                }
                String body = new String(ex.getRequestBody().readNBytes(4096), StandardCharsets.UTF_8);
                String url = params(body).getOrDefault("url", "").strip();
                if (!url.matches("(?i)^https?://.*")) url = "https://" + url;
                if (!url.isBlank() && crawler.enqueue(url, true)) msg = "<p class=\"note\">Added to the crawl queue. It will appear in results after it is crawled.</p>";
                else msg = "<p class=\"note\">That address is invalid or already known.</p>";
            }
            html(ex, 200, infoPage("Submit a site", "<h1>Submit a site</h1><p>Add a web address to the front of the crawl queue.</p>"
                    + "<form method=\"post\" action=\"/submit\"><input type=\"text\" name=\"url\" placeholder=\"https://example.com\" maxlength=\"500\" aria-label=\"Site address\"><button type=\"submit\">Add site</button></form>" + msg));
        }
    }

    // ================================================================== MAIN
    public static void main(String[] args) throws Exception {
        Files.createDirectories(DATA);
        Path indexFile = DATA.resolve("index.bin");

        Index idx = new Index();
        idx.load(indexFile);
        if (idx.size() == 0) loadStarter(idx);
        System.out.println("Loaded " + idx.size() + " pages.");

        Crawler crawler = new Crawler(idx);
        if (CRAWL) {
            crawler.start(loadSeeds());
            System.out.println("Crawler running with " + WORKERS + " workers, target " + MAX_PAGES + " pages.");
        }

        HttpServer server = HttpServer.create(new InetSocketAddress(BIND, PORT), 256);
        server.createContext("/", new Router(idx, crawler));
        server.setExecutor(Executors.newVirtualThreadPerTaskExecutor());
        server.start();

        ScheduledExecutorService saver = Executors.newSingleThreadScheduledExecutor();
        saver.scheduleWithFixedDelay(() -> {
            try { if (idx.dirty) idx.save(indexFile); } catch (Exception e) { System.err.println("Save failed: " + e); }
        }, 60, 60, TimeUnit.SECONDS);
        Runtime.getRuntime().addShutdownHook(new Thread(() -> {
            crawler.running = false;
            try { idx.save(indexFile); } catch (Exception ignored) { }
        }));

        System.out.println("Flax Search is running at http://" + (BIND.equals("0.0.0.0") ? "localhost" : BIND) + ":" + PORT);
    }
}
