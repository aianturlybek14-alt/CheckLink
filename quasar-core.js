/* QuasarCore — автономный движок QuasarAI для приложения CheckLink (Android, iOS) и веб-портала.
   Работает целиком на устройстве: без сервера, без ключей и без платных API.
     • check(type, text, lang)   — оценка риска ссылки, QR или сообщения: те же правила, что у сервера (analyzer.py);
     • checkFile(file, lang)     — тип файла по первым байтам и имени (файл никуда не отправляется);
     • answer(question, opts)    — ответ ассистента: проверка вставленного текста, темы базы знаний, советы;
     • quiz(n, lang)             — тренажёр: n случайных ситуаций с вариантами ответа и разбором.
   Данные — quasar-kb.json (собирается tools/build_kb.py). Тот же алгоритм ответов на сервере: quasar_local.py.
   Подключение: <script src="quasar-core.js"></script>, затем QuasarCore.load().then(...). */
(function (root) {
  'use strict';
  var LANGS = ['ru', 'kk', 'en'];
  var KB = null, RX = null, loading = null;
  var CORE = 8;   // версия движка: база знаний с min_core > CORE этому движку не подходит (обновление правил «по воздуху»)
  var KK_RE = /[әғқңөұүһіӘҒҚҢӨҰҮҺІ]/g, CYR_RE = /[а-яёА-ЯЁ]/g, LAT_RE = /[a-zA-Z]/g;
  var EN_STOP = ['the', 'is', 'are', 'what', 'how', 'why', 'my', 'me', 'you', 'your', 'this', 'it', 'i', 'to', 'a', 'an', 'and', 'of',
    'in', 'from', 'can', 'should', 'do', 'does', 'hello', 'hi', 'hey', 'thanks', 'thank', 'please', 'scam', 'help', 'someone', 'got'];
  var Q_WORDS = ['что', 'как', 'почему', 'зачем', 'можно', 'правда', 'где', 'куда', 'кто', 'какой', 'какая', 'какие', 'сколько', 'если',
    'чем', 'қалай', 'неге', 'не', 'қайда', 'кім', 'қандай', 'егер', 'what', 'how', 'why', 'is', 'can', 'should', 'do', 'does', 'where',
    'which', 'who', 'if', 'are'];
  var FOLLOW = ['подробнее', 'подробней', 'еще', 'ещё', 'а', 'почему', 'как', 'зачем', 'толығырақ', 'тағы', 'неге', 'қалай', 'more', 'why', 'how', 'and', 'what'];

  /* ---------------- общие мелочи ---------------- */
  function pickLang(l) { return LANGS.indexOf(l) >= 0 ? l : 'ru'; }
  function tr(o, lg) { return o ? (o[lg] != null ? o[lg] : o.ru) : ''; }
  function norm(s) { return String(s || '').toLowerCase().replace(/ё/g, 'е').replace(/\s+/g, ' ').trim(); }
  function tokens(s) { return s.match(/[\p{L}\p{N}]+/gu) || []; }
  function count(s, re) { var m = s.match(re); return m ? m.length : 0; }
  /* Одинаковый с Python хеш (по кодовым точкам): детерминированный выбор совета и т.п. */
  function hash(s) { var h = 0; for (var ch of s) { h = (Math.imul(h, 31) + ch.codePointAt(0)) >>> 0; } return h; }
  function fill(s, v) { return String(s).replace(/\{(\w+)\}/g, function (m, k) { return v[k] != null ? v[k] : m; }); }

  /* ---------------- загрузка базы ---------------- */
  function scriptBase() {
    try {
      var cs = document.currentScript || Array.prototype.slice.call(document.scripts).filter(function (s) { return /quasar-core\.js/.test(s.src); })[0];
      if (cs && cs.src) return cs.src.replace(/[^/]*$/, '');
    } catch (e) { }
    return '';
  }
  var BASE = typeof document !== 'undefined' ? scriptBase() : '';
  function load(url) {
    if (KB) return Promise.resolve(KB);
    if (loading) return loading;
    var u = url || root.QUASAR_KB_URL || (BASE + 'quasar-kb.json');
    loading = fetch(u, { cache: 'no-cache' }).then(function (r) {
      if (!r.ok) throw new Error('kb_http_' + r.status);
      return r.json();
    }).then(function (j) {
      init(j);
      if (!SEM && typeof fetch === 'function') fetch(root.QUASAR_SEM_URL || (BASE + 'quasar-sem.json'), { cache: 'no-cache' })
        .then(function (r) { return r.ok ? r.json() : null; }).then(function (s) { if (s) semInit(s); }).catch(function () { });
      return KB;
    }).catch(function (e) { loading = null; throw e; });
    return loading;
  }
  function init(j) {
    if (!j || !j.rules || !j.topics) throw new Error('kb_bad');
    KB = j;
    var R = j.rules;
    RX = { text: [], url: new RegExp(R.url_re, 'gi'), dbl: new RegExp(j.files.double_re, 'i'),
      short: new Set(R.shorteners), tld: new Set(R.bad_tlds), sl: new Set(R.second_level) };
    R.text_rules.forEach(function (r) {
      try { RX.text.push({ code: r.code, w: r.w, re: new RegExp(r.re, 'iu') }); } catch (e) { /* очень старый движок без \p{}: правило пропускаем */ }
    });
    RX.protect = [];
    (R.protect || []).forEach(function (src) { try { RX.protect.push(new RegExp(src, 'giu')); } catch (e) { } });
    var N = R.norm;
    if (N) {
      try {
        RX.joinFrag = new RegExp(N.join_frag, 'gu'); RX.joinSingle = new RegExp(N.join_single, 'gu');
        RX.defang = new RegExp(N.defang, 'giu'); RX.hxxp = new RegExp(N.hxxp, 'giu'); RX.joinSep = /[ .\-_*·]/g;
      } catch (e) { N = null; }
    }
    RX.norm = N || null;
    var M = R.ml;                                   // 1.8.0: модель на устройстве (нет в базе - работают только правила)
    RX.ml = M && M.w ? { w: new Map(Object.keys(M.w).map(function (k) { return [k, M.w[k]]; })), b: M.b, n: M.n, t: M.t,
      min: M.word_min == null ? 1 : M.word_min, cfg: R.ml_cfg || {} } : null;
    if (RX.ml) { try { RX.ml.link = R.ml_cfg && R.ml_cfg.link_re ? new RegExp(R.ml_cfg.link_re, 'u') : null; } catch (e) { RX.ml.link = null; } }
    return KB;
  }
  function need() { if (!KB) throw new Error('QuasarCore: call load() first'); }

  /* ---------------- нормализация текста (порт analyzer.clean_text / fold, 1.7.0) ----------------
     «кoд» с латинской o, «к0д», «к о д», «пе-ре-ве-ди-те», «заблакирована», невидимые пробелы, «kaspi[.]top».
     Правила проверяются по тексту как есть и по нормализованному тексту. Данные - quasar-kb.json (rules.norm). */
  var LETTER = /\p{L}/u;
  function has(o, k) { return Object.prototype.hasOwnProperty.call(o, k); }
  function isL(ch) { return LETTER.test(ch); }
  function isCyr(ch) { var c = ch.charCodeAt(0); return ch.length === 1 && c >= 0x400 && c <= 0x4ff; }
  function isLat(ch) { return (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z'); }
  function script(s) { var c = 0, l = 0; for (var ch of s) { if (isCyr(ch)) c++; else if (isLat(ch)) l++; } return c >= l ? 'cyr' : 'lat'; }
  function mapRuns(s, ok, fn) {
    var a = Array.from(s), out = '', i = 0, n = a.length;
    while (i < n) {
      if (ok(a[i])) { var j = i; while (j < n && ok(a[j])) j++; out += fn(a.slice(i, j).join('')); i = j; }
      else { out += a[i]; i++; }
    }
    return out;
  }
  function fixWord(w, def, all) {
    var N = RX.norm, A = Array.from(w), c = 0, l = 0, t = '';
    A.forEach(function (ch) { if (isCyr(ch)) c++; else if (isLat(ch)) l++; });
    if (c && l) t = c > l ? 'cyr' : l > c ? 'lat' : def;
    else if (all && l && !c && def === 'cyr' && A.length >= 2 && A.every(function (ch) { return has(N.lat2cyr, ch); })) t = 'cyr';
    else if (all && c && !l && def === 'lat' && A.length >= 2 && A.every(function (ch) { return has(N.cyr2lat, ch); })) t = 'lat';
    else return [w, ''];
    var m = t === 'cyr' ? N.lat2cyr : N.cyr2lat;
    return [A.map(function (ch) { return has(m, ch) ? m[ch] : ch; }).join(''), t];
  }
  /* Шаг 1 (регистр сохраняется, по нему ищутся ссылки) -> [текст, слова с подменой букв в латинице] */
  function cleanText(s) {
    var N = RX.norm;
    if (!N) return [s, []];
    s = Array.from(s).filter(function (ch) { return N.invisible.indexOf(ch) < 0; }).join('');
    s = s.replace(RX.defang, '.').replace(RX.hxxp, function (m, a) { return a + 'http'; });
    var def = script(s), mixed = [];
    s = mapRuns(s, isL, function (w) {
      var r = fixWord(w, def, false), lw = r[0].toLowerCase();
      if (r[1] === 'lat' && Array.from(r[0]).length >= 3 && mixed.indexOf(lw) < 0) mixed.push(lw);
      return r[0];
    });
    return [s, mixed];
  }
  function digitsIn(s, def) {
    var N = RX.norm;
    return mapRuns(s, function (ch) { return isL(ch) || '0134560@$'.indexOf(ch) >= 0; }, function (run) {
      var A = Array.from(run), c = 0, l = 0, any = false;
      A.forEach(function (ch) { if (isL(ch)) { any = true; if (isCyr(ch)) c++; else if (isLat(ch)) l++; } });
      if (!any) return run;
      var m = (c > l || (c === l && def === 'cyr')) ? N.dig_cyr : N.dig_lat, out = A.slice();
      for (var k = 1; k < A.length - 1; k++) if (has(m, A[k]) && isL(A[k - 1]) && isL(A[k + 1])) out[k] = m[A[k]];
      return out.join('');
    });
  }
  function fuzzy(t) {
    var S = RX.norm.stems, A = Array.from(t), n = A.length;
    if (n < 6 || S.some(function (st) { return t.indexOf(st) === 0; })) return t;
    for (var i = 0; i < S.length; i++) {
      var st = S[i], B = Array.from(st), L = B.length;
      if (B[0] !== A[0]) continue;
      var ks = [L, L + 1, L - 1];
      for (var q = 0; q < 3; q++) {
        var k = ks[q];
        if (k >= 5 && k <= n && editDistance(A.slice(0, k).join(''), st) <= 1) return st + A.slice(k).join('');
      }
    }
    return t;
  }
  function squeeze(s) {
    var A = Array.from(s), out = '', i = 0, n = A.length;
    while (i < n) { var j = i; while (j < n && A[j] === A[i]) j++; out += (j - i >= 3 && isL(A[i])) ? A[i] : A.slice(i, j).join(''); i = j; }
    return out;
  }
  /* Шаг 2 (только для правил): нижний регистр, склейка, цифры в словах, подмена букв, «ооо» -> «о», сленг, опечатки */
  function fold(clean) {
    var N = RX.norm;
    if (!N) return clean;
    var s = clean.toLowerCase().split('ё').join('е');
    s = s.replace(RX.joinFrag, function (m, a, b) { return a + b.replace(RX.joinSep, ''); });
    s = s.replace(RX.joinSingle, function (m, a, b) { return a + b.replace(RX.joinSep, ''); });
    var def = script(s);
    s = digitsIn(s, def);
    s = mapRuns(s, isL, function (w) { return fixWord(w, def, true)[0]; });
    s = squeeze(s);
    s = mapRuns(s, isL, function (w) { return fuzzy(has(N.slang, w) ? N.slang[w] : w); });
    return s.replace(/\s+/gu, ' ').trim();
  }
  /* Стандартные предупреждения банков («никому не сообщайте этот код») -> пробелы той же длины -> [текст, были ли] */
  function mask(s) {
    var hit = false;
    (RX.protect || []).forEach(function (re) { var s2 = s.replace(re, function (m) { return ' '.repeat(m.length); }); if (s2 !== s) hit = true; s = s2; });
    return [s, hit];
  }

  /* ---------------- проверка ссылок (порт analyzer.analyze_url) ---------------- */
  function urlparse(u) {
    var scheme = '', rest = u, netloc = '', query = '';
    var i = u.indexOf(':');
    if (i > 0 && /^[A-Za-z]/.test(u) && /^[A-Za-z0-9+\-.]+$/.test(u.slice(0, i))) { scheme = u.slice(0, i).toLowerCase(); rest = u.slice(i + 1); }
    if (rest.slice(0, 2) === '//') {
      var end = rest.length;
      '/?#'.split('').forEach(function (ch) { var k = rest.indexOf(ch, 2); if (k >= 0 && k < end) end = k; });
      netloc = rest.slice(2, end); rest = rest.slice(end);
    }
    var h = rest.indexOf('#'); if (h >= 0) rest = rest.slice(0, h);
    var q = rest.indexOf('?'); if (q >= 0) { query = rest.slice(q + 1); rest = rest.slice(0, q); }
    var host = netloc.slice(netloc.lastIndexOf('@') + 1);
    if (host.charAt(0) === '[') { var e = host.indexOf(']'); host = e > 0 ? host.slice(1, e) : host.slice(1); }
    else host = host.split(':')[0];
    return { scheme: scheme, netloc: netloc, path: rest, query: query, hostname: host.toLowerCase() };
  }
  function skeleton(s) {
    s = s.toLowerCase().split('rn').join('m').split('vv').join('w');
    var M = { '0': 'o', '1': 'i', 'l': 'i', '3': 'e', '5': 's', '$': 's' }, o = '';
    for (var ch of s) o += M[ch] || ch;
    return o;
  }
  function editDistance(a, b) {
    var A = Array.from(a), B = Array.from(b), prev = [], j;
    for (j = 0; j <= B.length; j++) prev.push(j);
    for (var i = 1; i <= A.length; i++) {
      var cur = [i];
      for (j = 1; j <= B.length; j++) cur.push(Math.min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (A[i - 1] !== B[j - 1] ? 1 : 0)));
      prev = cur;
    }
    return prev[prev.length - 1];
  }
  function registered(host) {
    var p = host.split('.');
    return (p.length >= 3 && RX.sl.has(p[p.length - 2]) ? p.slice(-3) : p.slice(-2)).join('.');
  }
  function analyzeUrl(raw, bareOk, mixed) {
    var R = KB.rules, W = R.url_weights;
    var u = raw.trim().replace(/[.,;:!?)»"']+$/, '');
    var p = urlparse(u.indexOf('://') >= 0 ? u : 'http://' + u), host = p.hostname, flags = [];
    if (!host) return [0, []];
    var reg = registered(host);
    if (p.scheme === 'http' && !(bareOk && u.indexOf('://') < 0)) flags.push('no_https');   // «Kaspi.kz» в тексте: схема неизвестна
    if (/^\d{1,3}(\.\d{1,3}){3}$/.test(host)) flags.push('ip_host');
    if (p.netloc.indexOf('@') >= 0) flags.push('at_sign');
    if (host.indexOf('xn--') === 0 || host.indexOf('.xn--') >= 0) flags.push('punycode');
    if ((mixed || []).some(function (w) { return host.indexOf(w) >= 0; })) flags.push('homoglyph');
    if (RX.short.has(host) || RX.short.has(reg)) flags.push('shortener');
    if (RX.tld.has(host.split('.').pop())) flags.push('bad_tld');
    if (count(host, /\./g) >= 4) flags.push('many_sub');
    var pq = (host + ' ' + p.path + '?' + p.query).toLowerCase();   // слова-приманки и в имени сайта, и в пути
    if (R.path_words.some(function (w) { return pq.indexOf(w) >= 0; })) flags.push('path_words');
    if (/\.apk$/.test(p.path.toLowerCase())) flags.push('apk');
    var hs = skeleton(host), label = skeleton(reg.split('.')[0]);
    var brands = Object.keys(R.brands);
    for (var b = 0; b < brands.length; b++) {
      var doms = R.brands[brands[b]];
      if (doms.some(function (d) { return host === d || host.slice(-(d.length + 1)) === '.' + d; })) break;   // официальный домен
      var bs = skeleton(brands[b]);
      if (hs.indexOf(bs) >= 0 || (bs.length >= 5 && label.length >= 5 && editDistance(label, bs) <= 1)) { flags.push('brand_fake'); break; }
    }
    return [flags.reduce(function (s, c) { return s + W[c]; }, 0), flags];
  }
  function levelOf(score) { var t = KB.rules.levels_at; return score >= t.dangerous ? 'dangerous' : score >= t.suspicious ? 'suspicious' : 'low'; }
  function result(level, score, codes, urls, lg, mlHit, semFam) {
    var R = KB.rules;
    var out = { level: level, score: score, label: tr(R.levels[level], lg),
      reasons: codes.map(function (c) { return { code: c, text: mlHit && c === mlHit[0] ? mlReason(c, mlHit[1], lg) : c === 'sem_match' ? semReason(semFam, lg) : tr(R.reasons[c], lg) }; }),
      advice: tr(R.advice[level], lg).slice(), urls: urls, disclaimer: tr(R.disclaimer, lg) };
    if (mlHit && mlHit[1].length) out.ml_words = mlHit[1].slice();
    return out;
  }
  /* ---------------- 1.8.3: семантический слой (тот же расчёт, что analyzer.sem_score) ----------------
     Текст -> признаки (фрагменты 3-5 букв, слова, пары слов) -> FNV-1a по UTF-8 -> корзина и знак -> сумма строк
     int8-матрицы W (целые числа) -> косинус с прототипами схем и обычных сообщений. Данные - quasar-sem.json
     (рядом с базой или «по воздуху» с GitHub Pages). Нет файла - слой просто не работает, правила и модель остаются. */
  var SEM = null, SEM_W = 25;
  function b64i8(b64) {
    var bin = typeof atob === 'function' ? atob(b64) : Buffer.from(b64, 'base64').toString('binary');
    var u = new Uint8Array(bin.length);
    for (var i = 0; i < bin.length; i++) u[i] = bin.charCodeAt(i);
    return new Int8Array(u.buffer);
  }
  function semInit(j) {
    if (!j || !j.W || !j.P || !j.lab || (+j.min_core || 0) > CORE) return false;
    if (SEM && (+j.rev || 0) < SEM.rev) return false;              // не откатываемся на старую базу смыслов
    var dim = j.dim, P = b64i8(j.P), n = j.lab.length, pn = new Float64Array(n);
    for (var k = 0; k < n; k++) { var a = 0; for (var d = 0; d < dim; d++) { var v = P[k * dim + d]; a += v * v; } pn[k] = Math.sqrt(a); }
    SEM = { rev: +j.rev || 0, dim: dim, mask: j.buckets - 1, W: b64i8(j.W), P: P, pn: pn, lab: j.lab, fam: j.fam, t: j.t,
      lo: j.n[0], hi: j.n[1], minw: j.min_words || 3 };
    return true;
  }
  function fnv(str) {
    var h = 2166136261;
    for (var ch of str) {
      var c = ch.codePointAt(0), b;
      if (c < 0x80) b = [c];
      else if (c < 0x800) b = [0xc0 | (c >> 6), 0x80 | (c & 63)];
      else if (c < 0x10000) b = [0xe0 | (c >> 12), 0x80 | ((c >> 6) & 63), 0x80 | (c & 63)];
      else b = [0xf0 | (c >> 18), 0x80 | ((c >> 12) & 63), 0x80 | ((c >> 6) & 63), 0x80 | (c & 63)];
      for (var i = 0; i < b.length; i++) h = Math.imul(h ^ b[i], 16777619) >>> 0;
    }
    return h;
  }
  function semFeats(s, lo, hi) {
    var out = new Set(), prev = null;
    mlWords(s).forEach(function (w) {
      out.add('w ' + w);
      mlGrams(w, lo, hi).forEach(function (g) { out.add(g); });
      if (prev !== null) out.add('b ' + prev + ' ' + w);
      prev = w;
    });
    return Array.from(out);
  }
  function semScore(s) {
    var S = SEM;
    if (!S || mlWords(s).length < S.minw) return null;
    var q = new Int32Array(S.dim), hit = false, d;
    semFeats(s, S.lo, S.hi).forEach(function (f) {
      var h = fnv(f), r = (h & S.mask) * S.dim, sg = h >>> 31 ? -1 : 1;
      for (d = 0; d < S.dim; d++) q[d] += sg * S.W[r + d];
      hit = true;
    });
    var nq = 0;
    for (d = 0; d < S.dim; d++) nq += q[d] * q[d];
    if (!hit || !nq) return null;
    nq = Math.sqrt(nq);
    var b1 = -1, b0 = -1, fam = -1;
    for (var k = 0; k < S.lab.length; k++) {
      var dot = 0, o = k * S.dim;
      for (d = 0; d < S.dim; d++) dot += q[d] * S.P[o + d];
      var c = dot / (nq * S.pn[k]);
      if (S.lab[k] >= 0) { if (c > b1) { b1 = c; fam = S.lab[k]; } } else if (c > b0) b0 = c;
    }
    var t = S.t[script(s)];
    return [b1 >= t.tau && b1 - b0 >= t.margin, b1, b0, fam];
  }
  function semReason(fam, lg) {
    var f = SEM && SEM.fam[fam] ? SEM.fam[fam][{ ru: 0, kk: 1, en: 2 }[lg] || 0] : '';
    return tr(KB.rules.reasons.sem_match, lg).replace('{f}', f);
  }
  /* ---------------- 1.8.0: модель на устройстве (тот же расчёт, что analyzer.ml_score) ---------------- */
  var ND = /\p{Nd}/u, LN = /[\p{L}\p{N}]/u;
  function mlWords(s) {
    var o = '';
    for (var ch of s) o += ND.test(ch) ? '0' : LN.test(ch) ? ch : ' ';
    return o.split(' ').filter(Boolean).slice(0, 200).map(function (w) { return Array.from(w).slice(0, 24).join(''); });
  }
  function mlGrams(word, lo, hi) {
    var P = Array.from(' ' + word + ' '), out = [];
    for (var n = lo; n <= hi; n++) for (var i = 0; i + n <= P.length; i++) out.push(P.slice(i, i + n).join(''));
    return out;
  }
  function mlScore(s) {
    var M = RX.ml;
    if (!M) return null;
    var seen = new Map(), per = [];
    mlWords(s).forEach(function (word) {
      var ws = 0;
      new Set(mlGrams(word, M.n[0], M.n[1])).forEach(function (g) {
        if (M.w.has(g)) { var v = M.w.get(g); ws += v; if (!seen.has(g)) seen.set(g, v); }
      });
      per.push([word, ws]);
    });
    var z = M.b;
    seen.forEach(function (v) { z += v; });
    var top = [], used = new Set();
    per.slice().sort(function (a, b) { return b[1] - a[1]; }).forEach(function (p) {
      if (p[1] < M.min || used.has(p[0]) || /^0+$/.test(p[0]) || top.length >= 3) return;
      used.add(p[0]); top.push(p[0]);
    });
    return [z, top];
  }
  function mlReason(code, words, lg) {
    var t = tr(KB.rules.reasons[code], lg);
    if (words.length) t += '. ' + tr(KB.rules.ml_words, lg).replace('{w}', words.map(function (w) { return '«' + w + '»'; }).join(', '));
    return t;
  }

  /* 1.8.2: только номер телефона - страна и тип номера (как analyzer.phone_check на сервере) */
  function phoneCheck(raw) {
    var t = String(raw).trim(), d = t.replace(/\D/g, ''), intl = t.charAt(0) === '+' || t.slice(0, 2) === '00';
    if (t.slice(0, 2) === '00') d = d.slice(2);
    if (!intl && d.length === 11 && d.charAt(0) === '8') d = '7' + d.slice(1);
    else if (!intl && d.length === 10 && '79'.indexOf(d.charAt(0)) >= 0) d = '7' + d;
    if (d.length <= 6 || d.indexOf('7800') === 0 || d.indexOf('8800') === 0) return ['unknown', 10, ['phone_note', 'phone_short', 'phone_rule']];
    if (d.charAt(0) === '7' && d.length === 11) {
      if ('67'.indexOf(d.charAt(1)) >= 0) return ['unknown', 0, ['phone_note', 'phone_kz', 'phone_rule']];
      return ['suspicious', 30, ['phone_note', 'phone_ru', 'phone_rule']];
    }
    if (d.charAt(0) !== '7' && d.length >= 8 && d.length <= 15 && intl) return ['suspicious', 40, ['phone_note', 'phone_foreign', 'phone_rule']];
    return ['unknown', 0, ['phone_note', 'phone_only', 'phone_rule']];
  }
  /* type: link | qr | sms | call. Результат как у сервера: {level, score, label, reasons[{code,text}], advice[], urls[], disclaimer} */
  function check(type, content, lang) {
    need();
    var lg = pickLang(lang), codes = [], score = 0, urls = [], mlHit = null, semFam = -1;
    content = String(content || '').trim();
    if (type === 'call' && /^[+\d\s()\-]{3,20}$/.test(content) && content.replace(/\D/g, '').length >= 3) {
      var ph = phoneCheck(content);
      return result(ph[0], ph[1], ph[2], urls, lg);
    }
    var cl = cleanText(content), clean = cl[0], mixed = cl[1], bare = type === 'sms' || type === 'call';
    RX.url.lastIndex = 0;
    var found = [], m;
    while ((m = RX.url.exec(clean))) { found.push(m[0]); if (!m[0]) RX.url.lastIndex++; }
    if ((type === 'link' || type === 'qr') && !found.length && clean.indexOf(' ') < 0) found = [clean];
    var us = 0;
    found.slice(0, 5).forEach(function (raw) {
      var r = analyzeUrl(raw, bare, mixed);
      urls.push({ url: Array.from(raw).slice(0, 200).join(''), score: r[0] });
      us = Math.max(us, r[0]);
      r[1].forEach(function (x) { if (codes.indexOf(x) < 0) codes.push(x); });
    });
    score += us;
    if (type !== 'link' || content.split(/\s+/).filter(Boolean).length > 1) {
      var tc = {}, a = mask(clean), b = mask(fold(clean));
      RX.text.forEach(function (r) {
        if (r.re.test(a[0]) || r.re.test(b[0])) { tc[r.code] = 1; score += r.w; if (codes.indexOf(r.code) < 0) codes.push(r.code); }
      });
      if (tc.official_claim && KB.rules.combo_base.some(function (c) { return tc[c]; })) score += 15;
      if (tc.money && (tc.foreign_card || tc.urgency || tc.link_action || us || (RX.ml && RX.ml.link && RX.ml.link.test(b[0])))) codes.push('hack_warning');
      var ml = mlScore(b[0]);
      if (ml) {
        var z = ml[0], t = RX.ml.t[script(b[0])], C = RX.ml.cfg, tk = Object.keys(tc), lw = !!(RX.ml.link && RX.ml.link.test(b[0]));
        if (z >= t.strong) { score += C.strong; codes.push('ml_strong'); mlHit = ['ml_strong', ml[1]]; }
        else if (z >= t.weak && codes.length) { score += C.weak; codes.push('ml_weak'); mlHit = ['ml_weak', ml[1]]; }
        else if (z < t.weak && tk.length === 1 && tc.money && !us && !lw) { codes[codes.indexOf('money')] = 'money_verify'; score = Math.min(score, C.money_cap); }
        else if (z <= t.calm && tk.length === 1 && C.calm_rules.indexOf(tk[0]) >= 0 && !us && !lw) { score = Math.max(score - C.calm, 0); codes.push('ml_calm'); }
      }
      if (SEM && codes.indexOf('money_verify') < 0 && type !== 'link') {
        var sm = semScore(b[0]);
        if (sm && sm[0]) { score += SEM_W; codes.push('sem_match'); semFam = sm[3]; }
      }
      if ((a[1] || b[1]) && !codes.length) codes = ['warning_text'];
    }
    score = Math.min(score, 100);
    if (!codes.length) codes = ['no_signals'];
    return result(levelOf(score), score, codes, urls, lg, mlHit, semFam);
  }

  /* ---------------- проверка файла ---------------- */
  function sizeText(n, lg) {
    var U = { ru: ['Б', 'КБ', 'МБ'], kk: ['Б', 'КБ', 'МБ'], en: ['B', 'KB', 'MB'] }[lg];
    return n < 1024 ? n + ' ' + U[0] : n < 1048576 ? Math.round(n / 1024) + ' ' + U[1] : (n / 1048576).toFixed(1) + ' ' + U[2];
  }
  /* Синхронная часть: имя, размер и первые байты (Uint8Array) */
  function fileInfo(name, size, head, lang) {
    need();
    var F = KB.files, lg = pickLang(lang), W = F.weights, codes = [], vars = {}, score = 0;
    var hx = Array.prototype.map.call(head || [], function (x) { return ('0' + x.toString(16)).slice(-2); }).join('');
    var sig = null;
    for (var i = 0; i < F.sigs.length; i++) if (hx.indexOf(F.sigs[i][0]) === 0) { sig = F.sigs[i]; break; }
    name = String(name || '');
    var low = name.toLowerCase(), dot = low.lastIndexOf('.'), ext = dot > 0 ? low.slice(dot + 1) : '';
    var add = function (c) { codes.push(c); score += W[c] || 0; };
    vars.ext = ext; vars.type = sig ? tr(sig[1], lg) : '';
    if (!size) codes.push('empty');
    if (/[‮‭]/.test(name)) add('rtlo');
    if (ext === 'apk') add('apk');
    else if (F.ext_exe.indexOf(ext) >= 0) add('exe');
    else if (F.ext_macro.indexOf(ext) >= 0) add('macro');
    if (RX.dbl.test(low)) add('double_ext');
    if (sig) {
      if (sig[2] === 'exe' && F.ext_exe.indexOf(ext) < 0 && F.ext_bin_ok.indexOf(ext) < 0) add('sig_exe');
      else if (F.ext_type[ext] && F.ext_type[ext] !== sig[2]) add('sig_mismatch');
    } else if (F.ext_type[ext] && size >= 16) add('sig_unknown');
    score = Math.min(100, score);
    var level = levelOf(score);
    if (!codes.length) codes.push('none');
    return { name: name, size: size, sizeText: sizeText(size, lg), type: sig ? sig[2] : '', typeName: sig ? tr(sig[1], lg) : tr(F.unknown_type, lg),
      level: level, score: score, label: tr(KB.rules.levels[level], lg),
      reasons: codes.map(function (c) { return { code: c, text: fill(tr(F.reasons[c], lg), vars) }; }),
      advice: [tr(F.advice[level], lg)] };
  }
  function checkFile(file, lang) {
    need();
    return file.slice(0, 16).arrayBuffer().then(function (b) { return fileInfo(file.name, file.size, new Uint8Array(b), lang); });
  }

  /* ---------------- ассистент ---------------- */
  function detectLang(text, ui) {
    ui = pickLang(ui);
    var kk = count(text, KK_RE), cyr = count(text, CYR_RE) + kk, lat = count(text, LAT_RE);
    if (kk >= 1 && cyr >= 3) return 'kk';
    if (cyr === 0 && lat >= 3) {
      if (ui === 'en') return 'en';
      var tk = tokens(text.toLowerCase());
      return tk.some(function (w) { return EN_STOP.indexOf(w) >= 0; }) ? 'en' : ui;
    }
    if (cyr > lat && ui === 'en') return 'ru';
    return ui;
  }
  function kwMatch(tok, k) {
    if (k.length <= 2) return tok === k;
    if (k.length === 3) return tok.indexOf(k) === 0 && tok.length <= 6;
    return tok.indexOf(k) === 0;
  }
  /* Фраза: все слова, кроме последнего, совпадают целиком, последнее — по началу; exact=true — целиком все */
  function phraseIn(tj, k, exact) {
    var pt = tokens(norm(k)).join(' ');
    return pt ? tj.indexOf(' ' + pt + (exact ? ' ' : '')) >= 0 : false;
  }
  function scoreKw(kws, tj, toks, exact) {
    var s = 0;
    kws.forEach(function (kw) {
      var k = norm(kw);
      if (/[\s-]/.test(k)) { if (phraseIn(tj, k, exact)) s += 3; }
      else if (toks.some(function (t) { return exact ? t === k : kwMatch(t, k); })) s += 1;
    });
    return s;
  }
  function bestTopic(tj, toks) {
    var best = null, bs = 0;
    KB.topics.forEach(function (t) { var s = scoreKw(t.kw, tj, toks, false); if (s > bs) { bs = s; best = t; } });
    return best;
  }
  function topicById(id) { for (var i = 0; i < KB.topics.length; i++) if (KB.topics[i].id === id) return KB.topics[i]; return null; }
  function P(k, lg) { return tr(KB.phrases[k], lg); }
  function topicAnswer(t, lg, more, h) {
    var L = [more ? P('more', lg) + ': ' + tr(t.title, lg) : t.icon + ' ' + tr(t.title, lg), '', tr(t.summary, lg)];
    var signs = tr(t.signs, lg) || [], steps = tr(t.steps, lg) || [];
    if (signs.length && !more) { L.push('', P('signs', lg) + ':'); signs.forEach(function (s) { L.push('• ' + s); }); }
    if (steps.length) { L.push('', P('steps', lg) + ':'); steps.forEach(function (s, i) { L.push((i + 1) + '. ' + s); }); }
    if (more) {
      L.push('', P('tip', lg) + ': ' + tr(KB.tips[h % KB.tips.length], lg));
      var rel = KB.topics.filter(function (x) { return x.cat === t.cat && x.id !== t.id; }).slice(0, 3);
      if (rel.length) L.push(P('see_also', lg) + ': ' + rel.map(function (x) { return tr(x.title, lg); }).join('; '));
    }
    return L.join('\n');
  }
  function hostOf(raw) {
    var u = raw.trim().replace(/[.,;:!?)»"']+$/, '');
    return urlparse(u.indexOf('://') >= 0 ? u : 'http://' + u).hostname;
  }
  function officialHosts(res) {
    var B = KB.rules.brands, out = [];
    res.urls.forEach(function (x) {
      var host = hostOf(x.url);
      if (!host || out.indexOf(host) >= 0) return;
      var ok = Object.keys(B).some(function (k) { return B[k].some(function (d) { return host === d || host.slice(-(d.length + 1)) === '.' + d; }); });
      if (ok) out.push(host);
    });
    return out;
  }
  function codeTopic(codes, only) {
    for (var i = 0; i < KB.code_priority.length; i++) {
      var c = KB.code_priority[i];
      if (codes.indexOf(c) >= 0 && (!only || only.indexOf(c) >= 0)) return topicById(KB.topic_by_code[c]);
    }
    return null;
  }
  function checkAnswer(res, codes, kwTopic, lg) {
    var L = [P('verdict', lg) + ': ' + res.label + ' — ' + res.score + '/100'];
    if (codes.length) { L.push('', P('reasons', lg) + ':'); res.reasons.forEach(function (r) { if (r.code !== 'no_signals') L.push('• ' + r.text); }); }
    else L.push('', P('no_signals', lg));
    officialHosts(res).forEach(function (host) { L.push('', fill(P('official', lg), { host: host })); });
    L.push('', P('advice', lg) + ':');
    res.advice.forEach(function (a, i) { L.push((i + 1) + '. ' + a); });
    var rel = codeTopic(codes, null);
    if (!rel && res.level !== 'low') rel = kwTopic;
    if (rel) L.push('', P('related', lg) + ': ' + tr(rel.title, lg) + '. ' + tr(rel.summary, lg));
    L.push('', P('disclaimer', lg));
    return L.join('\n');
  }
  function fallback(lg, h) {
    var ts = ['sms_phishing', 'bank_call', 'relative'].map(function (id) { return tr(topicById(id).title, lg); }).join(', ');
    return fill(P('fallback', lg), { topics: ts }) + '\n\n' + P('tip', lg) + ': ' + tr(KB.tips[h % KB.tips.length], lg);
  }
  /* opts: {lang, history:[{role,content}]} -> текст ответа (обычный текст с переносами строк) */
  function answer(question, opts) { return answerFull(question, opts).text; }
  /* -> {text, res}: res - результат check('sms'), только если в текст вошёл вердикт проверки (иначе null).
     По нему приложение рисует карточку риска без сети - и цифра на карточке та же, что в тексте. */
  function answerFull(question, opts) {
    need();
    opts = opts || {};
    var text = Array.from(String(question || '').trim()).slice(0, 4000).join('');
    var lg = detectLang(text, opts.lang), nt = norm(text), toks = tokens(nt), tj = ' ' + toks.join(' ') + ' ', h = hash(nt);
    if (!toks.length) return { text: fallback(lg, h), res: null };
    var res = check('sms', text, lg);
    var codes = res.reasons.map(function (r) { return r.code; }).filter(function (c) { return c !== 'no_signals' && c !== 'phone_only' && c !== 'phone_rule' && c !== 'phone_note' && c !== 'hack_warning'; });
    var question_ = text.indexOf('?') >= 0 || Q_WORDS.indexOf(toks[0]) >= 0;
    var topic = codeTopic(codes, KB.strong_codes) || bestTopic(tj, toks);
    if (res.urls.length || (codes.length && res.score >= 25 && (!question_ || toks.length > 14 || res.level === 'dangerous'))) return { text: checkAnswer(res, codes, topic, lg), res: res };
    var small = null;
    if (toks.length <= 6) {
      ['who', 'greet', 'thanks'].some(function (k) { if (scoreKw(KB.small[k].kw, tj, toks, true) > 0) { small = k; return true; } return false; });
    }
    if (small && (!topic || toks.length <= 3)) return { text: tr(KB.small[small].text, lg), res: null };
    if (topic) return { text: topicAnswer(topic, lg, false, h), res: null };
    var hist = (opts.history || []).filter(function (m) { return m && m.role === 'user' && typeof m.content === 'string'; });
    if (hist.length && toks.length <= 8 && FOLLOW.indexOf(toks[0]) >= 0) {
      for (var i = hist.length - 1; i >= 0; i--) {
        var pn = norm(hist[i].content), pt = tokens(pn);
        if (pn === nt) continue;
        var prev = bestTopic(' ' + pt.join(' ') + ' ', pt);
        if (prev) return { text: topicAnswer(prev, lg, true, h), res: null };
      }
    }
    if (codes.length) return { text: checkAnswer(res, codes, null, lg), res: res };
    return { text: fallback(lg, h), res: null };
  }

  /* ---------------- тренажёр ---------------- */
  function rng(seed) {   // mulberry32: воспроизводимая последовательность для одного seed
    var a = seed >>> 0;
    return function () { a = (a + 0x6D2B79F5) >>> 0; var t = a; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
  }
  function shuffle(a, r) { a = a.slice(); for (var i = a.length - 1; i > 0; i--) { var j = Math.floor(r() * (i + 1)), t = a[i]; a[i] = a[j]; a[j] = t; } return a; }
  function pick(a, r) { return a[Math.floor(r() * a.length)]; }
  function quizVars(tpl, lg, r) {
    var V = KB.quiz.vars, banks = V.brands.filter(function (b) { return !b.gov; });
    var brand = tpl.brand ? V.brands.filter(function (b) { return b.id === tpl.brand; })[0] : pick(banks, r);
    var fakes = shuffle(brand.fakes, r), mi = Math.floor(r() * V.market.length);
    var code = String(1000 + Math.floor(r() * 90000));
    return { brand: brand.name, bfile: brand.name.replace(/\s+/g, ''), real: brand.real, fake: fakes[0], fake2: fakes[1] || pick(banks.filter(function (b) { return b !== brand; }), r).fakes[0],
      amount: pick(V.amount, r), lowprice: pick(V.lowprice, r), paydomain: pick(V.paydomain, r), parcel: pick(V.parcel, r),
      courier: tr(pick(V.courier, r), lg), market: V.market[mi], mfake: V.mfake[mi % V.mfake.length], votefake: pick(V.votefake, r),
      metafake: pick(V.metafake, r), rel: tr(pick(V.rel, r), lg), code: code, qrurl: 'http://' + fakes[0] + '/login/verify?id=' + code };
  }
  /* n ситуаций из разных категорий; seed — для воспроизводимости (по умолчанию случайный) */
  function quiz(n, lang, seed) {
    need();
    var lg = pickLang(lang), r = rng(seed == null ? Math.floor(Math.random() * 4294967296) : seed), Q = KB.quiz;
    n = Math.max(1, Math.min(n || 10, Q.templates.length));
    var groups = {};
    shuffle(Q.templates, r).forEach(function (t) { (groups[t.cat] = groups[t.cat] || []).push(t); });
    var cats = shuffle(Object.keys(groups), r), chosen = [];
    while (chosen.length < n) {
      var took = false;
      for (var i = 0; i < cats.length && chosen.length < n; i++) { var g = groups[cats[i]]; if (g.length) { chosen.push(g.shift()); took = true; } }
      if (!took) break;
    }
    return shuffle(chosen, r).map(function (t, i) {
      var v = quizVars(t, lg, r);
      return { n: i + 1, id: t.id, cat: t.cat, catLabel: tr(Q.cats[t.cat], lg), q: fill(tr(t.q, lg), v), explain: fill(tr(t.explain, lg), v),
        opts: shuffle(t.opts, r).map(function (o) { return { t: fill(tr(o.t, lg), v), ok: !!o.ok, why: o.why ? fill(tr(o.why, lg), v) : '' }; }) };
    });
  }

  /* Где в тексте сработали правила проверки: [{s, e, code, text}] без пересечений, по порядку.
     Подсветка на сайте и в приложении строится по тем же правилам, что и оценка, поэтому не спорит с ней. */
  function highlight(content, lang) {
    need();
    var lg = pickLang(lang), text = mask(String(content || '').slice(0, 4000))[0], raw = [];
    RX.text.forEach(function (r) {
      var g = new RegExp(r.re.source, 'giu'), m, n = 0;
      while ((m = g.exec(text)) && n < 20) { if (!m[0]) { g.lastIndex++; continue; } raw.push({ s: m.index, e: m.index + m[0].length, code: r.code, w: r.w }); n++; }
    });
    var u = new RegExp(RX.url.source, 'gi'), mu, k = 0;
    while ((mu = u.exec(text)) && k < 20) { if (!mu[0]) { u.lastIndex++; continue; } raw.push({ s: mu.index, e: mu.index + mu[0].length, code: 'link', w: 0 }); k++; }
    // 1.8.0: слова, на которые сильнее всего опиралась модель на устройстве (если она сработала)
    try {
      var cr = check('sms', content, lang), low = text.toLowerCase().replace(/ё/g, 'е'), mc = (cr.reasons || []).filter(function (x) { return /^ml_(strong|weak)$/.test(x.code); })[0];
      (mc ? cr.ml_words || [] : []).forEach(function (w) {
        var i = low.indexOf(w);
        if (i >= 0 && low.length === text.length) raw.push({ s: i, e: i + w.length, code: mc.code, w: 0 });
      });
    } catch (e) { }
    raw.sort(function (a, b) { return a.s - b.s || (b.e - b.s) - (a.e - a.s); });
    var out = [], end = -1;
    raw.forEach(function (x) { if (x.s >= end) { out.push(x); end = x.e; } });
    return out.map(function (x) {
      var rs = KB.rules.reasons[x.code];
      return { s: x.s, e: x.e, code: x.code, w: x.w, text: rs ? tr(rs, lg) : '' };
    });
  }

  /* Надёжность пароля — одна оценка для сайта и приложения. Работает без базы знаний и без сети:
     пароль никуда не отправляется. bits — оценка энтропии с поправками на словарные слова, раскладку, повторы и годы;
     lv: 0 очень слабый … 4 очень надёжный; is — коды замечаний (pwShort, pwDigits, pwCommon, pwSeq, pwRep, pwYear, pwPattern, pwMix). */
  var PW_COMMON = ['password', 'passw0rd', 'qwerty', '123456', '111111', '000000', 'iloveyou', 'admin', 'welcome', 'monkey', 'dragon',
    'letmein', 'football', 'baseball', 'master', 'sunshine', 'princess', 'superman', 'kaspi', 'halyk', 'almaty', 'astana', 'kazakhstan',
    'qazaqstan', 'parol', 'пароль', 'love', 'secret', 'privet', 'привет', 'qwertyuiop', 'asdfgh', 'zxcvbn'];
  var PW_SEQ = '0123456789 abcdefghijklmnopqrstuvwxyz qwertyuiop asdfghjkl zxcvbnm йцукенгшщзхъ фывапролджэ ячсмитьбю';
  function password(p) {
    p = String(p || '');
    var low = p.toLowerCase(), is = [], pool = 0, chars = Array.from(p);
    if (/[a-z]/.test(p)) pool += 26;
    if (/[A-Z]/.test(p)) pool += 26;
    if (/\d/.test(p)) pool += 10;
    if (/[^A-Za-z0-9а-яёәғқңөұүһіА-ЯЁӘҒҚҢӨҰҮҺІ]/.test(p)) pool += 33;
    if (/[а-яёәғқңөұүһі]/i.test(p)) pool += 42;
    var bits = chars.length * Math.log2(Math.max(pool, 2));
    if (p.length < 12) is.push('pwShort');
    if (/^\d+$/.test(p)) { is.push('pwDigits'); bits = Math.min(bits, p.length * 3.32); }
    if (PW_COMMON.some(function (w) { return low.indexOf(w) >= 0; })) { is.push('pwCommon'); bits -= 28; }
    var seq = 0;
    for (var i = 0; i + 3 <= low.length; i++) {
      var g = low.slice(i, i + 3);
      if (PW_SEQ.indexOf(g) >= 0 || PW_SEQ.indexOf(Array.from(g).reverse().join('')) >= 0) seq++;
    }
    if (seq) { is.push('pwSeq'); bits -= seq * 4; }
    if (/(.)\1{2,}/.test(p)) { is.push('pwRep'); bits -= 8; }
    if (/(19|20)\d\d/.test(p) || /\d{1,2}[.\-/]\d{1,2}[.\-/]\d{2,4}/.test(p)) { is.push('pwYear'); bits -= 8; }
    // «Слово + цифры в конце» (Aidana1995, Almaty2024!) — такой шаблон перебирают первым: словарь имён и слов × годы
    if (/^[A-Za-zА-Яа-яЁёӘәҒғҚқҢңӨөҰұҮүҺһІі]{2,12}\d{1,6}[!.?@#$*]?$/.test(p)) { is.push('pwPattern'); bits -= 16; }
    if (pool <= 36 && p.length >= 4) is.push('pwMix');
    bits = Math.max(0, bits);
    return { bits: bits, lv: bits < 28 ? 0 : bits < 40 ? 1 : bits < 60 ? 2 : bits < 80 ? 3 : 4, is: is };
  }

  /* ---------------- база знаний для сайта ---------------- */
  function topics(lang) {
    need();
    var lg = pickLang(lang);
    return KB.topics.map(function (t) {
      return { id: t.id, cat: t.cat, catLabel: tr(KB.kb_cats[t.cat], lg), icon: t.icon, title: tr(t.title, lg), summary: tr(t.summary, lg),
        signs: tr(t.signs, lg) || [], steps: tr(t.steps, lg) || [] };
    });
  }
  function tips(lang) { need(); var lg = pickLang(lang); return KB.tips.map(function (t) { return tr(t, lg); }); }

  var api = { load: load, init: init, get ready() { return !!KB; }, get kb() { return KB; }, version: function () { return KB ? KB.version : 0; },
    rev: function () { return KB ? (KB.rev || 0) : 0; }, core: CORE, semInit: semInit, semRev: function () { return SEM ? SEM.rev : 0; }, fold: function (t) { need(); return fold(cleanText(String(t || ''))[0]); },
    check: check, checkFile: checkFile, fileInfo: fileInfo, answer: answer, answerFull: answerFull, highlight: highlight, password: password, detectLang: detectLang, quiz: quiz, topics: topics, tips: tips,
    phrase: function (k, lang) { need(); return P(k, pickLang(lang)); }, _analyzeUrl: function (u) { need(); return analyzeUrl(u); } };
  root.QuasarCore = api;
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
})(typeof window !== 'undefined' ? window : globalThis);
