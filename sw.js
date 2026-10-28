/* Сервис-воркер сайта CheckLink: портал открывается и работает без интернета (проверки, тренажёр, база знаний и
   QuasarAI выполняются в браузере). Страница, правила и движок - «сначала сеть» (всегда свежая версия), картинки -
   из кэша с обновлением в фоне. Запросы к API (/api/...) и веб-версия приложения (/app/) не кэшируются. */
'use strict';
const V = 'checklink-site-1.8.0';
const CORE = ['./', 'quasar-core.js', 'quasar-kb.json', 'portal-config.js', 'site.webmanifest',
  'assets/logo-64.png', 'assets/logo-180.png', 'assets/logo-192.png', 'assets/logo-512.png'];

self.addEventListener('install', e => {
  e.waitUntil(caches.open(V).then(c => Promise.all(CORE.map(u => c.add(u).catch(() => null)))).then(() => self.skipWaiting()));
});

self.addEventListener('activate', e => {
  e.waitUntil(caches.keys().then(keys => Promise.all(keys.filter(k => k.startsWith('checklink-site-') && k !== V).map(k => caches.delete(k))))
    .then(() => self.clients.claim()));
});

self.addEventListener('fetch', e => {
  const req = e.request;
  if (req.method !== 'GET') return;
  const url = new URL(req.url);
  if (url.origin !== self.location.origin) return;
  if (url.pathname.startsWith('/api/') || url.pathname.startsWith('/app') || url.pathname === '/health') return;
  if (req.mode === 'navigate') {
    e.respondWith(fetch(req).then(r => {
      if (r.ok) { const copy = r.clone(); caches.open(V).then(c => c.put('./', copy)); }
      return r;
    }).catch(() => caches.match('./').then(r => r || Response.error())));
    return;
  }
  // правила и движок проверки - «сначала сеть»: новые схемы мошенников видны сразу, без сети - из кэша
  if (/\/(quasar-kb\.json|quasar-core\.js)$/.test(url.pathname)) {
    e.respondWith(fetch(req).then(r => {
      if (r.ok) { const copy = r.clone(); caches.open(V).then(c => c.put(req, copy)); }
      return r;
    }).catch(() => caches.match(req).then(r => r || Response.error())));
    return;
  }
  e.respondWith(caches.match(req).then(hit => {
    const net = fetch(req).then(r => {
      if (r.ok && r.type === 'basic') { const copy = r.clone(); caches.open(V).then(c => c.put(req, copy)); }
      return r;
    }).catch(() => hit || Response.error());
    return hit || net;
  }));
});
