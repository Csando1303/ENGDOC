// Minimal service worker — required by Chromium for PWA installability
// (and installability is required for the File Handling API below to
// associate .engdoc with the app). Deliberately does no caching: EngDoc
// is fully client-side already and this app is small enough that an
// offline cache would just be another thing to invalidate correctly.
self.addEventListener('install', () => self.skipWaiting());
self.addEventListener('activate', (e) => e.waitUntil(self.clients.claim()));
self.addEventListener('fetch', () => {}); // no-op — required for Chrome to consider the app "installable"
