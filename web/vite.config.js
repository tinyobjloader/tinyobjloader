import { defineConfig } from 'vite';

// web/ is the Vite root so that demo/main.js can import ../js/index.js and the
// Emscripten glue in ../dist/ directly. The static, CDN-based demo at /demo/
// keeps working unchanged: Vite rewrites the bare `three` imports to the local
// node_modules copy, while the import map in demo/index.html remains for
// `npm run demo` / the browser-check harness (which do not use Vite).
export default defineConfig({
  server: {
    open: '/demo/',
  },
  build: {
    // The demo uses top-level await; Vite's default ES2020 target rejects it.
    target: 'es2022',
    // Do not clobber dist/, which holds the emscripten build consumed by the
    // published package.
    outDir: '.vite-demo-dist',
    emptyOutDir: true,
    rollupOptions: {
      input: 'demo/index.html',
    },
  },
});
