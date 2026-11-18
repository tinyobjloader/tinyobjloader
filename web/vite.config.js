import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { defineConfig } from 'vite';

const web = path.dirname(fileURLToPath(import.meta.url));

// The demo is the Vite root so the build emits index.html at the artifact root
// (ready for GitHub Pages). main.js still imports ../js/index.js and the
// Emscripten glue in ../dist/, which are served from the parent web/ directory.
export default defineConfig({
  root: path.join(web, 'demo'),
  // Relative asset URLs so the built demo works at any GitHub Pages path.
  base: './',
  plugins: [
    {
      // The source import map is only for the no-bundler static demo. A build
      // has three.js bundled, so leave no CDN reference in the artifact.
      apply: 'build',
      name: 'strip-importmap',
      transformIndexHtml(html) {
        return html.replace(/<script type="importmap">[\s\S]*?<\/script>\s*/g, '');
      },
    },
  ],
  server: {
    fs: { allow: [web, path.join(web, '..')] },
    open: '/',
  },
  build: {
    // The demo uses top-level await; Vite's default ES2020 target rejects it.
    target: 'es2022',
    // Do not clobber dist/, which holds the emscripten build consumed by the
    // published package.
    outDir: path.join(web, '.vite-demo-dist'),
    emptyOutDir: true,
  },
});
