/**
 * Browser check: serves web/, loads demo/index.html in headless Chrome, feeds
 * cube.obj / cube.mtl (then cornell_box) through the real <input type="file">,
 * and asserts the demo reports the expected geometry and draws a frame.
 *
 * Requires Chrome/Chromium (CHROME_PATH overrides detection) and Node 22+
 * (global WebSocket). Run from web/:  node test/browser_check.mjs
 */
import { spawn } from 'node:child_process';
import { existsSync } from 'node:fs';
import { mkdtemp, readFile, writeFile } from 'node:fs/promises';
import net from 'node:net';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const here = path.dirname(fileURLToPath(import.meta.url));
const web = path.resolve(here, '..');
const repo = path.resolve(web, '..');

const CHROME =
  process.env.CHROME_PATH ||
  [
    '/usr/bin/google-chrome',
    '/usr/bin/google-chrome-stable',
    '/usr/bin/chromium',
    '/usr/bin/chromium-browser',
  ].find((candidate) => existsSync(candidate));

if (!CHROME) {
  console.error(
    'browser_check: no Chrome/Chromium found. Set CHROME_PATH to a binary.',
  );
  process.exit(1);
}

let failures = 0;
function check(cond, message) {
  if (!cond) {
    failures++;
    console.error(`FAIL: ${message}`);
  }
}

const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

async function freePort() {
  return new Promise((resolve, reject) => {
    const server = net.createServer();
    server.on('error', reject);
    server.listen(0, '127.0.0.1', () => {
      const { port } = server.address();
      server.close(() => resolve(port));
    });
  });
}

async function waitForHttp(url, timeoutMs = 20000) {
  const started = Date.now();
  for (;;) {
    try {
      if ((await fetch(url)).ok) return;
    } catch {
      /* retry */
    }
    if (Date.now() - started > timeoutMs) throw new Error(`${url} never came up`);
    await sleep(150);
  }
}

/* Dependency-free static server for web/, run as a child process. */
async function startServer(port, root) {
  const types = {
    '.html': 'text/html; charset=utf-8',
    '.js': 'text/javascript; charset=utf-8',
    '.mjs': 'text/javascript; charset=utf-8',
    '.wasm': 'application/wasm',
    '.json': 'application/json',
    '.png': 'image/png',
  };
  const script = `import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
const root = ${JSON.stringify(root)};
const types = ${JSON.stringify(types)};
http.createServer((req, res) => {
  const url = new URL(req.url, 'http://x');
  let file = path.join(root, decodeURIComponent(url.pathname));
  if (file.endsWith('/')) file += 'index.html';
  fs.stat(file, (err, st) => {
    if (err || !st.isFile()) { res.statusCode = 404; return res.end('not found'); }
    res.setHeader('content-type', types[path.extname(file)] || 'application/octet-stream');
    fs.createReadStream(file).pipe(res);
  });
}).listen(${port}, '127.0.0.1');`;
  const file = path.join(await mkdtemp(path.join(os.tmpdir(), 'tobj-serve-')), 'server.mjs');
  await writeFile(file, script);
  return spawn(process.execPath, [file], { stdio: 'ignore' });
}

/* Minimal flat-session CDP client. */
async function connect(wsUrl) {
  const socket = new WebSocket(wsUrl);
  await new Promise((resolve, reject) => {
    socket.onopen = resolve;
    socket.onerror = () => reject(new Error(`cannot connect to ${wsUrl}`));
  });

  let nextId = 1;
  const pending = new Map();
  const sessionHandlers = new Map();
  const events = [];

  socket.onmessage = (event) => {
    const message = JSON.parse(event.data);
    if (message.id) {
      const entry = pending.get(message.id);
      if (!entry) return;
      pending.delete(message.id);
      message.error
        ? entry.reject(new Error(JSON.stringify(message.error)))
        : entry.resolve(message.result);
      return;
    }
    if (message.sessionId) {
      sessionHandlers.get(message.sessionId)?.(message);
    }
    events.push(message);
  };

  return {
    events,
    send(method, params = {}, sessionId) {
      const id = nextId++;
      socket.send(JSON.stringify({ id, method, params, sessionId }));
      return new Promise((resolve, reject) => pending.set(id, { resolve, reject }));
    },
    onSession(sessionId, handler) {
      sessionHandlers.set(sessionId, handler);
    },
    close() {
      socket.close();
    },
  };
}

async function b64(name) {
  return (await readFile(path.join(repo, 'models', name))).toString('base64');
}

async function main() {
  const profile = await mkdtemp(path.join(os.tmpdir(), 'tobj-chrome-'));
  const port = await freePort();
  const debugPort = await freePort();
  const server = await startServer(port, web);
  const origin = `http://127.0.0.1:${port}`;

  const chrome = spawn(
    CHROME,
    [
      '--headless=new',
      '--no-sandbox',
      '--disable-gpu',
      '--enable-unsafe-swiftshader',
      '--use-gl=swiftshader',
      '--window-size=1024,768',
      `--user-data-dir=${profile}`,
      `--remote-debugging-port=${debugPort}`,
      `${origin}/demo/`,
    ],
    { stdio: ['ignore', 'ignore', 'pipe'] },
  );
  let chromeErr = '';
  chrome.stderr.on('data', (chunk) => {
    chromeErr += chunk;
  });

  try {
    await waitForHttp(`${origin}/demo/index.html`);
    await waitForHttp(`${origin}/dist/tinyobj.wasm`);

    let target;
    for (let i = 0; i < 120 && !target; i++) {
      try {
        const list = await (await fetch(`http://127.0.0.1:${debugPort}/json/list`)).json();
        target = list.find((t) => t.type === 'page');
      } catch {
        /* chrome still starting */
      }
      if (!target) await sleep(150);
    }
    if (!target) throw new Error(`no CDP page target\n${chromeErr}`);

    const client = await connect(target.webSocketDebuggerUrl);
    const { sessionId } = await client.send('Target.attachToTarget', {
      targetId: target.id,
      flatten: true,
    });

    const consoleErrors = [];
    const exceptions = [];
    client.onSession(sessionId, (message) => {
      if (message.method === 'Runtime.consoleAPICalled' && message.params.type === 'error') {
        consoleErrors.push(message.params.args.map((a) => a.value ?? a.description).join(' '));
      }
      if (message.method === 'Runtime.exceptionThrown') {
        exceptions.push(
          message.params.exceptionDetails.exception?.description ??
            message.params.exceptionDetails.text,
        );
      }
    });
    await client.send('Runtime.enable', {}, sessionId);
    await client.send('Page.enable', {}, sessionId);

    const evaluate = async (expression) => {
      const res = await client.send(
        'Runtime.evaluate',
        { expression, awaitPromise: true, returnByValue: true },
        sessionId,
      );
      if (res.exceptionDetails) {
        throw new Error(
          res.exceptionDetails.exception?.description ??
            res.exceptionDetails.text ??
            'evaluate failed',
        );
      }
      return res.result.value;
    };

    const statusText = () => evaluate("document.getElementById('status').textContent");
    const statusKind = () => evaluate("document.getElementById('status').dataset.kind");

    const waitForStatus = async (predicate, label, attempts = 200) => {
      for (let i = 0; i < attempts; i++) {
        const [text, kind] = [await statusText(), await statusKind()];
        if (predicate(text, kind)) return { text, kind };
        await sleep(100);
      }
      return { text: await statusText(), kind: await statusKind(), timeout: label };
    };

    const ready = await waitForStatus((t) => t.startsWith('Ready'), 'wasm load');
    check(!ready.timeout, `demo never became ready: ${ready.text}`);
    if (ready.timeout) throw new Error(ready.text);

    /* Probe the scene graph the demo rendered. */
    await evaluate(`(() => {
      const input = document.getElementById('files');
      const dec = (b64) => Uint8Array.from(atob(b64), (c) => c.charCodeAt(0));
      window.__feed = (pairs) => {
        const dt = new DataTransfer();
        for (const [name, b64] of pairs) dt.items.add(new File([dec(b64)], name));
        input.files = dt.files;
        input.dispatchEvent(new Event('change'));
      };
      window.__stats = () => {
        const canvas = document.getElementById('view');
        const gl = canvas.getContext('webgl2') || canvas.getContext('webgl');
        return {
          status: document.getElementById('status').textContent,
          kind: document.getElementById('status').dataset.kind,
          width: canvas.width,
          height: canvas.height,
          hasContext: !!gl,
        };
      };
      return true;
    })()`);

    await evaluate(
      `window.__feed(${JSON.stringify([
        ['cube.obj', await b64('cube.obj')],
        ['cube.mtl', await b64('cube.mtl')],
      ])})`,
    );
    const cube = await waitForStatus((t) => t.includes('triangles'));
    check(cube.text.includes('12 triangles'), `cube: ${cube.text}`);
    check(/cube\.mtl/.test(cube.text), `cube: material name missing (${cube.text})`);
    check(cube.kind === 'info', `cube: status kind ${cube.kind} (${cube.text})`);

    const stats = await evaluate('window.__stats()');
    check(stats.hasContext, 'no WebGL context');
    check(stats.width > 100 && stats.height > 100, `canvas ${stats.width}x${stats.height}`);

    const shot = await client.send('Page.captureScreenshot', { format: 'png' }, sessionId);
    const png = Buffer.from(shot.data, 'base64');
    const shotPath = path.join(os.tmpdir(), 'tobj-demo-cube.png');
    await writeFile(shotPath, png);
    check(png.length > 4000, `screenshot suspiciously small: ${png.length} bytes`);

    await evaluate(
      `window.__feed(${JSON.stringify([
        ['cornell_box.obj', await b64('cornell_box.obj')],
        ['cornell_box.mtl', await b64('cornell_box.mtl')],
      ])})`,
    );
    const cornell = await waitForStatus((t) => t.includes('36 triangles'));
    check(cornell.text.includes('36 triangles'), `cornell: ${cornell.text}`);

    const dropped = await evaluate(`(() => {
      window.__feed([['notes.txt', btoa('hello')]]);
      return document.getElementById('status').textContent;
    })()`);
    check(
      /Please choose|No \.obj/.test(dropped),
      `non-obj drop should explain itself, got: ${dropped}`,
    );

    /* Drag-and-drop path, not just the <input> element. */
    await evaluate(`(() => {
      const dec = (s) => Uint8Array.from(atob(s), (c) => c.charCodeAt(0));
      const dt = new DataTransfer();
      dt.items.add(new File([dec(${JSON.stringify(await b64('cube.obj'))})], 'dropped.obj'));
      const zone = document.getElementById('view');
      for (const type of ['dragenter', 'dragover', 'drop']) {
        zone.dispatchEvent(new DragEvent(type, { dataTransfer: dt, bubbles: true, cancelable: true }));
      }
      return true;
    })()`);
    const afterDrop = await waitForStatus((t, k) => k !== 'error' && /\d+ triangles/.test(t));
    check(
      afterDrop.text.includes('12 triangles'),
      `drag-and-drop did not load cube.obj: ${afterDrop.text}`,
    );

    check(consoleErrors.length === 0, `console errors: ${consoleErrors.join(' | ')}`);
    check(exceptions.length === 0, `page exceptions: ${exceptions.join(' | ')}`);

    console.log(`screenshot: ${shotPath}`);
    client.close();
  } finally {
    chrome.kill('SIGKILL');
    server.kill('SIGKILL');
  }

  if (failures) {
    console.error(`\n${failures} check(s) failed`);
    process.exit(1);
  }
  console.log('browser_check: all checks passed');
}

await main().catch((error) => {
  console.error(error);
  process.exit(1);
});
