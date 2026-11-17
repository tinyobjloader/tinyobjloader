# Publishing `tinyobj` to npm

Procedure only — nothing in this repo has been uploaded to the npm registry.
The name `tinyobj` is unclaimed on npmjs.com, so the first publish reserves it.

Everything is run from `web/`, which is the npm package root (the repository root
is the C/C++ project and is not published).

Two ways to release:

- **CI (preferred): staged publishing via Trusted Publishing (OIDC).** Push an
  `npm-v<version>` tag or run the workflow manually; it stages the package and a
  maintainer approves it with 2FA. No registry tokens exist anywhere. See
  [CI release](#ci-release-github-actions--trusted-publishing).
- **Local:** run the commands below by hand with `npm login`.

## 0. One-time prerequisites

```sh
cd web

# 1. Authenticate. This must be the account that should own the package.
npm login                     # or: npm login --auth-type=web
npm whoami                    # must print your npm username

# 2. Confirm the name is still free. 404 == free to take.
npm view tinyobj version      # expect E404

# 3. Confirm 2FA / token setup. `npm publish` will prompt for an OTP if the
#    account requires one, so this is just a sanity check.
npm profile get
```

If the account has never published, `npm publish` will also create the package
and, on a fresh account, may require an email verification first.

For staged publishing (both CI and local `npm stage`) you also need npm CLI
>= 11.15.0 and 2FA enabled on the account. Check with `npm --version`.

## 1. Pre-flight (no registry writes)

```sh
cd web
npm run test:native      # native cc build of the shim, model assertions
npm run build            # emcc must be in PATH
npm test                 # node, against the built wasm
npm pack --dry-run       # inspect the tarball: 7 files, ~35 kB
```

Expected tarball contents — and nothing else:

```
LICENSE
README.md
dist/tinyobj.js
dist/tinyobj.wasm
js/index.d.ts
js/index.js
package.json
```

`demo/`, `test/`, `src/`, `scripts/` and `build.sh` are intentionally excluded
via `files` in `package.json`.

## 2. Publish (local)

The version in `package.json` is `2.0.0-rc.13`, a **prerelease**. Recent npm
rejects a prerelease when the dist-tag is left at its default, but an explicit
`npm publish --tag latest` is still accepted — and older npm (such as the 11.13
on this machine) does not check at all. Either way the RC would become the
version every `npm install tinyobj` gets.

`prepublishOnly` (`scripts/prepublish-check.sh`) enforces this: it rebuilds
`dist/`, runs both test suites, checks the tarball manifest, and **aborts** when
a prerelease would take the `latest` tag.

```sh
cd web

# Release candidate: publish under a prerelease tag, NOT latest.
npm publish --tag next            # or --tag rc / --tag beta

# Staged alternative (needs npm >= 11.15.0): queue it for 2FA approval.
npm stage publish --tag next
npm stage list tinyobj
npm stage approve <stage-id>      # publishes it

# ...later, promote that exact version to the default install tag:
npm dist-tag add tinyobj@2.0.0-rc.13 latest
npm dist-tag ls tinyobj           # latest: 2.0.0-rc.13 ; next: 2.0.0-rc.13
```

For the first stable release, bump `version` in `web/package.json` to `2.0.0`
(keep it in sync with `TINYOBJLOADER_VERSION` in `CMakeLists.txt`), then:

```sh
npm publish                       # tag: latest
```

`publishConfig.access` is already `public`, so the package is world-readable and
installable without a scope.

## CI release (GitHub Actions + Trusted Publishing)

`.github/workflows/npm-publish.yml` stages the package with OIDC, so no
`NPM_TOKEN` secret exists. Staging also means CI never gains the ability to
release on its own: a human approves every version with 2FA.

One-time npmjs.com setup — package **Settings → Trusted publishing → GitHub
Actions**:

| Field | Value |
| --- | --- |
| Organization or user | `tinyobjloader` |
| Repository | `tinyobjloader` |
| Workflow filename | `npm-publish.yml` (filename only, must match exactly) |
| Environment name | *(leave empty)* |
| Allowed actions | `npm stage publish` (leave `npm publish` and `npm dist-tag` off) |

Then restrict traditional tokens while you are there: package
**Settings → Publishing access → Require two-factor authentication and disallow
tokens**.

Trigger it only by pushing a tag that matches the package version. There is no
manual dispatch and no branch trigger: a tagged commit is the only way to stage.

```sh
# web/package.json must say 2.0.0-rc.13
git tag npm-v2.0.0-rc.13
git push origin npm-v2.0.0-rc.13
```

Note the `npm-` prefix: the repository's existing `v*` tags drive the C++/PyPI
releases (`python.yml`, `unit.yml`) and their versions do not track the npm
package, so `npm-publish.yml` deliberately uses its own namespace.

The workflow then: verifies the ref really is a tag, resolves and cross-checks
the version against the tag, derives the dist-tag from the version, skips if the
version is already published, builds with Emscripten 7.0.0, runs the native +
node tests, verifies the 7-file tarball, and finally
`npm stage publish --tag <tag>`.

Approve the staged package locally or on npmjs.com:

```sh
npm stage list tinyobj
npm stage approve <stage-id>      # prompts for 2FA
```

`wasm-package.yml` builds and tests `web/` on every push and pull request, so a
release tag cannot stage a broken module. It is separate from `npm-publish.yml`
because a release workflow that only runs on tags gives no early warning.

### Requirements for the workflow

- **GitHub-hosted runners only** — trusted publishing does not support
  self-hosted runners.
- npm CLI >= 11.15.0 (the workflow installs `npm@^11.15.0` explicitly; Node 24
  ships an older one) and Node >= 22.14.
- `id-token: write` permission — already set in the job.
- `package.json` `repository.url` must match the GitHub repository exactly; it
  does (`git+https://github.com/tinyobjloader/tinyobjloader.git`).
- A newly created trusted publisher must complete its first successful publish
  **within 2 days**, or it expires and has to be recreated. Do the first run
  right after saving the configuration.
- Provenance attestations are generated automatically for public packages from
  public repositories; no `--provenance` flag needed.

## 3. Verify the published artifact

```sh
npm view tinyobj                        # metadata, dist-tags
npm view tinyobj dist.tarball
npm dist-tag ls tinyobj

# Install from the registry, not the local tree, in a throwaway project:
scratch=$(mktemp -d) && cd "$scratch"
npm init -y
npm install tinyobj@next                # or tinyobj@2.0.0-rc.13 exactly
node -e "import('tinyobj').then(async (m) => {
  const t = await m.initTinyObj();
  const o = new TextEncoder().encode('v 0 0 0\nv 1 0 0\nv 0 1 0\nf 1 2 3\n');
  console.log(t.parse(o).shapes[0].triangleCount);   // 1
})"
```

The wasm file must arrive with the package: `node_modules/tinyobj/dist/tinyobj.wasm`
is loaded relative to `dist/tinyobj.js`, so no bundler config is needed.

## 4. After the first publish

- `package.json` now pins `repository.url` + `repository.directory: "web"`, and
  `homepage` points at the `release` branch's `web/README.md`. Adjust the branch
  if the package eventually lives elsewhere.
- The published README is `web/README.md` ("Not published yet — build from this
  repository" will need updating once it is live).
- Bump `version` in `web/package.json` for every publish; never reuse a version.
- npm does not allow unpublishing after 72 hours, and never allows reusing a
  version number. Use `npm deprecate tinyobj@<version> "<reason>"` instead of
  deleting.
- Tag npm releases as `npm-v<version>`, not `v<version>`: the `v*` namespace
  already belongs to the C++/PyPI releases.

## Troubleshooting

| error | cause / fix |
| --- | --- |
| `E401 Unauthorized` | expired token or not logged in: `npm login`, `npm whoami` |
| `E403 You do not have permission to publish` | the name is taken, or the account lacks publish rights for it |
| `EPRIVATE` | `private: true` in `package.json` — not set here |
| `EUNSCOPED` | `access: restricted` on an unscoped name — `publishConfig.access` is `public` |
| `prepublishOnly` guard aborts | publishing a prerelease as `latest`; use `--tag next` |
| `prepack` runs `build.sh` and fails | `emcc` not in `PATH` |
| `Unknown command: "stage"` | npm < 11.15.0: `npm install -g npm@^11.15.0` |
| `ENEEDAUTH` in CI | trusted publisher misconfigured — the workflow **filename** must match exactly, and the run must be on GitHub-hosted runners |
| trusted publisher expired | first publish did not happen within 2 days of saving the config; recreate it and publish promptly |
