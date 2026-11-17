#!/usr/bin/env bash
#
# Runs automatically on `npm publish` (prepublishOnly).
#
# Guard rails for the very first publishes:
#   1. Refuse to tag a prerelease version as `latest`. npm defaults the dist-tag
#      to `latest` with no prerelease detection, so `npm publish` on 2.0.0-rc.13
#      would make the RC the version everyone installing `tinyobj` gets.
#   2. Rebuild dist/ and run the test suites against exactly what will ship.
#   3. Assert the tarball carries the expected files and nothing else.
#
set -euo pipefail
cd "$(dirname "$0")/.."

pkg_name=$(node -p "require('./package.json').name")
version=$(node -p "require('./package.json').version")
tag="${npm_config_tag:-latest}"

echo "==> $pkg_name@$version (dist-tag: $tag)"

# --- 1. prerelease / dist-tag guard --------------------------------------
case "$version" in
  *-*)
    if [ "$tag" = "latest" ]; then
      cat >&2 <<EOF
error: $pkg_name@$version is a prerelease and would be published as \`latest\`.

Release candidates must not take over the default install tag. Publish with an
explicit prerelease tag instead:

    npm publish --tag next            # or: --tag rc, --tag beta, ...

To promote it to \`latest\` later, publish again with \`--tag latest\`, or:

    npm dist-tag add $pkg_name@$version latest

Override this guard only if you really mean it:

    ALLOW_PRERELEASE_LATEST=1 npm publish --tag latest
EOF
      if [ "${ALLOW_PRERELEASE_LATEST:-0}" != "1" ]; then
        exit 1
      fi
      echo "warning: ALLOW_PRERELEASE_LATEST=1 - publishing a prerelease as latest" >&2
    fi
    ;;
esac

# --- 2. rebuild and test the exact bytes that will ship -------------------
npm run --silent build

for f in dist/tinyobj.js dist/tinyobj.wasm js/index.js js/index.d.ts README.md LICENSE; do
  [ -s "$f" ] || { echo "error: missing or empty $f" >&2; exit 1; }
done

echo "==> smoke test (node)"
node test/smoke.mjs

echo "==> native shim test"
bash test/run_native.sh >/dev/null 2>&1 || {
  echo "error: native shim test failed (run: bash test/run_native.sh)" >&2
  exit 1
}

# --- 3. tarball contents -------------------------------------------------
expected=$(cat <<'EOF'
LICENSE
README.md
dist/tinyobj.js
dist/tinyobj.wasm
js/index.d.ts
js/index.js
package.json
EOF
)
actual=$(npm pack --dry-run --json --ignore-scripts 2>/dev/null |
  node -e "let s='';process.stdin.on('data',d=>s+=d).on('end',()=>{const j=JSON.parse(s);console.log(j[0].files.map(f=>f.path).sort().join('\n'))})")

if [ "$actual" != "$expected" ]; then
  echo "error: tarball contents differ from expectation" >&2
  diff <(echo "$expected") <(echo "$actual") >&2 || true
  exit 1
fi

echo "==> ok: 7 files, publishing $pkg_name@$version with tag $tag"
