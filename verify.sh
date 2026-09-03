#!/usr/bin/env bash

# Kernel re-check and axiom audit via `leanprover/comparator`.
# Requires x86_64 Linux; on other platforms use `verify_docker.sh`.

set -euo pipefail

if [[ "$(uname -s)" != "Linux" || "$(uname -m)" != "x86_64" ]]; then
  echo "error: verify.sh requires x86_64 Linux (all tool downloads are amd64-only)" >&2
  echo "       On other platforms, use verify_docker.sh instead." >&2
  exit 1
fi

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WS="$HERE/comparator"
WORK="${COMPARATOR_WORK:-$HOME/.cache/comparator-verify}"

source "$WS/versions.env"

PROJECT_TOOLCHAIN="$(tr -d '\r\n' < "$HERE/lean-toolchain")"
if [[ "$PROJECT_TOOLCHAIN" != "leanprover/lean4:${LEAN_VERSION}" ]]; then
  echo "error: lean-toolchain and comparator/versions.env disagree" >&2
  exit 1
fi

mkdir -p "$WORK" "$HOME/.local/bin"

verify_sha256() {
  local file="$1" expected="$2"
  echo "${expected}  ${file}" | sha256sum -c --status || {
    echo "error: SHA256 mismatch for $file" >&2
    exit 1
  }
  echo "$file: OK"
}

if ! command -v elan &>/dev/null; then
  echo "Installing elan ${ELAN_VERSION}..."
  curl -fsSL -o /tmp/elan.tar.gz \
    "https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-x86_64-unknown-linux-gnu.tar.gz"
  verify_sha256 /tmp/elan.tar.gz "$ELAN_SHA256"
  tar -xzf /tmp/elan.tar.gz -C /tmp
  /tmp/elan-init -y --no-modify-path
  export PATH="$HOME/.elan/bin:$PATH"
fi

TOOLCHAIN_DIR="$HOME/.elan/toolchains/leanprover--lean4---${LEAN_VERSION}"
if [ ! -d "$TOOLCHAIN_DIR" ]; then
  echo "Installing Lean toolchain ${LEAN_VERSION}..."
  curl -fsSL -o /tmp/lean.tar.zst \
    "https://releases.lean-lang.org/lean4/${LEAN_VERSION}/lean-${LEAN_VERSION#v}-linux.tar.zst"
  verify_sha256 /tmp/lean.tar.zst "$LEAN_SHA256"
  mkdir -p "$TOOLCHAIN_DIR"
  tar --zstd -xf /tmp/lean.tar.zst -C "$TOOLCHAIN_DIR" --strip-components=1
fi

if [ ! -d "$WORK/comparator" ]; then
  git clone -q --no-checkout https://github.com/leanprover/comparator "$WORK/comparator"
fi
git -C "$WORK/comparator" fetch -q --depth 1 origin "$COMPARATOR_REF"
COMPARATOR_FETCH_SHA="$(git -C "$WORK/comparator" rev-parse FETCH_HEAD)"
if [[ "$COMPARATOR_FETCH_SHA" != "$COMPARATOR_REF" ]]; then
  echo "error: fetched comparator revision does not match COMPARATOR_REF" >&2
  exit 1
fi
git -C "$WORK/comparator" checkout -q FETCH_HEAD
COMPARATOR_BUILD_KEY="${COMPARATOR_REF}:${LEAN_VERSION}"
COMPARATOR_STAMP="$WORK/.comparator-build-key"
COMPARATOR_CACHED_KEY="$(cat "$COMPARATOR_STAMP" 2>/dev/null || true)"
if [[ ! -x "$WORK/comparator/.lake/build/bin/comparator" ||
    "$COMPARATOR_CACHED_KEY" != "$COMPARATOR_BUILD_KEY" ]]; then
  (cd "$WORK/comparator" && lake exe cache get && lake build)
  printf '%s\n' "$COMPARATOR_BUILD_KEY" > "$COMPARATOR_STAMP"
fi

if [ ! -d "$WORK/lean4export" ]; then
  git clone -q --no-checkout https://github.com/leanprover/lean4export "$WORK/lean4export"
fi
git -C "$WORK/lean4export" fetch -q --depth 1 origin "$LEAN4EXPORT_REF"
LEAN4EXPORT_FETCH_SHA="$(git -C "$WORK/lean4export" rev-parse FETCH_HEAD)"
if [[ "$LEAN4EXPORT_FETCH_SHA" != "$LEAN4EXPORT_REF" ]]; then
  echo "error: fetched lean4export revision does not match LEAN4EXPORT_REF" >&2
  exit 1
fi
git -C "$WORK/lean4export" checkout -q FETCH_HEAD
cp "$HERE/lean-toolchain" "$WORK/lean4export/lean-toolchain"
LEAN4EXPORT_BUILD_KEY="${LEAN4EXPORT_REF}:${LEAN_VERSION}"
LEAN4EXPORT_STAMP="$WORK/.lean4export-build-key"
LEAN4EXPORT_CACHED_KEY="$(cat "$LEAN4EXPORT_STAMP" 2>/dev/null || true)"
if [[ ! -x "$WORK/lean4export/.lake/build/bin/lean4export" ||
    "$LEAN4EXPORT_CACHED_KEY" != "$LEAN4EXPORT_BUILD_KEY" ]]; then
  (cd "$WORK/lean4export" && lake build)
  printf '%s\n' "$LEAN4EXPORT_BUILD_KEY" > "$LEAN4EXPORT_STAMP"
fi

LANDRUN_BIN="$HOME/.local/bin/landrun"
if [ ! -x "$LANDRUN_BIN" ] || ! echo "${LANDRUN_SHA256}  ${LANDRUN_BIN}" | sha256sum -c --status 2>/dev/null; then
  echo "Downloading landrun ${LANDRUN_VERSION}..."
  curl -fsSL -o "$LANDRUN_BIN" \
    "https://github.com/Zouuup/landrun/releases/download/${LANDRUN_VERSION}/landrun-linux-amd64"
  verify_sha256 "$LANDRUN_BIN" "$LANDRUN_SHA256"
  chmod +x "$LANDRUN_BIN"
fi

LANDRUN_WRAPPER="$HOME/.local/bin/landrun-wrapper"
cat > "$LANDRUN_WRAPPER" << 'EOF'
#!/usr/bin/env bash
args=()
while [[ $# -gt 0 ]]; do
  if [[ "$1" == "--ro" && "$2" == "/" ]]; then
    args+=("--rox" "/")
    shift 2
  else
    args+=("$1")
    shift
  fi
done
exec "$HOME/.local/bin/landrun" "${args[@]}"
EOF
sed -i "s|\$HOME|$HOME|g" "$LANDRUN_WRAPPER"
chmod +x "$LANDRUN_WRAPPER"

export COMPARATOR_LANDRUN="$LANDRUN_WRAPPER"

NANODA_BIN="$WORK/nanoda_lib/target/release/nanoda_bin"

if [ ! -d "$WORK/nanoda_lib" ]; then
  git clone -q --no-checkout https://github.com/ammkrn/nanoda_lib "$WORK/nanoda_lib"
fi
git -C "$WORK/nanoda_lib" fetch -q --depth 1 origin "$NANODA_REF"

FETCH_SHA="$(git -C "$WORK/nanoda_lib" rev-parse FETCH_HEAD)"
if [[ "$FETCH_SHA" != "$NANODA_REF" ]]; then
  echo "error: fetched nanoda revision does not match NANODA_REF" >&2
  exit 1
fi
git -C "$WORK/nanoda_lib" checkout -q FETCH_HEAD
NANODA_BUILD_KEY="${NANODA_REF}:${RUST_VERSION}"
NANODA_STAMP="$WORK/.nanoda-build-key"
NANODA_CACHED_KEY="$(cat "$NANODA_STAMP" 2>/dev/null || true)"
if [[ ! -x "$NANODA_BIN" || "$NANODA_CACHED_KEY" != "$NANODA_BUILD_KEY" ]]; then
  echo "Building nanoda from pinned Rust ${RUST_VERSION}..."
  curl -fsSL -o /tmp/rust.tar.gz \
    "https://static.rust-lang.org/dist/rust-${RUST_VERSION}-x86_64-unknown-linux-gnu.tar.gz"
  verify_sha256 /tmp/rust.tar.gz "$RUST_SHA256"
  tar -xzf /tmp/rust.tar.gz -C /tmp
  "/tmp/rust-${RUST_VERSION}-x86_64-unknown-linux-gnu/install.sh" \
    --prefix="$HOME/.local" --without=rust-docs
  (cd "$WORK/nanoda_lib" && PATH="$HOME/.local/bin:$PATH" cargo build --release)
  printf '%s\n' "$NANODA_BUILD_KEY" > "$NANODA_STAMP"
fi

export COMPARATOR_NANODA="$NANODA_BIN"

export PATH="$WORK/lean4export/.lake/build/bin:$WORK/comparator/.lake/build/bin:$HOME/.local/bin:$HOME/.elan/bin:$PATH"

cd "$WS"
lake exe cache get
CHALLENGE="$(grep -o '"challenge_module"[[:space:]]*:[[:space:]]*"[^"]*"' config.json | grep -o '"[^"]*"$' | tr -d '"')"
SOLUTION="$(grep -o '"solution_module"[[:space:]]*:[[:space:]]*"[^"]*"' config.json | grep -o '"[^"]*"$' | tr -d '"')"
lake build "$CHALLENGE" "$SOLUTION"
exec lake env comparator config.json
