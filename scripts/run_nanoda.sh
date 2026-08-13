#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"

# lean-action's nanoda integration currently clones a stale parser branch; see
# https://github.com/leanprover/lean-action/issues/169.  Keep every executable
# source and the Rust compiler used by this independent check explicit here.
readonly lean4export_sha="15f6055e299ad5b89345e533cc2192f4cc00f659"
readonly nanoda_sha="418320295890faed83a96fd97907b12a3b6728c2"
readonly rust_toolchain="1.97.1"

scratch_dir="$(mktemp -d)"
cleanup() {
  if [[ -n "${scratch_dir:-}" && -d "$scratch_dir" ]]; then
    rm -rf -- "$scratch_dir"
  fi
}
trap cleanup EXIT

git clone --quiet --no-checkout \
  https://github.com/leanprover/lean4export.git \
  "$scratch_dir/lean4export"
git -C "$scratch_dir/lean4export" checkout --quiet --detach "$lean4export_sha"
test "$(git -C "$scratch_dir/lean4export" rev-parse HEAD)" = "$lean4export_sha"
cp lean-toolchain "$scratch_dir/lean4export/lean-toolchain"
(
  cd "$scratch_dir/lean4export"
  lake build lean4export
)

git clone --quiet --no-checkout \
  https://github.com/ammkrn/nanoda_lib.git \
  "$scratch_dir/nanoda_lib"
git -C "$scratch_dir/nanoda_lib" checkout --quiet --detach "$nanoda_sha"
test "$(git -C "$scratch_dir/nanoda_lib" rev-parse HEAD)" = "$nanoda_sha"
rustup toolchain install "$rust_toolchain" --profile minimal
cargo "+$rust_toolchain" build \
  --locked \
  --release \
  --manifest-path "$scratch_dir/nanoda_lib/Cargo.toml"

lake env \
  "$scratch_dir/lean4export/.lake/build/bin/lean4export" \
  AbelianCoverHodge | \
  "$scratch_dir/nanoda_lib/target/release/nanoda_bin" \
    scripts/nanoda.json
