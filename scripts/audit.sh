#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"

if grep -RInE --include='*.lean' '\b(sorry|admit|axiom)\b' \
    AbelianCoverHodge AbelianCoverHodge.lean; then
  echo "Forbidden proof placeholder or global postulate found." >&2
  exit 1
fi

lake build

audit_output="$(lake env lean AbelianCoverHodge/Audit/PrintAxioms.lean 2>&1)"
printf '%s\n' "$audit_output"

if grep -q 'sorryAx' <<<"$audit_output"; then
  echo "The dependency report contains sorryAx." >&2
  exit 1
fi

if grep -E 'AXIOM AUDIT .*\[.*AbelianCoverHodge\.' <<<"$audit_output"; then
  echo "The dependency report contains a project-defined postulate." >&2
  exit 1
fi

echo "Audit passed: build complete, no forbidden declarations, no sorryAx."
