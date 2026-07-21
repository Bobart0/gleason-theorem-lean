#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if command -v python3 >/dev/null 2>&1; then
  PYTHON=python3
elif command -v python >/dev/null 2>&1; then
  PYTHON=python
else
  echo "ERROR: Python 3 is required for source-aware verification." >&2
  exit 1
fi

tmp_dir=$(mktemp -d)
trap 'rm -rf "$tmp_dir"' EXIT

mapfile -d '' lean_files < <(git ls-files -z '*.lean')
"$PYTHON" scripts/check_lean_source.py "${lean_files[@]}"

echo "Building the pinned Lean project..."
NO_COLOR=1 lake build 2>&1 | tee "$tmp_dir/build.log"
if grep -E '(^|[[:space:]])warning:' "$tmp_dir/build.log" >/dev/null; then
  echo "ERROR: Lean build emitted warnings; see output above." >&2
  exit 1
fi

echo "Checking public theorem dependencies..."
NO_COLOR=1 lake env lean Verification/Axioms.lean 2>&1 | tee "$tmp_dir/axioms.log"
if grep -E '(^|[[:space:]])warning:' "$tmp_dir/axioms.log" >/dev/null; then
  echo "ERROR: axiom audit emitted warnings; see output above." >&2
  exit 1
fi
"$PYTHON" scripts/normalize_axioms.py "$tmp_dir/axioms.log" | tr -d '\r' > "$tmp_dir/axioms.normalized"
diff -u Verification/axioms.expected "$tmp_dir/axioms.normalized"

echo
echo "Verification succeeded:"
echo "  - pinned project build completed without Lean warnings"
echo "  - no admitted proofs or forbidden trust-expanding forms in tracked Lean source"
echo "  - no project-specific axioms in the four public results"
sed 's/^/  - /' "$tmp_dir/axioms.normalized"
