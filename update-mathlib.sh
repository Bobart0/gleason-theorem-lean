#!/usr/bin/env bash
# Avance délibérément vers un commit Mathlib donné, choisi explicitement.
#
# Usage : ./update-mathlib.sh <FULL_MATHLIB_COMMIT_SHA>
#
# ATTENTION : modifie `lakefile.toml`, `lean-toolchain` et `lake-manifest.json`,
# donc casse la reproductibilité d'un commit/tag déjà publié (ex. cité dans une
# publication). N'utiliser que pour faire progresser le dépôt lui-même, jamais
# pour reconstruire une version figée — voir `setup.sh` pour ça.
#
# Ce script ne suit plus implicitement `master` : le commit Mathlib cible doit
# être fourni explicitement en argument, comme SHA Git complet (40 caractères
# hexadécimaux). Il ne commite, ne pousse, ne crée de branche ni de tag.
set -euo pipefail

usage() {
  echo "Usage: $0 <FULL_MATHLIB_COMMIT_SHA>" >&2
  echo "  <FULL_MATHLIB_COMMIT_SHA> must be a full 40-character hexadecimal" >&2
  echo "  Git commit SHA from https://github.com/leanprover-community/mathlib4" >&2
  exit 1
}

if [ "$#" -ne 1 ]; then
  echo "ERROR: exactly one argument is required (got $#)." >&2
  usage
fi

SHA="$1"

if ! [[ "$SHA" =~ ^[0-9a-fA-F]{40}$ ]]; then
  echo "ERROR: '$SHA' is not a full 40-character hexadecimal Git SHA." >&2
  usage
fi

cd "$(dirname "$0")"

if [ -n "$(git status --short)" ]; then
  echo "ERROR: the working tree is not clean. Commit or stash your changes first." >&2
  exit 1
fi

echo "Target Mathlib commit: $SHA"

# 1. Pin the requested commit in lakefile.toml (Mathlib [[require]] block only).
python3 - "$SHA" <<'PY'
import re
import sys

sha = sys.argv[1]
path = "lakefile.toml"
with open(path, encoding="utf-8") as f:
    text = f.read()

pattern = re.compile(
    r'(\[\[require\]\]\s*\n'
    r'name = "mathlib"\s*\n'
    r'scope = "leanprover-community"\s*\n)'
    r'rev = "[0-9a-fA-F]{40}"'
)
new_text, count = pattern.subn(r'\1rev = "' + sha + '"', text)
if count != 1:
    raise SystemExit(
        f"ERROR: expected exactly one Mathlib rev entry to replace in {path}, "
        f"found {count}."
    )

with open(path, "w", encoding="utf-8", newline="\n") as f:
    f.write(new_text)
PY

# 2. Fetch the lean-toolchain pinned by that exact Mathlib commit.
toolchain_url="https://raw.githubusercontent.com/leanprover-community/mathlib4/${SHA}/lean-toolchain"
curl -fL "$toolchain_url" -o lean-toolchain
echo "Toolchain : $(cat lean-toolchain)"

# 3. Resolve dependencies, refresh the cache, and re-verify strictly.
lake update mathlib
lake exe cache get
./scripts/verify.sh

# 4. Confirm the pin actually took effect everywhere it must.
python3 - "$SHA" <<'PY'
import json
import sys

sha = sys.argv[1]

with open("lakefile.toml", encoding="utf-8") as f:
    lakefile_text = f.read()
if f'rev = "{sha}"' not in lakefile_text:
    raise SystemExit(f"ERROR: lakefile.toml does not contain rev = \"{sha}\".")

with open("lake-manifest.json", encoding="utf-8") as f:
    manifest = json.load(f)

mathlib = next((p for p in manifest["packages"] if p["name"] == "mathlib"), None)
if mathlib is None:
    raise SystemExit("ERROR: no 'mathlib' package found in lake-manifest.json.")
if mathlib.get("inputRev") != sha:
    raise SystemExit(
        f"ERROR: lake-manifest.json inputRev is {mathlib.get('inputRev')!r}, "
        f"expected {sha!r}."
    )
if mathlib.get("rev") != sha:
    raise SystemExit(
        f"ERROR: lake-manifest.json rev is {mathlib.get('rev')!r}, expected {sha!r}."
    )
PY

echo "MATHLIB_UPDATE_RESULT=PASS"
echo "MATHLIB_REV=$SHA"
echo "LEAN_TOOLCHAIN=$(cat lean-toolchain)"
