#!/usr/bin/env bash
# Garde-fou anti-régression : AUCUN axiome, AUCUN native_decide, comptage des sorry.
# La leçon du fichier legacy (128k lignes, incohérent) : un seul `axiom` mal quantifié
# suffit à rendre tout le développement réfutable.
set -euo pipefail
cd "$(dirname "$0")/.."

if grep -rnE '(^|[^[:alnum:]_])axiom[[:space:]]' Gleason Gleason.lean 2>/dev/null; then
  echo "ÉCHEC : 'axiom' est interdit dans ce dépôt."
  exit 1
fi
if grep -rn 'native_decide' Gleason Gleason.lean 2>/dev/null; then
  echo "ÉCHEC : 'native_decide' est interdit (élargit la base de confiance)."
  exit 1
fi
N=$(grep -rno '\bsorry\b' Gleason Gleason.lean 2>/dev/null | wc -l | tr -d ' ')
echo "OK — aucun axiome, aucun native_decide. Sorries restants : ${N}"
