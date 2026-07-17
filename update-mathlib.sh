#!/usr/bin/env bash
# Avance délibérément vers la dernière version de Mathlib (master).
#
# ATTENTION : modifie `lean-toolchain` et `lake-manifest.json`, donc casse la
# reproductibilité d'un commit/tag déjà publié (ex. cité dans une publication).
# N'utiliser que pour faire progresser le dépôt lui-même, jamais pour
# reconstruire une version figée — voir `setup.sh` pour ça.
set -euo pipefail
cd "$(dirname "$0")"

# 1. Synchroniser la toolchain avec Mathlib master.
curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
echo "Toolchain : $(cat lean-toolchain)"

# 2. Résoudre les dépendances et réécrire lake-manifest.json.
lake update mathlib

# 3. Télécharger le cache Mathlib précompilé.
lake exe cache get

# 4. Construire le projet.
lake build
