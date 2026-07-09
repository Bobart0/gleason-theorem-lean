#!/usr/bin/env bash
# Installation initiale. À lancer UNE FOIS après clonage.
set -euo pipefail
cd "$(dirname "$0")"

# 1. Synchroniser la toolchain avec Mathlib master (évite tout conflit de version)
curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
echo "Toolchain : $(cat lean-toolchain)"

# 2. Résoudre les dépendances
lake update mathlib

# 3. Télécharger le cache Mathlib précompilé (INDISPENSABLE : sinon ~4h de compilation)
lake exe cache get

# 4. Construire le projet
lake build
