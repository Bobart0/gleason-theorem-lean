#!/usr/bin/env bash
# Installation initiale. À lancer UNE FOIS après clonage.
#
# REPRODUCTIBILITÉ : ce script utilise la toolchain (`lean-toolchain`) et les
# versions de dépendances (`lake-manifest.json`) telles que COMMISES dans le
# dépôt, sans les modifier. C'est indispensable pour qu'un commit/tag donné
# (ex. cité dans une publication) reste reconstructible à l'identique des mois
# ou années plus tard, même si Mathlib a évolué entre-temps.
#
# Pour AVANCER délibérément vers une version plus récente de Mathlib (et donc
# modifier `lean-toolchain`/`lake-manifest.json`), utiliser `update-mathlib.sh`
# à la place — jamais ce script.
set -euo pipefail
cd "$(dirname "$0")"

# 1. Télécharger le cache Mathlib précompilé pour la révision figée dans
#    lake-manifest.json (INDISPENSABLE : sinon ~4h de compilation). Cette
#    étape clone/checkout les dépendances d'après le manifeste existant,
#    sans le modifier (seul `lake update` réécrit le manifeste).
lake exe cache get

# 2. Construire le projet.
lake build
