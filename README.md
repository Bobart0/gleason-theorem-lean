# gleason — Formalisation Lean 4 des théorèmes de Busch (2003) et Gleason

Objectif : première formalisation mécanisée, **sans axiome**, de :
1. **Théorème de Busch (2003)** — toute mesure d'effets (POVM) sur ℂⁿ est représentée
   par un unique opérateur densité (vaut dès n = 2) — *cible rapide* ;
2. **Théorème de Gleason** — idem pour les mesures de projections, n ≥ 3 — *cible dure*,
   voie Cooke–Keane–Moran / Richman–Bridges.

## Démarrage
```bash
./setup.sh          # toolchain + mathlib + cache + build (~10 min avec cache)
./scripts/guard.sh  # audit : 0 axiome, compte des sorry
```

## Carte du dépôt
```
Gleason/Defs.lean            ProjMeasure (additivité ORTHOGONALE), IsDensityOperator, bornValue
Gleason/Nonvacuity.lean      Tests d'inhabitation obligatoires (états purs sur ℂ³)
Gleason/Busch/               Effets, EffectMeasure, théorème de Busch      [jalon M-B]
Gleason/Real3/               Cœur analytique réel sur ℝ³ (CKM/RB)          [jalon M2]
Gleason/Complex/             Sections réelles + recollement (Dvurečenskij) [jalon M3]
Gleason/Operator.lean        Forme quadratique → opérateur densité         [phase O]
Gleason/Main.lean            Théorème de Gleason + corollaire dispersion-free
CLAUDE.md                    Règles pour l'agent (à lire par Claude Code au démarrage)
SORRIES.md                   Suivi des obligations restantes
```

## Jalons
| Jalon | Contenu | Critère |
|---|---|---|
| M0 | Squelette compilable | `lake build` vert (sorry autorisés) |
| M1 | Fondations | section M1 de SORRIES.md fermée |
| M-B | **Busch 2003 complet** | `#print axioms busch` propre → annonce/preprint |
| M2 | Régularité réelle ℝ³ | `frameFunction_regular` sans sorry |
| M3 | Réduction complexe | `cFrameFunction_regular` sans sorry |
| M4 | **Gleason complet** | `#print axioms gleason` propre |

## Règles
Aucun `axiom`, aucun `native_decide` (CI bloquante). Toute structure d'hypothèses a un
habitant concret dans `Nonvacuity.lean`, même commit. Un `sorry` honnête plutôt qu'un
énoncé affaibli en silence.
