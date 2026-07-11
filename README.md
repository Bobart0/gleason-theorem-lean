# gleason — Formalisation Lean 4 des théorèmes de Busch (2003) et Gleason

**Statut : PROJET COMPLET (2026-07-11).** Première formalisation mécanisée, **sans
axiome**, de :
1. **Théorème de Busch (2003)** : toute mesure d'effets (POVM) sur ℂⁿ est représentée
   par un unique opérateur densité (vaut dès n = 2) ;
2. **Théorème de Gleason** : idem pour les mesures de projections, n ≥ 3,
   voie Cooke–Keane–Moran / Richman–Bridges ;
3. **Corollaire** : aucune mesure « dispersion-free » (à valeurs dans {0,1}) n'existe
   en dimension ≥ 3 — le détecteur anti-vacuité final du projet.

## Démarrage
```bash
./setup.sh          # toolchain + mathlib + cache + build (~10 min avec cache)
./scripts/guard.sh  # audit : 0 axiome, compte des sorry
```

## Verifying the proofs

```bash
./setup.sh              # one-time: toolchain, Mathlib cache, first build
lake build              # rebuild everything; must finish green
./scripts/guard.sh      # 0 axiom, 0 native_decide; sorry count from this script
                         # also matches the word "sorry" inside comments/docstrings —
                         # grep '\bsorry\b' Gleason for actual `sorry` tactics (there are none)
```

The four delivered theorems each carry a live `#print axioms` check at the bottom of
[`Gleason/Main.lean`](Gleason/Main.lean), so `lake build Gleason.Main` prints, for
`Gleason.gleason`, `Gleason.busch`, `Gleason.busch_born_rule`, and
`Gleason.no_dispersion_free`:

```
'Gleason.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These three are the standard axioms accepted by Lean/Mathlib itself (propositional
extensionality, choice, quotient soundness) — no `sorryAx` and no project-specific
`axiom` anywhere in `Gleason/`.

## Carte du dépôt
```
Gleason/Defs.lean            ProjMeasure (additivité ORTHOG.), IsDensityOperator, bornValue
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
| Jalon| Contenu                 | Critère                                          | État |
| M0   | Squelette compilable    | `lake build` vert (sorry autorisés)              | ✅ |
| M1   | Fondations              | section M1 de SORRIES.md fermée                  | ✅ |
| M-B  | **Busch 2003 complet**  | `#print axioms busch` propre → annonce/preprint  | ✅ |
| M2   | Régularité réelle ℝ³    | `frameFunction_regular` sans sorry               | ✅ |
| M3   | Réduction complexe      | `cFrameFunction_regular` sans sorry              | ✅ |
| O    | Opérateur (assemblage)  | `isDensityOperator_of_represents` sans sorry     | ✅ |
| M4   | **Gleason complet**     | `#print axioms gleason` propre                   | ✅ |

## Règles
Aucun `axiom`, aucun `native_decide` (CI bloquante). Toute structure d'hypothèses a un
habitant concret dans `Nonvacuity.lean`, même commit. Un `sorry` honnête plutôt qu'un
énoncé affaibli en silence.

## Licence
[Apache License 2.0](LICENSE).
