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

---

## English translation

# gleason — Lean 4 formalization of Busch's (2003) and Gleason's theorems

**Status: PROJECT COMPLETE (2026-07-11).** First mechanized, **axiom-free**
formalization of:
1. **Busch's theorem (2003)**: every effect measure (POVM) on ℂⁿ is represented
   by a unique density operator (holds already at n = 2);
2. **Gleason's theorem**: likewise for projection measures, n ≥ 3, via the
   Cooke–Keane–Moran / Richman–Bridges route;
3. **Corollary**: no "dispersion-free" measure (valued in {0,1}) exists in
   dimension ≥ 3 — the project's final anti-vacuity detector.

## Getting started
```bash
./setup.sh          # toolchain + mathlib + cache + build (~10 min with cache)
./scripts/guard.sh  # audit: 0 axiom, sorry count
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

## Repository map
```
Gleason/Defs.lean            ProjMeasure (ORTHOG. additivity), IsDensityOperator, bornValue
Gleason/Nonvacuity.lean      Mandatory inhabitation tests (pure states on ℂ³)
Gleason/Busch/               Effects, EffectMeasure, Busch's theorem              [milestone M-B]
Gleason/Real3/                Real analytic core on ℝ³ (CKM/RB)                    [milestone M2]
Gleason/Complex/              Real sections + patching (Dvurečenskij)              [milestone M3]
Gleason/Operator.lean          Quadratic form → density operator                     [phase O]
Gleason/Main.lean               Gleason's theorem + dispersion-free corollary
CLAUDE.md                      Agent rules (read by Claude Code at startup)
SORRIES.md                     Tracking of remaining obligations
```

## Milestones
| Milestone | Content                | Criterion                                          | Status |
| M0   | Compilable skeleton    | `lake build` green (sorry allowed)               | ✅ |
| M1   | Foundations            | M1 section of SORRIES.md closed                  | ✅ |
| M-B  | **Busch 2003 complete**| clean `#print axioms busch` → announcement/preprint | ✅ |
| M2   | Real regularity ℝ³     | `frameFunction_regular` sorry-free               | ✅ |
| M3   | Complex reduction      | `cFrameFunction_regular` sorry-free              | ✅ |
| O    | Operator (assembly)    | `isDensityOperator_of_represents` sorry-free     | ✅ |
| M4   | **Gleason complete**   | clean `#print axioms gleason`                    | ✅ |

## Rules
No `axiom`, no `native_decide` (CI-blocking). Every hypothesis structure has a
concrete inhabitant in `Nonvacuity.lean`, same commit. An honest `sorry` rather
than a silently weakened statement.

## License
[Apache License 2.0](LICENSE).
