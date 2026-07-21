# gleason — Formalisation Lean 4 des théorèmes de Busch (2003) et Gleason

**Statut : PROJET COMPLET (2026-07-11).** Ce dépôt fournit une formalisation
complète en Lean 4 et Mathlib de versions complexes de dimension finie de :
1. **Théorème de Busch (2003)** : toute mesure d'effets (POVM) sur ℂⁿ est représentée
   par un unique opérateur densité (vaut dès n = 2) ;
2. **Théorème de Gleason** : idem pour les mesures de projections, n ≥ 3,
   voie Cooke–Keane–Moran / Richman–Bridges ;
3. **Corollaire** : aucune mesure « dispersion-free » (à valeurs dans {0,1}) n'existe
   en dimension ≥ 3 — un test d'intégration de bout en bout de la représentation.

L'additivité des mesures projectives porte sur les sous-espaces orthogonaux, et non
simplement sur les sous-espaces d'intersection nulle. La disjonction du treillis
imposerait une condition différente et nettement plus forte, non équivalente à
l'hypothèse de Gleason et non satisfaite par les mesures de Born générales.

Pour Busch, la structure Lean `EffectMeasure` utilise l'additivité binaire sur les
sommes admissibles d'effets. L'additivité finie en découle par itération, et cette
hypothèse suffit au résultat de dimension finie formalisé ici. La présentation
originale est couramment énoncée pour des familles finies ou dénombrables dont la
somme est bornée par l'identité ; le présent énoncé n'est donc pas présenté comme
textuellement identique à toutes les formulations de la littérature.

## Démarrage
```bash
./setup.sh          # cache + build à partir de la version figée (~10 min avec cache)
./scripts/guard.sh  # audit : aucun axiome propre au projet, compte des occurrences de sorry
```
`setup.sh` construit exactement la version figée dans `lean-toolchain` et
`lake-manifest.json` — il ne les modifie jamais, pour que tout commit/tag reste
reconstructible à l'identique (important si tu cites ce dépôt). Pour avancer
délibérément vers une version plus récente de Mathlib, utiliser
`./update-mathlib.sh` séparément (modifie ces fichiers).

## Verifying the proofs

```bash
./setup.sh              # one-time: cache + build from the pinned version
lake build              # rebuild everything; must finish green
./scripts/guard.sh      # 0 axiom, 0 native_decide; sorry count from this script
                         # also matches the word "sorry" inside comments/docstrings —
                         # grep '\bsorry\b' Gleason for actual `sorry` tactics (there are none)
```

`setup.sh` never modifies `lean-toolchain` or `lake-manifest.json` — it builds
exactly the pinned version, so that any given commit/tag remains reproducible
long after Mathlib has moved on. To deliberately advance to a newer Mathlib,
run `./update-mathlib.sh` instead (that one does rewrite those files).

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
AGENTS.md                    Règles agnostiques pour les agents IA de codage
SORRIES.md                   Historique des obligations désormais closes
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
Aucun axiome propre au projet, aucune preuve admise et aucun `native_decide` (CI
bloquante). Toute structure d'hypothèses a un habitant concret dans
`Nonvacuity.lean`. Les principes logiques signalés par `#print axioms` sont
`propext`, `Classical.choice` et `Quot.sound`, standards dans Lean et Mathlib.

## Licence
[Apache License 2.0](LICENSE).

## Citer ce travail
Le tag `v1.0.3-gleason`, commit
`e21729e0ba5cddcc40dff14a5ae9d2bb0718e878`, reste la version reproductible
précédemment archivée. La version documentaire corrigée prévue est
`v1.0.4-gleason`. Lorsqu'elle aura été fusionnée et taguée, citer le SHA exact du
commit porté par ce nouveau tag ainsi que les métadonnées de [`CITATION.cff`](CITATION.cff).

Identifiants propres à la future version `v1.0.4-gleason` :

- SHA du commit tagué : `[EXACT TAG COMMIT SHA TO BE ADDED]`
- DOI Zenodo : `[ZENODO VERSION DOI TO BE ADDED]`
- SWHID : `[SWHID TO BE ADDED]`

Ces espaces réservés indiquent explicitement que les identifiants de la nouvelle
version ne sont pas encore disponibles ; aucun DOI ni SWHID n'est revendiqué ici.

---

## English translation

# gleason — Lean 4 formalization of Busch's (2003) and Gleason's theorems

**Status: PROJECT COMPLETE (2026-07-11).** This repository provides a complete
Lean 4 and Mathlib formalization of finite-dimensional complex versions of:
1. **Busch's theorem (2003)**: every effect measure (POVM) on ℂⁿ is represented
   by a unique density operator (holds already at n = 2);
2. **Gleason's theorem**: likewise for projection measures, n ≥ 3, via the
   Cooke–Keane–Moran / Richman–Bridges route;
3. **Corollary**: no "dispersion-free" measure (valued in {0,1}) exists in
   dimension ≥ 3 — an end-to-end integration test of the representation.

Projection measures must be additive on orthogonal subspaces, not merely on
subspaces with trivial intersection. Lattice disjointness would impose a different
and substantially stronger condition. It is not equivalent to the hypothesis of
Gleason's theorem and is not satisfied by general Born measures.

For Busch, the Lean structure `EffectMeasure` uses binary additivity on admissible
sums of effects. Finite additivity follows by iteration, and this hypothesis is
sufficient for the finite-dimensional result formalized here. The original
presentation is commonly stated for finite or countable families whose sum is
bounded by the identity; the Lean statement is therefore not presented as
textually identical to every formulation in the literature.

## Getting started
```bash
./setup.sh          # cache + build from the pinned version (~10 min with cache)
./scripts/guard.sh  # audit: no project-specific axioms; sorry occurrence count
```
`setup.sh` builds exactly the version pinned in `lean-toolchain` and
`lake-manifest.json` — it never modifies them, so any commit/tag stays
reproducible (important if you cite this repo). To deliberately move to a
newer Mathlib, use `./update-mathlib.sh` separately (that one does rewrite
these files).

## Verifying the proofs

```bash
./setup.sh              # one-time: cache + build from the pinned version
lake build              # rebuild everything; must finish green
./scripts/guard.sh      # 0 axiom, 0 native_decide; sorry count from this script
                         # also matches the word "sorry" inside comments/docstrings —
                         # grep '\bsorry\b' Gleason for actual `sorry` tactics (there are none)
```

`setup.sh` never touches `lean-toolchain` or `lake-manifest.json` — it builds
exactly the pinned version, so any given commit/tag remains reproducible long
after Mathlib has moved on. To deliberately advance to a newer Mathlib, run
`./update-mathlib.sh` instead (that one does rewrite those files).

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
AGENTS.md                      Agent-agnostic rules for AI coding agents
SORRIES.md                     Historical record of completed obligations
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
No project-specific axioms, admitted proofs, or `native_decide` (CI-blocking).
Every hypothesis structure has a concrete inhabitant in `Nonvacuity.lean`. The
logical principles reported by `#print axioms` are `propext`, `Classical.choice`,
and `Quot.sound`, all standard in Lean and Mathlib.

## License
[Apache License 2.0](LICENSE).

## Citing this work
Tag `v1.0.3-gleason`, commit
`e21729e0ba5cddcc40dff14a5ae9d2bb0718e878`, remains the previously archived
reproducible release. The planned corrected documentation release is
`v1.0.4-gleason`. Once it has been merged and tagged, cite the exact commit SHA
carried by that new tag together with the metadata in [`CITATION.cff`](CITATION.cff).

Version-specific identifiers for the future `v1.0.4-gleason` release:

- Tagged commit SHA: `[EXACT TAG COMMIT SHA TO BE ADDED]`
- Zenodo DOI: `[ZENODO VERSION DOI TO BE ADDED]`
- SWHID: `[SWHID TO BE ADDED]`

These explicit placeholders mean that identifiers for the new release are not yet
available; no DOI or SWHID is claimed here.
