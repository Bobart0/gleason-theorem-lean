# gleason — Formalisation Lean 4 des théorèmes de Busch (2003) et Gleason

**Statut : PROJET COMPLET (2026-07-11).** Ce dépôt fournit une formalisation
complète en Lean 4 et Mathlib de versions complexes de dimension finie de :
1. **Théorème de Busch (2003)** : toute mesure d'effets (POVM) sur ℂⁿ est représentée
   par un unique opérateur densité pour `n ≥ 1` ;
2. **Théorème de Gleason** : toute mesure de projections sur l'espace concret
   `EuclideanSpace ℂ (Fin n)` est représentée par un unique opérateur densité pour
   `n ≥ 3`, par la voie Cooke–Keane–Moran / Richman–Bridges ;
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
./scripts/verify.sh # build strict, sources actives et dépendances axiomatiques
```
`setup.sh` construit exactement la version figée dans `lean-toolchain` et
`lake-manifest.json` — il ne les modifie jamais, pour que tout commit/tag reste
reconstructible à l'identique (important si tu cites ce dépôt). Pour avancer
délibérément vers une version plus récente de Mathlib, utiliser
`./update-mathlib.sh` séparément (modifie ces fichiers).

## Vérification des preuves

```bash
./setup.sh              # une fois : cache + build depuis les versions figées
./scripts/verify.sh     # vérification stricte utilisée par la CI
```

`setup.sh` never modifies `lean-toolchain` or `lake-manifest.json` — it builds
exactly the pinned version, so that any given commit/tag remains reproducible
long after Mathlib has moved on. To deliberately advance to a newer Mathlib,
run `./update-mathlib.sh` instead (that one does rewrite those files).

Le vérificateur analyse les sources Lean suivies après retrait des commentaires et
des chaînes, rejette les preuves admises et les formes élargissant la base de
confiance, construit le projet sans avertissement Lean, puis compare les quatre
sorties `#print axioms` de [`Verification/Axioms.lean`](Verification/Axioms.lean) au
bloc attendu versionné :

```
Gleason.<name>: [propext, Classical.choice, Quot.sound]
```

Ces trois dépendances sont les principes logiques standards utilisés par Lean et
Mathlib : extensionnalité propositionnelle, choix classique et compatibilité des
quotients. Le projet ne contient aucune preuve admise ni axiome mathématique propre.

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
MILESTONES.md                Registre historique des jalons achevés
Verification/Axioms.lean    Audit des dépendances des quatre résultats publics
scripts/verify.sh            Vérification stricte locale et CI
```

## Jalons
| Jalon| Contenu                 | Critère                                          | État |
| M0   | Squelette compilable    | `lake build` vert                                | ✅ |
| M1   | Fondations              | section M1 de MILESTONES.md achevée              | ✅ |
| M-B  | **Busch 2003 complet**  | `#print axioms busch` propre → annonce/preprint  | ✅ |
| M2   | Régularité réelle ℝ³    | `frameFunction_regular` démontré                 | ✅ |
| M3   | Réduction complexe      | `cFrameFunction_regular` démontré                | ✅ |
| O    | Opérateur (assemblage)  | `isDensityOperator_of_represents` démontré       | ✅ |
| M4   | **Gleason complet**     | `#print axioms gleason` propre                   | ✅ |

## Règles
Aucun axiome propre au projet, aucune preuve admise et aucun `native_decide` (CI
bloquante). Toute structure d'hypothèses a un habitant concret dans
`Nonvacuity.lean`. Les principes logiques signalés par `#print axioms` sont
`propext`, `Classical.choice` et `Quot.sound`, standards dans Lean et Mathlib.

## Formalisations connexes

Deux artefacts publics de Mark J. Soares sont proches par leur sujet :

- *Gleason's Theorem via Busch: A Lean 4 Formalization*, version 1.0.0,
  [DOI 10.5281/zenodo.19739805](https://doi.org/10.5281/zenodo.19739805), publié le
  24 avril 2026. Il traite un espace de Hilbert complexe abstrait de dimension finie
  et de finrank au moins deux. Sa cible publique autonome énonce existence,
  normalisation, représentation et positivité de l'appariement de trace, sans
  énoncer l'unicité. Le présent dépôt utilise les espaces concrets `H n`, atteint
  `n = 1` et énonce l'unicité.
- *Gleason's Theorem: A Lean 4 Formalization*, version 1.0.0,
  [DOI 10.5281/zenodo.21301925](https://doi.org/10.5281/zenodo.21301925), rendu
  public initialement le 10 juillet 2026. Son théorème de projections est plus
  général : espaces de Hilbert séparables réels et complexes, et additivité
  orthogonale dénombrable. Le présent dépôt fournit une preuve alternative plus
  étroite en dimension finie complexe, fondée sur Cooke–Keane–Moran et un recollement
  réel-vers-complexe explicite.

Les horodatages publics sont proches pour les artefacts Gleason de juillet 2026 ;
ils ne permettent aucune conclusion sur une chronologie privée, une connaissance
préalable ou une influence. L'apport distinctif documenté ici est l'artefact conjoint
Busch–Gleason, son infrastructure partagée, son architecture alternative, ses
corollaires et l'analyse d'ingénierie de preuve. Aucune revendication de priorité
n'est faite.

## Licence
[Apache License 2.0](LICENSE).

## Citer ce travail
Le tag `v1.0.3-gleason`, commit
`e21729e0ba5cddcc40dff14a5ae9d2bb0718e878`, reste la version reproductible
précédemment archivée. Les métadonnées générales du logiciel figurent dans
[`CITATION.cff`](CITATION.cff). Pour une future version, ajouter le SHA du tag, le
DOI Zenodo propre à la version et le SWHID uniquement après leur création effective.

---

## English translation

# gleason — Lean 4 formalization of Busch's (2003) and Gleason's theorems

**Status: PROJECT COMPLETE (2026-07-11).** This repository provides a complete
Lean 4 and Mathlib formalization of finite-dimensional complex versions of:
1. **Busch's theorem (2003)**: every effect measure (POVM) on ℂⁿ is represented
   by a unique density operator for `n ≥ 1`;
2. **Gleason's theorem**: every projection measure on the concrete space
   `EuclideanSpace ℂ (Fin n)` is represented by a unique density operator for
   `n ≥ 3`, via the Cooke–Keane–Moran / Richman–Bridges route;
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
./scripts/verify.sh # strict build, active-source, and axiom-dependency audit
```
`setup.sh` builds exactly the version pinned in `lean-toolchain` and
`lake-manifest.json` — it never modifies them, so any commit/tag stays
reproducible (important if you cite this repo). To deliberately move to a
newer Mathlib, use `./update-mathlib.sh` separately (that one does rewrite
these files).

## Verifying the proofs

```bash
./setup.sh              # one-time: cache + build from the pinned versions
./scripts/verify.sh     # strict verification used by CI
```

`setup.sh` never touches `lean-toolchain` or `lake-manifest.json` — it builds
exactly the pinned version, so any given commit/tag remains reproducible long
after Mathlib has moved on. To deliberately advance to a newer Mathlib, run
`./update-mathlib.sh` instead (that one does rewrite those files).

The verifier scans tracked Lean source after removing comments and strings, rejects
admitted proofs and trust-expanding forms, builds without Lean warnings, and
compares the four `#print axioms` results from
[`Verification/Axioms.lean`](Verification/Axioms.lean) with the committed expected
block:

```
Gleason.<name>: [propext, Classical.choice, Quot.sound]
```

These are standard logical principles used by Lean and Mathlib: propositional
extensionality, classical choice, and quotient soundness. The project contains no
admitted proofs or project-specific mathematical axioms.

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
MILESTONES.md                  Historical ledger of completed milestones
Verification/Axioms.lean      Dependency audit for the four public results
scripts/verify.sh              Strict local and CI verification
```

## Milestones
| Milestone | Content                | Criterion                                          | Status |
| M0   | Compilable skeleton    | `lake build` green                               | ✅ |
| M1   | Foundations            | M1 section of MILESTONES.md completed            | ✅ |
| M-B  | **Busch 2003 complete**| clean `#print axioms busch` → announcement/preprint | ✅ |
| M2   | Real regularity ℝ³     | `frameFunction_regular` proved                   | ✅ |
| M3   | Complex reduction      | `cFrameFunction_regular` proved                  | ✅ |
| O    | Operator (assembly)    | `isDensityOperator_of_represents` proved         | ✅ |
| M4   | **Gleason complete**   | clean `#print axioms gleason`                    | ✅ |

## Rules
No project-specific axioms, admitted proofs, or `native_decide` (CI-blocking).
Every hypothesis structure has a concrete inhabitant in `Nonvacuity.lean`. The
logical principles reported by `#print axioms` are `propext`, `Classical.choice`,
and `Quot.sound`, all standard in Lean and Mathlib.

## Related formalizations

Two public artifacts by Mark J. Soares are closely related in subject:

- *Gleason's Theorem via Busch: A Lean 4 Formalization*, version 1.0.0,
  [DOI 10.5281/zenodo.19739805](https://doi.org/10.5281/zenodo.19739805), released
  24 April 2026. It uses an abstract finite-dimensional complex Hilbert space of
  finrank at least two. Its standalone public target states existence,
  normalization, representation, and nonnegative trace pairing, but not uniqueness.
  The present repository uses concrete `H n`, reaches `n = 1`, and states uniqueness.
- *Gleason's Theorem: A Lean 4 Formalization*, version 1.0.0,
  [DOI 10.5281/zenodo.21301925](https://doi.org/10.5281/zenodo.21301925), initially
  released publicly 10 July 2026. Its projection theorem is more general: separable
  real and complex Hilbert spaces with countable orthogonal additivity. The present
  repository supplies a narrower alternative finite-dimensional complex proof based
  on Cooke–Keane–Moran and explicit real-to-complex patching.

The public timestamps of the July 2026 Gleason artifacts are nearly contemporaneous;
they do not establish private chronology, prior knowledge, or influence. The
distinctive contribution documented here is the joint Busch–Gleason artifact,
shared infrastructure, alternative architecture, corollaries, and proof-engineering
analysis. No priority claim is made.

## License
[Apache License 2.0](LICENSE).

## Citing this work
Tag `v1.0.3-gleason`, commit
`e21729e0ba5cddcc40dff14a5ae9d2bb0718e878`, remains the previously archived
reproducible release. General software metadata is provided in
[`CITATION.cff`](CITATION.cff). For a future version, add the tagged commit SHA,
version-specific Zenodo DOI, and SWHID only after they have actually been created.
