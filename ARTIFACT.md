# Artifact description / Description de l'artefact

**FR.** Ce document décrit l'artefact logiciel qui accompagne la soumission à
*Journal of Automated Reasoning* et indique, pour chaque affirmation vérifiable du
manuscrit, la commande exacte qui la contrôle. Pour l'installation et le détail des
temps de build, voir [`REPRODUCIBILITY.md`](REPRODUCIBILITY.md). Pour la description
scientifique complète, voir [`README.md`](README.md).

**EN.** This document describes the software artifact accompanying the submission to
the *Journal of Automated Reasoning* and lists, for every checkable claim in the
manuscript, the exact command that verifies it. For installation and build-time
details, see [`REPRODUCIBILITY.md`](REPRODUCIBILITY.md). For the full scientific
description, see [`README.md`](README.md).

## What the artifact is / Nature de l'artefact

**FR.** Un développement Lean 4 / Mathlib complet, vérifié par le noyau, formalisant :
1. le théorème de représentation de Busch (2003) sur les effets, `n ≥ 1` ;
2. le théorème de représentation de Gleason sur les projections, `n ≥ 3` ;
3. un corollaire d'exclusion des mesures « dispersion-free » en dimension ≥ 3.

**EN.** A complete, kernel-checked Lean 4 / Mathlib development formalizing:
1. Busch's (2003) effect representation theorem, `n ≥ 1`;
2. Gleason's projection representation theorem, `n ≥ 3`;
3. a corollary excluding dispersion-free measures in dimension ≥ 3.

It is not an experimental artifact in the empirical-sciences sense: there is no data,
no randomness, and no numerical approximation. Every reported result is a kernel-checked
proof term; "reproducing" this artifact means rebuilding and re-checking that term, not
re-running an experiment that could give a different numeric answer.

## Claim-by-claim verification map / Correspondance affirmation → commande

| Manuscript claim | Verification command | Expected result |
| --- | --- | --- |
| The project builds with the pinned Lean/Mathlib versions | `./setup.sh` | `lake build` completes; no error |
| No admitted proof, no forbidden escape hatch in active Lean source | `scripts/verify.sh` (source-scan stage) | `Lean source scan passed (21 tracked files).` |
| The build emits no Lean warnings | `scripts/verify.sh` (build stage) | `Build completed successfully (N jobs).`, no `warning:` line |
| `Gleason.busch`, `Gleason.busch_born_rule`, `Gleason.gleason`, `Gleason.no_dispersion_free` depend only on `[propext, Classical.choice, Quot.sound]` | `scripts/verify.sh` (axiom-audit stage), or manually: `lake env lean Verification/Axioms.lean` | Four lines, each `[propext, Classical.choice, Quot.sound]`; script exits 0 |
| `ProjMeasure 3` and `EffectMeasure 2/3` are inhabited (non-vacuity) | Included in `lake build` via `Gleason/Nonvacuity.lean`, which is imported by `Gleason.lean` and `Gleason/Main.lean` | Build succeeds (the three `example : Nonempty (...)` terms type-check) |
| The repository is left clean by the verification sequence | `git status --short` after `./setup.sh && ./scripts/verify.sh` | empty output |
| No code dependency on the two related Soares repositories | `grep -RIn "^import " --include=*.lean . \| grep -v "import Mathlib\|import Gleason"` | no output |

## Reusability / Réutilisabilité

**FR.** Les définitions centrales (`ProjMeasure`, `EffectMeasure`, `IsDensityOperator`,
`bornValue`, `projL`) et plusieurs lemmes d'infrastructure (extension de bases
orthonormées, cas d'égalité de positivité, additivité des projections orthogonales)
sont documentés comme candidats à une contribution amont vers Mathlib
(voir la section « Library-facing contributions » du manuscrit), mais ce dépôt ne
prétend reporter que leurs versions locales, telles qu'utilisées par l'artefact
soumis.

**EN.** The core definitions (`ProjMeasure`, `EffectMeasure`, `IsDensityOperator`,
`bornValue`, `projL`) and several infrastructure lemmas (orthonormal-basis extension,
positivity equality cases, orthogonal-projection additivity) are documented as
candidates for upstream contribution to Mathlib (see the manuscript's "Library-facing
contributions" section), but this repository reports only their repository-local
versions, as used by the submitted artifact.

## Known non-scientific limitation / Limitation non scientifique connue

**FR.** Sur les postes Windows où `git config core.autocrlf` vaut `true`, un
`checkout` peut convertir les fins de ligne de `Verification/axioms.expected` en
CRLF ; `scripts/verify.sh` normalise désormais les deux côtés de la comparaison
d'axiomes pour rester insensible à ce détail de plateforme. Voir
[`docs/manuscript-repository-audit.md`](docs/manuscript-repository-audit.md) §6.

**EN.** On Windows machines where `git config core.autocrlf` is `true`, a checkout
can convert `Verification/axioms.expected` to CRLF line endings; `scripts/verify.sh`
now normalizes both sides of the axiom comparison so it is insensitive to this
platform detail. See
[`docs/manuscript-repository-audit.md`](docs/manuscript-repository-audit.md) §6.
