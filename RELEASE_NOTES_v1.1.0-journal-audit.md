# Release notes — v1.1.0-journal-audit

**FR.** Notes de la release coordonnée d'audit pré-journal, premier maillon
(amont) de la chaîne `gleason-theorem-lean → quantum-foundations-lean →
everettian-probability-lean`.

**EN.** Release notes for the coordinated pre-journal audit release, the
first (upstream) link of the `gleason-theorem-lean →
quantum-foundations-lean → everettian-probability-lean` chain.

## Identification

- Selected release tag: `v1.1.0-journal-audit`
- Starting commit SHA (before this release's changes):
  `db97f4d3612521628bdd965f325512302153d30e`
- Lean toolchain: `leanprover/lean4:v4.32.0-rc1`
- Mathlib commit: `8bba4200986270d3b30be2bb2f8840af47a7854f`
  (explicit `rev` in `lakefile.toml`; see
  [`docs/REPRODUCIBILITY.md`](docs/REPRODUCIBILITY.md))

The final tagged commit's own SHA is intentionally not recorded here, since
this file is itself part of the commit that produces it; see the execution
report for that value.

## Scope

**FR.** Release de stabilisation de métadonnées et d'infrastructure CI.
Aucun énoncé mathématique et aucune preuve n'ont été modifiés dans cette
release.

**EN.** Metadata- and CI-infrastructure stabilization release. No
mathematical statement and no proof were changed in this release.

## Public theorems (unchanged)

```lean
Gleason.gleason
Gleason.no_dispersion_free
Gleason.busch
Gleason.busch_born_rule
```

- `Gleason.gleason` : Gleason's projection-measure representation theorem,
  for the concrete space `EuclideanSpace ℂ (Fin n)`, dimension `n ≥ 3`.
- `Gleason.no_dispersion_free` : no dispersion-free ({0,1}-valued) projection
  measure exists in dimension `n ≥ 3`.
- `Gleason.busch` : Busch's (2003) effect-measure representation theorem,
  dimension `n ≥ 1`. States **existence and uniqueness** of a density
  operator `ρ` such that `F.f T = Re tr(ρ T)` for every effect `T`.
- `Gleason.busch_born_rule` : the induced projective Born-rule corollary of
  `Gleason.busch` — an **existential** statement (existence of `ρ`, not
  packaged with the uniqueness clause) giving `F.toProjMeasure.μ A =
  bornValue ρ A` for every subspace `A`.

## Trust boundary

Expected for all four public results (`Verification/Axioms.lean`) and for
the `Gleason.EffectAPI` facade audit (`Verification/EffectAPI.lean`):

```
[propext, Classical.choice, Quot.sound]
```

No project-specific axiom, no `sorry`, no `native_decide`.

## Verification commands

```bash
lake exe cache get
bash scripts/verify.sh
lake env lean Verification/EffectAPI.lean
git diff --check
git status --short
```
