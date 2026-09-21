# Release notes — v1.1.1-afm-final

This is the final AFM-facing documentation release of the Busch--Gleason formalization.

## Scientific tree

No Lean source file or theorem body is changed relative to `v1.1.0-journal-audit`
at commit `5c5bc40d2e4a31a0d1b3112fcc9a3e92b2000ec5`.

The public theorem surface used by the AFM article remains:
- `Gleason.busch`
- `Gleason.busch_born_rule`
- `Gleason.gleason`
- `Gleason.no_dispersion_free`

## Publication-facing changes

- clean README wording for the AFM article;
- refresh `CITATION.cff` to version 1.1.1;
- add Zenodo release metadata;
- add an automated GitHub Release workflow.

The pre-release documentation head `bc01211e9308cfd3d96d404c863864b8e063a222` passed the repository's strict CI.

## Trust boundary

The existing `scripts/verify.sh` audit remains authoritative. The four public
results report only `[propext, Classical.choice, Quot.sound]`, with no
project-specific axioms, unresolved `sorry`, or `native_decide`.
