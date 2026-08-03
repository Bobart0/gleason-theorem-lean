# Changelog / Historique des versions

**FR.** Ce fichier recense les tags publiés de ce dépôt. Il complète
[`MILESTONES.md`](MILESTONES.md), qui détaille l'historique scientifique et
technique des jalons de preuve ; ce fichier se limite aux versions livrées.

**EN.** This file lists the published tags of this repository. It complements
[`MILESTONES.md`](MILESTONES.md), which records the scientific and technical
history of proof milestones; this file is limited to shipped releases.

## [Unreleased]

## [v1.1.0-journal-audit] — 2026-08-03

**FR.** Release coordonnée d'audit pré-journal (dépôts Gleason,
quantum-foundations, everettian-probability). Ce dépôt, en amont de la
chaîne, reçoit une stabilisation de métadonnées et d'infrastructure CI, sans
changement d'énoncé mathématique ni de preuve :
- CI : `lean-action` construit désormais explicitement le projet
  (`build: true`) en plus de la vérification stricte de `scripts/verify.sh`.
- Mathlib est désormais épinglé par un `rev` explicite dans `lakefile.toml`
  (`8bba4200986270d3b30be2bb2f8840af47a7854f`), au lieu d'une résolution
  implicite de `master` ; voir [`docs/REPRODUCIBILITY.md`](docs/REPRODUCIBILITY.md).
- `update-mathlib.sh` exige désormais un SHA Mathlib explicite en argument.
- Ajout de la façade publique stable `Gleason.EffectAPI`
  ([`Gleason/EffectAPI.lean`](Gleason/EffectAPI.lean)) et de son audit
  ([`Verification/EffectAPI.lean`](Verification/EffectAPI.lean)), destinés aux
  développements aval (mesure, dilatations de Naimark, représentations de
  chances) ; aucun nouveau résultat mathématique.

**EN.** Coordinated pre-journal audit release (Gleason, quantum-foundations,
everettian-probability repositories). This repository, upstream in the chain,
receives metadata and CI-infrastructure stabilization, with no change to any
mathematical statement or proof:
- CI: `lean-action` now explicitly builds the project (`build: true`) in
  addition to the strict `scripts/verify.sh` check.
- Mathlib is now pinned by an explicit `rev` in `lakefile.toml`
  (`8bba4200986270d3b30be2bb2f8840af47a7854f`), instead of an implicit
  resolution of `master`; see
  [`docs/REPRODUCIBILITY.md`](docs/REPRODUCIBILITY.md).
- `update-mathlib.sh` now requires an explicit Mathlib SHA argument.
- Added the stable public facade `Gleason.EffectAPI`
  ([`Gleason/EffectAPI.lean`](Gleason/EffectAPI.lean)) and its audit
  ([`Verification/EffectAPI.lean`](Verification/EffectAPI.lean)), intended for
  downstream developments (measurement, Naimark dilations, chance
  representations); no new mathematical result.

## [v1.0.5-journal-submission] — 2026-07-25

**FR.** Changements soumis avec ce tag pour la soumission au *Journal of
Automated Reasoning* :
- Correction d'une sensibilité aux fins de ligne (CRLF) dans
  `scripts/verify.sh` sur les checkouts Windows avec `core.autocrlf=true`
  (voir [`docs/manuscript-repository-audit.md`](docs/manuscript-repository-audit.md) §6).
- Ajout de `docs/manuscript-repository-audit.md`, `REPRODUCIBILITY.md`,
  `ARTIFACT.md`, `CHANGELOG.md`.
- Section « Relation avec le manuscrit » ajoutée au `README.md` (FR et EN).
- Correction d'un chemin de fichier erroné dans le manuscrit (table des étapes
  Gleason : `ProjMeasure.frameFunction` référence maintenant
  `Gleason/Complex/RealSections.lean`, et non `FrameFunction.lean`).
- Mise à jour du `.gitignore` (artefacts LaTeX, fichiers d'éditeur).

**EN.** Changes shipped with this tag for the *Journal of Automated
Reasoning* submission:
- Fixed a CRLF line-ending sensitivity in `scripts/verify.sh` on Windows
  checkouts with `core.autocrlf=true` (see
  [`docs/manuscript-repository-audit.md`](docs/manuscript-repository-audit.md) §6).
- Added `docs/manuscript-repository-audit.md`, `REPRODUCIBILITY.md`,
  `ARTIFACT.md`, `CHANGELOG.md`.
- Added a "Relation to the manuscript" section to `README.md` (FR and EN).
- Fixed an incorrect file path in the manuscript (Gleason stages table:
  `ProjMeasure.frameFunction` now references `Gleason/Complex/RealSections.lean`,
  not `FrameFunction.lean`).
- Updated `.gitignore` (LaTeX build artifacts, editor files).

## [v1.0.4-jar-audit] — 2026-07-21

Journal of Automated Reasoning presubmission audit.

## [v1.0.3-gleason] — 2026-07-17

reproductibilite garantie -- version recommandee pour citation.

## [v1.0.2-gleason] — 2026-07-17

documentation bilingue FR/EN.

## [v1.0.1-gleason] — 2026-07-11

documentation, licence et nettoyage de lint.

## [v1.0-gleason] — 2026-07-11

Formalisation complète, sans axiome, de Busch (2003) et Gleason.

## [v1.0-busch] — 2026-07-10

B8: busch — positivité de ρ (dernier `sorry` du théorème de Busch).
