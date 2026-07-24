# Changelog / Historique des versions

**FR.** Ce fichier recense les tags publiés de ce dépôt. Il complète
[`MILESTONES.md`](MILESTONES.md), qui détaille l'historique scientifique et
technique des jalons de preuve ; ce fichier se limite aux versions livrées.

**EN.** This file lists the published tags of this repository. It complements
[`MILESTONES.md`](MILESTONES.md), which records the scientific and technical
history of proof milestones; this file is limited to shipped releases.

## [Unreleased]

**FR.** Changements en attente d'un commit et d'un tag final pour la soumission
au *Journal of Automated Reasoning*, non encore publiés :
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

**EN.** Changes pending a final commit and tag for the *Journal of Automated
Reasoning* submission, not yet published:
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
