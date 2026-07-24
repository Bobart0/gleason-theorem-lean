# Reproducibility notes / Notes de reproductibilité

**FR.** Ce document consigne les conditions exactes dans lesquelles la procédure de
reproduction de [`README.md`](README.md) a été testée pour cette révision du dépôt,
ainsi qu'une procédure de diagnostic pour les reviewers qui rencontreraient un
problème. Pour la correspondance affirmation-du-manuscrit → commande, voir
[`ARTIFACT.md`](ARTIFACT.md). Pour l'audit détaillé des divergences manuscrit/code,
voir [`docs/manuscript-repository-audit.md`](docs/manuscript-repository-audit.md).

**EN.** This document records the exact conditions under which the reproduction
procedure in [`README.md`](README.md) was tested for this revision of the
repository, together with a diagnostic procedure for reviewers who hit a problem.
For the manuscript-claim → command correspondence, see
[`ARTIFACT.md`](ARTIFACT.md). For the detailed manuscript/code divergence audit,
see [`docs/manuscript-repository-audit.md`](docs/manuscript-repository-audit.md).

## Tested environment / Environnement testé

| Item | Value |
| --- | --- |
| OS | Windows 11 Enterprise 10.0.26100 (x86_64) |
| Shell | Git Bash (MSYS2 bash) |
| Lean | `leanprover/lean4:v4.32.0-rc1` (pinned in [`lean-toolchain`](lean-toolchain)) |
| Lake | `5.0.0-src+b4812ae` |
| Mathlib | commit `8bba4200986270d3b30be2bb2f8840af47a7854f` (pinned in [`lake-manifest.json`](lake-manifest.json)) |
| Python | 3.13.7 (used only by `scripts/check_lean_source.py` and `scripts/normalize_axioms.py`) |
| CPU | 16 logical processors |
| Free disk before build | ~478 GB available on the test volume |

These are the versions actually used for this audit; they are not hard requirements
beyond what `lean-toolchain` and `lake-manifest.json` already pin.

## Clean-clone test performed / Test en clone propre réalisé

**FR.** Un clone local indépendant (`git clone .`, sans copier `.lake/`) a été créé,
`git checkout` sur le dernier tag réellement publié (`v1.0.4-jar-audit`), puis
`./setup.sh` et `./scripts/verify.sh` ont été exécutés depuis zéro (aucun `.lake`
préexistant dans le clone). Ceci reproduit fidèlement l'expérience d'un reviewer
qui clone le dépôt public et exécute la séquence documentée.

**EN.** An independent local clone (`git clone .`, without copying `.lake/`) was
created, `git checkout` to the last actually published tag (`v1.0.4-jar-audit`),
then `./setup.sh` and `./scripts/verify.sh` were run from scratch (no pre-existing
`.lake` in the clone). This faithfully reproduces the experience of a reviewer who
clones the public repository and runs the documented sequence.

### Windows path-length prerequisite / Prérequis Windows sur la longueur des chemins

**FR.** Un premier essai, cloné dans un répertoire temporaire profondément imbriqué,
a échoué pendant `lake exe cache get` avec `error: unable to create file ...:
Filename too long` (limite `MAX_PATH` de 260 caractères de Windows, plusieurs
fichiers de Mathlib ayant des chemins longs). **Ce n'est pas un défaut du dépôt** :
c'est un prérequis standard, bien connu, pour toute utilisation de Mathlib sous
Windows. Un second essai, cloné dans un chemin court (`C:\glt\review-copy`) avec

```bash
git config --global core.longpaths true
```

(ou `git -c core.longpaths=true clone ...` pour un clone ponctuel) a réussi sans
autre changement. **Recommandation pour les reviewers Windows** : activer
`core.longpaths` et cloner dans un chemin court (par ex. `C:\gl\`) avant de lancer
`./setup.sh`.

**EN.** A first attempt, cloned into a deeply nested temporary directory, failed
during `lake exe cache get` with `error: unable to create file ...: Filename too
long` (Windows's 260-character `MAX_PATH` limit, since several Mathlib files have
long paths). **This is not a defect in this repository**: it is a standard,
well-known prerequisite for using Mathlib on Windows at all. A second attempt,
cloned into a short path (`C:\glt\review-copy`) with

```bash
git config --global core.longpaths true
```

(or `git -c core.longpaths=true clone ...` for a one-off clone) succeeded with no
other change. **Recommendation for Windows reviewers**: enable `core.longpaths`
and clone into a short path (e.g. `C:\gl\`) before running `./setup.sh`.

### Result / Résultat

With that prerequisite satisfied, the full sequence was run twice in the clean clone:

1. **Unpatched `scripts/verify.sh`** (as committed at tag `v1.0.4-jar-audit`):
   `./setup.sh` succeeded (full cold build, see timing below), but
   `./scripts/verify.sh` **failed** (`diff` reported a mismatch between
   `Verification/axioms.expected` and the freshly computed axiom output — a
   CRLF/LF line-ending artifact of `core.autocrlf=true`, not a content
   difference; see
   [`docs/manuscript-repository-audit.md`](docs/manuscript-repository-audit.md) §6).
2. **Patched `scripts/verify.sh`** (the fix in this working tree, normalizing
   both sides of the axiom diff): re-run in the same clean clone, `./scripts/verify.sh`
   **succeeded**, printing `Verification succeeded:` and the expected
   `[propext, Classical.choice, Quot.sound]` line for all four public results.
   `git status --short` afterward showed only the copied-in fix itself as
   modified — i.e. it would be empty once that fix is part of the tagged commit.

### Observed timing and disk usage (indicative) / Temps et disque observés (indicatifs)

| Measurement | Value | Notes |
| --- | --- | --- |
| `./setup.sh` wall-clock time, cold clone | **14 min 47 s** | `lake exe cache get` reused an already-downloaded compressed cache present on this machine (`Decompressing 8627 already-cached file(s)`), so this figure does **not** include first-time network download time, which depends on bandwidth; the 19 `Gleason/*.lean` files were compiled from scratch (34 s–118 s each) since project-specific `.olean`s are never part of the Mathlib cache |
| `.lake/` directory size after build | ~7.3 GB | ~6.9 GB is Mathlib source + its compiled `.olean`s; ~122 MB is this project's own build output |
| `scripts/verify.sh` (patched) re-run time | a few minutes | dominated by `lake build` re-checking/replaying already-built targets |

These figures are indicative for the tested machine and network conditions, not a
performance guarantee.

## Diagnostic procedure for reviewers / Procédure de diagnostic pour les reviewers

**FR.** Si `./scripts/verify.sh` échoue :
1. Relire le message d'erreur affiché : le script échoue explicitement à l'étape en
   cause (scan des sources, build, ou comparaison d'axiomes) plutôt que
   silencieusement.
2. Si l'échec survient sur la comparaison finale des axiomes et que le contenu
   affiché est visuellement identique de part et d'autre du `diff`, il s'agit très
   probablement d'un artefact de fin de ligne (CRLF/LF) lié à `core.autocrlf` —
   voir la correction déjà appliquée dans ce dépôt.
3. Si l'échec survient pendant `lake exe cache get`, vérifier `core.longpaths`
   (Windows) et la longueur du chemin de clonage.
4. Ne jamais faire passer le script en modifiant `scripts/guard.sh` ou
   `scripts/verify.sh` pour masquer un échec réel (`sorry`, axiome de projet,
   avertissement de build, ou divergence d'axiomes) : cela irait à l'encontre de
   l'objet même du script.

**EN.** If `./scripts/verify.sh` fails:
1. Read the printed error: the script fails explicitly at the stage responsible
   (source scan, build, or axiom comparison) rather than silently.
2. If the failure is at the final axiom comparison and the two sides of the
   `diff` look visually identical, it is most likely a CRLF/LF line-ending
   artifact tied to `core.autocrlf` — see the fix already applied in this
   repository.
3. If the failure happens during `lake exe cache get`, check `core.longpaths`
   (Windows) and the length of the clone path.
4. Never make the script pass by editing `scripts/guard.sh` or
   `scripts/verify.sh` to hide a real failure (a `sorry`, a project axiom, a
   build warning, or an axiom-list mismatch): doing so would defeat the purpose
   of the script.

## Verifying the tag and commit / Vérifier le tag et le commit

```bash
git rev-parse HEAD                 # full commit SHA
git describe --tags --exact-match  # tag name, if HEAD is exactly a tag
git tag -v <tag>                   # signature, if the tag is signed
```

## Expected axiom-audit output / Sortie attendue de l'audit d'axiomes

```
Gleason.busch: [propext, Classical.choice, Quot.sound]
Gleason.busch_born_rule: [propext, Classical.choice, Quot.sound]
Gleason.gleason: [propext, Classical.choice, Quot.sound]
Gleason.no_dispersion_free: [propext, Classical.choice, Quot.sound]
```

This was independently reproduced twice for this audit: once in the main working
copy, and once from a fully cold, independent clean clone of tag `v1.0.4-jar-audit`
(see above).
