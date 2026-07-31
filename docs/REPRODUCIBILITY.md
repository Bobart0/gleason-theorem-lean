# Reproducibility / Reproductibilité

**FR.** Ce document décrit la chaîne de reproductibilité technique du dépôt : quelles
versions sont épinglées, où, et comment les vérifier ou les faire évoluer
intentionnellement. Pour le journal d'audit d'un clone de revue (environnement testé,
temps de build, diagnostic d'échec), voir [`../REPRODUCIBILITY.md`](../REPRODUCIBILITY.md)
à la racine du dépôt — ce document-ci est structurel, l'autre est un journal d'essai.

**EN.** This document describes the repository's technical reproducibility chain:
which versions are pinned, where, and how to check them or advance them
intentionally. For the review-clone audit log (tested environment, build timings,
failure diagnostics), see [`../REPRODUCIBILITY.md`](../REPRODUCIBILITY.md) at the
repository root — this document is structural, the other one is a test log.

## Versions épinglées / Pinned versions

- Lean :

  ```
  leanprover/lean4:v4.32.0-rc1
  ```

- Mathlib :

  ```
  8bba4200986270d3b30be2bb2f8840af47a7854f
  ```

**FR.** `lakefile.toml` fixe désormais directement le commit Mathlib (`rev =
"8bba4200986270d3b30be2bb2f8840af47a7854f"` dans la déclaration `[[require]]`), au
lieu de laisser Lake résoudre implicitement la branche `master`. `lake-manifest.json`
enregistre séparément la fermeture transitive exacte de toutes les dépendances
(Mathlib et ses propres dépendances : `aesop`, `batteries`, `Qq`, `importGraph`,
`proofwidgets`, `plausible`, `LeanSearchClient`, `Cli`), chacune avec son `rev` résolu.
Ces deux fichiers doivent être commités ensemble après toute mise à jour : le
manifeste seul décrit fidèlement le commit courant, mais tant que le fichier
d'entrée (`lakefile.toml`) contenait un `rev = master` implicite, une nouvelle
résolution ou un `lake update` ultérieur pouvait ré-avancer silencieusement vers
un autre commit Mathlib sans qu'aucune ligne du dépôt ne l'exprime intentionnellement.
Avec le pin explicite, `lakefile.toml` et `lake-manifest.json` s'accordent : les deux
portent le même SHA, et une résolution future ne bouge que si ce SHA est changé à la
main.

**EN.** `lakefile.toml` now fixes the Mathlib commit directly (`rev =
"8bba4200986270d3b30be2bb2f8840af47a7854f"` in the `[[require]]` declaration),
instead of letting Lake implicitly resolve the `master` branch. `lake-manifest.json`
separately records the exact transitive closure of all dependencies (Mathlib and its
own dependencies: `aesop`, `batteries`, `Qq`, `importGraph`, `proofwidgets`,
`plausible`, `LeanSearchClient`, `Cli`), each with its resolved `rev`. Both files must
be committed together after any update: the manifest alone faithfully describes the
current commit, but as long as the input file (`lakefile.toml`) carried an implicit
`rev = master`, a later re-resolution or `lake update` could silently drift to a
different Mathlib commit with nothing in the repository expressing that
intentionally. With the explicit pin, `lakefile.toml` and `lake-manifest.json` agree:
both carry the same SHA, and a future resolution only moves if that SHA is changed by
hand.

## Reconstruction exacte / Exact reconstruction

```bash
git clone https://github.com/Bobart0/gleason-theorem-lean.git
cd gleason-theorem-lean
lake exe cache get
./scripts/verify.sh
```

**FR.** Ne pas exécuter `lake update` pour reconstruire une version publiée : cela
n'est nécessaire ni pour `setup.sh` ni pour `scripts/verify.sh`, qui utilisent tous
deux les versions déjà commitées dans `lean-toolchain` et `lake-manifest.json` sans
les modifier. La CI (`.github/workflows/ci.yml`) utilise exactement la même
toolchain, le même pin Mathlib et le même manifeste que ceux commités — elle ne fait
pas non plus de `lake update`.

**EN.** Do not run `lake update` to reconstruct a published version: it is not
required by either `setup.sh` or `scripts/verify.sh`, both of which use the versions
already committed in `lean-toolchain` and `lake-manifest.json` without modifying
them. CI (`.github/workflows/ci.yml`) uses exactly the same toolchain, the same
Mathlib pin, and the same manifest as committed — it does not run `lake update`
either.

## Vérification des pins / Pin verification

```bash
cat lean-toolchain
```

```bash
python3 - <<'PY'
import json
m = json.load(open("lake-manifest.json", encoding="utf-8"))
for p in m["packages"]:
    if p["name"] == "mathlib":
        print("rev:     ", p["rev"])
        print("inputRev:", p["inputRev"])
PY
```

**FR.** Les deux commandes ci-dessus doivent afficher `leanprover/lean4:v4.32.0-rc1`
pour la toolchain, et `8bba4200986270d3b30be2bb2f8840af47a7854f` pour `rev` et pour
`inputRev` de Mathlib.

**EN.** The two commands above should print `leanprover/lean4:v4.32.0-rc1` for the
toolchain, and `8bba4200986270d3b30be2bb2f8840af47a7854f` for both `rev` and
`inputRev` of Mathlib.

## Mise à jour intentionnelle / Intentional update

```bash
./update-mathlib.sh <FULL_MATHLIB_COMMIT_SHA>
```

**FR.** Une mise à jour Mathlib doit modifier et valider ensemble, dans le même
commit :
- `lakefile.toml` (nouveau `rev` du `[[require]]` Mathlib) ;
- `lake-manifest.json` (nouvelle fermeture transitive résolue) ;
- `lean-toolchain` (nouvelle toolchain associée au SHA Mathlib demandé) ;
- le code Lean, si l'API Mathlib utilisée a changé entre les deux commits.

Un commit Mathlib futur n'est jamais présumé compatible avant que
`./scripts/verify.sh` ait réussi intégralement (build sans avertissement, scan de
source, et audit d'axiomes identique au bloc attendu) sur le résultat de la mise à
jour.

**EN.** A Mathlib update must change and validate together, in the same commit:
- `lakefile.toml` (new `rev` in the Mathlib `[[require]]`);
- `lake-manifest.json` (newly resolved transitive closure);
- `lean-toolchain` (the toolchain associated with the requested Mathlib SHA);
- Lean source code, if the Mathlib API used here changed between the two commits.

A future Mathlib commit is never assumed compatible until `./scripts/verify.sh` has
fully succeeded (warning-free build, source scan, and an axiom audit identical to the
expected block) on the result of the update.
