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
./setup.sh          # cache + build à partir de la version figée (~10 min avec cache)
./scripts/guard.sh  # audit : 0 axiome, compte des sorry
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

## Citer ce travail
Version citable recommandée : tag `v1.0.3-gleason`, commit
`e21729e0ba5cddcc40dff14a5ae9d2bb0718e878`
(https://github.com/Bobart0/gleason-theorem-lean/tree/v1.0.3-gleason). `setup.sh`
reconstruit cette version à l'identique (voir « Démarrage » ci-dessus) ; c'est
le premier tag où c'est garanti (correction de reproductibilité de `setup.sh`,
voir historique).

Archive pérenne (indépendante de la disponibilité future de GitHub), archivée
sur [Software Heritage](https://archive.softwareheritage.org/browse/origin/?origin_url=https://github.com/Bobart0/gleason-theorem-lean) :
- Identifiant permanent (commit) : `swh:1:rev:e21729e0ba5cddcc40dff14a5ae9d2bb0718e878`
- Identifiant permanent (contenu) : `swh:1:dir:560c655af0075a721067a726597af09750949bbe`
- Lien direct : https://archive.softwareheritage.org/swh:1:rev:e21729e0ba5cddcc40dff14a5ae9d2bb0718e878

Pour un DOI (ex. Zenodo), relier le dépôt GitHub à un compte Zenodo
(https://zenodo.org/account/settings/github/) puis créer une *release* GitHub
sur ce tag.

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
./setup.sh          # cache + build from the pinned version (~10 min with cache)
./scripts/guard.sh  # audit: 0 axiom, sorry count
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

## Citing this work
Recommended citable version: tag `v1.0.3-gleason`, commit
`e21729e0ba5cddcc40dff14a5ae9d2bb0718e878`
(https://github.com/Bobart0/gleason-theorem-lean/tree/v1.0.3-gleason). `setup.sh`
rebuilds this version identically (see "Getting started" above); this is the
first tag where that's guaranteed (`setup.sh` reproducibility fix, see
history).

Long-term archive (independent of GitHub's future availability), archived on
[Software Heritage](https://archive.softwareheritage.org/browse/origin/?origin_url=https://github.com/Bobart0/gleason-theorem-lean):
- Permanent identifier (commit): `swh:1:rev:e21729e0ba5cddcc40dff14a5ae9d2bb0718e878`
- Permanent identifier (content): `swh:1:dir:560c655af0075a721067a726597af09750949bbe`
- Direct link: https://archive.softwareheritage.org/swh:1:rev:e21729e0ba5cddcc40dff14a5ae9d2bb0718e878

For a DOI (e.g. Zenodo), link the GitHub repo to a Zenodo account
(https://zenodo.org/account/settings/github/) and then create a GitHub
*release* on this tag.
