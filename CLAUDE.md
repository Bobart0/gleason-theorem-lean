# CLAUDE.md — Formalisation de Busch (2003) et Gleason en Lean 4 / Mathlib

## Mission
Produire la première formalisation mécanisée, SANS AXIOME, du théorème de Busch
(2003, effets/POVM, dès la dimension 2) puis du théorème de Gleason (projections,
dimension ≥ 3), en dimension finie sur `EuclideanSpace ℂ (Fin n)`.
Ordre : d'abord Busch (jalon M-B, purement algébrique), ensuite Gleason
(cœur analytique CKM/Richman–Bridges dans `Gleason/Real3/`).

L'utilisateur est débutant en Lean et non spécialiste du domaine : c'est TOI qui
portes les mathématiques et le Lean. Explique tes choix en français, brièvement.

## Règles absolues (non négociables)
1. **JAMAIS de `axiom`.** Jamais. Le prédécesseur de ce projet (128k lignes) est mort
   d'un axiome mal quantifié qui rendait `False` dérivable. `./scripts/guard.sh` et la
   CI échouent si le mot apparaît.
2. **JAMAIS `native_decide`**, jamais `admit`, jamais de modification de
   `scripts/guard.sh` pour le faire passer.
3. **Ne JAMAIS affaiblir un énoncé pour faire disparaître une difficulté** (retirer
   une hypothèse de dimension, remplacer l'orthogonalité par la disjonction de
   treillis, restreindre une quantification) sans le signaler EXPLICITEMENT à
   l'utilisateur et attendre son accord. Un `sorry` honnête vaut mieux qu'un théorème
   creux.
4. **Test d'inhabitation dans le même commit** : toute nouvelle structure d'hypothèses
   dans `Defs.lean` ou `Busch/Effects.lean` reçoit immédiatement un habitant concret
   sur ℂ³ (ou ℂ²) dans `Gleason/Nonvacuity.lean`. Si tu n'arrives pas à l'habiter,
   la définition est probablement fausse : STOP, signale-le.
5. **`lake build` après chaque modification.** Ne jamais enchaîner deux modifications
   sans build entre les deux. Une erreur = on répare avant d'avancer.
6. Fichiers ≤ 1500 lignes. Au-delà, découper.
7. Les linters restent ACTIVÉS (pas de `set_option ... false` global).

## Workflow standard
1. Lire l'état : `./scripts/guard.sh` (compte des sorry), `lake build`.
2. Choisir le sorry cible (ordre : Nonvacuity → Defs lemmes → Busch → Real3/Simplex →
   Real3/SphereGeometry → phase O (Operator) → Real3/Descent+Continuity+Regular →
   Complex → Main).
3. Boucle : proposer une preuve → `lake build` → lire les erreurs → corriger.
   Tactiques de recherche : insérer `exact?`, `apply?`, `rw?` et lire la suggestion
   dans la sortie du build ; `simp?` pour minimiser les appels simp.
4. Recherche de noms Mathlib : https://leansearch.net (langage naturel),
   https://loogle.lean-lang.org (par signature), et grep dans
   `.lake/packages/mathlib/Mathlib/`.
5. Quand un sorry tombe : `./scripts/guard.sh`, mettre à jour SORRIES.md, commit
   atomique avec message `feat(fichier): nom_du_lemme`.

## Première tâche (jalon M0→M1) — passe de compilation
Ce squelette a été écrit SANS compilateur : des noms d'API Mathlib ont pu dériver.
Réparer dans l'ordre, fichier par fichier, en gardant les énoncés mathématiquement
identiques :
- `Submodule.IsOrtho` et sa notation `⟂` (sinon écrire `Submodule.IsOrtho A B`) ;
- `Submodule.starProjection` (peut s'appeler `orthogonalProjection'` ou avoir changé) ;
- notation `⟪·,·⟫_ℂ` / `⟪·,·⟫` (`open scoped InnerProductSpace` /
  `RealInnerProductSpace`) ; sinon `inner ℂ x y` (argument 𝕜 explicite récent) ;
- `LinearMap.trace`, `LinearMap.IsSymmetric`, `QuadraticForm`, `OrthonormalBasis` ;
- `ℂ ∙ x` (span d'un singleton).
Tout renommage d'API : commentaire `-- Mathlib: ancien_nom → nouveau_nom`.

## Sources mathématiques
- Busch 2003, PRL 91 120403 (arXiv quant-ph/9909073) : preuve algébrique, suivre le
  plan dans `Gleason/Busch/Main.lean`.
- Cooke–Keane–Moran 1985 (preuve élémentaire de Gleason) ; Richman–Bridges 1999,
  J. Funct. Anal. 162, 287–312 (version quantitative, SOURCE PRINCIPALE pour Real3).
- Dvurečenskij 1992, ch. 3 (réduction complexe).

## Définition de « terminé »
`lake build` vert, `./scripts/guard.sh` : 0 sorry, et
`#print axioms Gleason.gleason` = `propext, Classical.choice, Quot.sound` uniquement.

## Git
Après chaque `sorry` fermé et `lake build` vert :
1. `./scripts/guard.sh`
2. `git add -A && git commit -m "<jalon>: <nom_du_lemme>"`
3. `git push`
Ne JAMAIS utiliser `git push --force` sans demander confirmation explicite à l'utilisateur.

## Pattern anti-lenteur : rw sur grosses sommes substituées
Si un `rw` substitue une variable par une grosse expression (ex. une double somme
∑ p : Fin n × Fin n, ...), et que des `rw`/`simp` suivants doivent la traverser :
généralise-la immédiatemnt sous un nom opaque (`generalize h : expr = T`) avant
de continuer, plutôt que de laisser chaque étape suivante refaire de l'isDefEq/whnf
dans le terme entier. Si un lemme mélange une élaboration lourde avec une preuve
par ailleurs simple, extrais la partie lourde dans un lemme séparé à contexte
minimal (`private theorem ..._assembly`). `maxHeartbeats` élevé masque ce
symptôme sans le corriger, voir Busch/Main.lean:riesz_rep_assembly pour un
exemple résolu.

---

## English translation

# CLAUDE.md — Formalization of Busch (2003) and Gleason in Lean 4 / Mathlib

## Mission
Produce the first mechanized, AXIOM-FREE formalization of Busch's theorem
(2003, effects/POVMs, from dimension 2) and then of Gleason's theorem
(projections, dimension ≥ 3), in finite dimension on `EuclideanSpace ℂ (Fin n)`.
Order: Busch first (milestone M-B, purely algebraic), then Gleason
(CKM/Richman–Bridges analytic core in `Gleason/Real3/`).

The user is a Lean beginner and not a domain specialist: YOU carry the
mathematics and the Lean. Explain your choices in French, briefly.

## Absolute rules (non-negotiable)
1. **NEVER `axiom`.** Ever. This project's predecessor (128k lines) died from a
   mis-quantified axiom that made `False` derivable. `./scripts/guard.sh` and CI
   fail if the word appears.
2. **NEVER `native_decide`**, never `admit`, never modify `scripts/guard.sh` to
   make it pass.
3. **NEVER weaken a statement to make a difficulty disappear** (dropping a
   dimension hypothesis, replacing orthogonality with lattice disjointness,
   restricting a quantifier) without EXPLICITLY flagging it to the user and
   waiting for their agreement. An honest `sorry` is better than a hollow
   theorem.
4. **Inhabitation test in the same commit**: any new hypothesis structure in
   `Defs.lean` or `Busch/Effects.lean` immediately gets a concrete inhabitant on
   ℂ³ (or ℂ²) in `Gleason/Nonvacuity.lean`. If you cannot inhabit it, the
   definition is probably wrong: STOP, flag it.
5. **`lake build` after every change.** Never chain two changes without a build
   in between. An error means fixing it before moving on.
6. Files ≤ 1500 lines. Split beyond that.
7. Linters stay ENABLED (no global `set_option ... false`).

## Standard workflow
1. Read the state: `./scripts/guard.sh` (sorry count), `lake build`.
2. Choose the target sorry (order: Nonvacuity → Defs lemmas → Busch →
   Real3/Simplex → Real3/SphereGeometry → phase O (Operator) →
   Real3/Descent+Continuity+Regular → Complex → Main).
3. Loop: propose a proof → `lake build` → read the errors → fix.
   Search tactics: insert `exact?`, `apply?`, `rw?` and read the suggestion in
   the build output; `simp?` to minimize `simp` calls.
4. Mathlib name search: https://leansearch.net (natural language),
   https://loogle.lean-lang.org (by signature), and grep in
   `.lake/packages/mathlib/Mathlib/`.
5. When a sorry falls: `./scripts/guard.sh`, update SORRIES.md, atomic commit
   with message `feat(file): lemma_name`.

## First task (milestone M0→M1) — compilation pass
This skeleton was written WITHOUT a compiler: Mathlib API names may have
drifted. Fix in order, file by file, keeping the statements mathematically
identical:
- `Submodule.IsOrtho` and its `⟂` notation (otherwise write
  `Submodule.IsOrtho A B`);
- `Submodule.starProjection` (may be called `orthogonalProjection'` or have
  changed);
- `⟪·,·⟫_ℂ` / `⟪·,·⟫` notation (`open scoped InnerProductSpace` /
  `RealInnerProductSpace`); otherwise `inner ℂ x y` (recent explicit 𝕜
  argument);
- `LinearMap.trace`, `LinearMap.IsSymmetric`, `QuadraticForm`,
  `OrthonormalBasis`;
- `ℂ ∙ x` (span of a singleton).
Any API rename: comment `-- Mathlib: old_name → new_name`.

## Mathematical sources
- Busch 2003, PRL 91 120403 (arXiv quant-ph/9909073): algebraic proof, follow
  the plan in `Gleason/Busch/Main.lean`.
- Cooke–Keane–Moran 1985 (elementary proof of Gleason); Richman–Bridges 1999,
  J. Funct. Anal. 162, 287–312 (quantitative version, MAIN SOURCE for Real3).
- Dvurečenskij 1992, ch. 3 (complex reduction).

## Definition of "done"
`lake build` green, `./scripts/guard.sh`: 0 sorry, and
`#print axioms Gleason.gleason` = `propext, Classical.choice, Quot.sound` only.

## Git
After every closed `sorry` and green `lake build`:
1. `./scripts/guard.sh`
2. `git add -A && git commit -m "<milestone>: <lemma_name>"`
3. `git push`
NEVER use `git push --force` without asking the user for explicit confirmation.

## Anti-slowness pattern: `rw` over large substituted sums
If a `rw` substitutes a variable with a large expression (e.g. a double sum
∑ p : Fin n × Fin n, ...), and subsequent `rw`/`simp` calls need to traverse
it: generalize it IMMEDIATELY under an opaque name (`generalize h : expr = T`)
before continuing, rather than letting each subsequent step redo
isDefEq/whnf over the whole term. If a lemma mixes heavy elaboration with an
otherwise simple proof, extract the heavy part into a separate lemma with
minimal context (`private theorem ..._assembly`). A high `maxHeartbeats`
masks this symptom without fixing it — see
Busch/Main.lean:riesz_rep_assembly for a resolved example.
