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
