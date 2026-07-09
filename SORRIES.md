# Suivi des sorry (mettre à jour à chaque commit qui en ferme un)

## M1 — fondations (faciles, à faire en premier, dans l'ordre)
- [x] Nonvacuity.pureState.top_eq_one
- [x] Nonvacuity.pureState.add_isOrtho   ← premier vrai lemme (P_{A⊔B} = P_A + P_B si A ⟂ B)
- [x] Nonvacuity.pureEffectMeasure.map_one
- [x] Nonvacuity.pureEffectMeasure.additive
- [x] ProjMeasure.bot_eq_zero
- [x] ProjMeasure.add_orthogonal_compl
- [x] ProjMeasure.le_one
- [x] ProjMeasure.mono

## M-B — Busch 2003 (cible de publication n°1)
- [x] EffectMeasure.map_zero
- [x] EffectMeasure.mono
- [x] EffectMeasure.isEffect_projL
- [x] EffectMeasure.toProjMeasure (2 sorry)
- [ ] busch (à décomposer en ~6 lemmes, plan dans Busch/Main.lean)
- [ ] busch_born_rule

## M2 — cœur analytique réel (le dur)
- [ ] bounded_additive_affine (Simplex — semaine 1, échauffement)
- [ ] IsFrameFunction.le_of_nonneg
- [ ] exists_orthonormalBasis_fst / _pair / frame_pair_sum_eq (SphereGeometry)
- [ ] exists_continuity_point (Descent — 3 à 5 semaines, poste de variance principal)
- [ ] frameFunction_continuousOn (Continuity)
- [ ] frameFunction_regular (Regular)

## M3 — réduction complexe
- [ ] ProjMeasure.isCFrameFunction
- [ ] ProjMeasure.frameFunction_phase
- [ ] cFrameFunction_regular (Patching)

## Phase O — opérateur (partagée Busch/Gleason)
- [ ] symmetric_ext_of_quadratic
- [ ] bornValue_span_singleton
- [ ] born_of_quadratic
- [ ] isDensityOperator_of_represents

## M4 — assemblage
- [ ] gleason
- [ ] no_dispersion_free
