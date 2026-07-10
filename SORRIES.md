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

## M-B — Busch 2003 
- [x] EffectMeasure.map_zero
- [x] EffectMeasure.mono
- [x] EffectMeasure.isEffect_projL
- [x] EffectMeasure.toProjMeasure (2 sorry)
- [x] busch (positivité + trace 1 + représentation + unicité)
- [ ] busch_born_rule


## M2 — cœur analytique réel (source : CKM 1985 §2-§7, PDF dans le projet)
- [x] A. P2 (frameFunction_even), P3 (frameFunction_pair_swap), P4 (frameFunction_P4)
      — SphereGeometry.lean, + infra réutilisable (exists_orthonormalBasis_of_triple/',
      exists_unit_orthogonal_to_pair, remplace le produit vectoriel par comptage de dim)
- [x] B. Géométrie du pôle : lat, northern, equator, sperp, descent (B0-B7,
      SphereGeometry.lean) — sperp_core groupe norme/orthogonalité/lat ;
      B6 lat_le_of_mem_descent (Parseval polarisé) ; B7 réalisabilité des
      latitudes (transport d'isométrie, sans matrices)
- [x] C. Basic Lemma (§4, Descent.lean) — architecture inversée : C0 (retire
      l'énoncé provisoire exists_continuity_point), C1 (exists_third_orthogonal,
      SphereGeometry.lean), C2 (equator_value_lt), C3 (basic_lemma_approx, le
      cœur), C4 (basic_lemma, exact), C5 (equator_value_le, pour F)
- [x] D. warmup_II : monotone + co-dénombrable + additif-à-1 ⇒ identité (§3)
      — Simplex.lean, 7 sous-lemmes (D1..D6-existence, D5) + assemblage,
      route cardinale pour la non-dénombrabilité de Ioo 0 1
- [x] E. piron_chain : chaîne de descentes, lat p t < lat p s (§5, spirale
      tan/cos, Fig. 1-3) — construction EXPLICITE (sans limite/IVT) en deux
      phases : E2 spiral_amplification (spirale d'azimut, borne de Taylor +
      Bernoulli), E3 spherePoint_mem_descent_of_tan (critère de pas en tan),
      E4 piron_chain_equator_case / piron_chain_main_case (cas cible sur
      l'équateur / cas général à 2 pas de phase B), E4 piron_chain (assemblage,
      dispatch via exists_basis_aligned/exists_sphereCoords) ; E5
      chain_decreasing + frameFunction_le_of_lat_lt (corollaire pour f,
      récurrence sur la chaîne via basic_lemma)
- [ ] F. frameFunction_exact_pole : f̄/f_, C dénombrable, Warmup II, C=∅ (§5)
- [ ] G. frameFunction_attains_extrema : Tychonoff + rotations + cas radial (§6) [DUR]
- [ ] H. frameFunction_regular : p̂/q̂/r̂, claim, h=g−f, 6 grands cercles (§7)

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
