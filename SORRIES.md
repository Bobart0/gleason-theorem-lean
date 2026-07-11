# Suivi des sorry (mettre à jour à chaque commit qui en ferme un)

**PROJET COMPLET — 2026-07-11.** `lake build` vert, `./scripts/guard.sh` : 0 axiome,
0 `native_decide` (le compteur de "sorry" du script matche aussi le mot dans les
commentaires/docstrings — grep `\bsorry\b` sur le code montre qu'aucun ne reste comme
tactique). `#print axioms` sur les quatre théorèmes livrés (actif dans `Main.lean`) :
`Gleason.gleason`, `Gleason.busch`, `Gleason.busch_born_rule`, `Gleason.no_dispersion_free`
→ `propext, Classical.choice, Quot.sound` uniquement, dans les quatre cas.

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
- [x] busch_born_rule (corollaire direct de `busch`, appliqué aux `projL A`)


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
- [x] F. frameFunction_exact_pole : f̄/f_, C dénombrable, Warmup II, densité (§5)
      — ExactPole.lean (nouveau fichier). F0 (SphereGeometry.lean) : lat_neg,
      eq_pole_of_lat_eq_one, exists_northern_rep. F1 : crude_lower_bound,
      exists_inf_approx (m₀ := sInf, réutilisable sans hypothèse externe),
      weight_eq_pole_add_equator (W = f p + 2c), c_le_f (réutilise C5). F2 :
      latSup/latInf (enveloppes sup/inf par classe de latitude),
      latSup_le_latInf_of_lt (monotonie croisée, cœur, via E5
      frameFunction_le_of_lat_lt + eq_pole_of_lat_eq_one pour le cas l'=1),
      extrémités l=0 (équateur, hconst) / l=1 (singleton {p}). F3 :
      countable_latGap (C := écart latInf<latSup dénombrable, injection dans
      ℚ via intervalles ordonnés-disjoints). F4 : latInf_le_latSup,
      latClass_const_of_not_mem_gap, latInf_additive_of_not_mem_gap (base de
      B7 + représentants nord + parité P2). F5 : latInf_mono/latSup_mono
      (monotonie globale, sans restriction), latInf_eq_affine_of_not_mem_C
      (application de warmup_II à G := (latInf-c)/(f p-c)), density
      (target_le_latInf / latSup_le_target via exists_not_mem_of_countable
      + le_of_forall_pos_lt_add, extension de l'affinité à TOUT [0,1], pas
      seulement hors de C) ⇒ latInf_eq_latSup_eq_affine. F6 :
      frameFunction_exact_pole (assemblage : cas dégénéré c=f p à part, cas
      général via exists_northern_rep + parité pour couvrir la sphère
      entière, pas seulement l'hémisphère nord)
- [x] G. frameFunction_attains_sup/inf : ultrafiltre + rotations + descente à
      2 pas (§6) — Attainment.lean (nouveau fichier) + exists_two_step_descent
      (Descent.lean). G1 : boîte à outils isométries
      (isometry_of_orthonormal_triples/pair, exists_isometry_of_unit,
      exists_isometry_pair — cas colinéaire via Cauchy-Schwarz dérivé
      directement de norm_sq_sub_inner_smul plutôt qu'un lemme Mathlib nommé —
      comp_isometry, add/neg/const/sub). G2 : exists_rotate90 (rotation 90°
      autour de p, expose u1/u2 pour G3/G8/G9). G3 : recenter + recenter_prop/
      northern + exists_recenter_isometry. G4 : symmetrize_frame/bounds/
      equator (h_q := g+g∘phat). G5 : exists_ultrafilter_tendsto_sphere/Icc
      (limites le long de `Ultrafilter.of atTop`, motif isCompact_iff_
      ultrafilter_le_nhds), suite maximisante (exists_seq_tendsto_sSup),
      q_n (représentant nord, parité), c'_n → 1. G6 : limite ponctuelle h
      (choix point par point le long de l'ultrafiltre), frame function de
      poids 2W (Tendsto.add sur la somme de trame + tendsto_nhds_unique),
      bornes, h(p)=2M₀, constante W−M₀ sur l'équateur — attention : les bornes
      de h_n doivent utiliser M₀ (sSup exact), pas la borne M fournie en
      hypothèse, sous peine de casser le budget d'epsilon de G9. G7 :
      application de frameFunction_exact_pole à h (ne demande PAS la
      positivité, contrairement à la crainte initiale). G8
      (exists_two_step_descent, Descent.lean) : descente radiale à 2 pas dans
      le plan méridien (p,e0), nécessaire car piron_chain (E4) a un nombre de
      pas variable — a nécessité clear_value/clear pour un contexte local
      devenu trop lourd (timeouts d'élaboration) et maxHeartbeats 1000000
      local justifié. G9 : assemblage avec budget d'epsilon explicite (2
      applications de basic_lemma_approx via exists_inf_approx_of_le sur
      h_n) ; frameFunction_attains_inf via -f. Remplace l'énoncé provisoire
      de Continuity.lean (jamais la structure réelle de CKM).
- [x] H. frameFunction_regular : p̂/q̂/r̂, claim, h=g−f, 6 grands cercles (§7)
      — Regular.lean. H1 (exists_extremal_frame, lemme-pivot comblant une
      lacune du papier, cf. bloc G) ; H3 (exists_axis_rotate/axis_rotate_coords,
      rotations d'axe génériques) ; H3-H4 (frame_eq_quadratic_of_extremal_triple,
      le Claim, 6 cas dont 2 primaires par télescopage d'identités (I)/(II)) ;
      H2 (normSqQF, cas dégénérés M=m/α=m/α=M) ; H5 (h:=g−f, poids nul, bornée,
      paire, nulle sur 6 cercles) ; H6-H7 (extrema de h via bloc G, cas
      constant ou triple extrémal (p2,q2,r2') avec M2+m2=0 via zéros
      équatoriaux) ; H8 (réapplique le Claim à h) ; H9 (comptage à six
      cercles : diagonales non primées u,w forcées dans le cercle primé
      x2=y2 par tiroir à 2 issues sur 3 témoins (unique_unit_orthogonal_to_pair,
      nouvelle brique dans SphereGeometry.lean, unicité à signe près de
      l'orthogonal d'une paire indépendante) ; r2' ∈ span{u,w} hérite de
      y=z par linéarité ⟹ contradiction M2>0 ⟹ h≡0). `heven` retirée de
      l'énoncé (dérivable via frameFunction_even, bloc A, cf. CLAUDE.md
      règle 3). `#print axioms` : propext, Classical.choice, Quot.sound
      uniquement. **M2 COMPLET.**

## M3 — réduction complexe (source : Dvurečenskij ch. 3, sections réelles)
- [x] M3-0 à M3-2 : extension de base orthonormée complexe
      (exists_orthonormalBasis_extension_complex), additivité finie de
      ProjMeasure.frameFunction, ProjMeasure.isCFrameFunction,
      ProjMeasure.frameFunction_phase, cframe_sum_invariant/cframe_le_weight
      (invariance de restriction, RealSections.lean)
- [x] M3-3 : homogExt (extension homogène de degré 2 de `g`), homogExt_smul/
      nonneg/le
- [x] M3-4 : realSection (plongement ℝ-linéaire E3 → H n associé à un
      triplet orthonormé complexe), isométrique, span-préservant ; exists_Qv
      + homogExt_realSection (applique frameFunction_regular de M2 !)
- [x] M3-5 : exists_phase_adjust (a), exists_unit_orthogonal_to_pair_complex
      (b, LE point d'entrée de n≥3), quadratic_polar_bound/quadratic_lipschitz
      (c, borne polaire générique), g_lipschitz (d, 2W-lipschitzianité de g),
      attains_max_on (e, compacité + continuité)
- [x] M3-6 : peel (identité d'épluchage CKM/Dvurečenskij, cas colinéaire par
      égalité de Cauchy-Schwarz, cas général par Gram-Schmidt (x,v,z) +
      tueur de terme croisé avec témoin explicite ε₀ := B/(K+1))
- [x] M3-7 : infrastructure de sous-espaces — sub_proj_mem_inf_orthogonal (a),
      finrank_inf_orthogonal_add_one (b, via
      Submodule.finrank_add_inf_finrank_orthogonal de Mathlib),
      span_pair_le_of_mem (c)
- [x] M3-8 : homogExt_peel (peel sans hypothèse de norme unité, par transport
      d'homogénéité), exists_symmetric_rep_of_finrank (induction sur
      finrank U, ρ := (g x : ℂ)·rankOne x x + ρ', réutilise
      InnerProductSpace.rankOne de Busch/Main.lean B8, sans le refaire)
- [x] M3-9 : cFrameFunction_regular (Patching.lean, assemblage avec U := ⊤).
      `#print axioms` : propext, Classical.choice, Quot.sound uniquement.
      **M3 COMPLET.**

## Phase O — opérateur (partagée Busch/Gleason, bloc d'assemblage, Operator.lean)
- [x] O0. symmetric_ext_of_quadratic : unicité par polarisation complexe
      (`ext_inner_map`, Mathlib) — aucune hypothèse de symétrie requise pour la
      polarisation elle-même, seulement pour passer de l'égalité des parties
      RÉELLES sur la sphère à l'égalité COMPLEXE partout
      (`IsSymmetric.conj_inner_sym` + homogénéité réelle `x = ‖x‖·u`)
- [x] O1. bornValue_span_singleton : même calcul que la positivité de `busch`
      (`Submodule.starProjection_singleton`, `InnerProductSpace.trace_rankOne`),
      sans hypothèse de symétrie sur ρ (juste `⟪x,ρx⟫ = conj⟪ρx,x⟫`, mêmes
      parties réelles)
- [x] O2a. Infrastructure d'additivité — (i) `Defs.lean` : projL_sup_of_isOrtho
      factorisé depuis les preuves inline (identiques) de
      `EffectMeasure.toProjMeasure` et `pureState` (refactor pur, commit dédié) ;
      (ii) `projL_sup_of_pairwise_isOrtho` (version Finset, même induction que
      M3-1) ; (iii) `bornValue_sum_of_pairwise_isOrtho` (additivité finie de la
      valeur de Born, via distributivité de la trace et de `Re`)
- [x] O2. born_of_quadratic : `A` découpé via `stdOrthonormalBasis ℂ A` (base
      orthonormée de `A` vu comme espace de Hilbert en soi) transportée dans
      `H n` par coercion ; `span(range(A.subtype ∘ e.toBasis)) = A` via
      `Submodule.span_image` + `Basis.span_eq` + `Submodule.map_subtype_top`
      (seul point de plomberie non trivial du bloc, résolu du premier coup en
      copiant le motif de `Mathlib/LinearAlgebra/Basis/Fin.lean`) ; aucun cas
      spécial requis pour `A = ⊥` (la récurrence dégénère correctement)
- [x] O3. isDensityOperator_of_represents : positivité par transport
      d'homogénéité (`t := ‖x‖⁻¹`, `Complex.re_ofReal_mul`) depuis la sphère ;
      trace 1 via O2 en `A := ⊤` pour la partie réelle, symétrie de ρ
      (`LinearMap.trace_eq_sum_inner` + conjugaison, motif de `busch`) pour la
      partie imaginaire nulle.
      `#print axioms` sur les quatre théorèmes : propext, Classical.choice,
      Quot.sound uniquement. **Phase O COMPLÈTE.**

## M4 — assemblage final (Main.lean)
- [x] M4-1. gleason : existence via `m.frameFunction` (frame function complexe de
      poids 1, positive, invariante de phase) → `cFrameFunction_regular` (M3-9) →
      `isDensityOperator_of_represents` + `born_of_quadratic` (O2/O3). Unicité via
      `symmetric_ext_of_quadratic` (O0), pontée par `bornValue_span_singleton` (O1).
      Aucune divergence de convention entre M3-9 et O1/O2/O3 (`⟪ρx,x⟫` partout) —
      pas de lemme-pont nécessaire.
- [x] M4-2. no_dispersion_free : route algébrique pure (pas de connexité de sphère,
      pas de théorème spectral). (a) existence d'une droite de mesure 1 (sinon somme
      nulle sur une base orthonormée = μ⊤ = 1, absurde). (b) toute droite unitaire
      ⊥ x a mesure 0 (base orthonormée étendant (x,y), M3-0 ; deux termes distincts
      de somme ≤ 1 avec l'un valant 1). (c) `positive_inner_self_eq_zero` (mini-lemme,
      Defs.lean). (d) ρ x = x (annule tous les `ρ bᵢ` pour `bᵢ ⊥ x` via (b)+(c),
      reconstruit par `OrthonormalBasis.sum_repr'`). (e) contradiction :
      `w := (√2)⁻¹•(x+y)` pour `y` unitaire ⊥ x (`exists_unit_orthogonal_to_pair_complex`,
      M3-5b — c'est ici que `n ≥ 3` est réellement utilisé) a mesure `1/2`,
      incompatible avec la dichotomie `0 ∨ 1`.
- [x] M4-3. Cérémonie de clôture : `#print axioms` actif dans `Main.lean` pour les
      quatre théorèmes livrés (`gleason`, `busch`, `busch_born_rule`,
      `no_dispersion_free`) → `propext, Classical.choice, Quot.sound` uniquement.
      **PROJET COMPLET.**
