# Historique des obligations de preuve closes

**PROJET COMPLET — 2026-07-11.** `lake build` vert, `./scripts/guard.sh` confirme
l'absence d'axiome propre au projet, de preuve admise et de `native_decide` (son
compteur lexical inclut aussi les occurrences dans les commentaires/docstrings).
`#print axioms` sur les quatre théorèmes livrés (actif dans `Main.lean`) :
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
- [x] EffectMeasure.toProjMeasure (2 obligations de preuve, closes)
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
      l'énoncé (dérivable via frameFunction_even, bloc A, cf. AGENTS.md
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

---

## English translation

# Historical record of completed proof obligations

**PROJECT COMPLETE — 2026-07-11.** `lake build` is green; `./scripts/guard.sh`
confirms that there are no project-specific axioms, admitted proofs, or
`native_decide` uses (its lexical counter also includes occurrences in comments
and docstrings). `#print axioms` on the four delivered theorems (active in
`Main.lean`):
`Gleason.gleason`, `Gleason.busch`, `Gleason.busch_born_rule`,
`Gleason.no_dispersion_free` → `propext, Classical.choice, Quot.sound` only, in all
four cases.

## M1 — foundations (easy, do first, in order)
- [x] Nonvacuity.pureState.top_eq_one
- [x] Nonvacuity.pureState.add_isOrtho   ← first real lemma (P_{A⊔B} = P_A + P_B if A ⟂ B)
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
- [x] EffectMeasure.toProjMeasure (2 proof obligations, closed)
- [x] busch (positivity + trace 1 + representation + uniqueness)
- [x] busch_born_rule (direct corollary of `busch`, applied to `projL A`)


## M2 — real analytic core (source: CKM 1985 §2-§7, PDF in the project)
- [x] A. P2 (frameFunction_even), P3 (frameFunction_pair_swap), P4 (frameFunction_P4)
      — SphereGeometry.lean, + reusable infrastructure (exists_orthonormalBasis_of_triple/',
      exists_unit_orthogonal_to_pair, replaces the cross product with dimension counting)
- [x] B. Pole geometry: lat, northern, equator, sperp, descent (B0-B7,
      SphereGeometry.lean) — sperp_core groups norm/orthogonality/lat;
      B6 lat_le_of_mem_descent (polarized Parseval); B7 realizability of
      latitudes (isometry transport, matrix-free)
- [x] C. Basic Lemma (§4, Descent.lean) — reversed architecture: C0 (removes
      the provisional statement exists_continuity_point), C1 (exists_third_orthogonal,
      SphereGeometry.lean), C2 (equator_value_lt), C3 (basic_lemma_approx, the
      core), C4 (basic_lemma, exact), C5 (equator_value_le, for F)
- [x] D. warmup_II: monotone + co-countable + additive-to-1 ⇒ identity (§3)
      — Simplex.lean, 7 sub-lemmas (D1..D6-existence, D5) + assembly,
      cardinal route for the uncountability of Ioo 0 1
- [x] E. piron_chain: chain of descents, lat p t < lat p s (§5, tan/cos
      spiral, Fig. 1-3) — EXPLICIT construction (no limit/IVT) in two
      phases: E2 spiral_amplification (azimuth spiral, Taylor bound +
      Bernoulli), E3 spherePoint_mem_descent_of_tan (tan-based step criterion),
      E4 piron_chain_equator_case / piron_chain_main_case (target case on
      the equator / general case with 2 phase-B steps), E4 piron_chain (assembly,
      dispatch via exists_basis_aligned/exists_sphereCoords); E5
      chain_decreasing + frameFunction_le_of_lat_lt (corollary for f,
      induction on the chain via basic_lemma)
- [x] F. frameFunction_exact_pole: f̄/f_, countable C, Warmup II, density (§5)
      — ExactPole.lean (new file). F0 (SphereGeometry.lean): lat_neg,
      eq_pole_of_lat_eq_one, exists_northern_rep. F1: crude_lower_bound,
      exists_inf_approx (m₀ := sInf, reusable with no external hypothesis),
      weight_eq_pole_add_equator (W = f p + 2c), c_le_f (reuses C5). F2:
      latSup/latInf (sup/inf envelopes per latitude class),
      latSup_le_latInf_of_lt (crossed monotonicity, core, via E5
      frameFunction_le_of_lat_lt + eq_pole_of_lat_eq_one for the l'=1 case),
      extremities l=0 (equator, hconst) / l=1 (singleton {p}). F3:
      countable_latGap (C := countable gap latInf<latSup, injection into
      ℚ via order-disjoint intervals). F4: latInf_le_latSup,
      latClass_const_of_not_mem_gap, latInf_additive_of_not_mem_gap (based on
      B7 + northern representatives + parity P2). F5: latInf_mono/latSup_mono
      (global monotonicity, unrestricted), latInf_eq_affine_of_not_mem_C
      (applying warmup_II to G := (latInf-c)/(f p-c)), density
      (target_le_latInf / latSup_le_target via exists_not_mem_of_countable
      + le_of_forall_pos_lt_add, extending affinity to ALL of [0,1], not
      just outside C) ⇒ latInf_eq_latSup_eq_affine. F6:
      frameFunction_exact_pole (assembly: degenerate case c=f p handled
      separately, general case via exists_northern_rep + parity to cover the
      whole sphere, not just the northern hemisphere)
- [x] G. frameFunction_attains_sup/inf: ultrafilter + rotations + 2-step
      descent (§6) — Attainment.lean (new file) + exists_two_step_descent
      (Descent.lean). G1: isometry toolbox
      (isometry_of_orthonormal_triples/pair, exists_isometry_of_unit,
      exists_isometry_pair — collinear case via Cauchy-Schwarz derived
      directly from norm_sq_sub_inner_smul rather than a named Mathlib lemma —
      comp_isometry, add/neg/const/sub). G2: exists_rotate90 (90° rotation
      about p, exposes u1/u2 for G3/G8/G9). G3: recenter + recenter_prop/
      northern + exists_recenter_isometry. G4: symmetrize_frame/bounds/
      equator (h_q := g+g∘phat). G5: exists_ultrafilter_tendsto_sphere/Icc
      (limits along `Ultrafilter.of atTop`, isCompact_iff_
      ultrafilter_le_nhds pattern), maximizing sequence
      (exists_seq_tendsto_sSup), q_n (northern representative, parity),
      c'_n → 1. G6: pointwise limit h (chosen point by point along the
      ultrafilter), frame function of weight 2W (Tendsto.add on the frame
      sum + tendsto_nhds_unique), bounds, h(p)=2M₀, constant W−M₀ on the
      equator — caution: the bounds on h_n must use M₀ (the exact sSup), not
      the bound M supplied as hypothesis, or the epsilon budget of G9 breaks.
      G7: applying frameFunction_exact_pole to h (does NOT require
      positivity, contrary to the initial worry). G8
      (exists_two_step_descent, Descent.lean): 2-step radial descent in the
      meridian plane (p,e0), needed because piron_chain (E4) has a variable
      number of steps — required clear_value/clear for a local context that
      had grown too heavy (elaboration timeouts) and a justified local
      maxHeartbeats 1000000. G9: assembly with an explicit epsilon budget (2
      applications of basic_lemma_approx via exists_inf_approx_of_le on
      h_n); frameFunction_attains_inf via -f. Replaces the provisional
      statement of Continuity.lean (never the actual CKM structure).
- [x] H. frameFunction_regular: p̂/q̂/r̂, claim, h=g−f, 6 great circles (§7)
      — Regular.lean. H1 (exists_extremal_frame, pivot lemma filling a
      gap in the paper, cf. block G); H3 (exists_axis_rotate/axis_rotate_coords,
      generic axis rotations); H3-H4 (frame_eq_quadratic_of_extremal_triple,
      the Claim, 6 cases of which 2 are primary via telescoping identities (I)/(II));
      H2 (normSqQF, degenerate cases M=m/α=m/α=M); H5 (h:=g−f, zero weight, bounded,
      even, zero on 6 circles); H6-H7 (extrema of h via block G, constant case
      or extremal triple (p2,q2,r2') with M2+m2=0 via equatorial
      zeros); H8 (reapplies the Claim to h); H9 (six-circle counting:
      unprimed diagonals u,w forced into the primed circle
      x2=y2 by a pigeonhole on 2 outcomes among 3 witnesses (unique_unit_orthogonal_to_pair,
      new brick in SphereGeometry.lean, uniqueness up to sign of
      the orthogonal of an independent pair); r2' ∈ span{u,w} inherits
      y=z by linearity ⟹ contradiction M2>0 ⟹ h≡0). `heven` removed from
      the statement (derivable via frameFunction_even, block A, cf. AGENTS.md
      rule 3). `#print axioms`: propext, Classical.choice, Quot.sound
      only. **M2 COMPLETE.**

## M3 — complex reduction (source: Dvurečenskij ch. 3, real sections)
- [x] M3-0 to M3-2: complex orthonormal basis extension
      (exists_orthonormalBasis_extension_complex), finite additivity of
      ProjMeasure.frameFunction, ProjMeasure.isCFrameFunction,
      ProjMeasure.frameFunction_phase, cframe_sum_invariant/cframe_le_weight
      (restriction invariance, RealSections.lean)
- [x] M3-3: homogExt (degree-2 homogeneous extension of `g`), homogExt_smul/
      nonneg/le
- [x] M3-4: realSection (ℝ-linear embedding E3 → H n associated with a
      complex orthonormal triple), isometric, span-preserving; exists_Qv
      + homogExt_realSection (applies frameFunction_regular from M2!)
- [x] M3-5: exists_phase_adjust (a), exists_unit_orthogonal_to_pair_complex
      (b, THE entry point of n≥3), quadratic_polar_bound/quadratic_lipschitz
      (c, generic polar bound), g_lipschitz (d, 2W-Lipschitz property of g),
      attains_max_on (e, compactness + continuity)
- [x] M3-6: peel (CKM/Dvurečenskij peeling identity, collinear case via
      Cauchy-Schwarz equality, general case via Gram-Schmidt (x,v,z) +
      cross-term killer with explicit witness ε₀ := B/(K+1))
- [x] M3-7: subspace infrastructure — sub_proj_mem_inf_orthogonal (a),
      finrank_inf_orthogonal_add_one (b, via
      Submodule.finrank_add_inf_finrank_orthogonal from Mathlib),
      span_pair_le_of_mem (c)
- [x] M3-8: homogExt_peel (peel without the unit-norm hypothesis, via
      transport of homogeneity), exists_symmetric_rep_of_finrank (induction on
      finrank U, ρ := (g x : ℂ)·rankOne x x + ρ', reuses
      InnerProductSpace.rankOne from Busch/Main.lean B8, without redoing it)
- [x] M3-9: cFrameFunction_regular (Patching.lean, assembly with U := ⊤).
      `#print axioms`: propext, Classical.choice, Quot.sound only.
      **M3 COMPLETE.**

## Phase O — operator (shared Busch/Gleason, assembly block, Operator.lean)
- [x] O0. symmetric_ext_of_quadratic: uniqueness via complex polarization
      (`ext_inner_map`, Mathlib) — no symmetry hypothesis is required for the
      polarization itself, only to pass from equality of the REAL parts on the
      sphere to COMPLEX equality everywhere
      (`IsSymmetric.conj_inner_sym` + real homogeneity `x = ‖x‖·u`)
- [x] O1. bornValue_span_singleton: same computation as the positivity of `busch`
      (`Submodule.starProjection_singleton`, `InnerProductSpace.trace_rankOne`),
      with no symmetry hypothesis on ρ (just `⟪x,ρx⟫ = conj⟪ρx,x⟫`, same
      real parts)
- [x] O2a. Additivity infrastructure — (i) `Defs.lean`: projL_sup_of_isOrtho
      factored out of the (identical) inline proofs of
      `EffectMeasure.toProjMeasure` and `pureState` (pure refactor, dedicated
      commit); (ii) `projL_sup_of_pairwise_isOrtho` (Finset version, same
      induction as M3-1); (iii) `bornValue_sum_of_pairwise_isOrtho` (finite
      additivity of the Born value, via distributivity of the trace and of
      `Re`)
- [x] O2. born_of_quadratic: `A` split via `stdOrthonormalBasis ℂ A` (an
      orthonormal basis of `A` viewed as a Hilbert space in its own right)
      transported into `H n` by coercion; `span(range(A.subtype ∘ e.toBasis)) = A`
      via `Submodule.span_image` + `Basis.span_eq` + `Submodule.map_subtype_top`
      (the only non-trivial plumbing point of the block, resolved on the first
      try by copying the pattern from `Mathlib/LinearAlgebra/Basis/Fin.lean`);
      no special case needed for `A = ⊥` (the induction degenerates correctly)
- [x] O3. isDensityOperator_of_represents: positivity via transport of
      homogeneity (`t := ‖x‖⁻¹`, `Complex.re_ofReal_mul`) from the sphere;
      trace 1 via O2 at `A := ⊤` for the real part, symmetry of ρ
      (`LinearMap.trace_eq_sum_inner` + conjugation, `busch` pattern) for the
      vanishing imaginary part.
      `#print axioms` on the four theorems: propext, Classical.choice,
      Quot.sound only. **Phase O COMPLETE.**

## M4 — final assembly (Main.lean)
- [x] M4-1. gleason: existence via `m.frameFunction` (complex frame function of
      weight 1, positive, phase-invariant) → `cFrameFunction_regular` (M3-9) →
      `isDensityOperator_of_represents` + `born_of_quadratic` (O2/O3). Uniqueness via
      `symmetric_ext_of_quadratic` (O0), bridged by `bornValue_span_singleton` (O1).
      No convention mismatch between M3-9 and O1/O2/O3 (`⟪ρx,x⟫` throughout) —
      no bridging lemma needed.
- [x] M4-2. no_dispersion_free: purely algebraic route (no sphere connectedness,
      no spectral theorem). (a) existence of a line of measure 1 (otherwise a zero
      sum over an orthonormal basis = μ⊤ = 1, absurd). (b) every unit line
      ⊥ x has measure 0 (orthonormal basis extending (x,y), M3-0; two distinct
      terms summing to ≤ 1 with one equal to 1). (c) `positive_inner_self_eq_zero`
      (mini-lemma, Defs.lean). (d) ρ x = x (cancels every `ρ bᵢ` for `bᵢ ⊥ x` via
      (b)+(c), reconstructed via `OrthonormalBasis.sum_repr'`). (e) contradiction:
      `w := (√2)⁻¹•(x+y)` for `y` a unit vector ⊥ x
      (`exists_unit_orthogonal_to_pair_complex`, M3-5b — this is where `n ≥ 3` is
      actually used) has measure `1/2`, incompatible with the dichotomy `0 ∨ 1`.
- [x] M4-3. Closing ceremony: live `#print axioms` check in `Main.lean` for the
      four delivered theorems (`gleason`, `busch`, `busch_born_rule`,
      `no_dispersion_free`) → `propext, Classical.choice, Quot.sound` only.
      **PROJECT COMPLETE.**
