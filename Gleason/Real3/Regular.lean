import Gleason.Real3.Attainment

/-!
# Régularité des frame functions positives sur ℝ³ (CKM 1985 §7)

**Théorème central du cœur analytique réel** : toute frame function positive
sur S² est la restriction d'une forme quadratique. Chemin CKM : cadre extrémal
(p,q,r) via le bloc G (H1, lemme-pivot COMBLANT une lacune du papier), deux
rotations d'axe (p̂, r̂) et les identités qu'elles induisent (H3), un « Claim »
de coïncidence f=g sur six grands cercles (H4), puis un second passage du même
argument à h:=g−f (poids nul, H6-H8) conclu par un argument de dénombrement
(H9, six cercles / deux paires de zéros / pigeonhole) qui exclut h≠0.

`heven` (parité) n'est PAS une hypothèse de ce théorème : elle est dérivable de
`hf` seule via `frameFunction_even` (P2, bloc A) — retirée de l'énoncé
d'origine (acté dans SORRIES.md, cf. règle 3 de CLAUDE.md).
-/

namespace Gleason

open scoped RealInnerProductSpace Real

noncomputable section

/- ═══════════════════════════════════════════════════════════════════
   H1 (lemme-pivot, comble une lacune du papier CKM). Étant un pôle `P`
   réalisant le sup d'une frame function bornée `φ` et un point `R0`
   réalisant l'inf, construit un triple orthonormé `(P, S1, U)` avec
   `φ(S1) = Wφ - φ(P) - φ(R0)` et `φ(U) = φ(R0)`.
   ═══════════════════════════════════════════════════════════════════ -/

/-- **H1.** `S1` orthogonal à `P` et `R0` (existence garantie en dimension 3,
`exists_unit_orthogonal_to_pair`) ; deux frames `(P,S1,T1)` et `(R0,S1,T2)`
encadrent `φ(S1)` par les extrema globaux `φ(P)` (max) et `φ(R0)` (min) des
DEUX côtés à la fois, forçant l'égalité `φ(S1) = Wφ-φ(P)-φ(R0)` (double
encadrement). `U` complète `(P,S1)` en un troisième frame, donnant
`φ(U) = φ(R0)` par soustraction. -/
theorem exists_extremal_frame {φ : E3 → ℝ} {Wφ : ℝ} (hφ : IsFrameFunction φ Wφ)
    {P : E3} (hP : ‖P‖ = 1) (hPmax : ∀ t : E3, ‖t‖ = 1 → φ t ≤ φ P)
    {R0 : E3} (hR0 : ‖R0‖ = 1) (hR0lb : ∀ t : E3, ‖t‖ = 1 → φ R0 ≤ φ t)
    (_hne : φ P ≠ φ R0) :
    ∃ S1 U : E3, ‖S1‖ = 1 ∧ ‖U‖ = 1 ∧ ⟪P, S1⟫ = 0 ∧ ⟪P, U⟫ = 0 ∧ ⟪S1, U⟫ = 0 ∧
      φ S1 = Wφ - φ P - φ R0 ∧ φ U = φ R0 := by
  obtain ⟨S1, hS1, hS1P', hS1R0'⟩ := exists_unit_orthogonal_to_pair P R0
  have hPS1 : ⟪P, S1⟫ = 0 := by rw [real_inner_comm]; exact hS1P'
  have hR0S1 : ⟪R0, S1⟫ = 0 := by rw [real_inner_comm]; exact hS1R0'
  obtain ⟨T1, hT1, hPT1, hS1T1⟩ := exists_third_orthogonal P S1 hP hS1 hPS1
  obtain ⟨T2, hT2, hR0T2, hS1T2⟩ := exists_third_orthogonal R0 S1 hR0 hS1 hR0S1
  obtain ⟨b1, hb1_0, hb1_1, hb1_2⟩ :=
    exists_orthonormalBasis_of_triple' P S1 T1 hP hS1 hT1 hPS1 hPT1 hS1T1
  obtain ⟨b2, hb2_0, hb2_1, hb2_2⟩ :=
    exists_orthonormalBasis_of_triple' R0 S1 T2 hR0 hS1 hT2 hR0S1 hR0T2 hS1T2
  have hsum1 := hφ b1
  rw [Fin.sum_univ_three, hb1_0, hb1_1, hb1_2] at hsum1
  have hsum2 := hφ b2
  rw [Fin.sum_univ_three, hb2_0, hb2_1, hb2_2] at hsum2
  have hT1le : φ T1 ≤ φ P := hPmax T1 hT1
  have hT1ge : φ R0 ≤ φ T1 := hR0lb T1 hT1
  have hT2le : φ T2 ≤ φ P := hPmax T2 hT2
  have hT2ge : φ R0 ≤ φ T2 := hR0lb T2 hT2
  have hS1eq : φ S1 = Wφ - φ P - φ R0 := by linarith [hsum1, hsum2, hT1le, hT1ge, hT2le, hT2ge]
  obtain ⟨U, hU, hUP', hUS1'⟩ := exists_unit_orthogonal_to_pair P S1
  have hPU : ⟪P, U⟫ = 0 := by rw [real_inner_comm]; exact hUP'
  have hS1U : ⟪S1, U⟫ = 0 := by rw [real_inner_comm]; exact hUS1'
  obtain ⟨b3, hb3_0, hb3_1, hb3_2⟩ :=
    exists_orthonormalBasis_of_triple' P S1 U hP hS1 hU hPS1 hPU hS1U
  have hsum3 := hφ b3
  rw [Fin.sum_univ_three, hb3_0, hb3_1, hb3_2] at hsum3
  have hUeq : φ U = φ R0 := by linarith [hsum3, hS1eq]
  exact ⟨S1, U, hS1, hU, hPS1, hPU, hS1U, hS1eq, hUeq⟩

/- ═══════════════════════════════════════════════════════════════════
   H3 (préliminaire). Rotation de 90° autour d'un axe `A`, envoyant une
   paire équatoriale prescrite `(X,Y) ↦ (Y,-X)`. Généralise `exists_rotate90`
   (bloc G) qui construisait sa propre paire ; ici `(X,Y)` est DONNÉE (on a
   besoin de coordonnées liées à un triple extrémal spécifique). Réutilisé
   deux fois : `p̂` (axe P, paire (Q,R)) et `r̂` (axe R, paire (P,Q)), puis à
   nouveau en H8 pour `h`.
   ═══════════════════════════════════════════════════════════════════ -/

/-- **H3 (préliminaire).** Même preuve que `exists_rotate90`, avec `(X,Y)`
prescrits au lieu d'auto-générés. -/
private theorem exists_axis_rotate {A X Y : E3} (hA : ‖A‖ = 1) (hX : ‖X‖ = 1) (hY : ‖Y‖ = 1)
    (hAX : ⟪A, X⟫ = 0) (hAY : ⟪A, Y⟫ = 0) (hXY : ⟪X, Y⟫ = 0) :
    ∃ ρ : E3 ≃ₗᵢ[ℝ] E3, ρ A = A ∧ ρ X = Y ∧ ρ Y = -X ∧
      ∀ s ∈ equator A, ρ s ∈ equator A ∧ ⟪s, ρ s⟫ = 0 := by
  have hYX : ⟪Y, X⟫ = 0 := by rw [real_inner_comm]; exact hXY
  have hAnX : ⟪A, -X⟫ = 0 := by rw [inner_neg_right, hAX]; ring
  have hYnX : ⟪Y, -X⟫ = 0 := by rw [inner_neg_right, hYX]; ring
  have hnX : ‖(-X : E3)‖ = 1 := by rw [norm_neg]; exact hX
  obtain ⟨ρ, hρA, hρX, hρY⟩ :=
    isometry_of_orthonormal_triples hA hX hY hAX hAY hXY hA hY hnX hAY hAnX hYnX
  refine ⟨ρ, hρA, hρX, hρY, ?_⟩
  intro s hs
  have hsu : ‖s‖ = 1 := hs.1
  have hsA : ⟪A, s⟫ = 0 := hs.2
  have hρsA : ⟪A, ρ s⟫ = 0 := by rw [← hρA, ρ.inner_map_map]; exact hsA
  have hρsnorm : ‖ρ s‖ = 1 := by rw [ρ.norm_map]; exact hsu
  refine ⟨⟨hρsnorm, hρsA⟩, ?_⟩
  obtain ⟨b, hb0, hb1, hb2⟩ := exists_orthonormalBasis_of_triple' A X Y hA hX hY hAX hAY hXY
  have hdecomp : ⟪X, s⟫ • X + ⟪Y, s⟫ • Y = s := by
    have h := b.sum_repr' s
    rw [Fin.sum_univ_three, hb0, hsA, zero_smul, zero_add, hb1, hb2] at h
    exact h
  set a : ℝ := ⟪X, s⟫ with ha_def
  set c : ℝ := ⟪Y, s⟫ with hc_def
  have hρs_eq : ρ s = a • Y - c • X := by
    rw [← hdecomp, ρ.map_add, ρ.map_smul, ρ.map_smul, hρX, hρY, smul_neg]
    abel
  rw [hρs_eq, ← hdecomp]
  simp only [inner_add_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hX, hY, hXY, hYX]
  ring

/-- **H3 (préliminaire).** Action de `ρ` (issue de `exists_axis_rotate`) sur
les coordonnées `⟪A,·⟫, ⟪X,·⟫, ⟪Y,·⟫` : `⟪a,ρs⟫ = ⟪ρ⁻¹a,s⟫` (isométrie),
puis `ρ⁻¹A=A, ρ⁻¹Y=X, ρ⁻¹X=-Y` (inverse de `ρA=A,ρX=Y,ρY=-X`). -/
private theorem axis_rotate_coords {A X Y : E3} {ρ : E3 ≃ₗᵢ[ℝ] E3}
    (hρA : ρ A = A) (hρX : ρ X = Y) (hρY : ρ Y = -X) (s : E3) :
    ⟪A, ρ s⟫ = ⟪A, s⟫ ∧ ⟪X, ρ s⟫ = -⟪Y, s⟫ ∧ ⟪Y, ρ s⟫ = ⟪X, s⟫ := by
  have hsymm : ∀ a : E3, ⟪a, ρ s⟫ = ⟪ρ.symm a, s⟫ := by
    intro a
    rw [← ρ.inner_map_map (ρ.symm a) s, ρ.apply_symm_apply]
  have hsymmA : ρ.symm A = A := by
    have h := congrArg ρ.symm hρA
    rw [ρ.symm_apply_apply] at h
    exact h.symm
  have hsymmY : ρ.symm Y = X := by
    have h := congrArg ρ.symm hρX
    rw [ρ.symm_apply_apply] at h
    exact h.symm
  have hsymmX : ρ.symm X = -Y := by
    have h := congrArg ρ.symm hρY
    rw [ρ.symm_apply_apply, map_neg] at h
    have h2 := congrArg Neg.neg h
    rw [neg_neg] at h2
    exact h2.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hsymm A, hsymmA]
  · rw [hsymm X, hsymmX, inner_neg_left]
  · rw [hsymm Y, hsymmY]

/- ═══════════════════════════════════════════════════════════════════
   H2 (préliminaires). Forme quadratique de la norme au carré (outil
   partagé par les cas dégénérés et l'assemblage final).
   ═══════════════════════════════════════════════════════════════════ -/

/-- **H2 (outil).** `∑ᵢ ⟪bᵢ,s⟫²` comme forme quadratique, valant `‖s‖²`. -/
def normSqQF (b : OrthonormalBasis (Fin 3) ℝ E3) : QuadraticForm ℝ E3 :=
  QuadraticMap.linMulLin (innerₗ E3 (b 0)) (innerₗ E3 (b 0)) +
  QuadraticMap.linMulLin (innerₗ E3 (b 1)) (innerₗ E3 (b 1)) +
  QuadraticMap.linMulLin (innerₗ E3 (b 2)) (innerₗ E3 (b 2))

theorem normSqQF_apply (b : OrthonormalBasis (Fin 3) ℝ E3) (s : E3) :
    normSqQF b s = ‖s‖ ^ 2 := by
  simp only [normSqQF, QuadraticMap.add_apply, QuadraticMap.linMulLin_apply, innerₗ_apply_apply]
  rw [← b.sum_sq_inner_right s, Fin.sum_univ_three]
  ring

/-- **Régularité (Gleason réel, dimension 3).** Toute frame function positive
est quadratique sur la sphère (`heven` retirée : dérivable via
`frameFunction_even`, cf. le commentaire d'en-tête). -/
theorem frameFunction_regular (f : E3 → ℝ) (W : ℝ)
    (hf : IsFrameFunction f W) (hnn : ∀ x, ‖x‖ = 1 → 0 ≤ f x) :
    ∃ q : QuadraticForm ℝ E3, ∀ x, ‖x‖ = 1 → f x = q x := by
  have hle : ∀ x : E3, ‖x‖ = 1 → f x ≤ W := fun x hx => hf.le_of_nonneg hnn hx
  obtain ⟨p, hp, hpmax⟩ := frameFunction_attains_sup hf hle
  obtain ⟨r0, hr0, hr0lb⟩ := frameFunction_attains_inf hf hnn
  set b0 := EuclideanSpace.basisFun (Fin 3) ℝ with hb0_def
  by_cases hMm : f p = f r0
  · -- **H2a.** M = m : f est constante.
    refine ⟨f p • normSqQF b0, fun x hx => ?_⟩
    have hle1 : f x ≤ f p := hpmax x hx
    have hge1 : f r0 ≤ f x := hr0lb x hx
    have hfx : f x = f p := by linarith [hMm ▸ hge1]
    rw [QuadraticMap.smul_apply, normSqQF_apply, hx]
    norm_num [hfx]
  · -- H1 fournit le triple extrémal (p, q, r) avec f(q) = W - f(p) - f(r0).
    obtain ⟨q, r, hq, hr, hpq, hpr, hqr, hqeq, hreq⟩ :=
      exists_extremal_frame hf hp hpmax hr0 hr0lb hMm
    set M : ℝ := f p with hM_def
    set α : ℝ := f q with hα_def
    set m : ℝ := f r0 with hm_def
    by_cases hαm : α = m
    · -- **H2b.** α = m ⟺ W = M + 2m : f ≡ m sur l'équateur de p, F conclut.
      have hWeq : W = M + 2 * m := by linarith [hqeq, hαm]
      have hconst : ∀ e ∈ equator p, f e = m := by
        intro e he
        obtain ⟨e', he', hpe', hee'⟩ := exists_third_orthogonal p e hp he.1 he.2
        obtain ⟨b, hb0, hb1, hb2⟩ :=
          exists_orthonormalBasis_of_triple' p e e' hp he.1 he' he.2 hpe' hee'
        have hsum := hf b
        rw [Fin.sum_univ_three, hb0, hb1, hb2] at hsum
        have hem : m ≤ f e := hr0lb e he.1
        have he'm : m ≤ f e' := hr0lb e' he'
        linarith [hsum, hWeq, hem, he'm]
      have hexact := frameFunction_exact_pole hf hp hpmax hconst
      refine ⟨m • normSqQF b0 + (M - m) • QuadraticMap.linMulLin (innerₗ E3 p) (innerₗ E3 p),
        fun x hx => ?_⟩
      have hex := hexact x hx
      unfold lat at hex
      rw [hex, QuadraticMap.add_apply, QuadraticMap.smul_apply, QuadraticMap.smul_apply,
        normSqQF_apply, hx, QuadraticMap.linMulLin_apply, innerₗ_apply_apply]
      ring
    · by_cases hαM : α = M
      · -- **H2c.** α = M ⟺ W = 2M + m : f ≡ M sur l'équateur de r0, F sur −f.
        have hWeq : W = 2 * M + m := by linarith [hqeq, hαM]
        have hconst : ∀ e ∈ equator r0, f e = M := by
          intro e he
          obtain ⟨e', he', hr0e', hee'⟩ := exists_third_orthogonal r0 e hr0 he.1 he.2
          obtain ⟨b, hb0, hb1, hb2⟩ :=
            exists_orthonormalBasis_of_triple' r0 e e' hr0 he.1 he' he.2 hr0e' hee'
          have hsum := hf b
          rw [Fin.sum_univ_three, hb0, hb1, hb2] at hsum
          have hem : f e ≤ M := hpmax e he.1
          have he'm : f e' ≤ M := hpmax e' he'
          linarith [hsum, hWeq, hem, he'm]
        have hconst_neg : ∀ e ∈ equator r0, (fun x => -f x) e = -M := by
          intro e he; simp only; rw [hconst e he]
        have hmax_neg : ∀ t : E3, ‖t‖ = 1 → (fun x => -f x) t ≤ (fun x => -f x) r0 := by
          intro t ht; simp only; linarith [hr0lb t ht]
        have hexact := frameFunction_exact_pole hf.neg hr0 hmax_neg hconst_neg
        refine ⟨M • normSqQF b0 - (M - m) • QuadraticMap.linMulLin (innerₗ E3 r0) (innerₗ E3 r0),
          fun x hx => ?_⟩
        have hex := hexact x hx
        unfold lat at hex
        rw [QuadraticMap.sub_apply, QuadraticMap.smul_apply, QuadraticMap.smul_apply,
          normSqQF_apply, hx, QuadraticMap.linMulLin_apply, innerₗ_apply_apply, smul_eq_mul,
          smul_eq_mul]
        linarith [hex]
      · -- Cas principal : m < α < M strictement (H3-H9).
        sorry

end
end Gleason
