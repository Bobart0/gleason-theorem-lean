import Gleason.Complex.Patching

/-!
# Réalisation opératorielle (phase O)

De la forme quadratique/sesquilinéaire à l'opérateur densité : positivité, trace 1,
unicité, et formule de Born sur tous les sous-espaces. Cette phase est PARTAGÉE entre
Busch et Gleason — la prouver d'abord côté Busch (M-B) amortit le travail.
-/

namespace Gleason

open scoped InnerProductSpace

noncomputable section

variable {n : ℕ}

/-- **O0.** Unicité : un opérateur symétrique est déterminé par sa forme quadratique sur la
sphère unité (polarisation complexe ; spécifique à ℂ, faux sur ℝ pour les non-symétriques).
Mathlib : `ext_inner_map` (polarisation complexe, sans hypothèse de symétrie sur les deux
opérateurs — la symétrie sert seulement à passer de l'égalité des parties RÉELLES sur la
sphère à l'égalité COMPLEXE partout). -/
theorem symmetric_ext_of_quadratic {ρ₁ ρ₂ : H n →ₗ[ℂ] H n}
    (h₁ : LinearMap.IsSymmetric ρ₁) (h₂ : LinearMap.IsSymmetric ρ₂)
    (h : ∀ x : H n, ‖x‖ = 1 → (⟪ρ₁ x, x⟫_ℂ).re = (⟪ρ₂ x, x⟫_ℂ).re) :
    ρ₁ = ρ₂ := by
  rw [← ext_inner_map]
  intro x
  by_cases hx0 : x = 0
  · subst hx0; simp
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  set u : H n := (‖x‖⁻¹ : ℂ) • x with hu_def
  have hunorm : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ hxnorm]
  have hx_eq : x = (‖x‖ : ℂ) • u := by
    rw [hu_def, smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hxnorm, Complex.ofReal_one, one_smul]
  have hreal1 : (⟪ρ₁ u, u⟫_ℂ).im = 0 := by
    apply Complex.conj_eq_iff_im.mp; exact h₁.conj_inner_sym u u
  have hreal2 : (⟪ρ₂ u, u⟫_ℂ).im = 0 := by
    apply Complex.conj_eq_iff_im.mp; exact h₂.conj_inner_sym u u
  have hux : ⟪ρ₁ u, u⟫_ℂ = ⟪ρ₂ u, u⟫_ℂ := Complex.ext (h u hunorm) (by rw [hreal1, hreal2])
  have hscale : ∀ T : H n →ₗ[ℂ] H n, ⟪T x, x⟫_ℂ = (‖x‖ : ℂ) ^ 2 * ⟪T u, u⟫_ℂ := by
    intro T
    conv_lhs => rw [hx_eq]
    rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    ring
  rw [hscale ρ₁, hscale ρ₂, hux]

/-- **O1.** La valeur de Born d'une droite est la forme quadratique :
`tr (ρ P_{ℂ∙x}) = ⟪ρ x, x⟫` pour `‖x‖ = 1`. Même calcul que la positivité de `busch`
(`Busch/Main.lean`, via `Submodule.starProjection_singleton` et `trace_rankOne`) ; aucune
hypothèse de symétrie sur `ρ` n'est nécessaire (seule la conjugaison `⟪x,ρx⟫ = conj ⟪ρx,x⟫`
sert à passer de l'un à l'autre, qui ont même partie réelle). -/
theorem bornValue_span_singleton (ρ : H n →ₗ[ℂ] H n) (x : H n) (hx : ‖x‖ = 1) :
    bornValue ρ (ℂ ∙ x) = (⟪ρ x, x⟫_ℂ).re := by
  unfold bornValue
  have hcomp : ρ ∘ₗ projL (ℂ ∙ x : Submodule ℂ (H n))
      = ((‖x‖ ^ 2 : ℝ) : ℂ)⁻¹ • (InnerProductSpace.rankOne ℂ (ρ x) x : H n →ₗ[ℂ] H n) := by
    ext1 w
    simp only [LinearMap.comp_apply, projL, ContinuousLinearMap.coe_coe,
      Submodule.starProjection_singleton ℂ, map_smul, LinearMap.smul_apply,
      InnerProductSpace.rankOne_apply, smul_smul, div_eq_inv_mul]
    rfl
  rw [hcomp]
  simp only [map_smul, smul_eq_mul, InnerProductSpace.trace_rankOne, hx, one_pow,
    Complex.ofReal_one, inv_one, one_mul]
  rw [show ⟪x, ρ x⟫_ℂ = starRingEnd ℂ ⟪ρ x, x⟫_ℂ from (inner_conj_symm x (ρ x)).symm,
    Complex.conj_re]

/-- (Phase O) De la représentation quadratique sur les droites à la formule de Born
sur TOUS les sous-espaces : découper `A` en droites orthogonales, additivité des deux
côtés. -/
theorem born_of_quadratic (m : ProjMeasure n) (ρ : H n →ₗ[ℂ] H n)
    (hρ : LinearMap.IsSymmetric ρ)
    (h : ∀ x : H n, ‖x‖ = 1 → m.frameFunction x = (⟪ρ x, x⟫_ℂ).re) :
    ∀ A : Submodule ℂ (H n), m.μ A = bornValue ρ A := by
  sorry

/-- (Phase O) Positivité et trace 1 de l'opérateur obtenu, à partir de la positivité
de la mesure et de `μ ⊤ = 1`. -/
theorem isDensityOperator_of_represents (m : ProjMeasure n) (ρ : H n →ₗ[ℂ] H n)
    (hρ : LinearMap.IsSymmetric ρ)
    (h : ∀ x : H n, ‖x‖ = 1 → m.frameFunction x = (⟪ρ x, x⟫_ℂ).re) :
    IsDensityOperator ρ := by
  sorry

end
end Gleason
