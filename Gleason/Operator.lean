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

/-- Unicité : un opérateur symétrique est déterminé par sa forme quadratique sur la
sphère unité (polarisation complexe ; spécifique à ℂ, faux sur ℝ pour les
non-symétriques). Mathlib : `inner_map_polarization` / `LinearMap.ext_inner_map`
ou variante — nom à vérifier. -/
theorem symmetric_ext_of_quadratic {ρ₁ ρ₂ : H n →ₗ[ℂ] H n}
    (h₁ : LinearMap.IsSymmetric ρ₁) (h₂ : LinearMap.IsSymmetric ρ₂)
    (h : ∀ x : H n, ‖x‖ = 1 → (⟪ρ₁ x, x⟫_ℂ).re = (⟪ρ₂ x, x⟫_ℂ).re) :
    ρ₁ = ρ₂ := by
  sorry

/-- La valeur de Born d'une droite est la forme quadratique :
`tr (ρ P_{ℂ∙x}) = ⟪ρ x, x⟫` pour `‖x‖ = 1`. Calcul de trace en base adaptée. -/
theorem bornValue_span_singleton (ρ : H n →ₗ[ℂ] H n) (x : H n) (hx : ‖x‖ = 1) :
    bornValue ρ (ℂ ∙ x) = (⟪ρ x, x⟫_ℂ).re := by
  sorry

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
