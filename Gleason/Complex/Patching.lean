import Gleason.Complex.RealSections

/-!
# Recollement des sections et sesquilinéarité (jalon M3)

Recolle les formes quadratiques obtenues sur chaque section réelle en une forme
sesquilinéaire globale sur ℂⁿ (`n ≥ 3`), réalisée par un opérateur symétrique.
Sources : Dvurečenskij ch. 3 (à suivre ligne à ligne) ; polarisation complexe
(`inner_map_polarization` côté Mathlib) — LÉGITIME ici car la sesquilinéarité est
d'abord établie géométriquement, pas supposée.
-/

namespace Gleason

open scoped InnerProductSpace

noncomputable section

/-- (Provisoire, M3) **Régularité complexe** : toute frame function complexe positive
et invariante de phase sur ℂⁿ, `n ≥ 3`, est de la forme `x ↦ Re ⟪ρ x, x⟫` pour un
opérateur symétrique `ρ`. -/
theorem cFrameFunction_regular {n : ℕ} (hn : 3 ≤ n) (g : H n → ℝ) (W : ℝ)
    (hg : IsCFrameFunction g W) (hnn : ∀ x, ‖x‖ = 1 → 0 ≤ g x)
    (hphase : ∀ (c : ℂ) (x : H n), ‖c‖ = 1 → g (c • x) = g x) :
    ∃ ρ : H n →ₗ[ℂ] H n, LinearMap.IsSymmetric ρ ∧
      ∀ x, ‖x‖ = 1 → g x = (⟪ρ x, x⟫_ℂ).re := by
  sorry

end
end Gleason
