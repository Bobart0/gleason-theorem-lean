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

/-- **M3-9 (assemblage).** Toute frame function complexe positive et invariante de phase sur
ℂⁿ, `n ≥ 3`, est de la forme `x ↦ Re ⟪ρ x, x⟫` pour un opérateur symétrique `ρ`. L'hypothèse
`n ≥ 3` n'est utilisée qu'une seule fois dans tout le bloc M3, dans
`exists_unit_orthogonal_to_pair_complex` (M3-5(b)) : c'est le seul point où la géométrie de
ℂⁿ (existence d'un vecteur orthogonal à deux vecteurs donnés) requiert la dimension ≥ 3. -/
theorem cFrameFunction_regular {n : ℕ} (hn : 3 ≤ n) (g : H n → ℝ) (W : ℝ)
    (hg : IsCFrameFunction g W) (hnn : ∀ x, ‖x‖ = 1 → 0 ≤ g x)
    (hphase : ∀ (c : ℂ) (x : H n), ‖c‖ = 1 → g (c • x) = g x) :
    ∃ ρ : H n →ₗ[ℂ] H n, LinearMap.IsSymmetric ρ ∧
      ∀ x, ‖x‖ = 1 → g x = (⟪ρ x, x⟫_ℂ).re := by
  obtain ⟨ρ, hρ_sym, -, hρ_val⟩ :=
    exists_symmetric_rep_of_finrank hg hnn hphase hn (Module.finrank ℂ (⊤ : Submodule ℂ (H n)))
      ⊤ rfl
  refine ⟨ρ, hρ_sym, fun x hx => ?_⟩
  have h1 : ⟪x, ρ x⟫_ℂ = (homogExt g x : ℂ) := hρ_val x Submodule.mem_top
  rw [homogExt_of_unit hx] at h1
  rw [hρ_sym x x, h1]
  simp

end
end Gleason
