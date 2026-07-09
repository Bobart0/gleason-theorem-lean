import Mathlib

/-!
# Frame functions sur ℝ³

Cœur analytique de Gleason, voie Cooke–Keane–Moran (1985) / Richman–Bridges (1999).
Une *frame function* de poids `W` sur la sphère unité de ℝ³ est une fonction dont la
somme sur toute base orthonormée vaut `W`. Le théorème dur (`Regular.lean`) : toute
frame function POSITIVE est la restriction d'une forme quadratique.
-/

namespace Gleason

open scoped RealInnerProductSpace

noncomputable section

/-- ℝ³ euclidien. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- **Frame function de poids `W`** : la somme sur toute base orthonormée vaut `W`.
(Seules les valeurs sur la sphère unité comptent.) -/
def IsFrameFunction (f : E3 → ℝ) (W : ℝ) : Prop :=
  ∀ b : OrthonormalBasis (Fin 3) ℝ E3, (∑ i, f (b i)) = W

/-- Une frame function positive est bornée par `W` sur la sphère
(compléter tout vecteur unitaire en base orthonormée, les deux autres termes sont ≥ 0). -/
theorem IsFrameFunction.le_of_nonneg {f : E3 → ℝ} {W : ℝ}
    (hf : IsFrameFunction f W) (hnn : ∀ x, ‖x‖ = 1 → 0 ≤ f x)
    {x : E3} (hx : ‖x‖ = 1) : f x ≤ W := by
  sorry

end
end Gleason
