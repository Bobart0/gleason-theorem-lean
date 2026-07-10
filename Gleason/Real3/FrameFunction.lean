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

-- `IsFrameFunction.le_of_nonneg` est dans `SphereGeometry.lean` : elle a besoin de
-- `exists_orthonormalBasis_fst` (complétion en base), et `SphereGeometry` importe
-- déjà `FrameFunction` (l'inverse créerait un cycle).

end
end Gleason
