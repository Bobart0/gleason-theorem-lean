import Gleason.Defs

/-!
# Effets et mesures d'effets (cadre de Busch 2003)

Un **effet** est un opérateur `T` avec `0 ≤ T ≤ 1` (ordre de Loewner). Le théorème de
Busch (2003) remplace les projections de Gleason par les effets : l'hypothèse
d'additivité est PLUS FORTE (elle porte sur beaucoup plus d'objets), la conclusion est
la même (représentation par un opérateur densité), et le résultat vaut dès la
dimension 2 — là où Gleason échoue.

Référence : P. Busch, « Quantum states and generalized observables: a simple proof of
Gleason's theorem », Phys. Rev. Lett. 91 (2003) 120403.
-/

namespace Gleason

open scoped InnerProductSpace

noncomputable section

variable {n : ℕ}

/-- Opérateur positif (symétrique + forme quadratique ≥ 0). -/
def IsPositiveOp (T : H n →ₗ[ℂ] H n) : Prop :=
  LinearMap.IsSymmetric T ∧ ∀ x : H n, 0 ≤ (⟪T x, x⟫_ℂ).re

/-- **Effet** : `0 ≤ T ≤ 1` au sens de Loewner. -/
def IsEffect (T : H n →ₗ[ℂ] H n) : Prop :=
  IsPositiveOp T ∧ IsPositiveOp (1 - T)

/-- **Mesure d'effets** (frame function généralisée de Busch) : positive sur les
effets, normalisée en `1`, finiment additive sur les sommes d'effets qui restent
des effets. -/
structure EffectMeasure (n : ℕ) where
  /-- La fonctionnelle (seules ses valeurs sur les effets ont un sens). -/
  f : (H n →ₗ[ℂ] H n) → ℝ
  nonneg : ∀ T, IsEffect T → 0 ≤ f T
  map_one : f 1 = 1
  additive : ∀ S T, IsEffect S → IsEffect T → IsEffect (S + T) → f (S + T) = f S + f T

namespace EffectMeasure

variable (F : EffectMeasure n)

/-- `f 0 = 0` (prendre `S = T = 0` dans l'additivité). -/
theorem map_zero : F.f 0 = 0 := by
  sorry

/-- Monotonie sur les effets : si `S ≤ T` (c.-à-d. `T - S` positif) alors `f S ≤ f T`. -/
theorem mono {S T : H n →ₗ[ℂ] H n} (hS : IsEffect S) (hT : IsEffect T)
    (h : IsPositiveOp (T - S)) : F.f S ≤ F.f T := by
  sorry

/-- Toute projection orthogonale est un effet. -/
theorem isEffect_projL (A : Submodule ℂ (H n)) : IsEffect (projL A) := by
  sorry

/-- **Pont Busch → Gleason** : la restriction d'une mesure d'effets aux projections
est une mesure de projection. (Additivité : pour `A ⟂ B`,
`projL (A ⊔ B) = projL A + projL B`.) -/
def toProjMeasure (F : EffectMeasure n) : ProjMeasure n where
  μ A := F.f (projL A)
  nonneg A := F.nonneg _ (isEffect_projL F A)
  top_eq_one := by
    -- projL ⊤ = 1
    sorry
  add_isOrtho A B hAB := by
    sorry

end EffectMeasure

end
end Gleason
