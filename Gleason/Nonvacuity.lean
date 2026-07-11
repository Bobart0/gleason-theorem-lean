import Gleason.Defs
import Gleason.Busch.Effects

/-!
# Tests d'inhabitation (non-vacuité)

**Discipline centrale du dépôt.** Chaque structure d'hypothèses doit posséder ici un
habitant CONCRET sur `ℂ³` (un vrai état quantique). C'est le test qui aurait détecté
dès le début les deux défauts fatals de l'ancien développement (types d'hypothèses
vides dès la dimension 2, axiome réfutable).

Règle : aucune structure nouvelle ne rentre dans `Defs.lean` sans son `example :
Nonempty (...)` ici, dans le même commit. Les `sorry` de ce fichier sont la
**première cible de preuve** du jalon M1.
-/

namespace Gleason

open scoped InnerProductSpace

noncomputable section

/-- **État pur** : un vecteur unitaire `ψ` induit la mesure `A ↦ ‖P_A ψ‖²`.
C'est la mesure de Born de l'état `|ψ⟩⟨ψ|`. -/
noncomputable def pureState {n : ℕ} (ψ : H n) (hψ : ‖ψ‖ = 1) : ProjMeasure n where
  μ A := ‖(A.starProjection ψ : H n)‖ ^ 2
  nonneg A := by positivity
  top_eq_one := by
    simp [Submodule.starProjection_top, hψ]
  add_isOrtho A B hAB := by
    have hpA := Submodule.starProjection_apply_mem A ψ
    have hpB := Submodule.starProjection_apply_mem B ψ
    have hkey : (A ⊔ B).starProjection ψ = A.starProjection ψ + B.starProjection ψ := by
      have h : projL (A ⊔ B) ψ = (projL A + projL B) ψ := by
        rw [projL_sup_of_isOrtho hAB]
      simpa [projL] using h
    simp only [hkey, sq]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
      (Submodule.isOrtho_iff_inner_eq.mp hAB _ hpA _ hpB)

/-- ℂ³ porte bien une mesure de projection : le type n'est PAS vide. -/
example : Nonempty (ProjMeasure 3) :=
  ⟨pureState (EuclideanSpace.single 0 1) (by simp)⟩

/-- Le même état pur induit une mesure d'effets (côté Busch) : `T ↦ Re ⟪T ψ, ψ⟫`. -/
noncomputable def pureEffectMeasure {n : ℕ} (ψ : H n) (hψ : ‖ψ‖ = 1) : EffectMeasure n where
  f T := (⟪T ψ, ψ⟫_ℂ).re
  nonneg T hT := hT.1.2 ψ
  map_one := by
    simp [inner_self_eq_norm_sq_to_K, hψ]
  additive S T _ _ _ := by
    simp [LinearMap.add_apply]

/-- ℂ³ porte bien une mesure d'effets : le type n'est PAS vide (et ℂ² aussi, cible Busch). -/
example : Nonempty (EffectMeasure 3) :=
  ⟨pureEffectMeasure (EuclideanSpace.single 0 1) (by simp)⟩

example : Nonempty (EffectMeasure 2) :=
  ⟨pureEffectMeasure (EuclideanSpace.single 0 1) (by simp)⟩

end
end Gleason
