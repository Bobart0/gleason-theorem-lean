import Gleason.Busch.Effects

/-!
# Théorème de Busch (2003) — énoncé principal

**Cible du jalon M-B** (avant Gleason). Le chemin de preuve, entièrement algébrique
(aucune analyse fine sur la sphère, contrairement à Gleason) :

1. `f 0 = 0`, additivité finie itérée ;
2. homogénéité rationnelle : `f (q • T) = q * f T` pour `q ∈ ℚ≥0` (bissection dyadique) ;
3. monotonie (déjà dans `Effects.lean`) ⇒ homogénéité RÉELLE par encadrement rationnel ;
4. extension de `f` en fonctionnelle réelle-linéaire sur les opérateurs auto-adjoints
   (tout auto-adjoint est différence d'effets à un facteur positif près) ;
5. représentation de Riesz en dimension finie : la fonctionnelle est `T ↦ Re tr (ρ T)`
   pour un unique `ρ` auto-adjoint ;
6. positivité de `ρ` (tester sur les effets de rang 1) et trace 1 (tester sur `1`).

Chaque étape est un lemme séparé à ajouter ici en M-B ; seul l'énoncé final est figé.
-/

namespace Gleason

noncomputable section

/-- **Théorème de Busch (2003), dimension finie.** Toute mesure d'effets est
représentée par un unique opérateur densité. Vaut dès `n = 1` (et surtout `n = 2`,
où Gleason échoue). -/
theorem busch {n : ℕ} (hn : 1 ≤ n) (F : EffectMeasure n) :
    ∃! ρ : H n →ₗ[ℂ] H n, IsDensityOperator ρ ∧
      ∀ T, IsEffect T → F.f T = (LinearMap.trace ℂ (H n) (ρ ∘ₗ T)).re := by
  sorry

/-- Corollaire : règle de Born sur les projections, dès la dimension 1, sous
l'hypothèse (plus forte que celle de Gleason) d'additivité sur les effets. -/
theorem busch_born_rule {n : ℕ} (hn : 1 ≤ n) (F : EffectMeasure n) :
    ∃ ρ : H n →ₗ[ℂ] H n, IsDensityOperator ρ ∧
      ∀ A : Submodule ℂ (H n), F.toProjMeasure.μ A = bornValue ρ A := by
  sorry

end
end Gleason
