import Gleason.Operator
import Gleason.Nonvacuity
import Gleason.Busch.Main

/-!
# Théorème de Gleason — assemblage final

`gleason` assemble : mesure → frame function complexe (`RealSections`) → régularité
complexe (`Patching`, qui repose sur `Real3/Regular`) → opérateur densité et formule
de Born (`Operator`). L'unicité vient de `symmetric_ext_of_quadratic`.

Garde de qualité : à la fin du projet, `#print axioms Gleason.gleason` ne doit
afficher QUE `propext`, `Classical.choice`, `Quot.sound` (et rien d'autre —
en particulier pas `sorryAx`).
-/

namespace Gleason

noncomputable section

/-- **Théorème de Gleason (projections, dimension finie ≥ 3).**
Toute mesure de probabilité finiment additive sur les sous-espaces de ℂⁿ, `n ≥ 3`,
est représentée par un unique opérateur densité via la règle de Born. -/
theorem gleason {n : ℕ} (hn : 3 ≤ n) (m : ProjMeasure n) :
    ∃! ρ : H n →ₗ[ℂ] H n, IsDensityOperator ρ ∧
      ∀ A : Submodule ℂ (H n), m.μ A = bornValue ρ A := by
  sorry

/-- **Test d'intégration** (corollaire classique) : pas de mesure dispersion-free
(à valeurs dans {0,1}) en dimension ≥ 3. Si `gleason` était vacuement vrai ou mal
énoncé, ce corollaire ne sortirait pas — c'est le détecteur anti-vacuité final. -/
theorem no_dispersion_free {n : ℕ} (hn : 3 ≤ n) (m : ProjMeasure n) :
    ¬ (∀ A : Submodule ℂ (H n), m.μ A = 0 ∨ m.μ A = 1) := by
  sorry

-- Audit d'axiomes : décommenter en fin de projet.
-- #print axioms gleason
-- #print axioms busch

end
end Gleason
