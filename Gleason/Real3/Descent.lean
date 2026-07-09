import Gleason.Real3.SphereGeometry
import Gleason.Real3.Simplex

/-!
# Lemme de descente (CKM §2) — LE morceau dur

Cœur de la preuve élémentaire de Cooke–Keane–Moran : contrôle de l'oscillation d'une
frame function positive par propagation géométrique le long de grands cercles, jusqu'à
produire un point de continuité. Richman–Bridges (1999, §2–4) en donnent une version
quantitative (des ε explicites), plus adaptée à Lean : PRENDRE RB COMME SOURCE.

⚠️ Les énoncés ci-dessous sont PROVISOIRES : le livrable du jalon M2 commence par les
figer (choix des quantificateurs, oscillation vs modules de continuité explicites).
Budget prévu : 3 à 5 semaines, c'est le poste de variance principal du projet.
-/

namespace Gleason

noncomputable section

/-- (Provisoire, M2) Toute frame function positive possède un point de continuité
sur la sphère. Version RB : contrôle quantitatif de l'oscillation près d'un point
où l'inf est presque atteint. -/
theorem exists_continuity_point (f : E3 → ℝ) (W : ℝ)
    (hf : IsFrameFunction f W) (hnn : ∀ x, ‖x‖ = 1 → 0 ≤ f x) :
    ∃ x : E3, ‖x‖ = 1 ∧ ContinuousWithinAt f (Metric.sphere (0 : E3) 1) x := by
  sorry

end
end Gleason
