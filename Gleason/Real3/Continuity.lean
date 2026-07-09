import Gleason.Real3.Descent

/-!
# De la continuité en un point à la continuité partout (CKM §2 fin)

Une frame function continue en UN point de la sphère est continue PARTOUT : la
structure de frame function transporte la continuité le long des bases orthonormées.
-/

namespace Gleason

noncomputable section

/-- (Provisoire, M2) Continuité globale sur la sphère à partir d'un point de
continuité. -/
theorem frameFunction_continuousOn (f : E3 → ℝ) (W : ℝ)
    (hf : IsFrameFunction f W) (hnn : ∀ x, ‖x‖ = 1 → 0 ≤ f x)
    (heven : ∀ x, f (-x) = f x) :
    ContinuousOn f (Metric.sphere (0 : E3) 1) := by
  sorry

end
end Gleason
