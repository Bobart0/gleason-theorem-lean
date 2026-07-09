import Gleason.Real3.Continuity

/-!
# Régularité des frame functions positives sur ℝ³ (CKM §3 / RB §5)

**Théorème central du cœur analytique réel** : toute frame function positive et paire
sur S² est la restriction d'une forme quadratique. Chemin : continuité
(`Continuity.lean`) → argument d'harmoniques sphériques élémentarisé par CKM
(moyennes sur cercles de latitude, lemme du simplexe) → forme quadratique.
-/

namespace Gleason

noncomputable section

/-- **Régularité (Gleason réel, dimension 3).** Toute frame function positive et
paire est quadratique sur la sphère. -/
theorem frameFunction_regular (f : E3 → ℝ) (W : ℝ)
    (hf : IsFrameFunction f W) (hnn : ∀ x, ‖x‖ = 1 → 0 ≤ f x)
    (heven : ∀ x, f (-x) = f x) :
    ∃ q : QuadraticForm ℝ E3, ∀ x, ‖x‖ = 1 → f x = q x := by
  sorry

end
end Gleason
