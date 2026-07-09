import Gleason.Real3.FrameFunction

/-!
# Lemme du simplexe (échauffement, semaine 1)

Version abstraite du « warm-up » de Cooke–Keane–Moran / du lemme quantitatif de
Richman–Bridges : une fonction bornée sur `[0,1]` dont la somme sur les paires ne
dépend que de la somme des arguments est affine. Preuve par récurrence dyadique +
bornitude (aucun choix, aucune continuité supposée).

C'est le PREMIER lemme analytique à prouver : il valide le style de preuve
(récurrences dyadiques, encadrements) avant d'attaquer la sphère.
-/

namespace Gleason

/-- **Lemme du simplexe.** Si `h` est bornée sur `[0,1]` et si `h x + h y` ne dépend
que de `x + y`, alors `h` est affine sur `[0,1]`. -/
theorem bounded_additive_affine (h : ℝ → ℝ) (C : ℝ)
    (hb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |h x| ≤ C)
    (hadd : ∀ x y u v : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
      u ∈ Set.Icc (0 : ℝ) 1 → v ∈ Set.Icc (0 : ℝ) 1 →
      x + y = u + v → h x + h y = h u + h v) :
    ∃ a b : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, h x = a * x + b := by
  sorry

end Gleason
