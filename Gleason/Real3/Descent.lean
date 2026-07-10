import Gleason.Real3.SphereGeometry
import Gleason.Real3.Simplex

/-!
# Basic Lemma (CKM 1985 §4, PDF du projet p. 122-123)

Remplace l'énoncé provisoire `exists_continuity_point` (qui ne correspondait pas à la
structure réelle de CKM — acté dans SORRIES.md, bloc C) par le Basic Lemma : si `f p`
est proche du sup et `f` est constante sur l'équateur de `p`, alors `f` décroît le long
de toute descente. Architecture inversée par rapport au papier : la version approchée
(`basic_lemma_approx`) est établie d'abord, la version exacte (`basic_lemma`) en est un
corollaire (limite `ξ → 0`).
-/

namespace Gleason

noncomputable section

/-- **C2.** Si `f` est une frame function bornée par `M`, dont l'inf `m₀` est
approché (même forme que `hm` dans `frameFunction_P4`), constante `= c` sur
l'équateur de `p`, et `f p` est proche du sup (`M - ξ < f p`), alors `c < m₀ + ξ` :
P4 en `s := p` fournit un point de l'équateur avec `f < m₀ + ξ`, qui vaut donc `c`. -/
theorem equator_value_lt {f : E3 → ℝ} {W M m₀ c ξ : ℝ} (hf : IsFrameFunction f W)
    {p : E3} (hp : ‖p‖ = 1)
    (hM : ∀ t : E3, ‖t‖ = 1 → f t ≤ M)
    (hm : ∀ ε > 0, ∃ x : E3, ‖x‖ = 1 ∧ f x < m₀ + ε)
    (hconst : ∀ e ∈ equator p, f e = c)
    (hfp : M - ξ < f p) :
    c < m₀ + ξ := by
  obtain ⟨t, htunit, htp, htlt⟩ := frameFunction_P4 hf hM hm hp hfp
  have hteq : t ∈ equator p := ⟨htunit, htp⟩
  rw [← hconst t hteq]
  exact htlt

end
end Gleason
