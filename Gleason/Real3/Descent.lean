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

open scoped RealInnerProductSpace

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

/-- **C3 (le cœur, version approchée).** Mêmes hypothèses que C2 (avec en plus
`hmlb`, un minorant EXPLICITE de `m₀` — l'approché seul ne suffit pas à borner
`f t'` par en dessous à l'étape (iv)), `s ∈ northern p`, `s ≠ p`,
`s' ∈ descent p s` : `f` décroît le long de la descente, à `ξ` près. Preuve :
point de B4b (`∈ descent p s ∩ equator p`, orthogonal à `s`) ; second point par
C1 sur `(sperp p s, s')` ; `frameFunction_pair_swap` (P3) avec `sperp p s`
comme vecteur partagé sur les deux paires donne `f s + f t = f s' + f t'` ;
`f t = c` (`hconst`), `f t' ≥ m₀` (`hmlb`), `c < m₀ + ξ` (C2) ; `linarith`. -/
theorem basic_lemma_approx {f : E3 → ℝ} {W M m₀ c ξ : ℝ} (hf : IsFrameFunction f W)
    {p : E3} (hp : ‖p‖ = 1)
    (hM : ∀ t : E3, ‖t‖ = 1 → f t ≤ M)
    (hmlb : ∀ t : E3, ‖t‖ = 1 → m₀ ≤ f t)
    (hm : ∀ ε > 0, ∃ x : E3, ‖x‖ = 1 ∧ f x < m₀ + ε)
    (hconst : ∀ e ∈ equator p, f e = c)
    (hfp : M - ξ < f p)
    {s : E3} (hs : ‖s‖ = 1) (hsN : s ∈ northern p) (hsp : s ≠ p)
    {s' : E3} (hs'd : s' ∈ descent p s) :
    f s' - ξ < f s := by
  have hs'N : s' ∈ northern p := hs'd.1
  have hs's : ‖s'‖ = 1 := hs'N.1
  have hsperp_s' : ⟪sperp p s, s'⟫ = 0 := hs'd.2
  obtain ⟨t, ⟨htd, hteq⟩, hst⟩ := exists_equator_orthogonal hp hs hsN hsp
  have htN : t ∈ northern p := htd.1
  have htsperp : ⟪sperp p s, t⟫ = 0 := htd.2
  have htunit : ‖t‖ = 1 := htN.1
  obtain ⟨t', ht'unit, ht'sperp, ht's'⟩ :=
    exists_third_orthogonal (sperp p s) s' (norm_sperp hp hs hsN hsp) hs's hsperp_s'
  have husp : ⟪sperp p s, s⟫ = 0 := by
    have h := inner_sperp_self hp hs hsN hsp
    rwa [real_inner_comm (sperp p s) s] at h
  have h := frameFunction_pair_swap hf (norm_sperp hp hs hsN hsp) hs htunit hs's ht'unit
    husp htsperp hst hsperp_s' ht'sperp ht's'
  have hft : f t = c := hconst t hteq
  have hft' : m₀ ≤ f t' := hmlb t' ht'unit
  have hcltm : c < m₀ + ξ := equator_value_lt hf hp hM hm hconst hfp
  linarith [h, hft, hft', hcltm]

end
end Gleason
