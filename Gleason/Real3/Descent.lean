import Gleason.Real3.SphereGeometry
import Gleason.Real3.SphereCoords
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

open scoped RealInnerProductSpace Real

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

/-- **C4 (exact, corollaire de C3).** Mêmes hypothèses que C3 avec `hfp`
remplacé par `hmax : ∀ t unitaire, f t ≤ f p` (`p` réalise le sup) : la
descente ne fait jamais AUGMENTER `f`. Preuve : pour tout `ξ > 0`, C3 avec
`M := f p` (`f p - ξ < f p` trivialement) donne `f s' < f s + ξ` ;
`le_of_forall_pos_lt_add` conclut. -/
theorem basic_lemma {f : E3 → ℝ} {W m₀ c : ℝ} (hf : IsFrameFunction f W)
    {p : E3} (hp : ‖p‖ = 1)
    (hmax : ∀ t : E3, ‖t‖ = 1 → f t ≤ f p)
    (hmlb : ∀ t : E3, ‖t‖ = 1 → m₀ ≤ f t)
    (hm : ∀ ε > 0, ∃ x : E3, ‖x‖ = 1 ∧ f x < m₀ + ε)
    (hconst : ∀ e ∈ equator p, f e = c)
    {s : E3} (hs : ‖s‖ = 1) (hsN : s ∈ northern p) (hsp : s ≠ p)
    {s' : E3} (hs'd : s' ∈ descent p s) :
    f s' ≤ f s := by
  apply le_of_forall_pos_lt_add
  intro ξ hξ
  have hfp : f p - ξ < f p := by linarith
  have h := basic_lemma_approx hf hp hmax hmlb hm hconst hfp hs hsN hsp hs'd
  linarith

/-- **C5 (corollaire, pour le bloc F).** Sous les hypothèses de C4, la valeur
constante `c` sur l'équateur de `p` est un minorant global de `f` : `c ≤ m₀`
par C2 appliqué à `M := f p` pour tout `ξ > 0` (même mécanisme que C4), puis
`c ≤ m₀ ≤ f t` (`hmlb`). -/
theorem equator_value_le {f : E3 → ℝ} {W m₀ c : ℝ} (hf : IsFrameFunction f W)
    {p : E3} (hp : ‖p‖ = 1)
    (hmax : ∀ t : E3, ‖t‖ = 1 → f t ≤ f p)
    (hmlb : ∀ t : E3, ‖t‖ = 1 → m₀ ≤ f t)
    (hm : ∀ ε > 0, ∃ x : E3, ‖x‖ = 1 ∧ f x < m₀ + ε)
    (hconst : ∀ e ∈ equator p, f e = c) :
    ∀ t : E3, ‖t‖ = 1 → c ≤ f t := by
  have hcm : c ≤ m₀ := by
    apply le_of_forall_pos_lt_add
    intro ξ hξ
    have hfp : f p - ξ < f p := by linarith
    exact equator_value_lt hf hp hmax hm hconst hfp
  intro t ht
  linarith [hcm, hmlb t ht]

/- ═══════════════════════════════════════════════════════════════════
   Chaîne de descente de Piron (CKM 1985 §5, PDF p. 123-124, Fig. 1-3).
   Construction EXPLICITE (sans limite ni IVT, contrairement au papier) en
   deux phases : ajustement d'azimut (E2, cette estimée de spirale) puis
   gain de distance pur (deux pas d'azimut opposé, dans E4).
   ═══════════════════════════════════════════════════════════════════ -/

/-- **E2.** Pour tout écart d'azimut `Δ` et tout facteur d'amplification cible
`ρ > 1`, il existe `n` pas d'angle égal `Δ/n` (avec `|Δ/n| < π/2`, condition de
validité du critère de descente) dont l'amplification cumulée
`(cos(Δ/n))⁻¹ⁿ` reste `≤ ρ`. Preuve : `cos x ≥ 1 - x²/2` (borne de Taylor) +
Bernoulli donnent `cos(Δ/n)ⁿ ≥ 1 - Δ²/(2n)`, minoré par `1/ρ` dès que `n`
dépasse un seuil explicite. -/
theorem spiral_amplification (Δ : ℝ) {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ n : ℕ, 0 < n ∧ |Δ| / n < π / 2 ∧ (Real.cos (Δ / n))⁻¹ ^ n ≤ ρ := by
  have hρ0 : 0 < ρ - 1 := by linarith
  set A : ℝ := 2 * |Δ| / π with hA_def
  set B : ℝ := |Δ| with hB_def
  set C : ℝ := Δ ^ 2 * ρ / (2 * (ρ - 1)) with hC_def
  have hA0 : 0 ≤ A := by rw [hA_def]; positivity
  have hB0 : 0 ≤ B := by rw [hB_def]; positivity
  have hC0 : 0 ≤ C := by rw [hC_def]; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (A + B + C)
  have hnR : (0 : ℝ) < n := by linarith
  have hn0 : 0 < n := by exact_mod_cast hnR
  have hnA : A < n := by linarith
  have hnB : B < n := by linarith
  have hnC : C < n := by linarith
  have hangle : |Δ| / n < π / 2 := by
    rw [hA_def, div_lt_iff₀ Real.pi_pos] at hnA
    rw [div_lt_iff₀ hnR]
    linarith
  set x : ℝ := Δ / n with hx_def
  have hxlt1 : |x| < 1 := by
    rw [hx_def, abs_div, abs_of_pos hnR, div_lt_one hnR]
    rw [hB_def] at hnB
    linarith
  have hx2lt1 : x ^ 2 < 1 := by nlinarith [hxlt1, abs_nonneg x, sq_abs x]
  have habs : |x| < π / 2 := by
    rw [hx_def, abs_div, abs_of_pos hnR]
    exact hangle
  have hcospos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo (abs_lt.mp habs)
  have hcosbound : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  have hcosnn : 0 ≤ 1 - x ^ 2 / 2 := by nlinarith [hx2lt1]
  have hbernoulli : 1 + (n : ℝ) * (-(x ^ 2 / 2)) ≤ (1 + (-(x ^ 2 / 2))) ^ n :=
    one_add_mul_le_pow (by nlinarith [hx2lt1]) n
  have hcos_pow : (1 - x ^ 2 / 2) ^ n ≤ Real.cos x ^ n :=
    pow_le_pow_left₀ hcosnn hcosbound n
  have hfinal_pow : 1 - (n : ℝ) * x ^ 2 / 2 ≤ Real.cos x ^ n := by
    calc 1 - (n : ℝ) * x ^ 2 / 2 = 1 + (n : ℝ) * (-(x ^ 2 / 2)) := by ring
      _ ≤ (1 + (-(x ^ 2 / 2))) ^ n := hbernoulli
      _ = (1 - x ^ 2 / 2) ^ n := by ring_nf
      _ ≤ Real.cos x ^ n := hcos_pow
  have hxsq : (n : ℝ) * x ^ 2 = Δ ^ 2 / n := by
    rw [hx_def, div_pow]; field_simp
  rw [hxsq] at hfinal_pow
  have hnC' : Δ ^ 2 * ρ < (n : ℝ) * (2 * (ρ - 1)) := by
    have h := hnC
    rw [hC_def, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (ρ - 1))] at h
    linarith
  have step1 : ρ * (1 - Δ ^ 2 / (n : ℝ) / 2) ≤ ρ * Real.cos x ^ n :=
    mul_le_mul_of_nonneg_left hfinal_pow (by linarith : (0 : ℝ) ≤ ρ)
  have step2 : ρ * (1 - Δ ^ 2 / (n : ℝ) / 2) = ρ - Δ ^ 2 * ρ / (2 * n) := by
    field_simp
  have step3 : Δ ^ 2 * ρ / (2 * (n : ℝ)) ≤ ρ - 1 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ))]
    nlinarith [hnC']
  refine ⟨n, hn0, hangle, ?_⟩
  rw [inv_pow, inv_eq_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < Real.cos x ^ n)]
  linarith [step1, step2, step3]

end
end Gleason
