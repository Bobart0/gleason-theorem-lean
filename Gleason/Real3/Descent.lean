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

/-- **E4 (assemblage, cas où la cible est sur l'équateur).** `n` pas de phase A
(ajustement d'azimut à rayon `tan θs` croissant géométriquement, via
`spiral_amplification` sur l'azimut cible `ψt - π/2` avec `ρ := 2` arbitraire —
seul l'angle de pas compte ici, pas l'amplification) puis un pas équatorial
terminal (`spherePoint_mem_descent_equatorial`) atterrissant exactement sur
`spherePoint b (π/2) ψt`. -/
private theorem piron_chain_equator_case {p : E3} {b : OrthonormalBasis (Fin 3) ℝ E3}
    (hb0 : b 0 = p) {θs : ℝ} (hθs0 : 0 < θs) (hθs1 : θs < π / 2) (ψt : ℝ) :
    ∃ (n : ℕ) (c : ℕ → E3), c 0 = spherePoint b θs 0 ∧ c n = spherePoint b (π / 2) ψt ∧
      ∀ i < n, c i ≠ p ∧ c (i + 1) ∈ descent p (c i) := by
  have hx0 : 0 < Real.tan θs := Real.tan_pos_of_pos_of_lt_pi_div_two hθs0 hθs1
  have harctan_s : Real.arctan (Real.tan θs) = θs := Real.arctan_tan (by linarith) hθs1
  set Δ' : ℝ := ψt - π / 2 with hΔ'_def
  obtain ⟨n, hn0, hangle, -⟩ := spiral_amplification Δ' (show (1 : ℝ) < 2 by norm_num)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnne : (n : ℝ) ≠ 0 := hnR.ne'
  set φ : ℝ := Δ' / n with hφ_def
  have hφabs : |φ| < π / 2 := by
    rw [hφ_def, abs_div, abs_of_pos hnR]
    exact hangle
  have hcosφpos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hφabs)
  set radius : ℕ → ℝ := fun i => Real.tan θs * (Real.cos φ)⁻¹ ^ i with hradius_def
  set azimuth : ℕ → ℝ := fun i => (i : ℝ) * φ with hazimuth_def
  have hradius_pos : ∀ i, 0 < radius i := fun i => mul_pos hx0 (by positivity)
  have hstepA : ∀ i < n, radius (i + 1) * Real.cos (azimuth (i + 1) - azimuth i) = radius i := by
    intro i _
    have hazi : azimuth (i + 1) - azimuth i = φ := by rw [hazimuth_def]; push_cast; ring
    rw [hazi]
    simp only [hradius_def]
    rw [pow_succ]
    field_simp
  have hchain := tan_chain_step b radius azimuth hradius_pos hstepA
  have hazimuth_n : azimuth n + π / 2 = ψt := by
    have hcancel : azimuth n = Δ' := by rw [hazimuth_def, hφ_def]; field_simp
    rw [hcancel, hΔ'_def]; ring
  set c : ℕ → E3 := fun i =>
    if i ≤ n then spherePoint b (Real.arctan (radius i)) (azimuth i)
    else spherePoint b (π / 2) ψt with hc_def
  refine ⟨n + 1, c, ?_, ?_, ?_⟩
  · rw [hc_def]
    simp only [Nat.zero_le, if_true]
    rw [hradius_def, hazimuth_def]
    norm_num [harctan_s]
  · rw [hc_def]
    simp only [if_neg (show ¬ (n + 1 ≤ n) from by omega)]
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
    · rw [hc_def]
      simp only [if_pos hilt.le, if_pos (show i + 1 ≤ n from by omega)]
      rw [← hb0]
      exact hchain i hilt
    · subst hieq
      rw [hc_def]
      simp only [if_pos (le_refl i), if_neg (show ¬ (i + 1 ≤ i) from by omega)]
      have hθn0 : 0 < Real.arctan (radius i) := Real.arctan_pos.mpr (hradius_pos i)
      have hθn1 : Real.arctan (radius i) < π / 2 := Real.arctan_lt_pi_div_two _
      refine ⟨hb0 ▸ ne_pole_spherePoint b hθn0 hθn1.le _, ?_⟩
      have hstep := spherePoint_mem_descent_equatorial b hθn0 hθn1 (azimuth i)
      rw [hazimuth_n] at hstep
      rwa [hb0] at hstep

/-- E4bis (cas général, `0 < θt < π/2`) : `n` pas de phase A (spirale de rayon
`tan θ` amenant `tan θs` à un rayon `Xn ≤ tan θt`, angle net `ψt`) puis 2 pas de
phase B d'azimuts opposés `±φB` (`cos²φB = Xn/tan θt`) qui remontent le rayon
exactement à `tan θt` en azimut net nul, atterrissant sur `spherePoint b θt ψt`. -/
private theorem piron_chain_main_case {p : E3} {b : OrthonormalBasis (Fin 3) ℝ E3}
    (hb0 : b 0 = p) {θs θt : ℝ} (hθs0 : 0 < θs) (hθs1 : θs < π / 2)
    (hθt0 : 0 < θt) (hθt1 : θt < π / 2) (hθorder : θs < θt) (ψt : ℝ) :
    ∃ (n : ℕ) (c : ℕ → E3), c 0 = spherePoint b θs 0 ∧ c (n + 2) = spherePoint b θt ψt ∧
      ∀ i < n + 2, c i ≠ p ∧ c (i + 1) ∈ descent p (c i) := by
  set x : ℝ := Real.tan θs with hx_def
  set y : ℝ := Real.tan θt with hy_def
  have hx0 : 0 < x := Real.tan_pos_of_pos_of_lt_pi_div_two hθs0 hθs1
  have hy0 : 0 < y := Real.tan_pos_of_pos_of_lt_pi_div_two hθt0 hθt1
  have harctan_s : Real.arctan x = θs := Real.arctan_tan (by linarith) hθs1
  have hxy : x < y := by
    rw [hx_def, hy_def]
    exact Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) hθt1 hθorder
  have hρ : 1 < y / x := (one_lt_div hx0).mpr hxy
  obtain ⟨n, hn0, hangle, hamp⟩ := spiral_amplification ψt hρ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  set φ : ℝ := ψt / n with hφ_def
  have hφabs : |φ| < π / 2 := by
    rw [hφ_def, abs_div, abs_of_pos hnR]
    exact hangle
  have hcosφpos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hφabs)
  set radius : ℕ → ℝ := fun i => x * (Real.cos φ)⁻¹ ^ i with hradius_def
  set azimuth : ℕ → ℝ := fun i => (i : ℝ) * φ with hazimuth_def
  have hradius_pos : ∀ i, 0 < radius i := fun i => mul_pos hx0 (by positivity)
  have hstepA : ∀ i < n, radius (i + 1) * Real.cos (azimuth (i + 1) - azimuth i) = radius i := by
    intro i _
    have hazi : azimuth (i + 1) - azimuth i = φ := by rw [hazimuth_def]; push_cast; ring
    rw [hazi]
    simp only [hradius_def]
    rw [pow_succ]
    field_simp
  have hchain := tan_chain_step b radius azimuth hradius_pos hstepA
  have hazimuth_n : azimuth n = ψt := by rw [hazimuth_def, hφ_def]; field_simp
  set Xn : ℝ := radius n with hXn_def
  have hXnpos : 0 < Xn := hradius_pos n
  have hXnley : Xn ≤ y := by
    have h := mul_le_mul_of_nonneg_left hamp hx0.le
    have hcalc : x * (y / x) = y := by field_simp
    rw [hcalc] at h
    rw [hXn_def, hradius_def]
    exact h
  have hXnynn : 0 ≤ Xn / y := div_nonneg hXnpos.le hy0.le
  have hXnyle1 : Xn / y ≤ 1 := (div_le_one hy0).mpr hXnley
  set φB : ℝ := Real.arccos (Real.sqrt (Xn / y)) with hφB_def
  have hsqrt_nn : 0 ≤ Real.sqrt (Xn / y) := Real.sqrt_nonneg _
  have hsqrt_le1 : Real.sqrt (Xn / y) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hXnyle1
  have hcosφB : Real.cos φB = Real.sqrt (Xn / y) := Real.cos_arccos (by linarith) hsqrt_le1
  have hφB0 : 0 ≤ φB := Real.arccos_nonneg _
  have hφB1 : φB ≤ π / 2 := Real.arccos_le_pi_div_two.mpr hsqrt_nn
  have hcosφB_pos : 0 < Real.cos φB := by
    rw [hcosφB]; exact Real.sqrt_pos.mpr (by positivity)
  have hcos2φB : Real.cos φB ^ 2 = Xn / y := by rw [hcosφB, Real.sq_sqrt hXnynn]
  set θn : ℝ := Real.arctan Xn with hθn_def
  have hθn0 : 0 < θn := Real.arctan_pos.mpr hXnpos
  have hθn1 : θn < π / 2 := Real.arctan_lt_pi_div_two _
  set θn1 : ℝ := Real.arctan (Xn / Real.cos φB) with hθn1_def
  have hXn_div_cosφB_pos : 0 < Xn / Real.cos φB := div_pos hXnpos hcosφB_pos
  have hθn1_0 : 0 < θn1 := Real.arctan_pos.mpr hXn_div_cosφB_pos
  have hθn1_1 : θn1 < π / 2 := Real.arctan_lt_pi_div_two _
  set c : ℕ → E3 := fun i =>
    if i ≤ n then spherePoint b (Real.arctan (radius i)) (azimuth i)
    else if i = n + 1 then spherePoint b θn1 (ψt + φB)
    else spherePoint b θt ψt with hc_def
  refine ⟨n, c, ?_, ?_, ?_⟩
  · rw [hc_def]
    simp only [Nat.zero_le, if_true]
    rw [hradius_def, hazimuth_def]
    norm_num [harctan_s]
  · rw [hc_def]
    simp only [if_neg (show ¬ (n + 2 ≤ n) from by omega),
      if_neg (show ¬ (n + 2 = n + 1) from by omega)]
  · intro i hi
    rcases lt_trichotomy i n with hilt | hieq | higt
    · rw [hc_def]
      simp only [if_pos hilt.le, if_pos (show i + 1 ≤ n from by omega)]
      rw [← hb0]
      exact hchain i hilt
    · subst hieq
      rw [hc_def]
      simp only [if_pos (le_refl i), if_neg (show ¬ (i + 1 ≤ i) from by omega)]
      refine ⟨hb0 ▸ ne_pole_spherePoint b hθn0 hθn1.le _, ?_⟩
      apply hb0 ▸ spherePoint_mem_descent_of_tan b hθn0 hθn1 hθn1_0 hθn1_1
      rw [hθn1_def, hθn_def, Real.tan_arctan, Real.tan_arctan, hazimuth_n]
      have hcancel : ψt + φB - ψt = φB := by ring
      rw [hcancel]
      field_simp
    · have hival : i = n + 1 := by omega
      subst hival
      rw [hc_def]
      simp only [if_neg (show ¬ (n + 1 ≤ n) from by omega),
        if_neg (show ¬ (n + 1 + 1 ≤ n) from by omega),
        if_neg (show ¬ (n + 1 + 1 = n + 1) from by omega)]
      refine ⟨hb0 ▸ ne_pole_spherePoint b hθn1_0 hθn1_1.le _, ?_⟩
      apply hb0 ▸ spherePoint_mem_descent_of_tan b hθn1_0 hθn1_1 hθt0 hθt1
      rw [hθn1_def, Real.tan_arctan, ← hy_def]
      have haz : ψt - (ψt + φB) = -φB := by ring
      rw [haz, Real.cos_neg, eq_div_iff hcosφB_pos.ne']
      have hringstep : y * Real.cos φB * Real.cos φB = y * Real.cos φB ^ 2 := by ring
      rw [hringstep, hcos2φB]
      field_simp

/-- **E4 (assemblage final).** Chaîne de descente de Piron : si `t` est
strictement plus proche de l'équateur de `p` que `s` (`lat p t < lat p s`),
il existe une chaîne finie de descentes reliant `s` à `t`. On aligne `s` en
azimut nul via `exists_basis_aligned`, on lit les coordonnées de `t` dans la
même base via `exists_sphereCoords`, on convertit `lat p t < lat p s` en
`θs < θt` (`cos` strictement décroissante sur `[0,π]`), puis on dispatche
entre `piron_chain_equator_case` (`θt = π/2`) et `piron_chain_main_case`
(`θt < π/2`). -/
theorem piron_chain {p : E3} (hp : ‖p‖ = 1) {s t : E3}
    (hs : ‖s‖ = 1) (hsN : s ∈ northern p) (hsp : s ≠ p)
    (ht : ‖t‖ = 1) (htN : t ∈ northern p) (htp : t ≠ p)
    (hlt : lat p t < lat p s) :
    ∃ (n : ℕ) (c : ℕ → E3), c 0 = s ∧ c n = t ∧
      ∀ i < n, c i ≠ p ∧ c (i + 1) ∈ descent p (c i) := by
  obtain ⟨b, θs, hb0, hθs0, hθs1, hs_eq⟩ := exists_basis_aligned hp hs hsN hsp
  have htN' : t ∈ northern (b 0) := hb0 ▸ htN
  have htp' : t ≠ b 0 := hb0 ▸ htp
  obtain ⟨θt, ψt, hθt0, hθt1, ht_eq⟩ := exists_sphereCoords b ht htN' htp'
  have hlat_s : lat p s = Real.cos θs ^ 2 := by rw [hs_eq, ← hb0, lat_spherePoint]
  have hlat_t : lat p t = Real.cos θt ^ 2 := by rw [ht_eq, ← hb0, lat_spherePoint]
  have hcos_sq_lt : Real.cos θt ^ 2 < Real.cos θs ^ 2 := by rw [← hlat_s, ← hlat_t]; exact hlt
  have hcosθt_nn : 0 ≤ Real.cos θt := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθt1⟩
  have hcosθs_nn : 0 ≤ Real.cos θs := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθs1⟩
  have hcos_lt : Real.cos θt < Real.cos θs := (sq_lt_sq₀ hcosθt_nn hcosθs_nn).mp hcos_sq_lt
  have hθs_lt_θt : θs < θt := by
    by_contra hcon
    push Not at hcon
    rcases hcon.lt_or_eq with hcon' | hcon'
    · have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith : (0 : ℝ) ≤ θt)
        (by linarith [Real.pi_pos] : θs ≤ π) hcon'
      linarith
    · rw [hcon'] at hcos_lt; linarith
  have hθs1' : θs < π / 2 := lt_of_lt_of_le hθs_lt_θt hθt1
  rcases hθt1.lt_or_eq with hθt_lt | hθt_eq
  · obtain ⟨n, c, hc0, hcn, hstep⟩ :=
      piron_chain_main_case hb0 hθs0 hθs1' hθt0 hθt_lt hθs_lt_θt ψt
    refine ⟨n + 2, c, ?_, ?_, hstep⟩
    · rw [hc0, hs_eq]
    · rw [hcn, ht_eq]
  · obtain ⟨n, c, hc0, hcn, hstep⟩ := piron_chain_equator_case hb0 hθs0 hθs1' ψt
    refine ⟨n, c, ?_, ?_, hstep⟩
    · rw [hc0, hs_eq]
    · rw [hcn, ht_eq, hθt_eq]

/-- **E5 (préliminaire).** Le long d'une chaîne de descente `c`, tous les
points restent dans `northern p` : `c 0` par hypothèse, puis hérité pas à pas
via la première composante de `descent`. -/
private theorem chain_mem_northern {p : E3} {c : ℕ → E3} (hc0N : c 0 ∈ northern p)
    {n : ℕ} (hstep : ∀ i < n, c i ≠ p ∧ c (i + 1) ∈ descent p (c i)) :
    ∀ i ≤ n, c i ∈ northern p := by
  intro i
  induction i with
  | zero => intro _; exact hc0N
  | succ k ih =>
    intro hik
    have _hkN : c k ∈ northern p := ih (by omega)
    exact (hstep k (by omega)).2.1

/-- **E5 (corollaire, décroissance le long d'une chaîne).** Si `f` vérifie les
hypothèses de `basic_lemma` (bornée, sup en `p`, minorée par `m₀` approché,
constante sur l'équateur de `p`) et `c` est une chaîne de descente issue de
`c 0 ∈ northern p`, alors `f (c n) ≤ f (c 0)`. Récurrence sur `n` : chaque pas
`c i → c (i+1)` applique `basic_lemma` (via `chain_mem_northern` pour la
membre `c i ∈ northern p` nécessaire à `hsN`). -/
theorem chain_decreasing {f : E3 → ℝ} {W m₀ cst : ℝ} (hf : IsFrameFunction f W)
    {p : E3} (hp : ‖p‖ = 1)
    (hmax : ∀ t : E3, ‖t‖ = 1 → f t ≤ f p)
    (hmlb : ∀ t : E3, ‖t‖ = 1 → m₀ ≤ f t)
    (hm : ∀ ε > 0, ∃ x : E3, ‖x‖ = 1 ∧ f x < m₀ + ε)
    (hconst : ∀ e ∈ equator p, f e = cst)
    {n : ℕ} {c : ℕ → E3} (hc0N : c 0 ∈ northern p)
    (hstep : ∀ i < n, c i ≠ p ∧ c (i + 1) ∈ descent p (c i)) :
    f (c n) ≤ f (c 0) := by
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    have hstep' : ∀ i < n, c i ≠ p ∧ c (i + 1) ∈ descent p (c i) := fun i hi => hstep i (by omega)
    have hih : f (c n) ≤ f (c 0) := ih hstep'
    have hcnN : c n ∈ northern p := chain_mem_northern hc0N hstep' n le_rfl
    have hcnne : c n ≠ p := (hstep n (by omega)).1
    have hstepn : c (n + 1) ∈ descent p (c n) := (hstep n (by omega)).2
    have hcnunit : ‖c n‖ = 1 := hcnN.1
    have hdec : f (c (n + 1)) ≤ f (c n) :=
      basic_lemma hf hp hmax hmlb hm hconst hcnunit hcnN hcnne hstepn
    linarith [hih, hdec]

/-- **E5 (assemblage).** Corollaire de `piron_chain` + `chain_decreasing` :
sous les hypothèses de `basic_lemma`, une frame function décroît entre deux
points de `northern p \ {p}` dès que la latitude (par rapport à `p`) augmente. -/
theorem frameFunction_le_of_lat_lt {f : E3 → ℝ} {W m₀ cst : ℝ} (hf : IsFrameFunction f W)
    {p : E3} (hp : ‖p‖ = 1)
    (hmax : ∀ t : E3, ‖t‖ = 1 → f t ≤ f p)
    (hmlb : ∀ t : E3, ‖t‖ = 1 → m₀ ≤ f t)
    (hm : ∀ ε > 0, ∃ x : E3, ‖x‖ = 1 ∧ f x < m₀ + ε)
    (hconst : ∀ e ∈ equator p, f e = cst)
    {s t : E3} (hs : ‖s‖ = 1) (hsN : s ∈ northern p) (hsp : s ≠ p)
    (ht : ‖t‖ = 1) (htN : t ∈ northern p) (htp : t ≠ p)
    (hlt : lat p t < lat p s) :
    f t ≤ f s := by
  obtain ⟨n, c, hc0, hcn, hstep⟩ := piron_chain hp hs hsN hsp ht htN htp hlt
  have h := chain_decreasing hf hp hmax hmlb hm hconst (hc0 ▸ hsN) hstep
  rwa [hc0, hcn] at h

end
end Gleason
