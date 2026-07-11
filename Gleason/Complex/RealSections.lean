import Gleason.Defs
import Gleason.Real3.Regular

/-!
# Réduction complexe par sections réelles (Dvurečenskij, ch. 3)

Passage de ℝ³ (cœur analytique de `Real3/`) au cas complexe ℂⁿ, `n ≥ 3` :

1. une frame function complexe, restreinte à un sous-espace RÉEL complètement réel
   de dimension 3 (une « section réelle »), est une frame function réelle sur ℝ³ ;
2. `Real3.frameFunction_regular` donne une forme quadratique sur chaque section ;
3. le recollement des sections (`Patching.lean`) produit une forme sesquilinéaire
   globale — c'est exactement là que l'ancienne « obligation G » (sesquilinéarité du
   noyau de polarisation) devient un THÉORÈME, démontré par la géométrie des sections
   et l'hypothèse `dim ≥ 3`, et non par l'algèbre seule.

⚠️ La définition précise de « section réelle » (image d'une isométrie ℝ-linéaire
`E3 →ₗᵢ[ℝ] H n` compatible avec les phases) est le livrable d'ouverture du jalon M3 ;
les énoncés ci-dessous sont provisoires.
-/

namespace Gleason

open scoped InnerProductSpace

noncomputable section

variable {n : ℕ}

/- ═══════════════════════════════════════════════════════════════════
   M3-0. Extension d'une famille orthonormée complexe, à positions
   prescrites (via `Fin.castLE`), en base orthonormée de `H n`. Généralise
   `exists_orthonormalBasis_of_triple'` (bloc A, `Real3/SphereGeometry.lean`,
   hardcodé `ℝ`/`Fin 3`) : ici `k` est arbitraire (`k ≤ n`) et le corps est
   `ℂ`. Le lemme Mathlib sous-jacent
   (`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`) est déjà
   générique en `𝕜`.
   ═══════════════════════════════════════════════════════════════════ -/

/-- Toute famille orthonormée `v : Fin k → H n` (`k ≤ n`) se complète en une base
orthonormée de `H n` qui coïncide avec `v` sur les `k` premières positions
(`Fin.castLE`). -/
theorem exists_orthonormalBasis_extension_complex {k : ℕ} (hk : k ≤ n) (v : Fin k → H n)
    (hv : Orthonormal ℂ v) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (H n), ∀ i : Fin k, b (Fin.castLE hk i) = v i := by
  have hinj : Function.Injective (Fin.castLE hk : Fin k → Fin n) := Fin.castLE_injective hk
  set V : Fin n → H n := Function.extend (Fin.castLE hk) v (fun _ => 0) with hV_def
  have hVv : ∀ i : Fin k, V (Fin.castLE hk i) = v i := fun i =>
    hinj.extend_apply v (fun _ => (0 : H n)) i
  set e : Fin k ≃ Set.range (Fin.castLE hk) := Equiv.ofInjective (Fin.castLE hk) hinj with he_def
  have hcomp : (Fin.castLE hk : Fin k → Fin n) ∘ e.symm = Subtype.val :=
    Equiv.self_comp_ofInjective_symm hinj
  have hrestrict : (Set.range (Fin.castLE hk)).restrict V = v ∘ e.symm := by
    funext x
    have hx1 : Fin.castLE hk (e.symm x) = (x : Fin n) := congrFun hcomp x
    show V (x : Fin n) = v (e.symm x)
    rw [← hx1, hVv]
  have hOrtho : Orthonormal ℂ ((Set.range (Fin.castLE hk)).restrict V) := by
    rw [hrestrict]; exact hv.comp e.symm e.symm.injective
  have hcard : Module.finrank ℂ (H n) = Fintype.card (Fin n) := by simp
  obtain ⟨b, hb⟩ := hOrtho.exists_orthonormalBasis_extension_of_card_eq hcard
  exact ⟨b, fun i => by rw [hb (Fin.castLE hk i) ⟨i, rfl⟩, hVv]⟩

/-- **Frame function complexe de poids `W`** sur `ℂⁿ`. -/
def IsCFrameFunction (g : H n → ℝ) (W : ℝ) : Prop :=
  ∀ b : OrthonormalBasis (Fin n) ℂ (H n), (∑ i, g (b i)) = W

/-- La frame function d'une mesure de projection : `x ↦ μ (ℂ ∙ x)`. -/
def ProjMeasure.frameFunction (m : ProjMeasure n) : H n → ℝ :=
  fun x => m.μ (ℂ ∙ x)

/-- **M3-1(b) préliminaire.** Additivité finie sur une famille deux à deux orthogonale
(indexée par un `Finset`) : généralise `add_isOrtho` par récurrence sur le `Finset`.
`i ∈ s` orthogonal à `s.sup A` s'obtient de `i ⊥ A j` pour tout `j ∈ s` via
`Submodule.isOrtho_iSup_right` (le sup fini est un cas particulier du sup indexé). -/
theorem ProjMeasure.sum_eq_of_pairwise_isOrtho (m : ProjMeasure n) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → Submodule ℂ (H n))
    (hortho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → A i ⟂ A j) :
    m.μ (s.sup A) = ∑ i ∈ s, m.μ (A i) := by
  induction s using Finset.induction with
  | empty => simp [m.bot_eq_zero]
  | insert i s hi ih =>
    have hi_ortho : A i ⟂ s.sup A := by
      apply Finset.sup_induction Submodule.isOrtho_bot_right
        (fun a1 h1 a2 h2 => Submodule.isOrtho_sup_right.mpr ⟨h1, h2⟩)
      intro j hj
      exact hortho i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
        (fun heq => hi (heq ▸ hj))
    have hs_sub : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → A j ⟂ A k := fun j hj k hk hjk =>
      hortho j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
    rw [Finset.sup_insert, m.add_isOrtho _ _ hi_ortho, ih hs_sub, Finset.sum_insert hi]

/-- (Phase M) La frame function d'une mesure de projection est une frame function
complexe de poids 1. Indication : une base orthonormée découpe `⊤` en droites deux à
deux orthogonales ; itérer `add_isOrtho` (via `sum_eq_of_pairwise_isOrtho`). -/
theorem ProjMeasure.isCFrameFunction (m : ProjMeasure n) :
    IsCFrameFunction m.frameFunction 1 := by
  intro b
  have hortho : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ j ∈ (Finset.univ : Finset (Fin n)),
      i ≠ j → (ℂ ∙ b i) ⟂ (ℂ ∙ b j) := by
    intro i _ j _ hij
    rw [Submodule.isOrtho_span]
    rintro x hx y hy
    simp only [Set.mem_singleton_iff] at hx hy
    rw [hx, hy, b.inner_eq_ite]
    simp [hij]
  have hsum := m.sum_eq_of_pairwise_isOrtho Finset.univ (fun i => ℂ ∙ b i) hortho
  have htop : (Finset.univ : Finset (Fin n)).sup (fun i => ℂ ∙ b i) = ⊤ := by
    rw [Finset.sup_eq_iSup]
    simp only [Finset.mem_univ, iSup_pos]
    rw [← Submodule.span_range_eq_iSup]
    exact b.toBasis.span_eq
  rw [htop, m.top_eq_one] at hsum
  unfold ProjMeasure.frameFunction
  exact hsum.symm

/-- Invariance de phase : `g (c • x) = g x` pour `‖c‖ = 1` — automatique pour les
frame functions issues de mesures, car `ℂ ∙ (c • x) = ℂ ∙ x`. -/
theorem ProjMeasure.frameFunction_phase (m : ProjMeasure n) (c : ℂ) (x : H n)
    (hc : ‖c‖ = 1) : m.frameFunction (c • x) = m.frameFunction x := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; norm_num at hc
  unfold ProjMeasure.frameFunction
  rw [Submodule.span_singleton_smul_eq hc0.isUnit]

/- ═══════════════════════════════════════════════════════════════════
   M3-2. Invariance de `∑ g(v i)` par changement de base orthonormée
   d'un même sous-espace (engendré par `v` ou par `v'`).
   ═══════════════════════════════════════════════════════════════════ -/

/-- **M3-2.** Si `v, v' : Fin k → H n` sont orthonormées et engendrent le même
sous-espace, les sommes `∑ g(v i)` et `∑ g(v' i)` coïncident, pour `g` frame
function complexe de poids `W`. Preuve : étend `v` en base `b` de `H n`
(`exists_orthonormalBasis_extension_complex`) ; la famille hybride `w`
(`v'` sur les `k` premières positions, la queue de `b` ensuite) est
orthonormée — la queue de `b` est orthogonale à `span(range v) = span(range v')`
donc à chaque `v' i` — donc base ; les deux sommes valent `W` (`hg`), la
queue commune s'annule par soustraction. -/
theorem cframe_sum_invariant {g : H n → ℝ} {W : ℝ} (hg : IsCFrameFunction g W)
    {k : ℕ} (hk : k ≤ n) (v v' : Fin k → H n) (hv : Orthonormal ℂ v) (hv' : Orthonormal ℂ v')
    (hspan : Submodule.span ℂ (Set.range v) = Submodule.span ℂ (Set.range v')) :
    ∑ i, g (v i) = ∑ i, g (v' i) := by
  have hzero_symm : ∀ x y : H n, ⟪x, y⟫_ℂ = 0 → ⟪y, x⟫_ℂ = 0 := by
    intro x y hxy
    have h := congrArg (starRingEnd ℂ) hxy
    rwa [inner_conj_symm, map_zero] at h
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_extension_complex hk v hv
  set w : Fin n → H n := fun j => if h : j.1 < k then v' ⟨j.1, h⟩ else b j with hw_def
  have hw_lt : ∀ j : Fin n, ∀ h : j.1 < k, w j = v' ⟨j.1, h⟩ := fun j h => by simp [hw_def, h]
  have hw_ge : ∀ j : Fin n, ¬ j.1 < k → w j = b j := fun j h => by simp [hw_def, h]
  have hw_castLE : ∀ i : Fin k, w (Fin.castLE hk i) = v' i := by
    intro i
    rw [hw_lt (Fin.castLE hk i) (by simp)]
    exact congrArg v' (Fin.ext rfl)
  have hb_tail_orth : ∀ j : Fin n, ¬ j.1 < k → ∀ x ∈ Submodule.span ℂ (Set.range v),
      ⟪b j, x⟫_ℂ = 0 := by
    intro j hj x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro y ⟨i, rfl⟩
      rw [← hb i]
      have hij : j ≠ Fin.castLE hk i := by
        intro heq; apply hj; rw [heq]; simp
      exact b.orthonormal.2 hij
    · simp
    · intro y z _ _ hy hz; rw [inner_add_right, hy, hz, add_zero]
    · intro c y _ hy; rw [inner_smul_right, hy, mul_zero]
  have hw_orth : Orthonormal ℂ w := by
    constructor
    · intro j
      by_cases hj : j.1 < k
      · rw [hw_lt j hj]; exact hv'.1 _
      · rw [hw_ge j hj]; exact b.orthonormal.1 j
    · intro i j hij
      by_cases hi : i.1 < k <;> by_cases hj : j.1 < k
      · rw [hw_lt i hi, hw_lt j hj]
        have hij' : (⟨i.1, hi⟩ : Fin k) ≠ ⟨j.1, hj⟩ := by
          simp only [ne_eq, Fin.mk.injEq]
          intro heq; exact hij (Fin.ext heq)
        exact hv'.2 hij'
      · rw [hw_lt i hi, hw_ge j hj]
        have hvi : v' ⟨i.1, hi⟩ ∈ Submodule.span ℂ (Set.range v) := by
          rw [hspan]; exact Submodule.subset_span ⟨⟨i.1, hi⟩, rfl⟩
        exact hzero_symm _ _ (hb_tail_orth j hj (v' ⟨i.1, hi⟩) hvi)
      · rw [hw_ge i hi, hw_lt j hj]
        have hvj : v' ⟨j.1, hj⟩ ∈ Submodule.span ℂ (Set.range v) := by
          rw [hspan]; exact Submodule.subset_span ⟨⟨j.1, hj⟩, rfl⟩
        exact hb_tail_orth i hi (v' ⟨j.1, hj⟩) hvj
      · rw [hw_ge i hi, hw_ge j hj]; exact b.orthonormal.2 hij
  have hcard : Module.finrank ℂ (H n) = Fintype.card (Fin n) := by simp
  have hw_univ : Orthonormal ℂ ((Set.univ : Set (Fin n)).restrict w) :=
    ⟨fun i => hw_orth.1 i.1, fun i j hij => hw_orth.2 (fun h => hij (Subtype.ext h))⟩
  obtain ⟨bw, hbw⟩ := hw_univ.exists_orthonormalBasis_extension_of_card_eq hcard
  have hbw' : ∀ i, bw i = w i := fun i => hbw i (Set.mem_univ i)
  have hsumb := hg b
  have hsumbw := hg bw
  have hD_zero_outside : ∀ i : Fin n, (∀ j : Fin k, Fin.castLE hk j ≠ i) →
      g (b i) - g (bw i) = 0 := by
    intro i hi
    have hnotlt : ¬ i.1 < k := fun hlt => hi ⟨i.1, hlt⟩ (Fin.ext rfl)
    rw [hbw' i, hw_ge i hnotlt]; ring
  have hsum_eq : ∑ i : Fin n, (g (b i) - g (bw i)) = ∑ j : Fin k, (g (v j) - g (v' j)) := by
    have hstep1 : ∑ i : Fin n, (g (b i) - g (bw i))
        = ∑ i ∈ Finset.univ.image (Fin.castLE hk), (g (b i) - g (bw i)) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      apply hD_zero_outside i
      intro j hji
      exact hi (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hji⟩)
    rw [hstep1, Finset.sum_image (fun a _ b _ hab => Fin.castLE_injective hk hab)]
    apply Finset.sum_congr rfl
    intro j _
    rw [hb j, hbw' (Fin.castLE hk j), hw_castLE j]
  have hsum0 : ∑ i : Fin n, (g (b i) - g (bw i)) = 0 := by
    rw [Finset.sum_sub_distrib, hsumb, hsumbw, sub_self]
  rw [hsum0] at hsum_eq
  have hfinal := hsum_eq.symm
  rw [Finset.sum_sub_distrib] at hfinal
  linarith [hfinal]

/-- **M3-2 (corollaire).** Une frame function complexe positive est bornée par son poids :
complète `x` en base (`k := 1`) et compare au terme isolé, les autres étant `≥ 0` (`hnn`). -/
theorem cframe_le_weight {g : H n → ℝ} {W : ℝ} (hg : IsCFrameFunction g W)
    (hnn : ∀ x, ‖x‖ = 1 → 0 ≤ g x) (hn1 : 1 ≤ n) {x : H n} (hx : ‖x‖ = 1) : g x ≤ W := by
  have hvx : Orthonormal ℂ (fun _ : Fin 1 => x) :=
    ⟨fun _ => hx, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_extension_complex hn1 (fun _ : Fin 1 => x) hvx
  have hsum := hg b
  have h0 : b (Fin.castLE hn1 0) = x := hb 0
  rw [← h0, ← hsum]
  exact Finset.single_le_sum (fun i _ => hnn (b i) (b.norm_eq_one i)) (Finset.mem_univ _)

/- ═══════════════════════════════════════════════════════════════════
   M3-3 à M3-9 : hypothèses de section communes. `g` frame function
   complexe positive et invariante de phase, `n ≥ 3`.
   ═══════════════════════════════════════════════════════════════════ -/

section CFrameSections

variable {g : H n → ℝ} {W : ℝ} (hg : IsCFrameFunction g W) (hnn : ∀ x, ‖x‖ = 1 → 0 ≤ g x)
  (hphase : ∀ (c : ℂ) (x : H n), ‖c‖ = 1 → g (c • x) = g x) (hn : 3 ≤ n)

/-- **M3-3.** Extension homogène de degré 2 de `g` (nulle en `0`, `g` sur la sphère unité
sinon, prolongée par `q(c • z) = ‖c‖² q z`). -/
noncomputable def homogExt (g : H n → ℝ) (z : H n) : ℝ :=
  if z = 0 then 0 else ‖z‖ ^ 2 * g ((‖z‖⁻¹ : ℂ) • z)

theorem homogExt_of_unit {z : H n} (hz : ‖z‖ = 1) : homogExt g z = g z := by
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; norm_num at hz
  unfold homogExt
  rw [if_neg hz0, hz]
  norm_num

include hphase in
theorem homogExt_smul (c : ℂ) (z : H n) :
    homogExt g (c • z) = ‖c‖ ^ 2 * homogExt g z := by
  by_cases hz0 : z = 0
  · subst hz0; simp [homogExt]
  by_cases hc0 : c = 0
  · subst hc0; simp [homogExt]
  have hcz0 : c • z ≠ 0 := smul_ne_zero hc0 hz0
  have hcnorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc0
  have hznorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  have hcC : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast hcnorm
  have hzC : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hznorm
  unfold homogExt
  rw [if_neg hcz0, if_neg hz0]
  have harg : (‖c • z‖⁻¹ : ℂ) • (c • z) = (c / (‖c‖ : ℂ)) • ((‖z‖⁻¹ : ℂ) • z) := by
    rw [norm_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    field_simp
  rw [harg, hphase (c / (‖c‖ : ℂ)) ((‖z‖⁻¹ : ℂ) • z) (by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hcnorm])]
  rw [norm_smul]
  ring

include hnn in
theorem homogExt_nonneg (z : H n) : 0 ≤ homogExt g z := by
  by_cases hz0 : z = 0
  · subst hz0; simp [homogExt]
  unfold homogExt
  rw [if_neg hz0]
  have hunit : ‖(‖z‖⁻¹ : ℂ) • z‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)]
  exact mul_nonneg (by positivity) (hnn _ hunit)

include hg hnn hn in
theorem homogExt_le (z : H n) : homogExt g z ≤ W * ‖z‖ ^ 2 := by
  by_cases hz0 : z = 0
  · subst hz0; simp [homogExt]
  unfold homogExt
  rw [if_neg hz0]
  have hunit : ‖(‖z‖⁻¹ : ℂ) • z‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)]
  have hle := cframe_le_weight hg hnn (by omega) hunit
  nlinarith [sq_nonneg ‖z‖, hle]

/- ═══════════════════════════════════════════════════════════════════
   M3-4. Sections réelles : plongement `ι_v` de `E3` dans `H n` associé
   à un triplet orthonormé complexe `v`, isométrique (préserve le
   produit scalaire réel), fournissant une frame function réelle
   `f_v := g ∘ ι_v` dont `frameFunction_regular` (M2) donne la forme
   quadratique `Q_v`.
   ═══════════════════════════════════════════════════════════════════ -/

/-- Section réelle associée à un triplet orthonormé complexe `v : Fin 3 → H n` :
plongement ℝ-linéaire (fonction nue, pas de bundling `LinearIsometry`) de `E3`
dans `H n`. -/
noncomputable def realSection (v : Fin 3 → H n) (x : E3) : H n := ∑ i, (x i : ℂ) • v i

theorem realSection_inner (v : Fin 3 → H n) (hv : Orthonormal ℂ v) (x y : E3) :
    ⟪realSection v x, realSection v y⟫_ℂ = (⟪x, y⟫_ℝ : ℂ) := by
  have hvite := orthonormal_iff_ite.mp hv
  have hstar_real : ∀ r : ℝ, star (r : ℂ) = (r : ℂ) := fun r => by
    rw [← starRingEnd_apply, Complex.conj_ofReal]
  unfold realSection
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hvite]
  simp only [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three,
    starRingEnd_apply, star_trivial, hstar_real]
  push_cast
  ring

theorem realSection_norm (v : Fin 3 → H n) (hv : Orthonormal ℂ v) (x : E3) :
    ‖realSection v x‖ = ‖x‖ := by
  have hkey := realSection_inner v hv x x
  rw [inner_self_eq_norm_sq_to_K, real_inner_self_eq_norm_sq] at hkey
  have h2 : ‖realSection v x‖ ^ 2 = ‖x‖ ^ 2 := by
    apply Complex.ofReal_inj.mp; push_cast at hkey ⊢; exact hkey
  have hh := Real.sqrt_sq (norm_nonneg (realSection v x))
  rw [h2, Real.sqrt_sq (norm_nonneg x)] at hh
  exact hh.symm

end CFrameSections

end
end Gleason
