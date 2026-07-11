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

theorem realSection_orthonormal (v : Fin 3 → H n) (hv : Orthonormal ℂ v)
    (b : OrthonormalBasis (Fin 3) ℝ E3) : Orthonormal ℂ (fun i => realSection v (b i)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [realSection_inner v hv, b.inner_eq_ite]
  split_ifs <;> simp

theorem realSection_span (v : Fin 3 → H n) (hv : Orthonormal ℂ v)
    (b : OrthonormalBasis (Fin 3) ℝ E3) : Submodule.span ℂ (Set.range (fun i => realSection v (b i)))
    = Submodule.span ℂ (Set.range v) := by
  have hle : Submodule.span ℂ (Set.range (fun i => realSection v (b i)))
      ≤ Submodule.span ℂ (Set.range v) := by
    rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    unfold realSection
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have hfin_v : Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = 3 := by
    have h := finrank_span_eq_card hv.linearIndependent
    simpa using h
  have hfin_b : Module.finrank ℂ (Submodule.span ℂ (Set.range (fun i => realSection v (b i))))
      = 3 := by
    have h := finrank_span_eq_card (realSection_orthonormal v hv b).linearIndependent
    simpa using h
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin_b, hfin_v])

include hg hn in
theorem realSection_isFrameFunction (v : Fin 3 → H n) (hv : Orthonormal ℂ v) :
    IsFrameFunction (fun x => g (realSection v x)) (∑ i, g (v i)) := by
  intro b
  exact (cframe_sum_invariant hg hn v (fun i => realSection v (b i)) hv
    (realSection_orthonormal v hv b) (realSection_span v hv b).symm).symm

include hnn in
theorem realSection_nonneg (v : Fin 3 → H n) (hv : Orthonormal ℂ v) {x : E3} (hx : ‖x‖ = 1) :
    0 ≤ g (realSection v x) := by
  rw [← realSection_norm v hv x] at hx; exact hnn _ hx

include hg hnn hn in
theorem exists_Qv (v : Fin 3 → H n) (hv : Orthonormal ℂ v) :
    ∃ Q : QuadraticForm ℝ E3, ∀ x : E3, ‖x‖ = 1 → g (realSection v x) = Q x :=
  frameFunction_regular (fun x => g (realSection v x)) (∑ i, g (v i))
    (realSection_isFrameFunction hg hn v hv) (fun _ hx => realSection_nonneg hnn v hv hx)

include hg hnn hphase hn in
/-- **M3-4 (assemblage).** Extension homogène de `g` composée avec la section réelle : c'est
la forme quadratique `Q_v` donnée par `frameFunction_regular` (M2), prolongée à `E3` entier par
homogénéité (`homogExt_smul` et `QuadraticMap.map_smul` des deux côtés). -/
theorem homogExt_realSection (v : Fin 3 → H n) (hv : Orthonormal ℂ v) :
    ∃ Q : QuadraticForm ℝ E3, ∀ x : E3, homogExt g (realSection v x) = Q x := by
  obtain ⟨Q, hQ⟩ := exists_Qv hg hnn hn v hv
  refine ⟨Q, fun x => ?_⟩
  by_cases hx0 : x = 0
  · subst hx0; simp [homogExt, realSection, map_zero]
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), inv_mul_cancel₀ hxnorm]
  have hcomp : realSection v x = (‖x‖ : ℂ) • realSection v ((‖x‖⁻¹ : ℝ) • x) := by
    unfold realSection
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_smul]
    congr 1
    simp only [PiLp.smul_apply, smul_eq_mul]
    push_cast
    field_simp [show (‖x‖ : ℂ) ≠ 0 from by exact_mod_cast hxnorm]
  have hunit' : ‖realSection v ((‖x‖⁻¹ : ℝ) • x)‖ = 1 := by
    rw [realSection_norm v hv]; exact hunit
  have hgoal : ‖x‖ ^ 2 * homogExt g (realSection v ((‖x‖⁻¹ : ℝ) • x)) = Q x := by
    rw [homogExt_of_unit hunit', hQ _ hunit, QuadraticMap.map_smul, smul_eq_mul]
    field_simp
  calc homogExt g (realSection v x)
      = homogExt g ((‖x‖ : ℂ) • realSection v ((‖x‖⁻¹ : ℝ) • x)) := by rw [hcomp]
    _ = ‖(‖x‖ : ℂ)‖ ^ 2 * homogExt g (realSection v ((‖x‖⁻¹ : ℝ) • x)) :=
        homogExt_smul hphase (‖x‖ : ℂ) (realSection v ((‖x‖⁻¹ : ℝ) • x))
    _ = ‖x‖ ^ 2 * homogExt g (realSection v ((‖x‖⁻¹ : ℝ) • x)) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr hx0)]
    _ = Q x := hgoal

/- ═══════════════════════════════════════════════════════════════════
   M3-5. Continuité Lipschitz de `g` (via un ajustement de phase et la
   borne polaire de `Q_v`) puis existence d'un maximum sur toute
   sous-espace non nul (compacité).
   ═══════════════════════════════════════════════════════════════════ -/

/-- **M3-5(a).** Ajustement de phase : pour deux vecteurs unitaires `u, w`, il existe une
phase `c` (`‖c‖ = 1`) qui aligne `⟪u, c•w⟫` sur le réel positif `‖⟪u,w⟫‖`, et rapproche
`c•w` de `u` (au sens large) par rapport à `w`. -/
theorem exists_phase_adjust (u w : H n) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ⟪u, c • w⟫_ℂ = (‖⟪u, w⟫_ℂ‖ : ℂ) ∧ ‖u - c • w‖ ≤ ‖u - w‖ := by
  by_cases hz : ⟪u, w⟫_ℂ = 0
  · exact ⟨1, by norm_num, by rw [one_smul, hz]; simp, by rw [one_smul]⟩
  · set z : ℂ := ⟪u, w⟫_ℂ with hz_def
    set c : ℂ := (starRingEnd ℂ z) / (‖z‖ : ℂ) with hc_def
    have hznorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hznormC : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hznorm
    have hnormz_castnorm : ‖(‖z‖ : ℂ)‖ = ‖z‖ := by simp
    have hre_castz : RCLike.re ((‖z‖ : ℝ) : ℂ) = ‖z‖ := by simp
    have hcnorm : ‖c‖ = 1 := by
      rw [hc_def, norm_div, RCLike.norm_conj, hnormz_castnorm, div_self hznorm]
    have hinner : ⟪u, c • w⟫_ℂ = (‖z‖ : ℂ) := by
      rw [inner_smul_right, hc_def, div_mul_eq_mul_div, RCLike.conj_mul, sq]
      field_simp
      norm_cast
    refine ⟨c, hcnorm, hinner, ?_⟩
    have hcw_norm : ‖c • w‖ = 1 := by rw [norm_smul, hcnorm, hw, one_mul]
    have h1 : ‖u - c • w‖ ^ 2 = 2 - 2 * ‖z‖ := by
      rw [norm_sub_sq (𝕜 := ℂ), hu, hcw_norm, hinner, hre_castz]; ring
    have h2 : ‖u - w‖ ^ 2 = 2 - 2 * RCLike.re (⟪u, w⟫_ℂ) := by
      rw [norm_sub_sq (𝕜 := ℂ), hu, hw]; ring
    have h3 : RCLike.re (⟪u, w⟫_ℂ) ≤ ‖z‖ := RCLike.re_le_norm z
    have h4 : ‖u - c • w‖ ^ 2 ≤ ‖u - w‖ ^ 2 := by rw [h1, h2]; linarith [h3]
    have h5 := Real.sqrt_le_sqrt h4
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h5

/-- **M3-5(b).** Version COMPLEXE de `exists_unit_orthogonal_to_pair` (`Real3/SphereGeometry.lean`,
bloc A) : l'orthogonal (complexe) d'un span engendré par deux vecteurs, de dimension complexe
`≤ 2`, est non nul dès que `dim_ℂ (H n) ≥ 3`. C'est ICI, et seulement ici, que l'hypothèse
`n ≥ 3` intervient dans tout le bloc M3 : c'est le théorème qui remplace l'axiome analytique de
l'ancien développement (comptage de dimension complexe, pas de produit vectoriel en dimension
`n` quelconque). -/
theorem exists_unit_orthogonal_to_pair_complex (hn : 3 ≤ n) (a b : H n) :
    ∃ u : H n, ‖u‖ = 1 ∧ ⟪u, a⟫_ℂ = 0 ∧ ⟪u, b⟫_ℂ = 0 := by
  classical
  set K : Submodule ℂ (H n) := Submodule.span ℂ ({a, b} : Set (H n)) with hK_def
  have hKfin : Module.finrank ℂ K ≤ 2 := by
    refine le_trans (finrank_span_le_card ({a, b} : Set (H n))) ?_
    simp only [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp)
  have hHn : Module.finrank ℂ (H n) = n := by simp
  have hsum : Module.finrank ℂ K + Module.finrank ℂ Kᗮ = Module.finrank ℂ (H n) :=
    Submodule.finrank_add_finrank_orthogonal K
  have hKperp : 1 ≤ Module.finrank ℂ Kᗮ := by omega
  have hne : Kᗮ ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hKperp; omega
  obtain ⟨w, hwK, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have haK : a ∈ K := Submodule.subset_span (by simp)
  have hbK : b ∈ K := Submodule.subset_span (by simp)
  have hwa : ⟪w, a⟫_ℂ = 0 := Submodule.inner_left_of_mem_orthogonal haK hwK
  have hwb : ⟪w, b⟫_ℂ = 0 := Submodule.inner_left_of_mem_orthogonal hbK hwK
  have hwnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  have hwnormC : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hwnorm
  refine ⟨(‖w‖⁻¹ : ℂ) • w, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ hwnorm]
  · rw [inner_smul_left, hwa, mul_zero]
  · rw [inner_smul_left, hwb, mul_zero]

/-- **M3-5(c) (générique, réel).** Si `0 ≤ Q ≤ W‖·‖²` sur `E3`, la forme polaire de `Q` est
bornée : `|Q.polar a b| ≤ 2W‖a‖‖b‖`. Preuve : rééchelonnage `t := √(‖b‖/‖a‖)` dans
`0 ≤ Q(t•a ± t⁻¹•b) = t²Q(a) + t⁻²Q(b) ± Q.polar a b`, puis `Q(a) ≤ W‖a‖²` etc. et
`t²‖a‖² = t⁻²‖b‖² = ‖a‖‖b‖` par le choix de `t`. -/
theorem quadratic_polar_bound {Q : QuadraticForm ℝ E3} {W : ℝ}
    (hQ_nonneg : ∀ x : E3, 0 ≤ Q x) (hQ_le : ∀ x : E3, Q x ≤ W * ‖x‖ ^ 2) (a b : E3) :
    |QuadraticMap.polar Q a b| ≤ 2 * W * ‖a‖ * ‖b‖ := by
  by_cases ha0 : a = 0
  · simp [ha0, QuadraticMap.polar]
  by_cases hb0 : b = 0
  · simp [hb0, QuadraticMap.polar]
  have hanorm : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha0
  have hbnorm : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hb0
  have hWnonneg : 0 ≤ W := by
    by_contra hW
    exact absurd ((hQ_nonneg a).trans (hQ_le a))
      (not_le.mpr (mul_neg_of_neg_of_pos (not_le.mp hW) (by positivity)))
  set t : ℝ := Real.sqrt (‖b‖ / ‖a‖) with ht_def
  have ht_pos : 0 < t := Real.sqrt_pos.mpr (div_pos hbnorm hanorm)
  have ht_ne : t ≠ 0 := ht_pos.ne'
  have htsq : t ^ 2 = ‖b‖ / ‖a‖ := Real.sq_sqrt (by positivity)
  have hexpand_plus : Q (t • a + t⁻¹ • b)
      = t ^ 2 * Q a + t⁻¹ ^ 2 * Q b + QuadraticMap.polar Q a b := by
    have hpolar_eq : QuadraticMap.polar Q (t • a) (t⁻¹ • b) = QuadraticMap.polar Q a b := by
      rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, smul_smul,
        mul_inv_cancel₀ ht_ne, one_smul]
    have hQsum : Q (t • a + t⁻¹ • b)
        = Q (t • a) + Q (t⁻¹ • b) + QuadraticMap.polar Q (t • a) (t⁻¹ • b) := by
      rw [QuadraticMap.polar]; ring
    rw [hQsum, hpolar_eq, QuadraticMap.map_smul, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hexpand_minus : Q (t • a - t⁻¹ • b)
      = t ^ 2 * Q a + t⁻¹ ^ 2 * Q b - QuadraticMap.polar Q a b := by
    have heq : t • a - t⁻¹ • b = t • a + (-1 : ℝ) • (t⁻¹ • b) := by
      rw [neg_one_smul]; abel
    have hpolar_eq : QuadraticMap.polar Q (t • a) ((-1 : ℝ) • (t⁻¹ • b))
        = -QuadraticMap.polar Q a b := by
      rw [QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_left,
        QuadraticMap.polar_smul_right, smul_smul, smul_smul,
        show (-1 : ℝ) * t * t⁻¹ = -1 from by field_simp, neg_one_smul]
    have hQneg : Q ((-1 : ℝ) • (t⁻¹ • b)) = Q (t⁻¹ • b) := by
      rw [QuadraticMap.map_smul]; ring
    rw [heq]
    have hQsum : Q (t • a + (-1 : ℝ) • (t⁻¹ • b)) = Q (t • a) + Q ((-1 : ℝ) • (t⁻¹ • b)) +
        QuadraticMap.polar Q (t • a) ((-1 : ℝ) • (t⁻¹ • b)) := by
      rw [QuadraticMap.polar]; ring
    rw [hQsum, hpolar_eq, hQneg, QuadraticMap.map_smul, QuadraticMap.map_smul, smul_eq_mul,
      smul_eq_mul]
    ring
  have h1 : 0 ≤ t ^ 2 * Q a + t⁻¹ ^ 2 * Q b + QuadraticMap.polar Q a b := by
    rw [← hexpand_plus]; exact hQ_nonneg _
  have h2 : 0 ≤ t ^ 2 * Q a + t⁻¹ ^ 2 * Q b - QuadraticMap.polar Q a b := by
    rw [← hexpand_minus]; exact hQ_nonneg _
  have h3 : t ^ 2 * Q a + t⁻¹ ^ 2 * Q b ≤ t ^ 2 * (W * ‖a‖ ^ 2) + t⁻¹ ^ 2 * (W * ‖b‖ ^ 2) := by
    gcongr
    · exact hQ_le a
    · exact hQ_le b
  have hval : t ^ 2 * (W * ‖a‖ ^ 2) + t⁻¹ ^ 2 * (W * ‖b‖ ^ 2) = 2 * W * ‖a‖ * ‖b‖ := by
    rw [htsq, inv_pow, htsq]
    field_simp
    ring
  rw [abs_le]
  constructor <;> nlinarith [h1, h2, h3, hval]

/-- **M3-5(c) (corollaire).** Si `0 ≤ Q ≤ W‖·‖²`, `Q` est `2W`-lipschitzienne sur la sphère
unité. Preuve : `Q.polar (a+b) (a-b) = 2(Q a - Q b)` (identités de polarisation), borné par
`2W‖a+b‖‖a-b‖ ≤ 4W‖a-b‖` via `quadratic_polar_bound` et `‖a+b‖ ≤ 2`. -/
theorem quadratic_lipschitz {Q : QuadraticForm ℝ E3} {W : ℝ}
    (hQ_nonneg : ∀ x : E3, 0 ≤ Q x) (hQ_le : ∀ x : E3, Q x ≤ W * ‖x‖ ^ 2)
    {a b : E3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    |Q a - Q b| ≤ 2 * W * ‖a - b‖ := by
  have hWnonneg : 0 ≤ W := by
    by_contra hW
    exact absurd ((hQ_nonneg a).trans (hQ_le a))
      (not_le.mpr (mul_neg_of_neg_of_pos (not_le.mp hW) (by rw [ha]; norm_num)))
  have hQa_neg : Q (-b) = Q b := by
    rw [show (-b : E3) = (-1 : ℝ) • b from (neg_one_smul ℝ b).symm, QuadraticMap.map_smul]; ring
  have hpolar_ab_neg : QuadraticMap.polar Q a (-b) = -QuadraticMap.polar Q a b := by
    rw [show (-b : E3) = (-1 : ℝ) • b from (neg_one_smul ℝ b).symm, QuadraticMap.polar_smul_right,
      neg_one_smul]
  have h1 : Q (a + b) = Q a + Q b + QuadraticMap.polar Q a b := by rw [QuadraticMap.polar]; ring
  have h2 : Q (a - b) = Q a + Q b - QuadraticMap.polar Q a b := by
    have heq : a - b = a + -b := by abel
    have h3 : Q (a + -b) = Q a + Q (-b) + QuadraticMap.polar Q a (-b) := by
      rw [QuadraticMap.polar]; ring
    rw [heq, h3, hQa_neg, hpolar_ab_neg]; ring
  have hpolar_sum : QuadraticMap.polar Q (a + b) (a - b)
      = Q ((a + b) + (a - b)) - Q (a + b) - Q (a - b) := by rw [QuadraticMap.polar]
  have hsum2a : (a + b) + (a - b) = (2 : ℝ) • a := by rw [two_smul]; abel
  have hQ2a : Q ((2 : ℝ) • a) = 4 * Q a := by rw [QuadraticMap.map_smul]; ring
  have hpolar_eq : QuadraticMap.polar Q (a + b) (a - b) = 2 * (Q a - Q b) := by
    rw [hpolar_sum, hsum2a, hQ2a, h1, h2]; ring
  have hbound := quadratic_polar_bound hQ_nonneg hQ_le (a + b) (a - b)
  rw [hpolar_eq, abs_mul] at hbound
  norm_num at hbound
  have hnormab : ‖a + b‖ ≤ 2 := by
    calc ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
    _ = 2 := by rw [ha, hb]; norm_num
  nlinarith [hbound, hnormab, norm_nonneg (a - b), abs_nonneg (Q a - Q b),
    mul_le_mul_of_nonneg_right hnormab (mul_nonneg hWnonneg (norm_nonneg (a - b)))]

include hg hnn in
/-- Le poids d'une frame function complexe positive est positif (somme de valeurs `≥ 0`
sur n'importe quelle base). -/
theorem cframe_weight_nonneg : 0 ≤ W := by
  have hsum := hg (EuclideanSpace.basisFun (Fin n) ℂ)
  rw [← hsum]
  exact Finset.sum_nonneg (fun i _ => hnn _ ((EuclideanSpace.basisFun (Fin n) ℂ).norm_eq_one i))

set_option maxHeartbeats 1000000 in
include hg hnn hphase hn in
/-- **M3-5(d).** `g` est `2W`-lipschitzienne sur la sphère unité. Ajustement de phase
(`exists_phase_adjust`) pour se ramener à `⟪u,w'⟫` réel `≥ 0` ; cas d'égalité de
Cauchy-Schwarz si `‖⟪u,w'⟫‖ = 1` (alors `w' = u`) ; sinon Gram-Schmidt (`v`, unitaire,
`⟪u,v⟫ = 0`), complété par `z` (`exists_unit_orthogonal_to_pair_complex`, LE point d'entrée
de `n ≥ 3`) en triplet orthonormé `(u,v,z)` ; la section réelle associée envoie
`p := (1,0,0)` sur `u` et `q := (C,s,0)` sur `w'`, et `quadratic_lipschitz` conclut. -/
theorem g_lipschitz (u w : H n) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    |g u - g w| ≤ 2 * W * ‖u - w‖ := by
  obtain ⟨c₀, hc₀norm, hc₀inner, hc₀close⟩ := exists_phase_adjust u w hu hw
  set w' : H n := c₀ • w with hw'_def
  have hw'norm : ‖w'‖ = 1 := by rw [hw'_def, norm_smul, hc₀norm, hw, one_mul]
  have hgw' : g w' = g w := hphase c₀ w hc₀norm
  set C : ℝ := ‖⟪u, w⟫_ℂ‖ with hC_def
  have hCnonneg : 0 ≤ C := norm_nonneg _
  have hCle1 : C ≤ 1 := by
    calc C ≤ ‖u‖ * ‖w‖ := norm_inner_le_norm u w
    _ = 1 := by rw [hu, hw]; ring
  have hWnonneg : 0 ≤ W := cframe_weight_nonneg hg hnn
  suffices hsuff : |g u - g w'| ≤ 2 * W * ‖u - w'‖ by
    calc |g u - g w| = |g u - g w'| := by rw [hgw']
    _ ≤ 2 * W * ‖u - w'‖ := hsuff
    _ ≤ 2 * W * ‖u - w‖ := mul_le_mul_of_nonneg_left hc₀close (by positivity)
  by_cases hC1 : C = 1
  · have heq_inner : ⟪u, w'⟫_ℂ = (‖u‖ : ℂ) * (‖w'‖ : ℂ) := by
      rw [hc₀inner, hu, hw'norm, hC1]; norm_num
    have heq : (‖w'‖ : ℂ) • u = (‖u‖ : ℂ) • w' := inner_eq_norm_mul_iff.mp heq_inner
    rw [hu, hw'norm] at heq
    simp only [Complex.ofReal_one, one_smul] at heq
    rw [heq]; simp
  · have hCsq_lt : C ^ 2 < 1 := by nlinarith [lt_of_le_of_ne hCle1 hC1, hCnonneg]
    set s : ℝ := Real.sqrt (1 - C ^ 2) with hs_def
    have hs_pos : 0 < s := Real.sqrt_pos.mpr (by linarith [hCsq_lt])
    have hssq : s ^ 2 = 1 - C ^ 2 := Real.sq_sqrt (by linarith [hCsq_lt])
    have hCssq : C ^ 2 + s ^ 2 = 1 := by rw [hssq]; ring
    have hwu_inner : ⟪w', u⟫_ℂ = (C : ℂ) := by
      rw [(inner_conj_symm w' u).symm, hc₀inner, Complex.conj_ofReal]
    set d : H n := w' - (C : ℂ) • u with hd_def
    have huu : ⟪u, u⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
    have hud : ⟪u, d⟫_ℂ = 0 := by
      have hstep : ⟪u, d⟫_ℂ = ⟪u, w'⟫_ℂ - (C : ℂ) * ⟪u, u⟫_ℂ := by
        rw [hd_def, inner_sub_right]
        congr 1
        exact inner_smul_right u u (C : ℂ)
      rw [hstep, huu, mul_one, hc₀inner, sub_self]
    have hCu_inner : ⟪w', (C : ℂ) • u⟫_ℂ = ((C ^ 2 : ℝ) : ℂ) := by
      rw [inner_smul_right, hwu_inner]; push_cast; ring
    have hCu_norm : ‖(C : ℂ) • u‖ = C := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hCnonneg, hu, mul_one]
    have hre_Csq : RCLike.re (((C ^ 2 : ℝ)) : ℂ) = C ^ 2 := RCLike.ofReal_re _
    have hd2 : ‖d‖ ^ 2 = s ^ 2 := by
      rw [hd_def, norm_sub_sq (𝕜 := ℂ), hw'norm, hCu_inner, hre_Csq, hCu_norm, hssq]; ring
    have hdnorm : ‖d‖ = s := by
      have hh := Real.sqrt_sq (norm_nonneg d)
      rw [hd2, Real.sqrt_sq hs_pos.le] at hh
      exact hh.symm
    set v : H n := (s⁻¹ : ℂ) • d with hv_def
    have hvnorm : ‖v‖ = 1 := by
      rw [hv_def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs_pos,
        hdnorm, inv_mul_cancel₀ hs_pos.ne']
    have huv : ⟪u, v⟫_ℂ = 0 := by rw [hv_def, inner_smul_right, hud, mul_zero]
    have hvu : ⟪v, u⟫_ℂ = 0 := by
      rw [(inner_conj_symm v u).symm, huv, map_zero]
    obtain ⟨z, hznorm, hzu, hzv⟩ := exists_unit_orthogonal_to_pair_complex hn u v
    have huz : ⟪u, z⟫_ℂ = 0 := by
      rw [(inner_conj_symm u z).symm, hzu, map_zero]
    have hvz : ⟪v, z⟫_ℂ = 0 := by
      rw [(inner_conj_symm v z).symm, hzv, map_zero]
    have hvv : ⟪v, v⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hvnorm]; norm_num
    have hzz : ⟪z, z⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hznorm]; norm_num
    set triple : Fin 3 → H n := ![u, v, z] with htriple_def
    have htriple_orth : Orthonormal ℂ triple := by
      rw [orthonormal_iff_ite]
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [htriple_def, hu, hvnorm, hznorm, huv, hvu, huz, hzu, hvz, hzv]
    obtain ⟨Q, hQ⟩ := homogExt_realSection hg hnn hphase hn triple htriple_orth
    set p : E3 := (!₂[1, 0, 0] : E3) with hp_def
    set q : E3 := (!₂[C, s, 0] : E3) with hq_def
    have hrsp : realSection triple p = u := by
      unfold realSection
      rw [Fin.sum_univ_three]
      simp [hp_def, htriple_def]
    have hrsq : realSection triple q = w' := by
      have hcomp : realSection triple q = (C : ℂ) • u + (s : ℂ) • v + (0 : ℂ) • z := by
        unfold realSection
        rw [Fin.sum_univ_three]
        simp [hq_def, htriple_def]
      rw [hcomp, zero_smul, add_zero, hv_def, hd_def, smul_smul,
        show (s : ℂ) * (s⁻¹ : ℂ) = 1 from by
          rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ hs_pos.ne',
            Complex.ofReal_one],
        one_smul]
      abel
    have hgu_eq : g u = Q p := by
      have h1 : ‖realSection triple p‖ = 1 := by rw [hrsp]; exact hu
      rw [← hrsp, ← homogExt_of_unit (g := g) h1]
      exact hQ p
    have hgw'_eq : g w' = Q q := by
      have h1 : ‖realSection triple q‖ = 1 := by rw [hrsq]; exact hw'norm
      rw [← hrsq, ← homogExt_of_unit (g := g) h1]
      exact hQ q
    have hQ_nonneg : ∀ x : E3, 0 ≤ Q x := fun x => by rw [← hQ x]; exact homogExt_nonneg hnn _
    have hQ_le : ∀ x : E3, Q x ≤ W * ‖x‖ ^ 2 := fun x => by
      rw [← hQ x, ← realSection_norm triple htriple_orth x]
      exact homogExt_le hg hnn hn _
    have hpnorm : ‖p‖ = 1 := by
      rw [hp_def, EuclideanSpace.norm_eq]
      simp [Fin.sum_univ_three]
    have hqnorm : ‖q‖ = 1 := by
      have hqsq : ‖q‖ ^ 2 = C ^ 2 + s ^ 2 := by
        rw [hq_def, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
        simp [Fin.sum_univ_three, sq_abs]
      rw [hCssq] at hqsq
      have hh := Real.sqrt_sq (norm_nonneg q)
      rw [hqsq] at hh
      rw [← hh]; norm_num
    have hlip := quadratic_lipschitz hQ_nonneg hQ_le hpnorm hqnorm
    rw [← hgu_eq, ← hgw'_eq] at hlip
    have hpq_eq : realSection triple (p - q) = u - w' := by
      have hlinear : realSection triple (p - q)
          = realSection triple p - realSection triple q := by
        unfold realSection
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← sub_smul]
        congr 1
        simp [PiLp.sub_apply]
      rw [hlinear, hrsp, hrsq]
    have hpq_norm : ‖p - q‖ = ‖u - w'‖ := by
      rw [← realSection_norm triple htriple_orth (p - q), hpq_eq]
    rwa [hpq_norm] at hlip

set_option maxHeartbeats 800000 in
include hg hnn hphase hn in
/-- **M3-5(e).** `g` atteint son maximum sur la sphère unité de tout sous-espace `U ≠ ⊥`,
par compacité (sphère de `H n` compacte, `U` fermé car de dimension finie, donc `S := U ∩ sphère`
compact) et continuité (`g_lipschitz` donne la lipschitzianité de `g` sur `S`). -/
theorem attains_max_on (U : Submodule ℂ (H n)) (hU : U ≠ ⊥) :
    ∃ x ∈ U, ‖x‖ = 1 ∧ ∀ w ∈ U, ‖w‖ = 1 → g w ≤ g x := by
  set S : Set (H n) := (U : Set (H n)) ∩ Metric.sphere (0 : H n) 1 with hS_def
  have hUclosed : IsClosed (U : Set (H n)) := Submodule.closed_of_finiteDimensional _
  have hScompact : IsCompact S := (isCompact_sphere (0 : H n) 1).inter_left hUclosed
  obtain ⟨x0, hx0U, hx0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  have hx0norm : ‖x0‖ ≠ 0 := norm_ne_zero_iff.mpr hx0ne
  set x1 : H n := ((‖x0‖ : ℝ)⁻¹ : ℂ) • x0 with hx1_def
  have hx1U : x1 ∈ U := U.smul_mem _ hx0U
  have hx1norm : ‖x1‖ = 1 := by
    rw [hx1_def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg x0), inv_mul_cancel₀ hx0norm]
  have hSne : S.Nonempty :=
    ⟨x1, hx1U, by rw [Metric.mem_sphere, dist_eq_norm, sub_zero, hx1norm]⟩
  have hLip : LipschitzOnWith (Real.toNNReal (2 * W)) g S :=
    LipschitzOnWith.of_dist_le' (fun a ha b hb => by
      have haS : ‖a‖ = 1 := by
        have h := ha.2; rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
      have hbS : ‖b‖ = 1 := by
        have h := hb.2; rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
      rw [Real.dist_eq, dist_eq_norm]
      exact g_lipschitz hg hnn hphase hn a b haS hbS)
  obtain ⟨x, hxS, hxmax⟩ := hScompact.exists_isMaxOn hSne hLip.continuousOn
  refine ⟨x, hxS.1, ?_, fun w hwU hwnorm => isMaxOn_iff.mp hxmax w ⟨hwU, ?_⟩⟩
  · have h := hxS.2; rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
  · rw [Metric.mem_sphere, dist_eq_norm, sub_zero, hwnorm]

/- ═══════════════════════════════════════════════════════════════════
   M3-6. Identité d'épluchage (CKM / Dvurečenskij, cœur de la récurrence
   d'assemblage). Si `x` maximise `g` sur la sphère unité du plan complexe
   engendré par `x` et `y`, la valeur de l'extension homogène `q := homogExt g`
   en `y` se décompose selon la projection orthogonale sur `x`.
   ═══════════════════════════════════════════════════════════════════ -/

set_option maxHeartbeats 1600000 in
include hg hnn hphase hn in
theorem peel (x y : H n) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hmax : ∀ w ∈ Submodule.span ℂ ({x, y} : Set (H n)), ‖w‖ = 1 → g w ≤ g x) :
    homogExt g y = g x * ‖⟪x, y⟫_ℂ‖ ^ 2 + homogExt g (y - ⟪x, y⟫_ℂ • x) := by
  have hxx : ⟪x, x⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hx]; norm_num
  by_cases hcol : ‖⟪x, y⟫_ℂ‖ = 1
  · -- Cas colinéaire : égalité de Cauchy-Schwarz, y = r • x pour un r unitaire.
    have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hx; norm_num at hx
    have hy0 : y ≠ 0 := by intro h; rw [h, norm_zero] at hy; norm_num at hy
    obtain ⟨r, -, hyr⟩ := (norm_inner_eq_norm_iff hx0 hy0).mp (by rw [hcol, hx, hy]; ring)
    have hrnorm : ‖r‖ = 1 := by
      have h := hy; rw [hyr, norm_smul, hx, mul_one] at h; exact h
    have hzero : y - ⟪x, y⟫_ℂ • x = 0 := by
      rw [hyr, inner_smul_right, hxx, mul_one, sub_self]
    rw [hzero, hcol, homogExt_of_unit hy, hyr, hphase r x hrnorm]
    simp [homogExt]
  · -- Cas général : Gram-Schmidt (x, v, z), tueur de terme croisé, décomposition quadratique.
    set α : ℝ := ‖⟪x, y⟫_ℂ‖ with hα_def
    have hα_nonneg : 0 ≤ α := norm_nonneg _
    have hα_le1 : α ≤ 1 := by
      calc α ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm x y
      _ = 1 := by rw [hx, hy]; ring
    have hα_lt1 : α < 1 := lt_of_le_of_ne hα_le1 hcol
    obtain ⟨c', hc'norm, hc'inner, -⟩ := exists_phase_adjust x y hx hy
    set w : H n := c' • y with hw_def
    have hwnorm : ‖w‖ = 1 := by rw [hw_def, norm_smul, hc'norm, hy, one_mul]
    have hxw_inner : ⟪x, w⟫_ℂ = (α : ℂ) := hc'inner
    have hy_eq : (starRingEnd ℂ c') • w = y := by
      rw [hw_def, smul_smul, RCLike.conj_mul, hc'norm]; simp
    have hxy_val : ⟪x, y⟫_ℂ = starRingEnd ℂ c' * (α : ℂ) := by
      rw [← hy_eq, inner_smul_right, hxw_inner]
    have hg_wy : g w = g y := by rw [hw_def]; exact hphase c' y hc'norm
    have hden1 : (0 : ℝ) < 1 - α := by linarith
    have hden2 : (0 : ℝ) < 1 + α := by linarith
    have hsq_pos : 0 < 1 - α ^ 2 := by nlinarith [mul_pos hden1 hden2]
    set s : ℝ := Real.sqrt (1 - α ^ 2) with hs_def
    have hs_pos : 0 < s := Real.sqrt_pos.mpr hsq_pos
    have hssq : s ^ 2 = 1 - α ^ 2 := Real.sq_sqrt hsq_pos.le
    set d : H n := w - (α : ℂ) • x with hd_def
    have hxd_inner : ⟪x, d⟫_ℂ = 0 := by
      have hstep : ⟪x, d⟫_ℂ = ⟪x, w⟫_ℂ - (α : ℂ) * ⟪x, x⟫_ℂ := by
        rw [hd_def, inner_sub_right]; congr 1; exact inner_smul_right x x (α : ℂ)
      rw [hstep, hxx, mul_one, hxw_inner, sub_self]
    have hwx_inner : ⟪w, x⟫_ℂ = (α : ℂ) := by
      rw [(inner_conj_symm w x).symm, hxw_inner, Complex.conj_ofReal]
    have hαx_inner : ⟪w, (α : ℂ) • x⟫_ℂ = ((α ^ 2 : ℝ) : ℂ) := by
      rw [inner_smul_right, hwx_inner]; push_cast; ring
    have hαx_norm : ‖(α : ℂ) • x‖ = α := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα_nonneg, hx, mul_one]
    have hre_ααsq : RCLike.re (((α ^ 2 : ℝ)) : ℂ) = α ^ 2 := RCLike.ofReal_re _
    have hd2 : ‖d‖ ^ 2 = s ^ 2 := by
      rw [hd_def, norm_sub_sq (𝕜 := ℂ), hwnorm, hαx_inner, hre_ααsq, hαx_norm, hssq]; ring
    have hdnorm : ‖d‖ = s := by
      have hh := Real.sqrt_sq (norm_nonneg d)
      rw [hd2, Real.sqrt_sq hs_pos.le] at hh
      exact hh.symm
    set v : H n := (s⁻¹ : ℂ) • d with hv_def
    have hvnorm : ‖v‖ = 1 := by
      rw [hv_def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs_pos,
        hdnorm, inv_mul_cancel₀ hs_pos.ne']
    have hxv_inner : ⟪x, v⟫_ℂ = 0 := by rw [hv_def, inner_smul_right, hxd_inner, mul_zero]
    have hvx_inner : ⟪v, x⟫_ℂ = 0 := by
      rw [(inner_conj_symm v x).symm, hxv_inner, map_zero]
    have hd_eq_v : d = (s : ℂ) • v := by
      rw [hv_def, smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ hs_pos.ne',
        Complex.ofReal_one, one_smul]
    obtain ⟨z, hznorm, hzx, hzv⟩ := exists_unit_orthogonal_to_pair_complex hn x v
    have hxz_inner : ⟪x, z⟫_ℂ = 0 := by
      rw [(inner_conj_symm x z).symm, hzx, map_zero]
    have hvz_inner : ⟪v, z⟫_ℂ = 0 := by
      rw [(inner_conj_symm v z).symm, hzv, map_zero]
    have hvv1 : ⟪v, v⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hvnorm]; norm_num
    have hzz1 : ⟪z, z⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hznorm]; norm_num
    set triple : Fin 3 → H n := ![x, v, z] with htriple_def
    have htriple_orth : Orthonormal ℂ triple := by
      rw [orthonormal_iff_ite]
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [htriple_def, hx, hvnorm, hznorm, hxv_inner, hvx_inner, hxz_inner, hzx, hvz_inner,
          hzv]
    obtain ⟨Q, hQ⟩ := homogExt_realSection hg hnn hphase hn triple htriple_orth
    set e1 : E3 := (!₂[1, 0, 0] : E3) with he1_def
    set e2 : E3 := (!₂[0, 1, 0] : E3) with he2_def
    have he1x : realSection triple e1 = x := by
      unfold realSection; rw [Fin.sum_univ_three]; simp [he1_def, htriple_def]
    have he2v : realSection triple e2 = v := by
      unfold realSection; rw [Fin.sum_univ_three]; simp [he2_def, htriple_def]
    have hQe1 : Q e1 = g x := by rw [← hQ e1, he1x, homogExt_of_unit hx]
    have hQe2 : Q e2 = g v := by rw [← hQ e2, he2v, homogExt_of_unit hvnorm]
    have hv_mem : v ∈ Submodule.span ℂ ({x, y} : Set (H n)) := by
      have hw_mem : w ∈ Submodule.span ℂ ({x, y} : Set (H n)) :=
        hw_def ▸ Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      have hd_mem : d ∈ Submodule.span ℂ ({x, y} : Set (H n)) :=
        hd_def ▸ Submodule.sub_mem _ hw_mem
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      exact hv_def ▸ Submodule.smul_mem _ _ hd_mem
    have hgv_le : g v ≤ g x := hmax v hv_mem hvnorm
    have hK_nonneg : 0 ≤ g x - g v := by linarith
    have hcomb_norm : ∀ ε : ℝ, ‖e1 + ε • e2‖ ^ 2 = 1 + ε ^ 2 := by
      intro ε
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp [he1_def, he2_def, Fin.sum_univ_three, sq_abs]
    have hQexpand : ∀ ε : ℝ,
        Q (e1 + ε • e2) = Q e1 + ε ^ 2 * Q e2 + ε * QuadraticMap.polar Q e1 e2 := by
      intro ε
      have h1 := QuadraticMap.map_add Q e1 (ε • e2)
      simp only [QuadraticMap.map_smul, QuadraticMap.polar_smul_right, smul_eq_mul] at h1
      nlinarith [h1]
    have hQ_bound : ∀ ε : ℝ, Q (e1 + ε • e2) ≤ g x * (1 + ε ^ 2) := by
      intro ε
      set nrm : ℝ := ‖e1 + ε • e2‖ with hnrm_def
      have hnrm_sq : nrm ^ 2 = 1 + ε ^ 2 := hcomb_norm ε
      have hnrm_pos : 0 < nrm := by
        have hpos : (0 : ℝ) < 1 + ε ^ 2 := by positivity
        nlinarith [sq_nonneg (nrm - 1), norm_nonneg (e1 + ε • e2), hnrm_sq]
      set nε : E3 := (nrm⁻¹ : ℝ) • (e1 + ε • e2) with hnε_def
      have hnε_norm : ‖nε‖ = 1 := by
        rw [hnε_def, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnrm_pos,
          inv_mul_cancel₀ hnrm_pos.ne']
      have hQnε : Q nε = (nrm ^ 2)⁻¹ * Q (e1 + ε • e2) := by
        rw [hnε_def, QuadraticMap.map_smul, smul_eq_mul]; ring
      have hrsnε_norm : ‖realSection triple nε‖ = 1 := by
        rw [realSection_norm triple htriple_orth]; exact hnε_norm
      have hcomp : realSection triple (e1 + ε • e2) = (1 : ℂ) • x + (ε : ℂ) • v + (0 : ℂ) • z := by
        unfold realSection
        rw [Fin.sum_univ_three]
        simp [he1_def, he2_def, htriple_def]
      have hsmul_comp : realSection triple nε = (nrm⁻¹ : ℂ) • realSection triple (e1 + ε • e2) := by
        rw [hnε_def]
        unfold realSection
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [smul_smul]; congr 1
        simp only [PiLp.smul_apply, smul_eq_mul]
        push_cast; ring
      have hrsnε_mem : realSection triple nε ∈ Submodule.span ℂ ({x, y} : Set (H n)) := by
        rw [hsmul_comp, hcomp, one_smul, zero_smul, add_zero]
        exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ _ hv_mem))
      have hglenε : g (realSection triple nε) ≤ g x := hmax _ hrsnε_mem hrsnε_norm
      have hQeq : Q nε = g (realSection triple nε) := by
        rw [← hQ nε, homogExt_of_unit hrsnε_norm]
      rw [hQeq] at hQnε
      have hle : (nrm ^ 2)⁻¹ * Q (e1 + ε • e2) ≤ g x := by rw [← hQnε]; exact hglenε
      rw [hnrm_sq] at hle
      have hpos : (0 : ℝ) < 1 + ε ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hle hpos.le
      rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_comm (1 + ε ^ 2) (g x)] at this
    have hbound : ∀ ε : ℝ, ε * QuadraticMap.polar Q e1 e2 ≤ ε ^ 2 * (g x - g v) := by
      intro ε
      have h1 := hQ_bound ε
      rw [hQexpand ε, hQe1, hQe2] at h1
      nlinarith [h1]
    have hB_zero : QuadraticMap.polar Q e1 e2 = 0 := by
      by_contra hBne
      set K : ℝ := g x - g v with hK_def2
      set ε0 : ℝ := QuadraticMap.polar Q e1 e2 / (K + 1) with hε0_def
      have hden_pos : 0 < K + 1 := by linarith
      have hidentity : ε0 * QuadraticMap.polar Q e1 e2 - ε0 ^ 2 * K
          = (QuadraticMap.polar Q e1 e2) ^ 2 / (K + 1) ^ 2 := by
        rw [hε0_def]; field_simp; ring
      have hpos : 0 < (QuadraticMap.polar Q e1 e2) ^ 2 / (K + 1) ^ 2 := by positivity
      have h := hbound ε0
      linarith [hidentity, hpos, h]
    have hQ_ab : ∀ a b : ℝ, Q (a • e1 + b • e2) = a ^ 2 * g x + b ^ 2 * g v := by
      intro a b
      have h1 := QuadraticMap.map_add Q (a • e1) (b • e2)
      simp only [QuadraticMap.map_smul, QuadraticMap.polar_smul_left,
        QuadraticMap.polar_smul_right, hB_zero, smul_eq_mul, hQe1, hQe2] at h1
      nlinarith [h1]
    have hy_sub : y - ⟪x, y⟫_ℂ • x = (starRingEnd ℂ c' * (s : ℂ)) • v := by
      rw [hxy_val, ← hy_eq, mul_smul, ← smul_sub, ← hd_def, hd_eq_v, ← smul_smul]
    have hscalar_norm : ‖starRingEnd ℂ c' * (s : ℂ)‖ = s := by
      rw [norm_mul, RCLike.norm_conj, hc'norm, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs_pos]
    have hq_sub : homogExt g (y - ⟪x, y⟫_ℂ • x) = s ^ 2 * g v := by
      rw [hy_sub, homogExt_smul hphase, hscalar_norm, homogExt_of_unit hvnorm]
    have hgy_eq : g y = α ^ 2 * g x + s ^ 2 * g v := by
      have hcombQ := hQ_ab α s
      have hrs_eq : realSection triple (α • e1 + s • e2) = w := by
        have hcomp2 : realSection triple (α • e1 + s • e2)
            = (α : ℂ) • x + (s : ℂ) • v + (0 : ℂ) • z := by
          unfold realSection
          rw [Fin.sum_univ_three]
          simp [he1_def, he2_def, htriple_def]
        rw [hcomp2, zero_smul, add_zero, ← hd_eq_v, hd_def]
        abel
      have hQw : Q (α • e1 + s • e2) = g w := by
        rw [← hQ (α • e1 + s • e2), hrs_eq, homogExt_of_unit hwnorm]
      rw [hQw, hg_wy] at hcombQ
      exact hcombQ
    rw [homogExt_of_unit hy, hq_sub, hgy_eq]
    ring

end CFrameSections

end
end Gleason
