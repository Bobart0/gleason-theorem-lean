import Gleason.Busch.Effects

/-!
# Théorème de Busch (2003) — énoncé principal

**Cible du jalon M-B** (avant Gleason). Le chemin de preuve, entièrement algébrique
(aucune analyse fine sur la sphère, contrairement à Gleason) :

1. `f 0 = 0`, additivité finie itérée ;
2. homogénéité rationnelle : `f (q • T) = q * f T` pour `q ∈ ℚ≥0` (bissection dyadique) ;
3. monotonie (déjà dans `Effects.lean`) ⇒ homogénéité RÉELLE par encadrement rationnel ;
4. extension de `f` en fonctionnelle réelle-linéaire sur les opérateurs auto-adjoints
   (tout auto-adjoint est différence d'effets à un facteur positif près) ;
5. représentation de Riesz en dimension finie : la fonctionnelle est `T ↦ Re tr (ρ T)`
   pour un unique `ρ` auto-adjoint ;
6. positivité de `ρ` (tester sur les effets de rang 1) et trace 1 (tester sur `1`).

Chaque étape est un lemme séparé à ajouter ici en M-B ; seul l'énoncé final est figé.
-/

namespace Gleason

open scoped InnerProductSpace

noncomputable section

variable {n : ℕ}

-- ═══════════════════════════════════════════════════════════════════
-- PLAN DE PREUVE — LEMMES INTERMÉDIAIRES (tous sorry, à valider)
-- ═══════════════════════════════════════════════════════════════════
--
-- CONVENTION SCALAIRE (utilisée uniformément dans tout ce fichier) :
--
--   Pour r : ℝ et T : H n →ₗ[ℂ] H n, on écrit  (↑r : ℂ) • T.
--
-- C'est l'action ℂ-module de (Complex.ofReal r) sur T, c.-à-d.
-- ((↑r : ℂ) • T) x = (↑r : ℂ) • (T x). Sémantiquement identique à
-- l'action ℝ-module (r • T via Module.complexToReal), mais la forme
-- explicite (↑r : ℂ) • T est préférée car :
--   1. elle évite les ambiguïtés de résolution d'instance SMul ℝ _;
--   2. elle rend visible le cast ℝ → ℂ dans les buts et les hypothèses ;
--   3. elle se compose bien avec les lemmes smul_sub, smul_add, etc.
--      du ℂ-module, qui sont déjà en scope.

-- ── (B1) Préservation des effets par homothétie réelle ────────────
-- Nécessaire pour que les énoncés B2–B4 aient un sens.
-- Preuve : 0 ≤ rT ≤ T ≤ 1 par positivité de r et (1-r)T.

theorem isEffect_complexSmul {T : H n →ₗ[ℂ] H n} (hT : IsEffect T)
    {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    IsEffect ((↑r : ℂ) • T) := by
  refine ⟨⟨hT.1.1.smul (Complex.conj_ofReal r), fun x => ?_⟩,
         ⟨LinearMap.IsSymmetric.one.sub (hT.1.1.smul (Complex.conj_ofReal r)), fun x => ?_⟩⟩
  · simp only [LinearMap.smul_apply, inner_smul_left, Complex.conj_ofReal,
               Complex.re_ofReal_mul]
    exact mul_nonneg hr₀ (hT.1.2 x)
  · simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply,
               inner_sub_left, inner_smul_left, Complex.conj_ofReal, Complex.sub_re,
               Complex.re_ofReal_mul]
    have h1 : (⟪T x, x⟫_ℂ).re ≤ (⟪x, x⟫_ℂ).re := by
      have := hT.2.2 x
      simp only [LinearMap.sub_apply, Module.End.one_apply, inner_sub_left,
                 Complex.sub_re] at this
      linarith
    linarith [mul_le_of_le_one_left (hT.1.2 x) hr₁]

-- ── (B2) Pas dyadique : f(T/2) = f(T)/2 ─────────────────────────
-- Base de l'induction dyadique.
-- Preuve : T = (1/2)T + (1/2)T, les deux sommandes sont des effets
-- (par B1), leur somme est T qui est un effet, donc
-- f(T) = f((1/2)T) + f((1/2)T) = 2 · f((1/2)T).

theorem EffectMeasure.map_half_smul (F : EffectMeasure n)
    {T : H n →ₗ[ℂ] H n} (hT : IsEffect T) :
    F.f ((↑(2⁻¹ : ℝ) : ℂ) • T) = 2⁻¹ * F.f T := by
  have heff : IsEffect ((↑(2⁻¹ : ℝ) : ℂ) • T) :=
    isEffect_complexSmul hT (by norm_num) (by norm_num)
  have hsum : (↑(2⁻¹ : ℝ) : ℂ) • T + (↑(2⁻¹ : ℝ) : ℂ) • T = T := by
    rw [← add_smul]
    have : (↑(2⁻¹ : ℝ) : ℂ) + (↑(2⁻¹ : ℝ) : ℂ) = 1 := by push_cast; norm_num
    rw [this, one_smul]
  have h := F.additive _ _ heff heff (by rw [hsum]; exact hT)
  rw [hsum] at h
  linarith

-- ── (B3) Homogénéité dyadique : f((m/2^k) · T) = (m/2^k) · f(T) ─
-- Induction sur k (B2) et sur m (additivité itérée).
-- Précondition : m/2^k ≤ 1, de sorte que (m/2^k)·T est un effet.

-- Helper : f((1/2^k) • T) = (1/2^k) * f T par itération de B2.
private theorem one_le_two_pow_real (k : ℕ) : (1 : ℝ) ≤ 2 ^ k := by
  calc (1 : ℝ) = 1 ^ k := (one_pow k).symm
    _ ≤ 2 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k

private theorem map_inv_pow2_smul (F : EffectMeasure n)
    {T : H n →ₗ[ℂ] H n} (hT : IsEffect T) (k : ℕ) :
    F.f ((↑(1 / 2 ^ k : ℝ) : ℂ) • T) = (1 / 2 ^ k : ℝ) * F.f T := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2k_pos : (0 : ℝ) < 2 ^ k := by positivity
    have heff_k : IsEffect ((↑(1 / 2 ^ k : ℝ) : ℂ) • T) :=
      isEffect_complexSmul hT (by positivity)
        ((div_le_one h2k_pos).mpr (one_le_two_pow_real k))
    have hconv : (↑(1 / 2 ^ (k + 1) : ℝ) : ℂ) • T =
        (↑(2⁻¹ : ℝ) : ℂ) • ((↑(1 / 2 ^ k : ℝ) : ℂ) • T) := by
      rw [← mul_smul]; congr 1; push_cast; ring
    rw [hconv, F.map_half_smul heff_k, ih]; ring

theorem EffectMeasure.map_dyadic_smul (F : EffectMeasure n)
    {T : H n →ₗ[ℂ] H n} (hT : IsEffect T) (k m : ℕ) (hm : m ≤ 2 ^ k) :
    F.f ((↑(m / 2 ^ k : ℝ) : ℂ) • T) = (m / 2 ^ k : ℝ) * F.f T := by
  have h2k_pos : (0 : ℝ) < 2 ^ k := by positivity
  induction m with
  | zero => simp [F.map_zero]
  | succ m ih =>
    have hm' : m ≤ 2 ^ k := Nat.le_of_succ_le hm
    have hmq : (↑m / 2 ^ k : ℝ) ≤ 1 := by
      rw [div_le_one h2k_pos]; exact_mod_cast hm'
    have hmq1 : (↑(m + 1) / 2 ^ k : ℝ) ≤ 1 := by
      rw [div_le_one h2k_pos]; exact_mod_cast hm
    have hunit : (1 / 2 ^ k : ℝ) ≤ 1 :=
      (div_le_one h2k_pos).mpr (one_le_two_pow_real k)
    have heff_m : IsEffect ((↑(↑m / 2 ^ k : ℝ) : ℂ) • T) :=
      isEffect_complexSmul hT (by positivity) hmq
    have heff_unit : IsEffect ((↑(1 / 2 ^ k : ℝ) : ℂ) • T) :=
      isEffect_complexSmul hT (by positivity) hunit
    have heff_m1 : IsEffect ((↑(↑(m + 1) / 2 ^ k : ℝ) : ℂ) • T) :=
      isEffect_complexSmul hT (by positivity) hmq1
    have hdecomp : (↑(↑(m + 1) / 2 ^ k : ℝ) : ℂ) • T =
        (↑(↑m / 2 ^ k : ℝ) : ℂ) • T + (↑(1 / 2 ^ k : ℝ) : ℂ) • T := by
      rw [← add_smul]; congr 1; push_cast; ring
    rw [hdecomp, F.additive _ _ heff_m heff_unit (by rw [← hdecomp]; exact heff_m1),
        ih hm', map_inv_pow2_smul F hT k]
    push_cast; ring

-- ── (B4) Homogénéité rationnelle ─────────────────────────────────
-- Tout rationnel q ∈ [0,1] s'écrit m/2^k après réduction au même
-- dénominateur (q = a/b, b | 2^k pour k assez grand — ou, plus
-- directement, combiner additivité itérée pour le numérateur et B2
-- pour la division). On peut aussi passer par :
--   f(n · T) = n · f(T)  (additivité itérée, n : ℕ, n·T effet)
-- puis diviser.

-- Lemme auxiliaire : si A et B sont positifs et A+B est un effet, alors A l'est.
-- (car 1 − A = (1 − (A+B)) + B, somme de deux positifs)
private theorem isEffect_summand {A B : H n →ₗ[ℂ] H n}
    (hA : IsPositiveOp A) (hB : IsPositiveOp B) (hAB : IsEffect (A + B)) :
    IsEffect A := by
  refine ⟨hA, ⟨LinearMap.IsSymmetric.one.sub hA.1, fun x => ?_⟩⟩
  have heq : (1 - A) x = (1 - (A + B)) x + B x := by
    simp [LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply]; abel
  rw [heq, inner_add_left, Complex.add_re]
  exact add_nonneg (hAB.2.2 x) (hB.2 x)

theorem EffectMeasure.map_nat_smul (F : EffectMeasure n)
    {T : H n →ₗ[ℂ] H n} (hT : IsEffect T) (m : ℕ)
    (heff : IsEffect ((↑(m : ℝ) : ℂ) • T)) :
    F.f ((↑(m : ℝ) : ℂ) • T) = (m : ℝ) * F.f T := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, Complex.ofReal_zero, zero_smul, zero_mul, F.map_zero]
  | succ m ih =>
    have hdecomp : (↑(↑(m + 1) : ℝ) : ℂ) • T = (↑(↑m : ℝ) : ℂ) • T + T := by
      have : (↑(↑(m + 1) : ℝ) : ℂ) = (↑(↑m : ℝ) : ℂ) + 1 := by push_cast; ring
      rw [this, add_smul, one_smul]
    have hm_pos : IsPositiveOp ((↑(↑m : ℝ) : ℂ) • T) :=
      ⟨hT.1.1.smul (Complex.conj_ofReal _), fun x => by
        simp only [LinearMap.smul_apply, inner_smul_left, Complex.conj_ofReal,
                   Complex.re_ofReal_mul]
        exact mul_nonneg (Nat.cast_nonneg m) (hT.1.2 x)⟩
    have hm_eff : IsEffect ((↑(↑m : ℝ) : ℂ) • T) :=
      isEffect_summand hm_pos hT.1 (by rw [← hdecomp]; exact heff)
    rw [hdecomp, F.additive _ _ hm_eff hT (by rw [← hdecomp]; exact heff), ih hm_eff]
    push_cast; ring

-- ── (B5) Homogénéité réelle (le cœur de Busch 2003) ─────────────
-- Pour r ∈ [0,1] et T effet, on encadre r par des rationnels :
-- q₁ ≤ r ≤ q₂. Alors q₁·T ≤ r·T ≤ q₂·T (opérateurs positifs),
-- tous trois effets, et par monotonie (EffectMeasure.mono) :
--   q₁ · f(T) = f(q₁·T) ≤ f(r·T) ≤ f(q₂·T) = q₂ · f(T).
-- En faisant tendre q₁, q₂ → r on obtient f(r·T) = r · f(T).
-- Note : la borne 0 ≤ f(T) ≤ 1 (de nonneg + map_one) assure que
-- les inégalités ne dégénèrent pas.

private theorem isPositiveOp_smul_sub {T : H n →ₗ[ℂ] H n}
    (hT : IsPositiveOp T) {s t : ℝ} (hst : s ≤ t) :
    IsPositiveOp ((↑t : ℂ) • T - (↑s : ℂ) • T) := by
  have : (↑t : ℂ) • T - (↑s : ℂ) • T = (↑(t - s) : ℂ) • T := by
    rw [← sub_smul, Complex.ofReal_sub]
  rw [this]
  exact ⟨hT.1.smul (Complex.conj_ofReal _), fun x => by
    simp only [LinearMap.smul_apply, inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul]
    exact mul_nonneg (sub_nonneg.mpr hst) (hT.2 x)⟩

theorem EffectMeasure.map_realSmul (F : EffectMeasure n)
    {T : H n →ₗ[ℂ] H n} (hT : IsEffect T)
    {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    F.f ((↑r : ℂ) • T) = r * F.f T := by
  rcases eq_or_lt_of_le hr₁ with rfl | hr₁'
  · simp [Complex.ofReal_one]
  have hrT : IsEffect ((↑r : ℂ) • T) := isEffect_complexSmul hT hr₀ hr₁
  have hfT_le : F.f T ≤ 1 := by
    have : IsEffect (1 : H n →ₗ[ℂ] H n) :=
      ⟨⟨LinearMap.IsSymmetric.one, fun x => by
          simp only [Module.End.one_apply]; exact @inner_self_nonneg ℂ _ _ _ _ x⟩,
       ⟨by simp, fun x => by simp⟩⟩
    linarith [F.mono hT this hT.2, F.map_one]
  suffices h : ∀ k : ℕ, |F.f ((↑r : ℂ) • T) - r * F.f T| ≤ (2⁻¹ : ℝ) ^ k by
    by_contra hne
    have hpos := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (2⁻¹ : ℝ) < 1)
    linarith [h k]
  intro k
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  set m := ⌊r * 2 ^ k⌋₊
  have hmr : (↑m : ℝ) ≤ r * 2 ^ k := Nat.floor_le (mul_nonneg hr₀ h2k.le)
  have hmr' : r * 2 ^ k < ↑m + 1 := Nat.lt_floor_add_one _
  have hm_lt : m < 2 ^ k := by
    exact_mod_cast (show (↑m : ℝ) < (2 : ℝ) ^ k from lt_of_le_of_lt hmr (by nlinarith))
  have hm1_le : m + 1 ≤ 2 ^ k := hm_lt
  have hlo : (↑m : ℝ) / 2 ^ k ≤ r := (div_le_iff₀ h2k).mpr hmr
  have hhi : r ≤ (↑(m + 1) : ℝ) / 2 ^ k := by
    rw [le_div_iff₀ h2k]; push_cast; linarith
  have hlo_eff : IsEffect ((↑((m : ℝ) / 2 ^ k) : ℂ) • T) :=
    isEffect_complexSmul hT (by positivity) ((div_le_one h2k).mpr (by exact_mod_cast hm_lt.le))
  have hhi_eff : IsEffect ((↑(((m + 1 : ℕ) : ℝ) / 2 ^ k) : ℂ) • T) :=
    isEffect_complexSmul hT (by positivity) ((div_le_one h2k).mpr (by exact_mod_cast hm1_le))
  have h_lo_val := F.map_dyadic_smul hT k m hm_lt.le
  have h_hi_val := F.map_dyadic_smul hT k (m + 1) hm1_le
  have h_mono_lo := F.mono hlo_eff hrT (isPositiveOp_smul_sub hT.1 hlo)
  rw [h_lo_val] at h_mono_lo
  have h_mono_hi := F.mono hrT hhi_eff (isPositiveOp_smul_sub hT.1 hhi)
  rw [h_hi_val] at h_mono_hi
  have h_inv : (2⁻¹ : ℝ) ^ k = 1 / 2 ^ k := by rw [one_div, inv_pow]
  have h_gap : (↑(m + 1) : ℝ) / 2 ^ k - r ≤ 1 / 2 ^ k := by
    push_cast; rw [add_div]; linarith [hlo]
  have h_gap' : r - (↑m : ℝ) / 2 ^ k ≤ 1 / 2 ^ k := by
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ h2k]; linarith
  rw [abs_le]; constructor
  · nlinarith [F.nonneg T hT,
      mul_le_mul_of_nonneg_right h_gap' (F.nonneg T hT),
      mul_le_of_le_one_right (div_nonneg one_pos.le h2k.le) hfT_le]
  · nlinarith [F.nonneg T hT,
      mul_le_mul_of_nonneg_right h_gap (F.nonneg T hT),
      mul_le_of_le_one_right (div_nonneg one_pos.le h2k.le) hfT_le]

-- ── (B4b) Corollaire : homogénéité rationnelle ─────────────────
theorem EffectMeasure.map_rat_smul (F : EffectMeasure n)
    {T : H n →ₗ[ℂ] H n} (hT : IsEffect T)
    (q : ℚ) (hq₀ : 0 ≤ q) (hq₁ : (q : ℝ) ≤ 1) :
    F.f ((↑(q : ℝ) : ℂ) • T) = (q : ℝ) * F.f T :=
  F.map_realSmul hT (by exact_mod_cast hq₀) hq₁

-- ── (B6) Décomposition des auto-adjoints en effets ───────────────
-- Tout opérateur auto-adjoint S se décompose en
--   S = c · E₊ − c · E₋
-- avec E₊ = (1 + S/c)/2, E₋ = (1 − S/c)/2 effets, et c > 0.
-- Choix naturel : c = ‖S‖ + 1 (garantit ‖S/c‖ < 1, donc
-- 0 ≤ E± ≤ 1).

theorem selfAdjoint_effect_decomp (S : H n →ₗ[ℂ] H n) (hS : S.IsSymmetric) :
    ∃ (Ep Em : H n →ₗ[ℂ] H n) (c : ℝ),
      IsEffect Ep ∧ IsEffect Em ∧ 0 < c ∧
      S = (↑c : ℂ) • Ep - (↑c : ℂ) • Em := by
  -- Operator norm bound via finite-dimensional continuity
  set c := ‖LinearMap.toContinuousLinearMap S‖ + 1 with hc_def
  have hc : (0 : ℝ) < c := by positivity
  have hSb : ∀ x : H n, ‖S x‖ ≤ (c - 1) * ‖x‖ := by
    intro x
    have h := (LinearMap.toContinuousLinearMap S).le_opNorm x
    simp only [LinearMap.coe_toContinuousLinearMap'] at h
    have hc1 : ‖LinearMap.toContinuousLinearMap S‖ = c - 1 := by linarith [hc_def]
    linarith [mul_le_mul_of_nonneg_right hc1.le (norm_nonneg x)]
  -- Quadratic form bound: |re ⟪Sx, x⟫| ≤ (c-1) ‖x‖²
  have hq : ∀ x : H n, |(⟪S x, x⟫_ℂ).re| ≤ (c - 1) * ‖x‖ ^ 2 := by
    intro x
    calc |(⟪S x, x⟫_ℂ).re|
        ≤ ‖⟪S x, x⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖S x‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ (c - 1) * ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_right (hSb x) (norm_nonneg _)
      _ = (c - 1) * ‖x‖ ^ 2 := by ring
  -- Key identities
  have h_cinv_c : c⁻¹ * c = 1 := inv_mul_cancel₀ (ne_of_gt hc)
  have hcinv : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc
  -- Symmetry of summands
  have hScS := hS.smul (Complex.conj_ofReal (c⁻¹ : ℝ))
  have hSp := (LinearMap.IsSymmetric.one.add hScS).smul (Complex.conj_ofReal (2⁻¹ : ℝ))
  have hSm := (LinearMap.IsSymmetric.one.sub hScS).smul (Complex.conj_ofReal (2⁻¹ : ℝ))
  -- 1 - Ep = Em and 1 - Em = Ep
  have h1p : (1 : H n →ₗ[ℂ] H n) - (↑(2⁻¹ : ℝ) : ℂ) • (1 + (↑(c⁻¹) : ℂ) • S) =
             (↑(2⁻¹ : ℝ) : ℂ) • (1 - (↑(c⁻¹) : ℂ) • S) := by
    ext x; simp [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply,
                  Module.End.one_apply]; ring
  have h1m : (1 : H n →ₗ[ℂ] H n) - (↑(2⁻¹ : ℝ) : ℂ) • (1 - (↑(c⁻¹) : ℂ) • S) =
             (↑(2⁻¹ : ℝ) : ℂ) • (1 + (↑(c⁻¹) : ℂ) • S) := by
    ext x; simp [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply,
                  Module.End.one_apply]; ring
  -- Zero product for nlinarith
  have h_zero : ∀ x : H n, (c⁻¹ * c - 1) * ‖x‖ ^ 2 = 0 := fun _ => by
    rw [h_cinv_c, sub_self, zero_mul]
  -- Positivity of Ep
  have hpos_p : ∀ x : H n,
      0 ≤ (⟪((↑(2⁻¹ : ℝ) : ℂ) • (1 + (↑(c⁻¹) : ℂ) • S)) x, x⟫_ℂ).re := by
    intro x
    simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
               inner_smul_left, inner_add_left, Complex.conj_ofReal,
               Complex.re_ofReal_mul, Complex.add_re]
    apply mul_nonneg (by positivity : (0 : ℝ) ≤ 2⁻¹)
    have hre : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [hre]
    nlinarith [mul_le_mul_of_nonneg_left ((abs_le.mp (hq x)).1) hcinv.le,
               h_zero x, mul_nonneg hcinv.le (sq_nonneg ‖x‖)]
  -- Positivity of Em
  have hpos_m : ∀ x : H n,
      0 ≤ (⟪((↑(2⁻¹ : ℝ) : ℂ) • (1 - (↑(c⁻¹) : ℂ) • S)) x, x⟫_ℂ).re := by
    intro x
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply,
               inner_smul_left, inner_sub_left, Complex.conj_ofReal,
               Complex.re_ofReal_mul, Complex.sub_re]
    apply mul_nonneg (by positivity : (0 : ℝ) ≤ 2⁻¹)
    have hre : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [hre]
    nlinarith [mul_le_mul_of_nonneg_left ((abs_le.mp (hq x)).2) hcinv.le,
               h_zero x, mul_nonneg hcinv.le (sq_nonneg ‖x‖)]
  -- Assemble
  refine ⟨(↑(2⁻¹ : ℝ) : ℂ) • (1 + (↑(c⁻¹) : ℂ) • S),
          (↑(2⁻¹ : ℝ) : ℂ) • (1 - (↑(c⁻¹) : ℂ) • S), c, ?_, ?_, hc, ?_⟩
  · -- IsEffect Ep
    constructor
    · exact ⟨hSp, hpos_p⟩
    · rw [h1p]; exact ⟨hSm, hpos_m⟩
  · -- IsEffect Em
    constructor
    · exact ⟨hSm, hpos_m⟩
    · rw [h1m]; exact ⟨hSp, hpos_p⟩
  · -- Decomposition: S = c • Ep - c • Em
    rw [← smul_sub, ← smul_sub]
    have hsub : (1 + (↑(c⁻¹) : ℂ) • S : H n →ₗ[ℂ] H n) - (1 - (↑(c⁻¹) : ℂ) • S) =
                (2 : ℂ) • ((↑(c⁻¹) : ℂ) • S) := by
      ext x; simp [LinearMap.add_apply, LinearMap.smul_apply, two_smul]
    rw [hsub]; simp only [smul_smul]
    have hscal : (↑c : ℂ) * ((↑(2⁻¹ : ℝ) : ℂ) * ((2 : ℂ) * (↑(c⁻¹) : ℂ))) = 1 := by
      have h2 : (↑(2⁻¹ : ℝ) : ℂ) * 2 = 1 := by norm_num
      rw [← mul_assoc (↑(2⁻¹ : ℝ) : ℂ) 2 _, h2, one_mul,
          ← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hc), Complex.ofReal_one]
    rw [hscal, one_smul]

-- ── (B7a) Bonne définition de l'extension ────────────────────────
-- Si deux décompositions c₁(Ep₁ − Em₁) = c₂(Ep₂ − Em₂) du même
-- opérateur auto-adjoint sont données, les valeurs
-- c₁ f(Ep₁) − c₁ f(Em₁) et c₂ f(Ep₂) − c₂ f(Em₂) coïncident.
-- Preuve : réécrire c₁ Ep₁ + c₂ Em₂ = c₂ Ep₂ + c₁ Em₁, diviser par
-- C = c₁ + c₂ pour obtenir des effets dans [0,1], appliquer B5
-- (map_realSmul) + additivité, puis multiplier par C.

theorem EffectMeasure.extendSA_well_defined (F : EffectMeasure n)
    {Ep₁ Em₁ Ep₂ Em₂ : H n →ₗ[ℂ] H n} {c₁ c₂ : ℝ}
    (hEp₁ : IsEffect Ep₁) (hEm₁ : IsEffect Em₁) (hc₁ : 0 < c₁)
    (hEp₂ : IsEffect Ep₂) (hEm₂ : IsEffect Em₂) (hc₂ : 0 < c₂)
    (heq : (↑c₁ : ℂ) • Ep₁ - (↑c₁ : ℂ) • Em₁ =
           (↑c₂ : ℂ) • Ep₂ - (↑c₂ : ℂ) • Em₂) :
    c₁ * F.f Ep₁ - c₁ * F.f Em₁ = c₂ * F.f Ep₂ - c₂ * F.f Em₂ := by
  -- Normalize by C = c₁ + c₂
  set C := c₁ + c₂
  have hC : 0 < C := add_pos hc₁ hc₂
  have hC_ne := ne_of_gt hC
  set r₁ := c₁ / C with hr₁_def
  set r₂ := c₂ / C with hr₂_def
  have hr₁ : 0 ≤ r₁ := div_nonneg hc₁.le hC.le
  have hr₁' : r₁ ≤ 1 := (div_le_one hC).mpr (by linarith)
  have hr₂ : 0 ≤ r₂ := div_nonneg hc₂.le hC.le
  have hr₂' : r₂ ≤ 1 := (div_le_one hC).mpr (by linarith)
  have hrs : r₁ + r₂ = 1 := by
    simp only [hr₁_def, hr₂_def]
    rw [← add_div]
    exact div_self hC_ne
  -- Rearrange: c₁ Ep₁ + c₂ Em₂ = c₂ Ep₂ + c₁ Em₁
  have hrearr : (↑c₁ : ℂ) • Ep₁ + (↑c₂ : ℂ) • Em₂ =
                (↑c₂ : ℂ) • Ep₂ + (↑c₁ : ℂ) • Em₁ :=
    calc (↑c₁ : ℂ) • Ep₁ + (↑c₂ : ℂ) • Em₂
        = ((↑c₁ : ℂ) • Ep₁ - (↑c₁ : ℂ) • Em₁) +
          ((↑c₁ : ℂ) • Em₁ + (↑c₂ : ℂ) • Em₂) := by abel
      _ = ((↑c₂ : ℂ) • Ep₂ - (↑c₂ : ℂ) • Em₂) +
          ((↑c₁ : ℂ) • Em₁ + (↑c₂ : ℂ) • Em₂) := by rw [heq]
      _ = (↑c₂ : ℂ) • Ep₂ + (↑c₁ : ℂ) • Em₁ := by abel
  -- Normalize: divide by C
  have hnorm : (↑r₁ : ℂ) • Ep₁ + (↑r₂ : ℂ) • Em₂ =
               (↑r₂ : ℂ) • Ep₂ + (↑r₁ : ℂ) • Em₁ := by
    have h := congr_arg ((↑(C⁻¹ : ℝ) : ℂ) • ·) hrearr
    simp only [smul_add, smul_smul, ← Complex.ofReal_mul] at h
    rwa [show (C⁻¹ : ℝ) * c₁ = r₁ from by rw [inv_mul_eq_div],
         show (C⁻¹ : ℝ) * c₂ = r₂ from by rw [inv_mul_eq_div]] at h
  -- Individual scaled effects (B1)
  have he₁ := isEffect_complexSmul hEp₁ hr₁ hr₁'
  have he₂ := isEffect_complexSmul hEm₂ hr₂ hr₂'
  have he₃ := isEffect_complexSmul hEp₂ hr₂ hr₂'
  have he₄ := isEffect_complexSmul hEm₁ hr₁ hr₁'
  -- Convex combination of effects is an effect
  have heff_sum : IsEffect ((↑r₁ : ℂ) • Ep₁ + (↑r₂ : ℂ) • Em₂) := by
    refine ⟨⟨he₁.1.1.add he₂.1.1, fun x => ?_⟩, ?_⟩
    · rw [LinearMap.add_apply, inner_add_left, Complex.add_re]
      exact add_nonneg (he₁.1.2 x) (he₂.1.2 x)
    · have h1 : (1 : H n →ₗ[ℂ] H n) - ((↑r₁ : ℂ) • Ep₁ + (↑r₂ : ℂ) • Em₂) =
                (↑r₁ : ℂ) • (1 - Ep₁) + (↑r₂ : ℂ) • (1 - Em₂) := by
        have hsum : (↑r₁ : ℂ) • (1 : H n →ₗ[ℂ] H n) + (↑r₂ : ℂ) • 1 = 1 := by
          rw [← add_smul, ← Complex.ofReal_add, hrs, Complex.ofReal_one, one_smul]
        conv_lhs => rw [← hsum]
        simp only [smul_sub]; abel
      rw [h1]
      refine ⟨(hEp₁.2.1.smul (Complex.conj_ofReal r₁)).add
              (hEm₂.2.1.smul (Complex.conj_ofReal r₂)), fun x => ?_⟩
      simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_smul_left,
                  Complex.conj_ofReal, Complex.add_re, Complex.re_ofReal_mul]
      exact add_nonneg (mul_nonneg hr₁ (hEp₁.2.2 x)) (mul_nonneg hr₂ (hEm₂.2.2 x))
  have heff_sum' : IsEffect ((↑r₂ : ℂ) • Ep₂ + (↑r₁ : ℂ) • Em₁) := by rwa [← hnorm]
  -- Apply additivity + map_realSmul (B5)
  have key : r₁ * F.f Ep₁ + r₂ * F.f Em₂ = r₂ * F.f Ep₂ + r₁ * F.f Em₁ := by
    have h := congr_arg F.f hnorm
    rw [F.additive _ _ he₁ he₂ heff_sum, F.additive _ _ he₃ he₄ heff_sum'] at h
    rw [F.map_realSmul hEp₁ hr₁ hr₁', F.map_realSmul hEm₂ hr₂ hr₂',
        F.map_realSmul hEp₂ hr₂ hr₂', F.map_realSmul hEm₁ hr₁ hr₁'] at h
    exact h
  -- Multiply by C and conclude
  have hCr₁ : C * r₁ = c₁ := by
    rw [hr₁_def, ← mul_div_assoc, mul_div_cancel_left₀ c₁ hC_ne]
  have hCr₂ : C * r₂ = c₂ := by
    rw [hr₂_def, ← mul_div_assoc, mul_div_cancel_left₀ c₂ hC_ne]
  have h_scaled := congr_arg (C * ·) (show r₁ * F.f Ep₁ - r₁ * F.f Em₁ =
                                            r₂ * F.f Ep₂ - r₂ * F.f Em₂ from by linarith [key])
  simp only [mul_sub, ← mul_assoc, hCr₁, hCr₂] at h_scaled
  exact h_scaled

-- ── (B7) Extension ℝ-linéaire aux auto-adjoints ─────────────────
-- On définit g(S) := c · f(Ep) − c · f(Em) pour une décomposition
-- quelconque S = c(Ep − Em) (existence par B6, bonne définition par B7a).
-- Linéarité ℝ : décomposer S+T et r·S, appliquer B7a.

-- Combinaison convexe d'effets est un effet.
private theorem isEffect_convex_comb {A B : H n →ₗ[ℂ] H n} {r₁ r₂ : ℝ}
    (hA : IsEffect A) (hB : IsEffect B)
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hrs : r₁ + r₂ = 1) :
    IsEffect ((↑r₁ : ℂ) • A + (↑r₂ : ℂ) • B) := by
  have hr₁' : r₁ ≤ 1 := by linarith
  have hr₂' : r₂ ≤ 1 := by linarith
  have he₁ := isEffect_complexSmul hA hr₁ hr₁'
  have he₂ := isEffect_complexSmul hB hr₂ hr₂'
  refine ⟨⟨he₁.1.1.add he₂.1.1, fun x => ?_⟩, ?_⟩
  · rw [LinearMap.add_apply, inner_add_left, Complex.add_re]
    exact add_nonneg (he₁.1.2 x) (he₂.1.2 x)
  · have h1 : (1 : H n →ₗ[ℂ] H n) - ((↑r₁ : ℂ) • A + (↑r₂ : ℂ) • B) =
              (↑r₁ : ℂ) • (1 - A) + (↑r₂ : ℂ) • (1 - B) := by
      have hsum : (↑r₁ : ℂ) • (1 : H n →ₗ[ℂ] H n) + (↑r₂ : ℂ) • 1 = 1 := by
        rw [← add_smul, ← Complex.ofReal_add, hrs, Complex.ofReal_one, one_smul]
      conv_lhs => rw [← hsum]
      simp only [smul_sub]; abel
    rw [h1]
    refine ⟨(hA.2.1.smul (Complex.conj_ofReal r₁)).add
            (hB.2.1.smul (Complex.conj_ofReal r₂)), fun x => ?_⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_smul_left,
                Complex.conj_ofReal, Complex.add_re, Complex.re_ofReal_mul]
    exact add_nonneg (mul_nonneg hr₁ (hA.2.2 x)) (mul_nonneg hr₂ (hB.2.2 x))

open Classical in
noncomputable def EffectMeasure.extendSA (F : EffectMeasure n) (_ : 1 ≤ n) :
    (H n →ₗ[ℂ] H n) → ℝ := fun S =>
  if hS : S.IsSymmetric then
    (selfAdjoint_effect_decomp S hS).choose_spec.choose_spec.choose *
      F.f (selfAdjoint_effect_decomp S hS).choose -
    (selfAdjoint_effect_decomp S hS).choose_spec.choose_spec.choose *
      F.f (selfAdjoint_effect_decomp S hS).choose_spec.choose
  else 0

-- Indépendance du choix de décomposition : toute décomposition valide
-- S = c(Ep - Em) donne la même valeur extendSA(S).
private theorem EffectMeasure.extendSA_eq (F : EffectMeasure n) (hn : 1 ≤ n)
    {S : H n →ₗ[ℂ] H n} (hS : S.IsSymmetric)
    {Ep Em : H n →ₗ[ℂ] H n} {c : ℝ}
    (hEp : IsEffect Ep) (hEm : IsEffect Em) (hc : 0 < c)
    (heq : S = (↑c : ℂ) • Ep - (↑c : ℂ) • Em) :
    F.extendSA hn S = c * F.f Ep - c * F.f Em := by
  classical
  unfold EffectMeasure.extendSA
  rw [dif_pos hS]
  set d := selfAdjoint_effect_decomp S hS
  obtain ⟨hEp₀, hEm₀, hc₀, heq₀⟩ := d.choose_spec.choose_spec.choose_spec
  exact F.extendSA_well_defined hEp₀ hEm₀ hc₀ hEp hEm hc (heq₀.symm.trans heq)

-- L'extension est ℝ-additive sur les auto-adjoints.
theorem EffectMeasure.extendSA_add (F : EffectMeasure n) (hn : 1 ≤ n)
    {S T : H n →ₗ[ℂ] H n} (hS : S.IsSymmetric) (hT : T.IsSymmetric) :
    F.extendSA hn (S + T) = F.extendSA hn S + F.extendSA hn T := by
  obtain ⟨EpS, EmS, cS, hEpS, hEmS, hcS, heqS⟩ := selfAdjoint_effect_decomp S hS
  obtain ⟨EpT, EmT, cT, hEpT, hEmT, hcT, heqT⟩ := selfAdjoint_effect_decomp T hT
  rw [F.extendSA_eq hn hS hEpS hEmS hcS heqS,
      F.extendSA_eq hn hT hEpT hEmT hcT heqT]
  -- Construct decomposition of S + T via convex combination
  set C := cS + cT
  have hC : 0 < C := add_pos hcS hcT
  have hC_ne := ne_of_gt hC
  set rS := cS / C with hrS_def
  set rT := cT / C with hrT_def
  have hrS : 0 ≤ rS := div_nonneg hcS.le hC.le
  have hrT : 0 ≤ rT := div_nonneg hcT.le hC.le
  have hrs : rS + rT = 1 := by
    simp only [hrS_def, hrT_def]; rw [← add_div]; exact div_self hC_ne
  have hrS' : rS ≤ 1 := by linarith
  have hrT' : rT ≤ 1 := by linarith
  set Ep' := (↑rS : ℂ) • EpS + (↑rT : ℂ) • EpT
  set Em' := (↑rS : ℂ) • EmS + (↑rT : ℂ) • EmT
  have hEp' : IsEffect Ep' := isEffect_convex_comb hEpS hEpT hrS hrT hrs
  have hEm' : IsEffect Em' := isEffect_convex_comb hEmS hEmT hrS hrT hrs
  have heqST : S + T = (↑C : ℂ) • Ep' - (↑C : ℂ) • Em' := by
    simp only [Ep', Em', smul_add, smul_smul, ← Complex.ofReal_mul]
    rw [show (C : ℝ) * rS = cS from by rw [hrS_def, ← mul_div_assoc, mul_div_cancel_left₀ cS hC_ne],
        show (C : ℝ) * rT = cT from by rw [hrT_def, ← mul_div_assoc, mul_div_cancel_left₀ cT hC_ne]]
    rw [heqS, heqT]; abel
  rw [F.extendSA_eq hn (hS.add hT) hEp' hEm' hC heqST]
  -- Expand f(Ep') and f(Em') using additivity + B5
  have heffS := isEffect_complexSmul hEpS hrS hrS'
  have heffT := isEffect_complexSmul hEpT hrT hrT'
  have heffSm := isEffect_complexSmul hEmS hrS hrS'
  have heffTm := isEffect_complexSmul hEmT hrT hrT'
  rw [F.additive _ _ heffS heffT hEp', F.map_realSmul hEpS hrS hrS',
      F.map_realSmul hEpT hrT hrT',
      F.additive _ _ heffSm heffTm hEm', F.map_realSmul hEmS hrS hrS',
      F.map_realSmul hEmT hrT hrT']
  -- Arithmetic: C * (rS * f EpS + rT * f EpT) - C * (rS * f EmS + rT * f EmT)
  --           = (cS * f EpS - cS * f EmS) + (cT * f EpT - cT * f EmT)
  have hCrS : C * rS = cS := by
    rw [hrS_def, ← mul_div_assoc, mul_div_cancel_left₀ cS hC_ne]
  have hCrT : C * rT = cT := by
    rw [hrT_def, ← mul_div_assoc, mul_div_cancel_left₀ cT hC_ne]
  simp only [mul_add, ← mul_assoc, hCrS, hCrT]; ring

-- L'extension est ℝ-homogène sur les auto-adjoints.
theorem EffectMeasure.extendSA_realSmul (F : EffectMeasure n) (hn : 1 ≤ n)
    {S : H n →ₗ[ℂ] H n} (hS : S.IsSymmetric) (r : ℝ) :
    F.extendSA hn ((↑r : ℂ) • S) = r * F.extendSA hn S := by
  obtain ⟨Ep, Em, c, hEp, hEm, hc, heq⟩ := selfAdjoint_effect_decomp S hS
  rw [F.extendSA_eq hn hS hEp hEm hc heq]
  by_cases hr : 0 ≤ r
  · -- r ≥ 0 : r·S = (r·c)·Ep - (r·c)·Em
    by_cases hr0 : r = 0
    · subst hr0; simp only [Complex.ofReal_zero, zero_smul]
      have h0 : IsEffect (0 : H n →ₗ[ℂ] H n) := ⟨⟨fun _ _ => by simp, fun _ => by simp⟩,
        by simp only [sub_zero]; exact ⟨.one, fun x => by
          simp only [Module.End.one_apply]; exact @inner_self_nonneg ℂ _ _ _ _ x⟩⟩
      rw [F.extendSA_eq hn (fun _ _ => by simp) h0 h0 one_pos (by simp)]
      simp [F.map_zero]
    · have hrc : 0 < r * c := mul_pos (lt_of_le_of_ne hr (Ne.symm hr0)) hc
      have h_rc : (↑r : ℂ) * (↑c : ℂ) = (↑(r * c) : ℂ) := by push_cast; ring
      have heq' : (↑r : ℂ) • S = (↑(r * c) : ℂ) • Ep - (↑(r * c) : ℂ) • Em := by
        rw [heq, smul_sub, smul_smul, smul_smul, h_rc]
      rw [F.extendSA_eq hn (hS.smul (Complex.conj_ofReal r)) hEp hEm hrc heq']; ring
  · -- r < 0 : r·S = (-r·c)·Em - (-r·c)·Ep
    push Not at hr
    have hnrc : 0 < -r * c := mul_pos (neg_pos.mpr hr) hc
    have h_rc : (↑r : ℂ) * (↑c : ℂ) = -(↑(-r * c) : ℂ) := by push_cast; ring
    have heq' : (↑r : ℂ) • S = (↑(-r * c) : ℂ) • Em - (↑(-r * c) : ℂ) • Ep := by
      rw [heq, smul_sub, smul_smul, smul_smul, h_rc]
      simp only [neg_smul, neg_sub_neg]
    rw [F.extendSA_eq hn (hS.smul (Complex.conj_ofReal r)) hEm hEp hnrc heq']; ring

-- L'extension coïncide avec f sur les effets.
theorem EffectMeasure.extendSA_extends (F : EffectMeasure n) (hn : 1 ≤ n)
    {T : H n →ₗ[ℂ] H n} (hT : IsEffect T) :
    F.extendSA hn T = F.f T := by
  have h0 : IsEffect (0 : H n →ₗ[ℂ] H n) := by
    refine ⟨⟨fun _ _ => by simp, fun x => by simp⟩, ?_⟩
    simp only [sub_zero]
    exact ⟨LinearMap.IsSymmetric.one, fun x => by
      simp only [Module.End.one_apply]; exact @inner_self_nonneg ℂ _ _ _ _ x⟩
  have heq : T = (↑(1 : ℝ) : ℂ) • T - (↑(1 : ℝ) : ℂ) • (0 : H n →ₗ[ℂ] H n) := by simp
  rw [F.extendSA_eq hn hT.1.1 hT h0 one_pos heq]
  simp [F.map_zero]

-- ── (B8) Représentation de Riesz en dimension finie ─────────────
-- Sur l'espace réel des auto-adjoints de H n, le produit scalaire
-- de Hilbert–Schmidt ⟨A, B⟩ := Re tr(A ∘ B) est un produit
-- scalaire réel (défini positif car A auto-adjoint ⇒ tr(A²) ≥ 0,
-- = 0 ssi A = 0). Par le théorème de Riesz–Fréchet
-- (InnerProductSpace.toDual de Mathlib, pour espaces complets —
-- automatique en dimension finie), toute fonctionnelle ℝ-linéaire
-- g est de la forme S ↦ ⟨ρ, S⟩ = Re tr(ρ ∘ S) pour un unique
-- ρ auto-adjoint.
--
-- Alternative : construction directe via la base orthonormée.
-- Fixer (eᵢ) ONB de H n. Les opérateurs rang-1
--   Eᵢⱼ = (rankOne eⱼ eᵢ + rankOne eᵢ eⱼ) / 2  (partie réelle)
--   Fᵢⱼ = i·(rankOne eⱼ eᵢ − rankOne eᵢ eⱼ) / 2 (partie imaginaire)
-- forment une base des auto-adjoints. On pose
--   ⟪ρ eᵢ, eⱼ⟫ := g(rankOne eⱼ eᵢ)
-- (fonctionnelle évaluée sur le rang-1) et on vérifie
-- g(S) = Re tr(ρ S) par linéarité sur cette base.
-- NB : Mathlib fournit rankOne, trace_rankOne, isPositive_rankOne_self.

theorem riesz_selfAdjoint (hn : 1 ≤ n)
    (g : (H n →ₗ[ℂ] H n) → ℝ)
    (hg_add : ∀ S T : H n →ₗ[ℂ] H n, S.IsSymmetric → T.IsSymmetric →
      g (S + T) = g S + g T)
    (hg_smul : ∀ (r : ℝ) (S : H n →ₗ[ℂ] H n), S.IsSymmetric →
      g ((↑r : ℂ) • S) = r * g S) :
    ∃! ρ : H n →ₗ[ℂ] H n, ρ.IsSymmetric ∧
      ∀ (S : H n →ₗ[ℂ] H n), S.IsSymmetric →
        g S = (LinearMap.trace ℂ (H n) (ρ ∘ₗ S)).re := by
  sorry

-- ── (B9) Assemblage : positivité et trace 1 ─────────────────────
-- L'opérateur ρ fourni par B8, appliqué à g = F.extendSA, vérifie :
--
-- • Positivité : pour tout x : H n, poser T = rankOne x x / ‖x‖².
--   C'est un effet (projection rang 1). Alors
--     Re ⟪ρ x, x⟫ = ‖x‖² · Re tr(ρ ∘ T)      (par trace_rankOne)
--                   = ‖x‖² · g(T) = ‖x‖² · f(T) ≥ 0.
--   Mathlib : isPositive_rankOne_self, trace_rankOne.
--
-- • Trace 1 : Re tr(ρ) = Re tr(ρ ∘ 1) = g(1) = f(1) = 1.
--   Comme ρ est auto-adjoint, tr(ρ) ∈ ℝ, donc tr(ρ) = 1.
--
-- • Unicité : si ρ₁, ρ₂ conviennent, alors pour tout effet T,
--   Re tr((ρ₁ − ρ₂) ∘ T) = 0. En testant sur les rankOne eᵢ eⱼ
--   (base des auto-adjoints), on obtient ρ₁ = ρ₂.

-- ═══════════════════════════════════════════════════════════════════
-- ÉNONCÉS PRINCIPAUX (figés — ne pas modifier)
-- ═══════════════════════════════════════════════════════════════════

/-- **Théorème de Busch (2003), dimension finie.** Toute mesure d'effets est
représentée par un unique opérateur densité. Vaut dès `n = 1` (et surtout `n = 2`,
où Gleason échoue). -/
theorem busch {n : ℕ} (hn : 1 ≤ n) (F : EffectMeasure n) :
    ∃! ρ : H n →ₗ[ℂ] H n, IsDensityOperator ρ ∧
      ∀ T, IsEffect T → F.f T = (LinearMap.trace ℂ (H n) (ρ ∘ₗ T)).re := by
  -- Assemblage : B1–B5 → map_realSmul ; B6–B7 → extendSA linéaire ;
  -- B8 → ρ auto-adjoint avec g = Re tr(ρ ·) ; B9 → ρ densité.
  sorry

/-- Corollaire : règle de Born sur les projections, dès la dimension 1, sous
l'hypothèse (plus forte que celle de Gleason) d'additivité sur les effets. -/
theorem busch_born_rule {n : ℕ} (hn : 1 ≤ n) (F : EffectMeasure n) :
    ∃ ρ : H n →ₗ[ℂ] H n, IsDensityOperator ρ ∧
      ∀ A : Submodule ℂ (H n), F.toProjMeasure.μ A = bornValue ρ A := by
  -- De busch : ρ représente f sur les effets ; projL A est un effet
  -- (isEffect_projL) ; toProjMeasure.μ A = f(projL A) par définition ;
  -- bornValue ρ A = Re tr(ρ ∘ projL A) par définition.
  sorry

end
end Gleason
