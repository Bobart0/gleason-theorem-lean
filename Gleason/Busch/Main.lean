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

theorem EffectMeasure.map_rat_smul (F : EffectMeasure n)
    {T : H n →ₗ[ℂ] H n} (hT : IsEffect T)
    (q : ℚ) (hq₀ : 0 ≤ q) (hq₁ : (q : ℝ) ≤ 1) :
    F.f ((↑(q : ℝ) : ℂ) • T) = (q : ℝ) * F.f T := by
  sorry

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
       ⟨by simp [LinearMap.sub_apply, Module.End.one_apply], fun x => by simp⟩⟩
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
  sorry

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
  sorry

-- ── (B7) Extension ℝ-linéaire aux auto-adjoints ─────────────────
-- On définit g(S) := c · f(Ep) − c · f(Em) pour une décomposition
-- quelconque S = c(Ep − Em) (existence par B6, bonne définition par B7a).
-- Linéarité ℝ : décomposer S+T et r·S, appliquer B7a.

noncomputable def EffectMeasure.extendSA (F : EffectMeasure n) (hn : 1 ≤ n) :
    (H n →ₗ[ℂ] H n) → ℝ := by
  sorry

-- L'extension est ℝ-additive sur les auto-adjoints.
theorem EffectMeasure.extendSA_add (F : EffectMeasure n) (hn : 1 ≤ n)
    {S T : H n →ₗ[ℂ] H n} (hS : S.IsSymmetric) (hT : T.IsSymmetric) :
    F.extendSA hn (S + T) = F.extendSA hn S + F.extendSA hn T := by
  sorry

-- L'extension est ℝ-homogène sur les auto-adjoints.
theorem EffectMeasure.extendSA_realSmul (F : EffectMeasure n) (hn : 1 ≤ n)
    {S : H n →ₗ[ℂ] H n} (hS : S.IsSymmetric) (r : ℝ) :
    F.extendSA hn ((↑r : ℂ) • S) = r * F.extendSA hn S := by
  sorry

-- L'extension coïncide avec f sur les effets.
theorem EffectMeasure.extendSA_extends (F : EffectMeasure n) (hn : 1 ≤ n)
    {T : H n →ₗ[ℂ] H n} (hT : IsEffect T) :
    F.extendSA hn T = F.f T := by
  sorry

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
