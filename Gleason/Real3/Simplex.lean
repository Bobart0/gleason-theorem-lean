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

/- ═══════════════════════════════════════════════════════════════════
   Recherche Mathlib (avant de prouver quoi que ce soit) :
   AUCUN théorème générique « additive + bornée ⇒ linéaire » (équation de
   Cauchy) n'existe dans Mathlib : ni version measurable/continue automatique,
   ni théorème de Steinhaus. Le seul élément utile,
   `AddMonoidHom.toRealLinearMap` (continue ⇒ ℝ-linéaire sur un morphisme
   GLOBAL), ne s'applique pas ici car `g` n'est défini que sur `[0,1]` avec
   une additivité restreinte (pas un morphisme sur `ℝ` tout entier) : l'argument
   classique « f(nx) mod 1 » suppose un domaine global. Il faut donc l'argument
   dyadique à la main (étapes ci-dessous, toutes prouvées : 0 `sorry`).
   ═══════════════════════════════════════════════════════════════════ -/

/-- **Étape 1.** `g x := h x - h 0 - x * (h 1 - h 0)` s'annule en `0` et en `1`,
reste bornée sur `[0,1]` (par `4C`), et hérite de l'additivité restreinte de `h`. -/
private theorem simplex_g_props (h : ℝ → ℝ) (C : ℝ)
    (hb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |h x| ≤ C)
    (hadd : ∀ x y u v : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
      u ∈ Set.Icc (0 : ℝ) 1 → v ∈ Set.Icc (0 : ℝ) 1 →
      x + y = u + v → h x + h y = h u + h v) :
    h 0 - h 0 - (0 : ℝ) * (h 1 - h 0) = 0 ∧
    h 1 - h 0 - (1 : ℝ) * (h 1 - h 0) = 0 ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, |h x - h 0 - x * (h 1 - h 0)| ≤ 4 * C) ∧
    (∀ x y u v : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
      u ∈ Set.Icc (0 : ℝ) 1 → v ∈ Set.Icc (0 : ℝ) 1 → x + y = u + v →
      (h x - h 0 - x * (h 1 - h 0)) + (h y - h 0 - y * (h 1 - h 0)) =
      (h u - h 0 - u * (h 1 - h 0)) + (h v - h 0 - v * (h 1 - h 0))) := by
  refine ⟨by ring, by ring, ?_, ?_⟩
  · intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hbx := hb x ⟨hx0, hx1⟩
    have hb0 := hb 0 ⟨le_refl 0, zero_le_one⟩
    have hb1 := hb 1 ⟨zero_le_one, le_refl 1⟩
    have hxabs : |x| = x := abs_of_nonneg hx0
    have htri1 : |h 1 - h 0| ≤ |h 1| + |h 0| := by
      have := abs_add_le (h 1) (-(h 0))
      simpa [sub_eq_add_neg] using this
    have h2C : |h 1 - h 0| ≤ 2 * C := by linarith
    have hxy : |x * (h 1 - h 0)| ≤ 2 * C := by
      rw [abs_mul, hxabs]
      calc x * |h 1 - h 0| ≤ 1 * |h 1 - h 0| :=
            mul_le_mul_of_nonneg_right hx1 (abs_nonneg _)
        _ = |h 1 - h 0| := one_mul _
        _ ≤ 2 * C := h2C
    have htri2 : |h x - h 0 - x * (h 1 - h 0)| ≤ |h x - h 0| + |x * (h 1 - h 0)| := by
      have := abs_add_le (h x - h 0) (-(x * (h 1 - h 0)))
      simpa [sub_eq_add_neg] using this
    have htri3 : |h x - h 0| ≤ |h x| + |h 0| := by
      have := abs_add_le (h x) (-(h 0))
      simpa [sub_eq_add_neg] using this
    linarith
  · intro x y u v hx hy hu hv hsum
    have heq := hadd x y u v hx hy hu hv hsum
    have key : x * (h 1 - h 0) + y * (h 1 - h 0) = u * (h 1 - h 0) + v * (h 1 - h 0) := by
      rw [← add_mul, ← add_mul, hsum]
    linarith [heq, key]

/-- **Étape 2.** Spécialisation de l'additivité restreinte à `y = 0`, `v = x - u` :
pour `0 ≤ u ≤ x ≤ 1`, `g x = g u + g (x - u)`. -/
private theorem simplex_split (g : ℝ → ℝ) (hg0 : g 0 = 0)
    (hgadd : ∀ x y u v : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
      u ∈ Set.Icc (0 : ℝ) 1 → v ∈ Set.Icc (0 : ℝ) 1 → x + y = u + v →
      g x + g y = g u + g v) :
    ∀ x u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 → x ∈ Set.Icc (0 : ℝ) 1 → u ≤ x →
      g x = g u + g (x - u) := by
  intro x u hu hx hux
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hx0, hx1⟩ := hx
  have hv : x - u ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have heq := hgadd x 0 u (x - u) ⟨hx0, hx1⟩ h0mem ⟨hu0, hu1⟩ hv (by ring)
  rw [hg0] at heq
  linarith

/-- **Étape 3a (halving).** Récurrence sur `n` via `simplex_split` (avec
`u = x / 2`) : `g (x / 2^n) = g x / 2^n` pour `x ∈ [0,1]`. -/
private theorem simplex_halve (g : ℝ → ℝ)
    (hsplit : ∀ x u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 → x ∈ Set.Icc (0 : ℝ) 1 → u ≤ x →
      g x = g u + g (x - u)) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ n : ℕ, g (x / 2 ^ n) = g x / 2 ^ n := by
  have hhalf : ∀ x ∈ Set.Icc (0 : ℝ) 1, g (x / 2) = g x / 2 := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hu : x / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have heq := hsplit x (x / 2) hu ⟨hx0, hx1⟩ (by linarith)
    have hsub : x - x / 2 = x / 2 := by ring
    rw [hsub] at heq
    linarith
  have main : ∀ n : ℕ, ∀ x ∈ Set.Icc (0 : ℝ) 1, g (x / 2 ^ n) = g x / 2 ^ n := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      obtain ⟨hx0, hx1⟩ := hx
      have hx2 : x / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      have step1 : x / 2 ^ (n + 1) = (x / 2) / 2 ^ n := by rw [pow_succ]; ring
      rw [step1, ih (x / 2) hx2, hhalf x ⟨hx0, hx1⟩, pow_succ]
      ring
  intro x hx n
  exact main n x hx

/-- **Étape 3b (multiples entiers, base réelle arbitraire).** Récurrence sur `k`
via `simplex_split` (avec `u = k * t`, `x = (k+1) * t`) : `g (k * t) = k * g t`
pour tout réel `t ≥ 0` tel que `k * t ≤ 1`. Généralise le cas dyadique
`t = 1/2^n` : nécessaire pour `simplex_vanish`, où l'amplification
`g (2^n * r) = 2^n * g r` porte sur un réel `r` quelconque (le reste de
`Int.fract`), pas seulement sur `t = 1/2^n`. Le cas de base `k = 0` utilise
`g 0 = 0`, lui-même dérivable de `hsplit` en `x = u = 0`. -/
private theorem simplex_nat_mul (g : ℝ → ℝ)
    (hsplit : ∀ x u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 → x ∈ Set.Icc (0 : ℝ) 1 → u ≤ x →
      g x = g u + g (x - u)) :
    ∀ (k : ℕ) (t : ℝ), 0 ≤ t → (k : ℝ) * t ≤ 1 → g ((k : ℝ) * t) = (k : ℝ) * g t := by
  have hg0 : g 0 = 0 := by
    have := hsplit 0 0 ⟨le_refl 0, zero_le_one⟩ ⟨le_refl 0, zero_le_one⟩ (le_refl 0)
    simpa using this
  intro k
  induction k with
  | zero => intro t _ _; simp [hg0]
  | succ k ih =>
    intro t ht0 ht1
    push_cast at ht1 ⊢
    have hkt1 : (k : ℝ) * t ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_right (by linarith : (k : ℝ) ≤ (k : ℝ) + 1) ht0) ht1
    have hmem_kt : (k : ℝ) * t ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg (Nat.cast_nonneg k) ht0, hkt1⟩
    have hmem_succ : ((k : ℝ) + 1) * t ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg (by positivity) ht0, ht1⟩
    have hle : (k : ℝ) * t ≤ ((k : ℝ) + 1) * t :=
      mul_le_mul_of_nonneg_right (by linarith) ht0
    have heq := hsplit (((k : ℝ) + 1) * t) ((k : ℝ) * t) hmem_kt hmem_succ hle
    have hdiff : ((k : ℝ) + 1) * t - (k : ℝ) * t = t := by ring
    rw [hdiff, ih t ht0 hkt1] at heq
    rw [heq]
    ring

/-- **Étape 3 (assemblage, corollaire dyadique de `simplex_nat_mul`).** Combine
`simplex_halve` en `x = 1` (donnant `g (1/2^n) = g 1 / 2^n = 0`) avec
`simplex_nat_mul` en `t = 1/2^n` : `g` s'annule sur tous les dyadiques de
`[0,1]`. Purement algébrique, AUCUNE bornitude requise (contrairement à
l'étape 4). -/
private theorem simplex_dyadic_vanish (g : ℝ → ℝ) (hg1 : g 1 = 0)
    (hhalve : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ n : ℕ, g (x / 2 ^ n) = g x / 2 ^ n)
    (hmul : ∀ (k : ℕ) (t : ℝ), 0 ≤ t → (k : ℝ) * t ≤ 1 → g ((k : ℝ) * t) = (k : ℝ) * g t) :
    ∀ n k : ℕ, k ≤ 2 ^ n → g ((k : ℝ) / 2 ^ n) = 0 := by
  intro n k hk
  have hmem1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  have ht0 : (0 : ℝ) ≤ 1 / 2 ^ n := by positivity
  have hgt : g (1 / 2 ^ n) = 0 := by
    have := hhalve 1 hmem1 n
    rw [hg1] at this
    simpa using this
  have hkcast : (k : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hk
  have hkt1 : (k : ℝ) * (1 / 2 ^ n) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]
    exact hkcast
  have heq := hmul k (1 / 2 ^ n) ht0 hkt1
  rw [hgt, mul_zero] at heq
  have hcast : (k : ℝ) / 2 ^ n = (k : ℝ) * (1 / 2 ^ n) := by rw [mul_one_div]
  rw [hcast]
  exact heq

/-- **Étape 4 (le cœur analytique).** Pour `x ∈ [0,1]` et tout `n`, en posant
`k = ⌊x·2^n⌋` et `r = x - k/2^n ∈ [0, 1/2^n)`, `simplex_split` donne
`g x = g (k/2^n) + g r = g r` (dyadique nul). Puis `simplex_nat_mul` en
`k' = 2^n`, `t = r` (licite car `2^n · r < 1`) donne
`g (2^n · r) = 2^n · g r`, donc `|g r| ≤ C / 2^n` (bornitude de `g (2^n r)`
via `hb`), d'où `|g x| ≤ C / 2^n` pour tout `n` : `g x = 0` par la propriété
d'Archimède. C'est ici, et seulement ici, que la bornitude de `g` est
utilisée. -/
private theorem simplex_vanish (g : ℝ → ℝ) (C : ℝ)
    (hb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ C)
    (hsplit : ∀ x u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 → x ∈ Set.Icc (0 : ℝ) 1 → u ≤ x →
      g x = g u + g (x - u))
    (hmul : ∀ (k : ℕ) (t : ℝ), 0 ≤ t → (k : ℝ) * t ≤ 1 → g ((k : ℝ) * t) = (k : ℝ) * g t)
    (hdyadic : ∀ n k : ℕ, k ≤ 2 ^ n → g ((k : ℝ) / 2 ^ n) = 0) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, g x = 0 := by
  intro x hx
  obtain ⟨hx0, hx1⟩ := hx
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hb 0 ⟨le_refl 0, zero_le_one⟩)
  have hbound : ∀ n : ℕ, |g x| ≤ C / 2 ^ n := by
    intro n
    have hpow_pos : (0:ℝ) < 2 ^ n := by positivity
    set y : ℝ := (2 : ℝ) ^ n * x with hy_def
    have hy0 : 0 ≤ y := by positivity
    have hm0 : 0 ≤ ⌊y⌋ := Int.le_floor.mpr (by simpa using hy0)
    set k : ℕ := ⌊y⌋.toNat with hk_def
    have hk_cast : (k : ℤ) = ⌊y⌋ := Int.toNat_of_nonneg hm0
    have hk_cast' : (k : ℝ) = (⌊y⌋ : ℝ) := by exact_mod_cast hk_cast
    have hyle : y ≤ (2 : ℝ) ^ n := by rw [hy_def]; nlinarith
    have hkle : k ≤ 2 ^ n := by
      have h1 : ⌊y⌋ ≤ ⌊(2 : ℝ) ^ n⌋ := Int.floor_le_floor hyle
      rw [show ((2 : ℝ) ^ n) = ((2 ^ n : ℕ) : ℝ) by push_cast; ring,
          Int.floor_natCast] at h1
      have h2 : (k : ℤ) ≤ (2 ^ n : ℕ) := hk_cast ▸ h1
      exact_mod_cast h2
    have hd_le_x : (k : ℝ) / 2 ^ n ≤ x := by
      rw [hk_cast', div_le_iff₀ hpow_pos]
      have := Int.floor_le y
      rw [hy_def] at this
      linarith
    have hd_mem : (k : ℝ) / 2 ^ n ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, by linarith⟩
    have hgd : g ((k : ℝ) / 2 ^ n) = 0 := hdyadic n k hkle
    have hsplit_eq := hsplit x ((k : ℝ) / 2 ^ n) hd_mem ⟨hx0, hx1⟩ hd_le_x
    rw [hgd, zero_add] at hsplit_eq
    set r : ℝ := x - (k : ℝ) / 2 ^ n with hr_def
    have hr0 : 0 ≤ r := by rw [hr_def]; linarith
    have hr_lt : (2 : ℝ) ^ n * r < 1 := by
      have hlt := Int.lt_floor_add_one y
      rw [hy_def] at hlt
      have hexpand : (2 : ℝ) ^ n * r = (2 : ℝ) ^ n * x - (k : ℝ) := by
        rw [hr_def, hk_cast']; field_simp
      rw [hexpand]
      linarith
    have hr_le : (2 : ℝ) ^ n * r ≤ 1 := le_of_lt hr_lt
    have hmul_eq := hmul (2 ^ n) r hr0 (by push_cast; exact hr_le)
    rw [show ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n by push_cast; ring] at hmul_eq
    have hmem2r : (2 : ℝ) ^ n * r ∈ Set.Icc (0 : ℝ) 1 := ⟨by positivity, hr_le⟩
    have hb2r : |g ((2 : ℝ) ^ n * r)| ≤ C := hb _ hmem2r
    have hgr_bound : |g r| ≤ C / 2 ^ n := by
      rw [hmul_eq, abs_mul, abs_of_pos hpow_pos] at hb2r
      rw [le_div_iff₀ hpow_pos]
      linarith
    rw [hsplit_eq]
    exact hgr_bound
  by_contra hne
  have hpos : 0 < |g x| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / |g x|) (by norm_num : (1:ℝ) < 2)
  rw [div_lt_iff₀ hpos] at hn
  have hb2 := hbound n
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 ^ n)] at hb2
  linarith

/-- **Étape 5 / Lemme du simplexe (assemblage final).** `g ≡ 0` sur `[0,1]` se
retraduit en `h x = a * x + b` avec `a = h 1 - h 0`, `b = h 0`. Si `h` est bornée
sur `[0,1]` et si `h x + h y` ne dépend que de `x + y`, alors `h` est affine
sur `[0,1]`. -/
theorem bounded_additive_affine (h : ℝ → ℝ) (C : ℝ)
    (hb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |h x| ≤ C)
    (hadd : ∀ x y u v : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
      u ∈ Set.Icc (0 : ℝ) 1 → v ∈ Set.Icc (0 : ℝ) 1 →
      x + y = u + v → h x + h y = h u + h v) :
    ∃ a b : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, h x = a * x + b := by
  obtain ⟨hg0, hg1, hgb, hgadd⟩ := simplex_g_props h C hb hadd
  have hsplit := simplex_split (fun x => h x - h 0 - x * (h 1 - h 0)) hg0 hgadd
  have hhalve := simplex_halve (fun x => h x - h 0 - x * (h 1 - h 0)) hsplit
  have hmul := simplex_nat_mul (fun x => h x - h 0 - x * (h 1 - h 0)) hsplit
  have hdyadic := simplex_dyadic_vanish (fun x => h x - h 0 - x * (h 1 - h 0)) hg1 hhalve hmul
  have hvanish := simplex_vanish (fun x => h x - h 0 - x * (h 1 - h 0)) (4 * C) hgb hsplit
    hmul hdyadic
  refine ⟨h 1 - h 0, h 0, fun x hx => ?_⟩
  have hgx : h x - h 0 - x * (h 1 - h 0) = 0 := hvanish x hx
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- Warmup Theorem II (CKM 1985 §3) : monotone + additif-à-1 sur [0,1] \ C
-- (C dénombrable, C ⊆ (0,1)) ⇒ f = identité sur [0,1] \ C.
-- Recherche Mathlib (avant de prouver quoi que ce soit) : aucun théorème
-- générique « monotone + additif ⇒ linéaire » n'existe. Non-dénombrabilité de
-- Ioo 0 1 : pas de lemme direct `¬Countable`, mais route cardinale propre via
-- Cardinal.mk_Ioo_real + Cardinal.aleph0_lt_continuum + le_aleph0_iff_set_countable
-- (préférée à la route mesure, qui marche aussi via Real.volume_Ioo +
-- Set.Countable.measure_zero mais alourdit les imports).
-- ═══════════════════════════════════════════════════════════════════

/-- **D1.** `f 1 = 1`, via le triplet `(0,0,1)` (`0,1 ∉ C` car `C ⊆ Ioo 0 1`). -/
private theorem warmup_II_D1 {C : Set ℝ} (hCsub : C ⊆ Set.Ioo (0 : ℝ) 1) (f : ℝ → ℝ)
    (hf0 : f 0 = 0)
    (htriple : ∀ a b c, a ∈ Set.Icc (0 : ℝ) 1 \ C → b ∈ Set.Icc (0 : ℝ) 1 \ C →
      c ∈ Set.Icc (0 : ℝ) 1 \ C → a + b + c = 1 → f a + f b + f c = 1) :
    f 1 = 1 := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 \ C := by
    refine ⟨⟨le_refl 0, zero_le_one⟩, fun hc => ?_⟩
    exact absurd (hCsub hc).1 (lt_irrefl 0)
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 \ C := by
    refine ⟨⟨zero_le_one, le_refl 1⟩, fun hc => ?_⟩
    exact absurd (hCsub hc).2 (lt_irrefl 1)
  have h := htriple 0 0 1 h0 h0 h1 (by ring)
  rw [hf0] at h
  linarith

/-- **D2.** Il existe un point `a₀ ∈ (0,1)` « générique » : pour tous `p q : ℕ`
avec `q > 0` et `(p/q)·a₀ ≤ 1`, ni `(p/q)·a₀` ni `1 - (p/q)·a₀` ne sont dans `C`.
Construit via l'ensemble dénombrable `⋃_{c∈C} ℚ·c ∪ ⋃_{c∈C} ℚ·(1-c)` : tout point
hors de cet ensemble a la propriété (sinon `a₀` s'écrirait `(q/p)·c` ou
`(q/p)·(1-c)` pour un `c ∈ C`, avec `p ≠ 0` car `c ∈ (0,1)`). -/
private theorem warmup_II_D2 {C : Set ℝ} (hC : C.Countable) (hCsub : C ⊆ Set.Ioo (0 : ℝ) 1) :
    ∃ a₀ ∈ Set.Ioo (0 : ℝ) 1, ∀ p q : ℕ, 0 < q → (p : ℝ) / q * a₀ ≤ 1 →
      (p : ℝ) / q * a₀ ∉ C ∧ 1 - (p : ℝ) / q * a₀ ∉ C := by
  sorry

/-- **D3.** Additivité sur l'orbite de `a₀` : deux applications de `htriple`
(`(p/q·a₀, p'/q·a₀, 1-(p+p')/q·a₀)` puis `((p+p')/q·a₀, 1-(p+p')/q·a₀, 0)`),
soustraction, `hf0`. Toutes les appartenances viennent de `hgen` (D2). -/
private theorem warmup_II_D3 {C : Set ℝ} (f : ℝ → ℝ) (hf0 : f 0 = 0)
    (htriple : ∀ a b c, a ∈ Set.Icc (0 : ℝ) 1 \ C → b ∈ Set.Icc (0 : ℝ) 1 \ C →
      c ∈ Set.Icc (0 : ℝ) 1 \ C → a + b + c = 1 → f a + f b + f c = 1)
    {a₀ : ℝ} (ha₀ : a₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hgen : ∀ p q : ℕ, 0 < q → (p : ℝ) / q * a₀ ≤ 1 →
      (p : ℝ) / q * a₀ ∉ C ∧ 1 - (p : ℝ) / q * a₀ ∉ C) :
    ∀ p p' q : ℕ, 0 < q → ((p + p' : ℕ) : ℝ) / q * a₀ ≤ 1 →
      f ((p : ℝ) / q * a₀) + f ((p' : ℝ) / q * a₀) = f (((p + p' : ℕ) : ℝ) / q * a₀) := by
  sorry

/-- **D4.** Homogénéité rationnelle sur l'orbite : `f((p/q)·a₀) = (p/q)·f(a₀)`.
Deux temps : (i) récurrence sur `p` via D3 pour `f(p·(a₀/q)) = p·f(a₀/q)` tant
que `p·(a₀/q) ≤ 1` ; (ii) cas `p = q` donne `f(a₀) = q·f(a₀/q)` ; combiner. -/
private theorem warmup_II_D4 {C : Set ℝ} (f : ℝ → ℝ) (hf0 : f 0 = 0)
    (htriple : ∀ a b c, a ∈ Set.Icc (0 : ℝ) 1 \ C → b ∈ Set.Icc (0 : ℝ) 1 \ C →
      c ∈ Set.Icc (0 : ℝ) 1 \ C → a + b + c = 1 → f a + f b + f c = 1)
    {a₀ : ℝ} (ha₀ : a₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hgen : ∀ p q : ℕ, 0 < q → (p : ℝ) / q * a₀ ≤ 1 →
      (p : ℝ) / q * a₀ ∉ C ∧ 1 - (p : ℝ) / q * a₀ ∉ C) :
    ∀ p q : ℕ, 0 < q → (p : ℝ) / q * a₀ ≤ 1 → f ((p : ℝ) / q * a₀) = (p : ℝ) / q * f a₀ := by
  sorry

/-- **D6-existence.** Il existe `b ∈ (0,1)` avec `b ∉ C` et `1 - b ∉ C`
(l'ensemble `C ∪ {x | 1 - x ∈ C}` est dénombrable, ne peut recouvrir `(0,1)`). -/
private theorem warmup_II_D6_exists {C : Set ℝ} (hC : C.Countable) :
    ∃ b ∈ Set.Ioo (0 : ℝ) 1, b ∉ C ∧ 1 - b ∉ C := by
  sorry

/-- **D5 (le cœur, squeeze).** Pour `a ∈ [0,1) \ C`, `f a = (f a₀ / a₀) · a`.
Par `le_antisymm`, chaque sens via `∀ ε > 0` : `exists_rat_btwn` donne des
rationnels `r < a/a₀ < r'` (dénominateur commun `q`) avec `r'·a₀ ≤ 1` et
`(r' - r)·a₀` arbitrairement petit ; `hmono` encadre `f a` par
`f(r·a₀) ≤ f a ≤ f(r'·a₀)`, D4 réécrit les bornes en `r·f(a₀)` et `r'·f(a₀)`. -/
private theorem warmup_II_D5 {C : Set ℝ} (f : ℝ → ℝ)
    (hmono : ∀ a b, a ∈ Set.Icc (0 : ℝ) 1 \ C → b ∈ Set.Icc (0 : ℝ) 1 \ C → a ≤ b → f a ≤ f b)
    {a₀ : ℝ} (ha₀ : a₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hgen : ∀ p q : ℕ, 0 < q → (p : ℝ) / q * a₀ ≤ 1 →
      (p : ℝ) / q * a₀ ∉ C ∧ 1 - (p : ℝ) / q * a₀ ∉ C)
    (hD4 : ∀ p q : ℕ, 0 < q → (p : ℝ) / q * a₀ ≤ 1 → f ((p : ℝ) / q * a₀) = (p : ℝ) / q * f a₀) :
    ∀ a ∈ Set.Ico (0 : ℝ) 1 \ C, f a = (f a₀ / a₀) * a := by
  sorry

/-- **D6.** `f a₀ / a₀ = 1` : triplet `(b, 1-b, 0)` (`htriple`) donne
`f b + f(1-b) = 1` (avec `f 0 = 0`) ; D5 sur `b` et `1-b` (tous deux `< 1`)
donne `β·b + β·(1-b) = β = 1`. -/
private theorem warmup_II_D6 {C : Set ℝ} (f : ℝ → ℝ) (hf0 : f 0 = 0)
    (htriple : ∀ a b c, a ∈ Set.Icc (0 : ℝ) 1 \ C → b ∈ Set.Icc (0 : ℝ) 1 \ C →
      c ∈ Set.Icc (0 : ℝ) 1 \ C → a + b + c = 1 → f a + f b + f c = 1)
    {a₀ : ℝ} (ha₀ : a₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hD5 : ∀ a ∈ Set.Ico (0 : ℝ) 1 \ C, f a = (f a₀ / a₀) * a)
    {b : ℝ} (hb : b ∈ Set.Ioo (0 : ℝ) 1) (hbC : b ∉ C) (hbC' : 1 - b ∉ C) :
    f a₀ / a₀ = 1 := by
  sorry

/-- **D7 / Warmup Theorem II (CKM 1985 §3).** Si `f` est monotone et
« additive-à-1 » sur `[0,1] \ C` (`C` dénombrable, `C ⊆ (0,1)`), avec `f 0 = 0`,
alors `f = id` sur `[0,1] \ C`. -/
theorem warmup_II (C : Set ℝ) (hC : C.Countable) (hCsub : C ⊆ Set.Ioo (0 : ℝ) 1) (f : ℝ → ℝ)
    (hf0 : f 0 = 0)
    (hmono : ∀ a b, a ∈ Set.Icc (0 : ℝ) 1 \ C → b ∈ Set.Icc (0 : ℝ) 1 \ C → a ≤ b → f a ≤ f b)
    (htriple : ∀ a b c, a ∈ Set.Icc (0 : ℝ) 1 \ C → b ∈ Set.Icc (0 : ℝ) 1 \ C →
      c ∈ Set.Icc (0 : ℝ) 1 \ C → a + b + c = 1 → f a + f b + f c = 1) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1 \ C, f a = a := by
  have hD1 := warmup_II_D1 hCsub f hf0 htriple
  obtain ⟨a₀, ha₀, hgen⟩ := warmup_II_D2 hC hCsub
  have hD4 := warmup_II_D4 f hf0 htriple ha₀ hgen
  have hD5 := warmup_II_D5 f hmono ha₀ hgen hD4
  obtain ⟨b, hb, hbC, hbC'⟩ := warmup_II_D6_exists hC
  have hβ := warmup_II_D6 f hf0 htriple ha₀ hD5 hb hbC hbC'
  intro a ha
  obtain ⟨ha01, haC⟩ := ha
  rcases ha01.2.lt_or_eq with hlt | heq
  · have haIco : a ∈ Set.Ico (0 : ℝ) 1 \ C := ⟨⟨ha01.1, hlt⟩, haC⟩
    rw [hD5 a haIco, hβ, one_mul]
  · rw [heq]; exact hD1

end Gleason
