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
-- Convention scalaire : pour r : ℝ et T : H n →ₗ[ℂ] H n, on écrit
-- (↑r : ℂ) • T (action du ℂ-module, restreinte aux réels).
-- L'instance Module ℝ (H n →ₗ[ℂ] H n) existe (Module.complexToReal)
-- mais (↑r : ℂ) • T est plus explicite et évite les problèmes d'inférence.

-- ── (B1) Préservation des effets par homothétie réelle ────────────
-- Nécessaire pour que les énoncés B2–B4 aient un sens.
-- Preuve : 0 ≤ rT ≤ T ≤ 1 par positivité de r et (1-r)T.

theorem isEffect_complexSmul {T : H n →ₗ[ℂ] H n} (hT : IsEffect T)
    {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    IsEffect ((↑r : ℂ) • T) := by
  sorry

-- ── (B2) Pas dyadique : f(T/2) = f(T)/2 ─────────────────────────
-- Base de l'induction dyadique.
-- Preuve : T = (1/2)T + (1/2)T, les deux sommandes sont des effets
-- (par B1), leur somme est T qui est un effet, donc
-- f(T) = f((1/2)T) + f((1/2)T) = 2 · f((1/2)T).

theorem EffectMeasure.map_half_smul (F : EffectMeasure n)
    {T : H n →ₗ[ℂ] H n} (hT : IsEffect T) :
    F.f ((↑(2⁻¹ : ℝ) : ℂ) • T) = 2⁻¹ * F.f T := by
  sorry

-- ── (B3) Homogénéité dyadique : f((m/2^k) · T) = (m/2^k) · f(T) ─
-- Induction sur k (B2) et sur m (additivité itérée).
-- Précondition : m/2^k ≤ 1, de sorte que (m/2^k)·T est un effet.

theorem EffectMeasure.map_dyadic_smul (F : EffectMeasure n)
    {T : H n →ₗ[ℂ] H n} (hT : IsEffect T) (k m : ℕ) (hm : m ≤ 2 ^ k) :
    F.f ((↑(m / 2 ^ k : ℝ) : ℂ) • T) = (m / 2 ^ k : ℝ) * F.f T := by
  sorry

-- ── (B4) Homogénéité rationnelle ─────────────────────────────────
-- Tout rationnel q ∈ [0,1] s'écrit m/2^k après réduction au même
-- dénominateur (q = a/b, b | 2^k pour k assez grand — ou, plus
-- directement, combiner additivité itérée pour le numérateur et B2
-- pour la division). On peut aussi passer par :
--   f(n · T) = n · f(T)  (additivité itérée, n : ℕ, n·T effet)
-- puis diviser.

theorem EffectMeasure.map_nat_smul (F : EffectMeasure n)
    {T : H n →ₗ[ℂ] H n} (hT : IsEffect T) (m : ℕ)
    (heff : IsEffect ((↑(m : ℝ) : ℂ) • T)) :
    F.f ((↑(m : ℝ) : ℂ) • T) = (m : ℝ) * F.f T := by
  sorry

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

theorem EffectMeasure.map_realSmul (F : EffectMeasure n)
    {T : H n →ₗ[ℂ] H n} (hT : IsEffect T)
    {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    F.f ((↑r : ℂ) • T) = r * F.f T := by
  sorry

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

-- ── (B7) Extension ℝ-linéaire aux auto-adjoints ─────────────────
-- On définit g(S) := c · f(E₊) − c · f(E₋) pour une décomposition
-- quelconque. Bonne définition : si S = c₁ E₁ − c₁ E₁' = c₂ E₂ − c₂ E₂',
-- alors c₁ E₁ + c₂ E₂' = c₂ E₂ + c₁ E₁' (somme d'effets pondérés),
-- et map_realSmul + additivité donne l'égalité des deux expressions.
-- Linéarité ℝ : par la même technique (décomposer S+T et r·S).

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
