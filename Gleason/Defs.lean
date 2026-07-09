import Mathlib

/-!
# Définitions centrales

Objets de base pour la formalisation du théorème de Gleason (variante « projection
only », dimension finie) et du théorème de Busch (2003).

## Correction du défaut fatal de l'ancien développement

L'additivité de `ProjMeasure` est exigée pour l'ORTHOGONALITÉ (`Submodule.IsOrtho`),
et non pour la disjonction de treillis (`Disjoint`). Avec la disjonction de treillis,
le type des mesures est VIDE dès la dimension 2 (trois droites distinctes d'un plan
forcent 3/2 = 1). Chaque structure introduite ici doit être accompagnée, dans le même
commit, d'un test d'inhabitation dans `Gleason/Nonvacuity.lean`.

## Conventions

* `H n = EuclideanSpace ℂ (Fin n)` : espace de Hilbert complexe de dimension `n`.
* Produit scalaire Mathlib `⟪·,·⟫_ℂ` : linéaire en la SECONDE variable.
* Aucune déclaration `axiom` n'est autorisée dans ce dépôt (voir `scripts/guard.sh`).
-/

namespace Gleason

open scoped InnerProductSpace

noncomputable section

/-- Espace de Hilbert complexe de dimension finie `n`. -/
abbrev H (n : ℕ) := EuclideanSpace ℂ (Fin n)

variable {n : ℕ}

/-- **Mesure de probabilité finiment additive sur les sous-espaces** d'un espace de
Hilbert complexe de dimension finie. L'additivité est exigée pour l'orthogonalité
au sens du produit scalaire (`Submodule.IsOrtho`, notation `A ⟂ B`). -/
structure ProjMeasure (n : ℕ) where
  /-- La valuation sur les sous-espaces. -/
  μ : Submodule ℂ (H n) → ℝ
  nonneg : ∀ A, 0 ≤ μ A
  top_eq_one : μ ⊤ = 1
  /-- Additivité sur les paires orthogonales (au sens du produit scalaire !). -/
  add_isOrtho : ∀ A B : Submodule ℂ (H n), A ⟂ B → μ (A ⊔ B) = μ A + μ B

/-- **Opérateur densité** : symétrique (auto-adjoint), positif, de trace 1. -/
structure IsDensityOperator (ρ : H n →ₗ[ℂ] H n) : Prop where
  symmetric : LinearMap.IsSymmetric ρ
  nonneg : ∀ x : H n, 0 ≤ (⟪ρ x, x⟫_ℂ).re
  trace_one : LinearMap.trace ℂ (H n) ρ = 1

/-- Projection orthogonale sur `A`, vue comme endomorphisme linéaire de `H n`.
TODO(M1) : vérifier le nom Mathlib courant (`Submodule.starProjection`,
anciennement `orthogonalProjection'`). En dimension finie, l'instance
`HasOrthogonalProjection` est automatique. -/
def projL (A : Submodule ℂ (H n)) : H n →ₗ[ℂ] H n :=
  (A.starProjection : H n →L[ℂ] H n).toLinearMap

/-- **Valeur de Born** : `Re (tr (ρ ∘ P_A))`. Pour `ρ` densité et `A` sous-espace,
cette trace est réelle ; on prend la partie réelle pour typer en `ℝ`. -/
def bornValue (ρ : H n →ₗ[ℂ] H n) (A : Submodule ℂ (H n)) : ℝ :=
  (LinearMap.trace ℂ (H n) (ρ ∘ₗ projL A)).re

namespace ProjMeasure

variable (m : ProjMeasure n)

/-- Premier exercice de preuve (M1) : `μ ⊥ = 0`.
Indication : `⊥ ⟂ ⊥` et `⊥ ⊔ ⊥ = ⊥`, donc `μ ⊥ = 2 * μ ⊥`. -/
theorem bot_eq_zero : m.μ ⊥ = 0 := by
  have h := m.add_isOrtho ⊥ ⊥ (Submodule.IsOrtho.symm (Submodule.isOrtho_bot_left))
  simp at h
  linarith

/-- Additivité avec le complément orthogonal : `μ A + μ Aᗮ = 1`.
Indication : en dimension finie, `A ⊔ Aᗮ = ⊤` et `A ⟂ Aᗮ`. -/
theorem add_orthogonal_compl (A : Submodule ℂ (H n)) : m.μ A + m.μ Aᗮ = 1 := by
  rw [← m.top_eq_one, ← Submodule.sup_orthogonal_of_hasOrthogonalProjection (K := A)]
  exact (m.add_isOrtho A Aᗮ (Submodule.isOrtho_orthogonal_right A)).symm

/-- Toute valeur est ≤ 1. Conséquence de `add_orthogonal_compl` et `nonneg`. -/
theorem le_one (A : Submodule ℂ (H n)) : m.μ A ≤ 1 := by
  linarith [m.add_orthogonal_compl A, m.nonneg Aᗮ]

/-- Monotonie : si `A ≤ B` alors `μ A ≤ μ B`.
Indication : `B = A ⊔ (B ⊓ Aᗮ)` en dimension finie, et les deux morceaux sont orthogonaux. -/
theorem mono {A B : Submodule ℂ (H n)} (h : A ≤ B) : m.μ A ≤ m.μ B := by
  have hdecomp := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection h
  have hortho : A ⟂ (Aᗮ ⊓ B) :=
    (Submodule.isOrtho_orthogonal_right A).mono_right inf_le_left
  rw [← hdecomp, m.add_isOrtho _ _ hortho]
  linarith [m.nonneg (Aᗮ ⊓ B)]

end ProjMeasure

end
end Gleason
