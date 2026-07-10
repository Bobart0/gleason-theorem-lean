import Gleason.Real3.FrameFunction

/-!
# Mini-bibliothèque de géométrie sphérique

Lemmes de géométrie sur S² nécessaires à la descente CKM. Stratégie : tout exprimer
par des TRIPLETS ORTHONORMÉS (extension de bases orthonormées, Gram–Schmidt), en
évitant SO(3) et les angles d'Euler, mal couverts par Mathlib.
-/

namespace Gleason

open scoped RealInnerProductSpace

noncomputable section

/-- Tout vecteur unitaire se complète en base orthonormée de ℝ³.
Mathlib : chercher l'extension d'une famille orthonormée en `OrthonormalBasis`
(`Orthonormal` + `exists_orthonormalBasis_extension` ou équivalent). -/
theorem exists_orthonormalBasis_fst (x : E3) (hx : ‖x‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ E3, b 0 = x := by
  have hcard : Module.finrank ℝ E3 = Fintype.card (Fin 3) := by simp
  have hv : Orthonormal ℝ (({0} : Set (Fin 3)).restrict (fun _ : Fin 3 => x)) := by
    constructor
    · rintro ⟨i, hi⟩
      simp [Set.restrict_apply, hx]
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp only [Set.mem_singleton_iff] at hi hj
      exact absurd (Subtype.ext (hi.trans hj.symm)) hij
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hcard
  exact ⟨b, hb 0 rfl⟩

/-- Toute paire orthonormée se complète en base orthonormée de ℝ³. -/
theorem exists_orthonormalBasis_pair (x y : E3) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ⟪x, y⟫ = 0) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ E3, b 0 = x ∧ b 1 = y := by
  have hcard : Module.finrank ℝ E3 = Fintype.card (Fin 3) := by simp
  have hyx : ⟪y, x⟫ = 0 := by rw [real_inner_comm]; exact hxy
  have hv : Orthonormal ℝ (({0, 1} : Set (Fin 3)).restrict ![x, y, 0]) := by
    constructor
    · rintro ⟨i, hi⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      rcases hi with hi | hi <;> subst hi <;> simp [Set.restrict_apply, hx, hy]
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
      simp only [ne_eq, Subtype.mk.injEq] at hij
      rcases hi with hi | hi <;> rcases hj with hj | hj <;> subst hi <;> subst hj
      · exact absurd rfl hij
      · simp [Set.restrict_apply, hxy]
      · simp [Set.restrict_apply, hyx]
      · exact absurd rfl hij
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hcard
  refine ⟨b, ?_, ?_⟩
  · have := hb 0 (by simp)
    simpa using this
  · have := hb 1 (by simp)
    simpa using this

/-- Un triplet EXPLICITEMENT prescrit (les trois vecteurs, pas seulement deux) qui
est orthonormé coïncide avec une base orthonormée — cas `s = univ` de l'extension.
Outil de base pour construire des bases par manipulation directe de triplets
(retournement de signe, produit vectoriel, etc.), utilisé dans toute la suite. -/
theorem exists_orthonormalBasis_of_triple (v : Fin 3 → E3)
    (hnorm : ∀ i, ‖v i‖ = 1) (hperp : Pairwise (fun i j => ⟪v i, v j⟫ = 0)) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ E3, ∀ i, b i = v i := by
  have hcard : Module.finrank ℝ E3 = Fintype.card (Fin 3) := by simp
  have hv : Orthonormal ℝ ((Set.univ : Set (Fin 3)).restrict v) :=
    ⟨fun i => hnorm i.1, fun i j hij => hperp (fun h => hij (Subtype.ext h))⟩
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hcard
  exact ⟨b, fun i => hb i (Set.mem_univ i)⟩

/-- Deux bases partageant un vecteur : la somme de `f` sur les deux autres vecteurs
est la même (conséquence directe de la définition de frame function ; utilisé
partout dans la descente). -/
theorem frame_pair_sum_eq {f : E3 → ℝ} {W : ℝ} (hf : IsFrameFunction f W)
    (b b' : OrthonormalBasis (Fin 3) ℝ E3) (h : b 0 = b' 0) :
    f (b 1) + f (b 2) = f (b' 1) + f (b' 2) := by
  have h1 := hf b
  have h2 := hf b'
  rw [Fin.sum_univ_three] at h1 h2
  rw [h] at h1
  linarith

/-- Une frame function positive est bornée par `W` sur la sphère
(compléter tout vecteur unitaire en base orthonormée, les deux autres termes sont ≥ 0). -/
theorem IsFrameFunction.le_of_nonneg {f : E3 → ℝ} {W : ℝ}
    (hf : IsFrameFunction f W) (hnn : ∀ x, ‖x‖ = 1 → 0 ≤ f x)
    {x : E3} (hx : ‖x‖ = 1) : f x ≤ W := by
  obtain ⟨b, hb0⟩ := exists_orthonormalBasis_fst x hx
  have hsum := hf b
  rw [Fin.sum_univ_three, hb0] at hsum
  have hn1 : 0 ≤ f (b 1) := hnn (b 1) (b.norm_eq_one 1)
  have hn2 : 0 ≤ f (b 2) := hnn (b 2) (b.norm_eq_one 2)
  linarith

/-- **P2 (parité).** `f(-s) = f(s)` : on remplace `b 0` par `-(b 0)` dans une base
contenant `s`, les deux triplets sont orthonormés (retournement de signe préserve
normes et orthogonalité). -/
theorem frameFunction_even {f : E3 → ℝ} {W : ℝ} (hf : IsFrameFunction f W)
    (s : E3) (hs : ‖s‖ = 1) : f (-s) = f s := by
  obtain ⟨b, hb0⟩ := exists_orthonormalBasis_fst s hs
  have hnorm : ∀ i, ‖(![-(b 0), b 1, b 2] : Fin 3 → E3) i‖ = 1 := by
    intro i; fin_cases i <;> simp [b.norm_eq_one]
  have hperp : Pairwise (fun i j =>
      ⟪(![-(b 0), b 1, b 2] : Fin 3 → E3) i, (![-(b 0), b 1, b 2] : Fin 3 → E3) j⟫ = 0) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | simp [inner_neg_left, inner_neg_right, b.inner_eq_ite]
  obtain ⟨b', hb'⟩ := exists_orthonormalBasis_of_triple _ hnorm hperp
  have h1 := hf b
  have h2 := hf b'
  rw [Fin.sum_univ_three] at h1 h2
  rw [hb' 0, hb' 1, hb' 2] at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val_two, Matrix.tail_cons] at h2
  rw [hb0] at h1 h2
  linarith

end
end Gleason
