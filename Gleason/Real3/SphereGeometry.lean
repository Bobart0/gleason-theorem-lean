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

/-- Variante « symétrique » de `exists_orthonormalBasis_of_triple` : au lieu d'une
`Pairwise`, les 3 produits scalaires deux-à-deux sont donnés explicitement (plus
commode à fournir à chaque site d'appel). -/
theorem exists_orthonormalBasis_of_triple' (v0 v1 v2 : E3)
    (h0 : ‖v0‖ = 1) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1)
    (h01 : ⟪v0, v1⟫ = 0) (h02 : ⟪v0, v2⟫ = 0) (h12 : ⟪v1, v2⟫ = 0) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ E3, b 0 = v0 ∧ b 1 = v1 ∧ b 2 = v2 := by
  have h10 : ⟪v1, v0⟫ = 0 := by rw [real_inner_comm]; exact h01
  have h20 : ⟪v2, v0⟫ = 0 := by rw [real_inner_comm]; exact h02
  have h21 : ⟪v2, v1⟫ = 0 := by rw [real_inner_comm]; exact h12
  have hnorm : ∀ i, ‖(![v0, v1, v2] : Fin 3 → E3) i‖ = 1 := by
    intro i; fin_cases i <;> simp_all
  have hperp : Pairwise (fun i j =>
      ⟪(![v0, v1, v2] : Fin 3 → E3) i, (![v0, v1, v2] : Fin 3 → E3) j⟫ = 0) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | simp_all
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_of_triple _ hnorm hperp
  exact ⟨b, by simpa using hb 0, by simpa using hb 1, by simpa using hb 2⟩

/-- Il existe un vecteur unitaire orthogonal à deux vecteurs donnés : l'orthogonal
d'un sous-espace engendré par 2 vecteurs, dans un espace de dimension 3, est de
dimension ≥ 1 (comptage de dimension). Remplace le produit vectoriel : couvre
uniformément le cas dégénéré où les deux vecteurs sont colinéaires, sans
disjonction de cas. -/
theorem exists_unit_orthogonal_to_pair (a b : E3) :
    ∃ u : E3, ‖u‖ = 1 ∧ ⟪u, a⟫ = 0 ∧ ⟪u, b⟫ = 0 := by
  classical
  set K : Submodule ℝ E3 := Submodule.span ℝ ({a, b} : Set E3) with hK_def
  have hKfin : Module.finrank ℝ K ≤ 2 := by
    refine le_trans (finrank_span_le_card ({a, b} : Set E3)) ?_
    simp only [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp)
  have hE3 : Module.finrank ℝ E3 = 3 := by simp
  have hsum : Module.finrank ℝ K + Module.finrank ℝ Kᗮ = Module.finrank ℝ E3 :=
    Submodule.finrank_add_finrank_orthogonal K
  have hKperp : 1 ≤ Module.finrank ℝ Kᗮ := by omega
  have hne : Kᗮ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hKperp
    omega
  obtain ⟨w, hwK, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have haK : a ∈ K := Submodule.subset_span (by simp)
  have hbK : b ∈ K := Submodule.subset_span (by simp)
  have hwa : ⟪w, a⟫ = 0 := Submodule.inner_left_of_mem_orthogonal haK hwK
  have hwb : ⟪w, b⟫ = 0 := Submodule.inner_left_of_mem_orthogonal hbK hwK
  refine ⟨(‖w‖⁻¹ : ℝ) • w, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (norm_pos_iff.mpr hw0)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)
  · rw [real_inner_smul_left, hwa, mul_zero]
  · rw [real_inner_smul_left, hwb, mul_zero]

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

/-- **P3.** Si `(u,s,t)` et `(u,s',t')` sont deux triplets orthonormés partageant
`u`, alors `f s + f t = f s' + f t'` — corollaire direct de `frame_pair_sum_eq`
appliqué aux bases construites sur `(u,s,t)` et `(u,s',t')`. -/
theorem frameFunction_pair_swap {f : E3 → ℝ} {W : ℝ} (hf : IsFrameFunction f W)
    {u s t s' t' : E3}
    (hu : ‖u‖ = 1) (hs : ‖s‖ = 1) (ht : ‖t‖ = 1) (hs' : ‖s'‖ = 1) (ht' : ‖t'‖ = 1)
    (hus : ⟪u, s⟫ = 0) (hut : ⟪u, t⟫ = 0) (hst : ⟪s, t⟫ = 0)
    (hus' : ⟪u, s'⟫ = 0) (hut' : ⟪u, t'⟫ = 0) (hs't' : ⟪s', t'⟫ = 0) :
    f s + f t = f s' + f t' := by
  obtain ⟨b, hb0, hb1, hb2⟩ := exists_orthonormalBasis_of_triple' u s t hu hs ht hus hut hst
  obtain ⟨b', hb0', hb1', hb2'⟩ :=
    exists_orthonormalBasis_of_triple' u s' t' hu hs' ht' hus' hut' hs't'
  have h := frame_pair_sum_eq hf b b' (by rw [hb0, hb0'])
  rwa [hb1, hb2, hb1', hb2'] at h

/-- **P4.** Si `f(s) > M - ξ` (proche du sup) alors il existe `t ⊥ s` avec
`f(t) < m + ξ` (proche de l'inf). Preuve CKM §2 : on choisit `t'` avec
`f(t') < m + δ` où `δ = ξ - (M - f s) > 0`, un vecteur `u` orthogonal à `s`
et `t'` (`exists_unit_orthogonal_to_pair`, remplace le produit vectoriel —
couvre le cas dégénéré `t' = ±s` sans disjonction de cas), puis on complète
en `t ⊥ (s,u)` et `s' ⊥ (t',u)`. `frameFunction_pair_swap` sur `(u,s,t)` et
`(u,s',t')` donne `f s + f t = f s' + f t'`, d'où `f t < m + ξ` en
combinant `f s' ≤ M` et `f t' < m + δ`. -/
theorem frameFunction_P4 {f : E3 → ℝ} {W M m : ℝ} (hf : IsFrameFunction f W)
    (hMub : ∀ x : E3, ‖x‖ = 1 → f x ≤ M)
    (hm : ∀ ε > 0, ∃ x : E3, ‖x‖ = 1 ∧ f x < m + ε)
    {s : E3} (hs : ‖s‖ = 1) {ξ : ℝ} (hfs : M - ξ < f s) :
    ∃ t : E3, ‖t‖ = 1 ∧ ⟪s, t⟫ = 0 ∧ f t < m + ξ := by
  set δ : ℝ := ξ - (M - f s) with hδ_def
  have hδpos : 0 < δ := by rw [hδ_def]; linarith
  obtain ⟨t', ht'unit, ht'lt⟩ := hm δ hδpos
  obtain ⟨u, huunit, hus, hut'⟩ := exists_unit_orthogonal_to_pair s t'
  obtain ⟨t, htunit, hts, htu⟩ := exists_unit_orthogonal_to_pair s u
  obtain ⟨s', hs'unit, hs't', hs'u⟩ := exists_unit_orthogonal_to_pair t' u
  have hut : ⟪u, t⟫ = 0 := by rw [real_inner_comm]; exact htu
  have hst : ⟪s, t⟫ = 0 := by rw [real_inner_comm]; exact hts
  have hus' : ⟪u, s'⟫ = 0 := by rw [real_inner_comm]; exact hs'u
  have h := frameFunction_pair_swap hf huunit hs htunit hs'unit ht'unit
    hus hut hst hus' hut' hs't'
  have hs'M : f s' ≤ M := hMub s' hs'unit
  refine ⟨t, htunit, hst, ?_⟩
  rw [hδ_def] at ht'lt
  linarith

/- ═══════════════════════════════════════════════════════════════════
   Géométrie du pôle (CKM 1985 §4). Le pôle `p` reste un ARGUMENT
   EXPLICITE de chaque définition (pas de `variable` fixée globalement au
   sens mathématique) : le §7 utilisera trois pôles différents.
   ═══════════════════════════════════════════════════════════════════ -/

section PoleGeometry

variable (p : E3)

/-- **Latitude** de `s` relative au pôle `p` : `⟪p,s⟫²`. -/
def lat (s : E3) : ℝ := ⟪p, s⟫ ^ 2

/-- **Hémisphère nord** : vecteurs unitaires du côté du pôle (`⟪p,·⟫ ≥ 0`). -/
def northern : Set E3 := {t : E3 | ‖t‖ = 1 ∧ 0 ≤ ⟪p, t⟫}

/-- **Équateur** : vecteurs unitaires orthogonaux au pôle. -/
def equator : Set E3 := {t : E3 | ‖t‖ = 1 ∧ ⟪p, t⟫ = 0}

/-- Point de l'équateur (à normalisation près) déterminé par `p` et `s` : la
projection de `s` sur `pᗮ`, complétée par la composante `√(1-⟪p,s⟫²)` sur `p`
pour former un vecteur unitaire orthogonal à `s` dans le plan `(p,s)`.
Valeur poubelle en `s = p` (jamais utilisée : voir les hypothèses de B2). -/
noncomputable def sperp (s : E3) : E3 :=
  Real.sqrt (1 - ⟪p, s⟫ ^ 2) • p - ⟪p, s⟫ • (‖s - ⟪p, s⟫ • p‖⁻¹ • (s - ⟪p, s⟫ • p))

/-- **Cercle de descente** de `s` relatif au pôle `p` : les points de
l'hémisphère nord orthogonaux à `sperp p s`. -/
def descent (s : E3) : Set E3 := {t : E3 | t ∈ northern p ∧ ⟪sperp p s, t⟫ = 0}

@[simp] theorem mem_northern_iff {t : E3} : t ∈ northern p ↔ ‖t‖ = 1 ∧ 0 ≤ ⟪p, t⟫ := Iff.rfl

@[simp] theorem mem_equator_iff {t : E3} : t ∈ equator p ↔ ‖t‖ = 1 ∧ ⟪p, t⟫ = 0 := Iff.rfl

@[simp] theorem mem_descent_iff {s t : E3} :
    t ∈ descent p s ↔ t ∈ northern p ∧ ⟪sperp p s, t⟫ = 0 := Iff.rfl

end PoleGeometry

end
end Gleason
