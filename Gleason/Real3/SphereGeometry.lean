import Gleason.Real3.FrameFunction

/-!
# Mini-bibliothèque de géométrie sphérique

Lemmes de géométrie sur S² nécessaires à la descente CKM. Stratégie : tout exprimer
par des TRIPLETS ORTHONORMÉS (extension de bases orthonormées, Gram–Schmidt), en
évitant SO(3) et les angles d'Euler, mal couverts par Mathlib.
-/

namespace Gleason

open scoped RealInnerProductSpace Real

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

/-- **C1.** Étant donné une paire orthonormée, il existe un troisième vecteur
unitaire orthogonal aux deux (le 3ᵉ vecteur d'une base les complétant). -/
theorem exists_third_orthogonal (x y : E3) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ⟪x, y⟫ = 0) :
    ∃ z, ‖z‖ = 1 ∧ ⟪x, z⟫ = 0 ∧ ⟪y, z⟫ = 0 := by
  obtain ⟨b, hb0, hb1⟩ := exists_orthonormalBasis_pair x y hx hy hxy
  refine ⟨b 2, b.norm_eq_one 2, ?_, ?_⟩
  · rw [← hb0]; exact b.inner_eq_zero (by decide)
  · rw [← hb1]; exact b.inner_eq_zero (by decide)

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

/-- **B1.** Faits basiques sur `lat`, `northern`, `equator`. -/
theorem lat_nonneg (s : E3) : 0 ≤ lat p s := sq_nonneg _

theorem lat_le_one {s : E3} (hp : ‖p‖ = 1) (hs : ‖s‖ = 1) : lat p s ≤ 1 := by
  have h := abs_real_inner_le_norm p s
  rw [hp, hs, mul_one] at h
  have h' := abs_le.mp h
  have h2 : ⟪p, s⟫ ^ 2 ≤ 1 ^ 2 := sq_le_sq' h'.1 h'.2
  simpa [lat] using h2

theorem lat_self (hp : ‖p‖ = 1) : lat p p = 1 := by
  unfold lat
  rw [real_inner_self_eq_norm_sq, hp]
  norm_num

theorem equator_subset_northern : equator p ⊆ northern p := by
  intro t ht
  exact ⟨ht.1, le_of_eq ht.2.symm⟩

theorem mem_equator_iff_lat_eq_zero (t : E3) : t ∈ equator p ↔ ‖t‖ = 1 ∧ lat p t = 0 := by
  simp [equator, lat]

end PoleGeometry

/-- **B2 (préliminaire).** `‖s - ⟪p,s⟫•p‖² = 1 - ⟪p,s⟫²`, par développement de
l'inner product (algèbre pure, aucune hypothèse `s ≠ p`). -/
theorem norm_sq_sub_inner_smul {p s : E3} (hp : ‖p‖ = 1) (hs : ‖s‖ = 1) :
    ‖s - ⟪p, s⟫ • p‖ ^ 2 = 1 - ⟪p, s⟫ ^ 2 := by
  set c : ℝ := ⟪p, s⟫ with hc_def
  rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm p s, ← hc_def,
      norm_smul, hp, mul_one, Real.norm_eq_abs, sq_abs, hs]
  ring

/-- **B2 (préliminaire).** `⟪p,s⟫ < 1` pour `p,s` unitaires, `s ≠ p` : `⟪p,s⟫ = 1`
forcerait `‖s-p‖ = 0` (via le préliminaire ci-dessus), donc `s = p`. -/
theorem sperp_c_lt_one {p s : E3} (hp : ‖p‖ = 1) (hs : ‖s‖ = 1) (hsp : s ≠ p) :
    ⟪p, s⟫ < 1 := by
  have hle : ⟪p, s⟫ ≤ 1 := by
    have h := abs_real_inner_le_norm p s
    rw [hp, hs, mul_one] at h
    exact (abs_le.mp h).2
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    apply hsp
    have hnorm : ‖s - ⟪p, s⟫ • p‖ ^ 2 = 1 - ⟪p, s⟫ ^ 2 := norm_sq_sub_inner_smul hp hs
    rw [h, one_smul] at hnorm
    norm_num at hnorm
    have h0 : s - p = 0 := hnorm
    exact sub_eq_zero.mp h0

/-- **B2 (cœur, groupé).** Les trois faits sur `sperp p s` (norme, orthogonalité
à `s`, produit scalaire avec `p`), établis ensemble car ils partagent la même
construction intermédiaire (`e`, le vecteur unitaire de `pᗮ` dans le plan
`(p,s)`). -/
private theorem sperp_core {p s : E3} (hp : ‖p‖ = 1) (hs : ‖s‖ = 1) (hsN : s ∈ northern p)
    (hsp : s ≠ p) :
    ‖sperp p s‖ = 1 ∧ ⟪s, sperp p s⟫ = 0 ∧ ⟪p, sperp p s⟫ = Real.sqrt (1 - ⟪p, s⟫ ^ 2) := by
  set c : ℝ := ⟪p, s⟫ with hc_def
  have hc0 : 0 ≤ c := hsN.2
  have hc1 : c < 1 := sperp_c_lt_one hp hs hsp
  have hc2lt1 : c ^ 2 < 1 := by nlinarith
  have hpos : (0 : ℝ) < 1 - c ^ 2 := by linarith
  have hnormsq : ‖s - c • p‖ ^ 2 = 1 - c ^ 2 := norm_sq_sub_inner_smul hp hs
  have hvne : s - c • p ≠ 0 := by
    intro h
    rw [h] at hnormsq
    simp at hnormsq
    linarith
  have hvnormpos : 0 < ‖s - c • p‖ := norm_pos_iff.mpr hvne
  have hvnorm_eq : ‖s - c • p‖ = Real.sqrt (1 - c ^ 2) := by
    rw [← hnormsq, Real.sqrt_sq (norm_nonneg _)]
  set e : E3 := ‖s - c • p‖⁻¹ • (s - c • p) with he_def
  have hpp : ⟪p, p⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hp]; norm_num
  have hss : ⟪s, s⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hs]; norm_num
  have hpv : ⟪p, s - c • p⟫ = 0 := by
    rw [inner_sub_right, real_inner_smul_right, hpp, ← hc_def]
    ring
  have hpe : ⟪p, e⟫ = 0 := by rw [he_def, real_inner_smul_right, hpv, mul_zero]
  have hsv : ⟪s, s - c • p⟫ = 1 - c ^ 2 := by
    rw [inner_sub_right, real_inner_smul_right, real_inner_comm p s, ← hc_def, hss]
    ring
  have hse : ⟪s, e⟫ = Real.sqrt (1 - c ^ 2) := by
    rw [he_def, real_inner_smul_right, hsv, ← hnormsq, Real.sqrt_sq (norm_nonneg _)]
    field_simp
  have he_norm : ‖e‖ = 1 := by
    rw [he_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvnormpos)]
    field_simp
  have hnormsq1 : ‖Real.sqrt (1 - c ^ 2) • p‖ ^ 2 = 1 - c ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hpos.le, hp]
    ring
  have hnormsq2 : ‖c • e‖ ^ 2 = c ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, he_norm]
    ring
  have hcross : ⟪Real.sqrt (1 - c ^ 2) • p, c • e⟫ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hpe, mul_zero, mul_zero]
  have hnormsq_sperp : ‖sperp p s‖ ^ 2 = 1 := by
    unfold sperp
    rw [← hc_def, ← he_def, norm_sub_sq_real, hcross, hnormsq1, hnormsq2]
    ring
  have hnorm_sperp : ‖sperp p s‖ = 1 := by
    have h1 : (‖sperp p s‖ - 1) * (‖sperp p s‖ + 1) = 0 := by linear_combination hnormsq_sperp
    rcases mul_eq_zero.mp h1 with h | h
    · linarith
    · linarith [norm_nonneg (sperp p s)]
  have step3 : ⟪s, sperp p s⟫ = 0 := by
    unfold sperp
    rw [← hc_def, ← he_def, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_comm p s, ← hc_def, hse]
    ring
  have step4 : ⟪p, sperp p s⟫ = Real.sqrt (1 - c ^ 2) := by
    unfold sperp
    rw [← hc_def, ← he_def, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
        hpp, hpe]
    ring
  exact ⟨hnorm_sperp, step3, step4⟩

theorem norm_sperp {p s : E3} (hp : ‖p‖ = 1) (hs : ‖s‖ = 1) (hsN : s ∈ northern p)
    (hsp : s ≠ p) : ‖sperp p s‖ = 1 := (sperp_core hp hs hsN hsp).1

theorem inner_sperp_self {p s : E3} (hp : ‖p‖ = 1) (hs : ‖s‖ = 1) (hsN : s ∈ northern p)
    (hsp : s ≠ p) : ⟪s, sperp p s⟫ = 0 := (sperp_core hp hs hsN hsp).2.1

theorem inner_p_sperp {p s : E3} (hp : ‖p‖ = 1) (hs : ‖s‖ = 1) (hsN : s ∈ northern p)
    (hsp : s ≠ p) : ⟪p, sperp p s⟫ = Real.sqrt (1 - ⟪p, s⟫ ^ 2) := (sperp_core hp hs hsN hsp).2.2

theorem sperp_mem_northern {p s : E3} (hp : ‖p‖ = 1) (hs : ‖s‖ = 1) (hsN : s ∈ northern p)
    (hsp : s ≠ p) : sperp p s ∈ northern p := by
  refine ⟨norm_sperp hp hs hsN hsp, ?_⟩
  rw [inner_p_sperp hp hs hsN hsp]
  exact Real.sqrt_nonneg _

theorem lat_sperp {p s : E3} (hp : ‖p‖ = 1) (hs : ‖s‖ = 1) (hsN : s ∈ northern p) (hsp : s ≠ p) :
    lat p (sperp p s) = 1 - lat p s := by
  have hnn : (0 : ℝ) ≤ 1 - ⟪p, s⟫ ^ 2 := by
    have := lat_le_one p hp hs
    unfold lat at this
    linarith
  unfold lat
  rw [inner_p_sperp hp hs hsN hsp, Real.sq_sqrt hnn]

/-- Cas particulier de vérification : quand `⟪p,s⟫ = 0`, `sperp p s` se réduit à
`p` (le point de l'équateur "évident"). -/
example (p s : E3) (hc : ⟪p, s⟫ = 0) : sperp p s = p := by
  unfold sperp
  rw [hc]
  simp

/-- **B3.** La somme des latitudes sur une base orthonormée vaut `1` (Parseval,
`x = y = p`, puis `real_inner_comm` pour recoller `⟪p,b i⟫²`). -/
theorem sum_lat_eq_one {p : E3} (hp : ‖p‖ = 1) (b : OrthonormalBasis (Fin 3) ℝ E3) :
    ∑ i, lat p (b i) = 1 := by
  have h := b.sum_inner_mul_inner p p
  rw [real_inner_self_eq_norm_sq, hp] at h
  norm_num at h
  unfold lat
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm p (b i)]
  ring

/-- **B4a (lemme-outil).** Complète `sperp p s` et `s` en base orthonormée dont
le 3ᵉ vecteur est sur l'équateur : par B3, `lat(b 0) + lat(b 1) + lat(b 2) = 1`
avec `lat(b 0) = 1 - lat s` (B2) et `lat(b 1) = lat s`, donc `lat(b 2) = 0`. -/
theorem exists_descent_basis {p s : E3} (hp : ‖p‖ = 1) (hs : ‖s‖ = 1) (hsN : s ∈ northern p)
    (hsp : s ≠ p) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ E3, b 0 = sperp p s ∧ b 1 = s ∧ b 2 ∈ equator p := by
  have hortho : ⟪sperp p s, s⟫ = 0 := by
    have h := inner_sperp_self hp hs hsN hsp
    rwa [real_inner_comm (sperp p s) s] at h
  obtain ⟨b, hb0, hb1⟩ :=
    exists_orthonormalBasis_pair (sperp p s) s (norm_sperp hp hs hsN hsp) hs hortho
  have hsum := sum_lat_eq_one hp b
  rw [Fin.sum_univ_three, hb0, hb1, lat_sperp hp hs hsN hsp] at hsum
  have hlat2 : lat p (b 2) = 0 := by linarith
  exact ⟨b, hb0, hb1, (mem_equator_iff_lat_eq_zero p (b 2)).mpr ⟨b.norm_eq_one 2, hlat2⟩⟩

/-- **B4b (corollaire).** Le 3ᵉ vecteur de la base de B4a est à la fois dans le
cercle de descente et sur l'équateur, et orthogonal à `s`. -/
theorem exists_equator_orthogonal {p s : E3} (hp : ‖p‖ = 1) (hs : ‖s‖ = 1)
    (hsN : s ∈ northern p) (hsp : s ≠ p) :
    ∃ u, u ∈ descent p s ∩ equator p ∧ ⟪s, u⟫ = 0 := by
  obtain ⟨b, hb0, hb1, hb2⟩ := exists_descent_basis hp hs hsN hsp
  have hd : ⟪sperp p s, b 2⟫ = 0 := by rw [← hb0]; exact b.inner_eq_zero (by decide)
  have hse : ⟪s, b 2⟫ = 0 := by rw [← hb1]; exact b.inner_eq_zero (by decide)
  exact ⟨b 2, ⟨⟨equator_subset_northern p hb2, hd⟩, hb2⟩, hse⟩

/-- **B5.** `s` est toujours dans son propre cercle de descente. -/
theorem self_mem_descent {p s : E3} (hp : ‖p‖ = 1) (hs : ‖s‖ = 1) (hsN : s ∈ northern p)
    (hsp : s ≠ p) : s ∈ descent p s := by
  refine ⟨hsN, ?_⟩
  have h := inner_sperp_self hp hs hsN hsp
  rwa [real_inner_comm (sperp p s) s] at h

/-- **B6.** Le sommet du cercle de descente est le point de latitude maximale :
`t ∈ descent p s → lat p t ≤ lat p s`. Preuve : Parseval polarisé
(`x=p,y=t`) sur la base de B4a donne `⟪p,t⟫ = ⟪p,s⟫·⟪s,t⟫` (les deux autres
termes s'annulent : `⟪sperp,t⟫=0` par définition de la descente,
`⟪p,b 2⟫=0` par B4a) ; Parseval `x=y=t` donne `⟪s,t⟫² ≤ 1`. -/
theorem lat_le_of_mem_descent {p s t : E3} (hp : ‖p‖ = 1) (hs : ‖s‖ = 1) (hsN : s ∈ northern p)
    (hsp : s ≠ p) (ht : t ∈ descent p s) : lat p t ≤ lat p s := by
  obtain ⟨b, hb0, hb1, hb2⟩ := exists_descent_basis hp hs hsN hsp
  have htd : ⟪sperp p s, t⟫ = 0 := ht.2
  have htN : t ∈ northern p := ht.1
  have hpol := b.sum_inner_mul_inner p t
  rw [Fin.sum_univ_three, hb0, hb1, htd, hb2.2, mul_zero, zero_mul, add_zero, zero_add] at hpol
  have hlat_eq : lat p t = lat p s * ⟪s, t⟫ ^ 2 := by
    unfold lat
    rw [← hpol]
    ring
  have hsum_t := b.sum_sq_inner_right t
  rw [htN.1] at hsum_t
  norm_num at hsum_t
  rw [Fin.sum_univ_three, hb1] at hsum_t
  have hββ : ⟪s, t⟫ ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (⟪b 0, t⟫ : ℝ), sq_nonneg (⟪b 2, t⟫ : ℝ), hsum_t]
  rw [hlat_eq]
  exact mul_le_of_le_one_right (lat_nonneg p s) hββ

/-- **B7.** Réalisabilité des latitudes : pour tout triplet de latitudes
positives sommant à 1, il existe une base orthonormée les réalisant.
Construction sans matrices : `v := √l₁•E0+√l₂•E1+√l₃•E2` (`E` = base standard)
est unitaire ; on transporte `E` par l'isométrie envoyant `v` sur `p`
(composée des représentations de deux bases étendant `v` et `p`). -/
theorem exists_frame_with_lat {p : E3} (hp : ‖p‖ = 1) {l₁ l₂ l₃ : ℝ}
    (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂) (h₃ : 0 ≤ l₃) (hsum : l₁ + l₂ + l₃ = 1) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ E3,
      lat p (b 0) = l₁ ∧ lat p (b 1) = l₂ ∧ lat p (b 2) = l₃ := by
  set E := EuclideanSpace.basisFun (Fin 3) ℝ with hE_def
  set v : E3 := Real.sqrt l₁ • E 0 + Real.sqrt l₂ • E 1 + Real.sqrt l₃ • E 2 with hv_def
  have hE01 : (⟪E 0, E 1⟫ : ℝ) = 0 := E.inner_eq_zero (by decide)
  have hE11 : (⟪E 1, E 1⟫ : ℝ) = 1 := E.inner_eq_one 1
  have hE21 : (⟪E 2, E 1⟫ : ℝ) = 0 := E.inner_eq_zero (by decide)
  have hE00 : (⟪E 0, E 0⟫ : ℝ) = 1 := E.inner_eq_one 0
  have hE10 : (⟪E 1, E 0⟫ : ℝ) = 0 := E.inner_eq_zero (by decide)
  have hE20 : (⟪E 2, E 0⟫ : ℝ) = 0 := E.inner_eq_zero (by decide)
  have hE02 : (⟪E 0, E 2⟫ : ℝ) = 0 := E.inner_eq_zero (by decide)
  have hE12 : (⟪E 1, E 2⟫ : ℝ) = 0 := E.inner_eq_zero (by decide)
  have hE22 : (⟪E 2, E 2⟫ : ℝ) = 1 := E.inner_eq_one 2
  have hv0 : ⟪v, E 0⟫ = Real.sqrt l₁ := by
    rw [hv_def, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_left, hE00, hE10, hE20]
    ring
  have hv1 : ⟪v, E 1⟫ = Real.sqrt l₂ := by
    rw [hv_def, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_left, hE01, hE11, hE21]
    ring
  have hv2 : ⟪v, E 2⟫ = Real.sqrt l₃ := by
    rw [hv_def, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_left, hE02, hE12, hE22]
    ring
  have hvv : ⟪v, v⟫ = l₁ + l₂ + l₃ := by
    nth_rewrite 2 [hv_def]
    rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_smul_right, hv0, hv1, hv2, Real.mul_self_sqrt h₁, Real.mul_self_sqrt h₂,
        Real.mul_self_sqrt h₃]
  have hvnorm : ‖v‖ = 1 := by
    have hsq : ‖v‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hvv, hsum]
    nlinarith [norm_nonneg v, hsq]
  obtain ⟨bᵥ, hbᵥ0⟩ := exists_orthonormalBasis_fst v hvnorm
  obtain ⟨c_p, hc_p0⟩ := exists_orthonormalBasis_fst p hp
  set U : E3 ≃ₗᵢ[ℝ] E3 := bᵥ.repr.trans c_p.repr.symm with hU_def
  have hUv : U v = p := by
    have h1 : bᵥ.repr v = EuclideanSpace.single 0 (1 : ℝ) := by
      conv_lhs => rw [← hbᵥ0]
      exact bᵥ.repr_self 0
    have h2 : c_p.repr (c_p 0) = EuclideanSpace.single 0 (1 : ℝ) := c_p.repr_self 0
    rw [hU_def, LinearIsometryEquiv.trans_apply, h1, ← h2, LinearIsometryEquiv.symm_apply_apply,
        hc_p0]
  set b := E.map U with hb_def
  have hinner : ∀ j, ⟪p, b j⟫ = ⟪v, E j⟫ := by
    intro j
    rw [hb_def, OrthonormalBasis.map_apply, ← hUv, U.inner_map_map]
  refine ⟨b, ?_, ?_, ?_⟩
  · unfold lat; rw [hinner 0, hv0, Real.sq_sqrt h₁]
  · unfold lat; rw [hinner 1, hv1, Real.sq_sqrt h₂]
  · unfold lat; rw [hinner 2, hv2, Real.sq_sqrt h₃]

/- ═══════════════════════════════════════════════════════════════════
   Chaîne de descente de Piron (CKM 1985 §5, PDF p. 123-124, Fig. 1-3).
   Stratégie : paramétrisation explicite `spherePoint b θ ψ` (colatitude θ
   depuis le pôle `b 0`, azimut ψ dans le plan `(b 1, b 2)`), puis
   construction FERMÉE (sans limite ni IVT) d'une chaîne de descente en deux
   phases : ajustement d'azimut (n pas égaux, amplification contrôlée par
   Bernoulli) puis gain de distance pur (2 pas d'azimut opposé).
   ═══════════════════════════════════════════════════════════════════ -/

/-- **E1a.** Point de colatitude `θ` et azimut `ψ` dans la base `b` (pôle `b 0`,
plan équatorial `(b 1, b 2)`). -/
noncomputable def spherePoint (b : OrthonormalBasis (Fin 3) ℝ E3) (θ ψ : ℝ) : E3 :=
  Real.cos θ • b 0 + (Real.sin θ * Real.cos ψ) • b 1 + (Real.sin θ * Real.sin ψ) • b 2

theorem inner_pole_spherePoint (b : OrthonormalBasis (Fin 3) ℝ E3) (θ ψ : ℝ) :
    ⟪b 0, spherePoint b θ ψ⟫ = Real.cos θ := by
  unfold spherePoint
  rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, b.inner_eq_one 0, b.inner_eq_zero (i := 0) (j := 1) (by decide),
      b.inner_eq_zero (i := 0) (j := 2) (by decide)]
  ring

theorem inner_snd_spherePoint (b : OrthonormalBasis (Fin 3) ℝ E3) (θ ψ : ℝ) :
    ⟪b 1, spherePoint b θ ψ⟫ = Real.sin θ * Real.cos ψ := by
  unfold spherePoint
  rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, b.inner_eq_zero (i := 1) (j := 0) (by decide), b.inner_eq_one 1,
      b.inner_eq_zero (i := 1) (j := 2) (by decide)]
  ring

theorem inner_trd_spherePoint (b : OrthonormalBasis (Fin 3) ℝ E3) (θ ψ : ℝ) :
    ⟪b 2, spherePoint b θ ψ⟫ = Real.sin θ * Real.sin ψ := by
  unfold spherePoint
  rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, b.inner_eq_zero (i := 2) (j := 0) (by decide),
      b.inner_eq_zero (i := 2) (j := 1) (by decide), b.inner_eq_one 2]
  ring

theorem norm_spherePoint (b : OrthonormalBasis (Fin 3) ℝ E3) (θ ψ : ℝ) :
    ‖spherePoint b θ ψ‖ = 1 := by
  set v : E3 := spherePoint b θ ψ with hv_def
  have hv0 : ⟪b 0, v⟫ = Real.cos θ := inner_pole_spherePoint b θ ψ
  have hv1 : ⟪b 1, v⟫ = Real.sin θ * Real.cos ψ := inner_snd_spherePoint b θ ψ
  have hv2 : ⟪b 2, v⟫ = Real.sin θ * Real.sin ψ := inner_trd_spherePoint b θ ψ
  have hvv : ⟪v, v⟫ = 1 := by
    nth_rewrite 1 [hv_def]
    unfold spherePoint
    rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_left, hv0, hv1, hv2]
    nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq ψ]
  have hsq : ‖v‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hvv
  nlinarith [norm_nonneg v, hsq]

theorem lat_spherePoint (b : OrthonormalBasis (Fin 3) ℝ E3) (θ ψ : ℝ) :
    lat (b 0) (spherePoint b θ ψ) = Real.cos θ ^ 2 := by
  unfold lat
  rw [inner_pole_spherePoint]

theorem mem_northern_spherePoint (b : OrthonormalBasis (Fin 3) ℝ E3) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ π / 2) (ψ : ℝ) : spherePoint b θ ψ ∈ northern (b 0) := by
  refine ⟨norm_spherePoint b θ ψ, ?_⟩
  rw [inner_pole_spherePoint]
  exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ1⟩

theorem ne_pole_spherePoint (b : OrthonormalBasis (Fin 3) ℝ E3) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ π / 2) (ψ : ℝ) : spherePoint b θ ψ ≠ b 0 := by
  intro heq
  have hsinpos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have h1 : ⟪b 1, spherePoint b θ ψ⟫ = 0 := by rw [heq]; exact b.inner_eq_zero (by decide)
  have h2 : ⟪b 2, spherePoint b θ ψ⟫ = 0 := by rw [heq]; exact b.inner_eq_zero (by decide)
  rw [inner_snd_spherePoint] at h1
  rw [inner_trd_spherePoint] at h2
  have hcosψ : Real.cos ψ = 0 := (mul_eq_zero.mp h1).resolve_left hsinpos.ne'
  have hsinψ : Real.sin ψ = 0 := (mul_eq_zero.mp h2).resolve_left hsinpos.ne'
  have hpyth := Real.sin_sq_add_cos_sq ψ
  rw [hcosψ, hsinψ] at hpyth
  norm_num at hpyth

/-- **E1d (préliminaire).** Norme d'un point purement équatorial (colatitude
`π/2`) exprimé dans le plan `(b 1, b 2)`. -/
theorem norm_equatorial_combo (b : OrthonormalBasis (Fin 3) ℝ E3) (ψ : ℝ) :
    ‖Real.cos ψ • b 1 + Real.sin ψ • b 2‖ = 1 := by
  have hb11 : (⟪b 1, b 1⟫ : ℝ) = 1 := b.inner_eq_one 1
  have hb22 : (⟪b 2, b 2⟫ : ℝ) = 1 := b.inner_eq_one 2
  have hb12 : (⟪b 1, b 2⟫ : ℝ) = 0 := b.inner_eq_zero (by decide)
  have hb21 : (⟪b 2, b 1⟫ : ℝ) = 0 := b.inner_eq_zero (by decide)
  set w : E3 := Real.cos ψ • b 1 + Real.sin ψ • b 2 with hw_def
  have hw1 : ⟪b 1, w⟫ = Real.cos ψ := by
    rw [hw_def, inner_add_right, real_inner_smul_right, real_inner_smul_right, hb11, hb12]
    ring
  have hw2 : ⟪b 2, w⟫ = Real.sin ψ := by
    rw [hw_def, inner_add_right, real_inner_smul_right, real_inner_smul_right, hb21, hb22]
    ring
  have hww : ⟪w, w⟫ = 1 := by
    nth_rewrite 1 [hw_def]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hw1, hw2]
    nlinarith [Real.sin_sq_add_cos_sq ψ]
  have hsq : ‖w‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hww
  nlinarith [norm_nonneg w, hsq]

/-- **E1d.** `sperp` d'un point de colatitude `θ ∈ (0, π/2]` : le point de
l'équateur diamétralement opposé dans le plan `(pôle, point)`, exprimé dans
la base `(b 0, b 1, b 2)`. -/
theorem sperp_spherePoint (b : OrthonormalBasis (Fin 3) ℝ E3) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ π / 2) (ψ : ℝ) :
    sperp (b 0) (spherePoint b θ ψ) =
      Real.sin θ • b 0 - Real.cos θ • (Real.cos ψ • b 1 + Real.sin ψ • b 2) := by
  have hsinpos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hcs : ⟪b 0, spherePoint b θ ψ⟫ = Real.cos θ := inner_pole_spherePoint b θ ψ
  have hdecomp : spherePoint b θ ψ - Real.cos θ • b 0 =
      Real.sin θ • (Real.cos ψ • b 1 + Real.sin ψ • b 2) := by
    unfold spherePoint
    module
  have hnormw : ‖spherePoint b θ ψ - Real.cos θ • b 0‖ = Real.sin θ := by
    rw [hdecomp, norm_smul, norm_equatorial_combo, mul_one, Real.norm_eq_abs,
        abs_of_pos hsinpos]
  have hsqrt : Real.sqrt (1 - Real.cos θ ^ 2) = Real.sin θ := by
    rw [show (1 : ℝ) - Real.cos θ ^ 2 = Real.sin θ ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ]]
    exact Real.sqrt_sq hsinpos.le
  unfold sperp
  rw [hcs, hnormw, hsqrt, hdecomp, smul_smul, smul_smul]
  have hscalar : Real.cos θ * (Real.sin θ)⁻¹ * Real.sin θ = Real.cos θ := by
    field_simp
  rw [hscalar]

/-- **E1d (critère de pas).** `spherePoint b θ' ψ'` est dans le cercle de
descente de `spherePoint b θ ψ` (autour du pôle `b 0`) ssi l'identité
trigonométrique suivante est vérifiée. Calcul direct de
`⟪sperp (b0) (spherePoint b θ ψ), spherePoint b θ' ψ'⟫` via `sperp_spherePoint`
et les formules `inner_*_spherePoint`. -/
theorem spherePoint_mem_descent_iff (b : OrthonormalBasis (Fin 3) ℝ E3) {θ θ' : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ π / 2) (hθ'0 : 0 ≤ θ') (hθ'1 : θ' ≤ π / 2) (ψ ψ' : ℝ) :
    spherePoint b θ' ψ' ∈ descent (b 0) (spherePoint b θ ψ) ↔
      Real.sin θ * Real.cos θ' = Real.cos θ * Real.sin θ' * Real.cos (ψ' - ψ) := by
  have hmemN : spherePoint b θ' ψ' ∈ northern (b 0) := mem_northern_spherePoint b hθ'0 hθ'1 ψ'
  have hexpand : ⟪sperp (b 0) (spherePoint b θ ψ), spherePoint b θ' ψ'⟫ =
      Real.sin θ * Real.cos θ' - Real.cos θ * Real.sin θ' * Real.cos (ψ' - ψ) := by
    rw [sperp_spherePoint b hθ0 hθ1 ψ, Real.cos_sub]
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, inner_add_left,
        real_inner_smul_left, real_inner_smul_left, inner_pole_spherePoint,
        inner_snd_spherePoint, inner_trd_spherePoint]
    ring
  rw [mem_descent_iff]
  constructor
  · rintro ⟨_, h⟩
    rw [hexpand] at h
    linarith
  · intro h
    refine ⟨hmemN, ?_⟩
    rw [hexpand]
    linarith

/-- **E1c.** Tout vecteur unitaire de `northern (b 0) \ {b 0}` s'exprime en
coordonnées sphériques dans la base `b`. Décomposition polaire de la
projection sur `(b 1, b 2)` via `Complex.arg` (aucun lemme Mathlib direct
« a²+b²=1 → ∃ψ, cosψ=a∧sinψ=b » : détour par `Complex.mk`/`normSq`). -/
theorem exists_sphereCoords (b : OrthonormalBasis (Fin 3) ℝ E3) {t : E3}
    (ht : ‖t‖ = 1) (htN : t ∈ northern (b 0)) (htp : t ≠ b 0) :
    ∃ θ ψ : ℝ, 0 < θ ∧ θ ≤ π / 2 ∧ t = spherePoint b θ ψ := by
  set c : ℝ := ⟪b 0, t⟫ with hc_def
  have hc0 : 0 ≤ c := htN.2
  have hc1 : c ≤ 1 := by
    have h := abs_real_inner_le_norm (b 0) t
    rw [b.norm_eq_one 0, ht, mul_one] at h
    exact (abs_le.mp h).2
  have hcne1 : c ≠ 1 := by
    intro heq
    apply htp
    have hns : ‖t - c • b 0‖ ^ 2 = 1 - c ^ 2 := norm_sq_sub_inner_smul (b.norm_eq_one 0) ht
    rw [heq, one_smul] at hns
    norm_num at hns
    exact sub_eq_zero.mp hns
  set θ : ℝ := Real.arccos c with hθ_def
  have hθ0 : 0 < θ := by rw [hθ_def]; exact Real.arccos_pos.mpr (lt_of_le_of_ne hc1 hcne1)
  have hθ1 : θ ≤ π / 2 := by rw [hθ_def]; exact Real.arccos_le_pi_div_two.mpr hc0
  have hcosθ : Real.cos θ = c := Real.cos_arccos (by linarith) hc1
  have hsinθnn : Real.sin θ = Real.sqrt (1 - c ^ 2) := by rw [hθ_def]; exact Real.sin_arccos c
  have hsinθpos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  set w : E3 := t - c • b 0 with hw_def
  have hw0 : ⟪b 0, w⟫ = 0 := by
    rw [hw_def, inner_sub_right, real_inner_smul_right, b.inner_eq_one 0, ← hc_def]
    ring
  have hwsq : ‖w‖ ^ 2 = Real.sin θ ^ 2 := by
    rw [hw_def, hc_def, norm_sq_sub_inner_smul (b.norm_eq_one 0) ht, ← hc_def, hsinθnn,
        Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - c ^ 2)]
  have hwnorm : ‖w‖ = Real.sin θ := by
    have heq0 : (‖w‖ - Real.sin θ) * (‖w‖ + Real.sin θ) = 0 := by linear_combination hwsq
    rcases mul_eq_zero.mp heq0 with h | h
    · linarith
    · linarith [norm_nonneg w]
  have hwne : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hwnorm
    linarith
  have hdecomp_w : ⟪b 1, w⟫ • b 1 + ⟪b 2, w⟫ • b 2 = w := by
    have h := b.sum_repr' w
    rw [Fin.sum_univ_three, hw0, zero_smul, zero_add] at h
    exact h
  have hw_sq_decomp : ‖w‖ ^ 2 = ⟪b 1, w⟫ ^ 2 + ⟪b 2, w⟫ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rewrite 1 [← hdecomp_w]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  have hwnn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hwne
  set a : ℝ := ⟪b 1, w⟫ / ‖w‖ with ha_def
  set d : ℝ := ⟪b 2, w⟫ / ‖w‖ with hd_def
  have had : a ^ 2 + d ^ 2 = 1 := by
    have hstep : a ^ 2 + d ^ 2 = (⟪b 1, w⟫ ^ 2 + ⟪b 2, w⟫ ^ 2) / ‖w‖ ^ 2 := by
      rw [ha_def, hd_def, div_pow, div_pow]; ring
    rw [hstep, ← hw_sq_decomp, div_self (pow_ne_zero 2 hwnn)]
  set z : ℂ := ⟨a, d⟩ with hz_def
  have hnormSqz : Complex.normSq z = 1 := by
    rw [hz_def, Complex.normSq_mk]
    nlinarith [had]
  have hzne : z ≠ 0 := by
    intro h
    rw [h, map_zero] at hnormSqz
    norm_num at hnormSqz
  have hzabs : ‖z‖ = 1 := by
    have hsq : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact hnormSqz
    have heq0 : (‖z‖ - 1) * (‖z‖ + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp heq0 with h | h
    · linarith
    · linarith [norm_nonneg z]
  set ψ : ℝ := Complex.arg z with hψ_def
  have hcosψ : Real.cos ψ = a := by
    rw [hψ_def, Complex.cos_arg hzne, hzabs, div_one]
  have hsinψ : Real.sin ψ = d := by
    rw [hψ_def, Complex.sin_arg, hzabs, div_one]
  refine ⟨θ, ψ, hθ0, hθ1, ?_⟩
  unfold spherePoint
  rw [hcosθ, hsinθnn, hcosψ, hsinψ, ha_def, hd_def]
  have h1 : Real.sqrt (1 - c ^ 2) * (⟪b 1, w⟫ / ‖w‖) = ⟪b 1, w⟫ := by
    rw [← hsinθnn, hwnorm]; field_simp
  have h2 : Real.sqrt (1 - c ^ 2) * (⟪b 2, w⟫ / ‖w‖) = ⟪b 2, w⟫ := by
    rw [← hsinθnn, hwnorm]; field_simp
  rw [h1, h2, add_assoc, hdecomp_w, hw_def]
  abel

/-- **E3 (lemme de pas générique).** Formulation en `tan` du critère de
descente : pour `θ, θ' ∈ (0, π/2)`, si `tan θ' · cos(ψ'-ψ) = tan θ`, alors
`spherePoint b θ' ψ'` est dans le cercle de descente de `spherePoint b θ ψ`.
Se réduit à une tautologie pour les pas de la phase A de E4 (ajustement
d'azimut à rapport de distance constant). -/
theorem spherePoint_mem_descent_of_tan (b : OrthonormalBasis (Fin 3) ℝ E3) {θ θ' : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < π / 2) (hθ'0 : 0 < θ') (hθ'1 : θ' < π / 2) (ψ ψ' : ℝ)
    (htan : Real.tan θ' * Real.cos (ψ' - ψ) = Real.tan θ) :
    spherePoint b θ' ψ' ∈ descent (b 0) (spherePoint b θ ψ) := by
  have hcosθpos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
  have hcosθ'pos : 0 < Real.cos θ' := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ'1⟩
  rw [spherePoint_mem_descent_iff b hθ0 hθ1.le hθ'0.le hθ'1.le]
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos] at htan
  field_simp at htan
  linarith [htan]

/-- **E4 équatorial (pas terminal).** `spherePoint b (π/2) (ψ+π/2)` (un point de
l'équateur) est dans le cercle de descente de `spherePoint b θ ψ`, pour tout
`θ ∈ (0, π/2)`. Le critère se réduit à `0 = 0` (`cos(π/2) = 0` des deux côtés). -/
theorem spherePoint_mem_descent_equatorial (b : OrthonormalBasis (Fin 3) ℝ E3) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < π / 2) (ψ : ℝ) :
    spherePoint b (π / 2) (ψ + π / 2) ∈ descent (b 0) (spherePoint b θ ψ) := by
  rw [spherePoint_mem_descent_iff b hθ0 hθ1.le (by linarith [Real.pi_pos]) le_rfl]
  simp

/-- **E4 (lemme-outil, réutilisé pour les phases A et B).** Une suite de rayons
`radius i > 0` et d'azimuts `azimuth i` satisfaisant la relation de pas
(`radius (i+1) · cos(Δazimut) = radius i`, i.e. `tan θᵢ₊₁ · cos(Δψ) = tan θᵢ`
une fois passée par `arctan`) produit, point par point, une chaîne de
descente valide via `spherePoint_mem_descent_of_tan`. -/
theorem tan_chain_step (b : OrthonormalBasis (Fin 3) ℝ E3) (radius azimuth : ℕ → ℝ)
    (hradius_pos : ∀ i, 0 < radius i) {N : ℕ}
    (hstep : ∀ i < N, radius (i + 1) * Real.cos (azimuth (i + 1) - azimuth i) = radius i) :
    ∀ i < N, spherePoint b (Real.arctan (radius i)) (azimuth i) ≠ b 0 ∧
      spherePoint b (Real.arctan (radius (i + 1))) (azimuth (i + 1)) ∈
        descent (b 0) (spherePoint b (Real.arctan (radius i)) (azimuth i)) := by
  intro i hi
  have hθi0 : 0 < Real.arctan (radius i) := Real.arctan_pos.mpr (hradius_pos i)
  have hθi1 : Real.arctan (radius i) < π / 2 := Real.arctan_lt_pi_div_two _
  have hθi1'0 : 0 < Real.arctan (radius (i + 1)) := Real.arctan_pos.mpr (hradius_pos (i + 1))
  have hθi1'1 : Real.arctan (radius (i + 1)) < π / 2 := Real.arctan_lt_pi_div_two _
  refine ⟨ne_pole_spherePoint b hθi0 hθi1.le _, ?_⟩
  apply spherePoint_mem_descent_of_tan b hθi0 hθi1 hθi1'0 hθi1'1
  rw [Real.tan_arctan, Real.tan_arctan]
  exact hstep i hi

end
end Gleason
