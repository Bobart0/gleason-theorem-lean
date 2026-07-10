import Gleason.Real3.ExactPole

/-!
# Attention des valeurs extrémales (CKM 1985 §6, PDF p. 125-126)

`frameFunction_attains_sup`/`frameFunction_attains_inf` : toute frame function
BORNÉE (pas nécessairement positive : le bloc H l'appliquera à des différences
`g - f`) atteint son sup et son inf sur la sphère. Preuve par ultrafiltre
(l'espace produit `[2m,2M]^S` n'est pas métrisable, donc pas de sous-suites) :
limite `p` d'une suite maximisante le long d'un ultrafiltre, symétrisation par
rotation 90°, recentrage par isométrie, passage à la limite le long de
l'ultrafiltre de la forme quadratique exacte (bloc F), puis descente radiale
à 2 pas pour contredire une éventuelle perte de masse en `p`.
-/

namespace Gleason

open scoped RealInnerProductSpace Real

noncomputable section

/- ═══════════════════════════════════════════════════════════════════
   G1. Boîte à outils isométries (réutilisable par le bloc H).
   ═══════════════════════════════════════════════════════════════════ -/

/-- **G1a.** Deux triplets orthonormés se correspondent par une isométrie
linéaire de `E3` : bases orthonormées prescrites (`exists_orthonormalBasis_of_triple'`)
des deux côtés, puis composition des représentations (`repr.trans repr.symm`),
même technique que dans `exists_frame_with_lat` (B7). -/
theorem isometry_of_orthonormal_triples {a0 a1 a2 b0 b1 b2 : E3}
    (ha0 : ‖a0‖ = 1) (ha1 : ‖a1‖ = 1) (ha2 : ‖a2‖ = 1)
    (ha01 : ⟪a0, a1⟫ = 0) (ha02 : ⟪a0, a2⟫ = 0) (ha12 : ⟪a1, a2⟫ = 0)
    (hb0 : ‖b0‖ = 1) (hb1 : ‖b1‖ = 1) (hb2 : ‖b2‖ = 1)
    (hb01 : ⟪b0, b1⟫ = 0) (hb02 : ⟪b0, b2⟫ = 0) (hb12 : ⟪b1, b2⟫ = 0) :
    ∃ ρ : E3 ≃ₗᵢ[ℝ] E3, ρ a0 = b0 ∧ ρ a1 = b1 ∧ ρ a2 = b2 := by
  obtain ⟨a, ha0', ha1', ha2'⟩ :=
    exists_orthonormalBasis_of_triple' a0 a1 a2 ha0 ha1 ha2 ha01 ha02 ha12
  obtain ⟨b, hb0', hb1', hb2'⟩ :=
    exists_orthonormalBasis_of_triple' b0 b1 b2 hb0 hb1 hb2 hb01 hb02 hb12
  set ρ : E3 ≃ₗᵢ[ℝ] E3 := a.repr.trans b.repr.symm with hρ_def
  have key : ∀ i : Fin 3, ρ (a i) = b i := by
    intro i
    have h1 : a.repr (a i) = EuclideanSpace.single i (1 : ℝ) := a.repr_self i
    have h2 : b.repr (b i) = EuclideanSpace.single i (1 : ℝ) := b.repr_self i
    rw [hρ_def, LinearIsometryEquiv.trans_apply, h1, ← h2, LinearIsometryEquiv.symm_apply_apply]
  exact ⟨ρ, by rw [← ha0', key 0, hb0'], by rw [← ha1', key 1, hb1'], by rw [← ha2', key 2, hb2']⟩

/-- **G1a' (variante paire, outil interne).** Même énoncé pour une paire
orthonormée, via `exists_orthonormalBasis_pair`. -/
theorem isometry_of_orthonormal_pair {a0 a1 b0 b1 : E3}
    (ha0 : ‖a0‖ = 1) (ha1 : ‖a1‖ = 1) (ha01 : ⟪a0, a1⟫ = 0)
    (hb0 : ‖b0‖ = 1) (hb1 : ‖b1‖ = 1) (hb01 : ⟪b0, b1⟫ = 0) :
    ∃ ρ : E3 ≃ₗᵢ[ℝ] E3, ρ a0 = b0 ∧ ρ a1 = b1 := by
  obtain ⟨a, ha0', ha1'⟩ := exists_orthonormalBasis_pair a0 a1 ha0 ha1 ha01
  obtain ⟨b, hb0', hb1'⟩ := exists_orthonormalBasis_pair b0 b1 hb0 hb1 hb01
  set ρ : E3 ≃ₗᵢ[ℝ] E3 := a.repr.trans b.repr.symm with hρ_def
  have key : ∀ i : Fin 3, ρ (a i) = b i := by
    intro i
    have h1 : a.repr (a i) = EuclideanSpace.single i (1 : ℝ) := a.repr_self i
    have h2 : b.repr (b i) = EuclideanSpace.single i (1 : ℝ) := b.repr_self i
    rw [hρ_def, LinearIsometryEquiv.trans_apply, h1, ← h2, LinearIsometryEquiv.symm_apply_apply]
  exact ⟨ρ, by rw [← ha0', key 0, hb0'], by rw [← ha1', key 1, hb1']⟩

/-- **G1a'' (unitaire simple, outil interne).** Un seul vecteur : cas
dégénéré de G1a' (`exists_orthonormalBasis_fst` des deux côtés). -/
theorem exists_isometry_of_unit {x y : E3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∃ ρ : E3 ≃ₗᵢ[ℝ] E3, ρ x = y := by
  obtain ⟨a, ha0⟩ := exists_orthonormalBasis_fst x hx
  obtain ⟨b, hb0⟩ := exists_orthonormalBasis_fst y hy
  set ρ : E3 ≃ₗᵢ[ℝ] E3 := a.repr.trans b.repr.symm with hρ_def
  have h1 : a.repr (a 0) = EuclideanSpace.single 0 (1 : ℝ) := a.repr_self 0
  have h2 : b.repr (b 0) = EuclideanSpace.single 0 (1 : ℝ) := b.repr_self 0
  exact ⟨ρ, by rw [← ha0, hρ_def, LinearIsometryEquiv.trans_apply, h1, ← h2,
    LinearIsometryEquiv.symm_apply_apply, hb0]⟩

/-- **G1b.** Deux paires de vecteurs unitaires de même produit scalaire se
correspondent par une isométrie. Cas `c² = 1` (colinéaire) : `u2 = c•u1` et
`v2 = c•v1` par annulation de `norm_sq_sub_inner_smul` (égalité de
Cauchy-Schwarz, dérivée directement plutôt que via un lemme Mathlib nommé),
toute isométrie envoyant `u1` sur `v1` convient (linéarité). Cas `c² < 1` :
résidus de Gram-Schmidt `u2' := ‖u2-c•u1‖⁻¹•(u2-c•u1)`, `v2'` idem,
`isometry_of_orthonormal_pair` sur `(u1,u2')`/`(v1,v2')`, puis
`ρu2 = ρ(c•u1+√(1-c²)•u2') = c•v1+√(1-c²)•v2' = v2` par linéarité de `ρ`. -/
theorem exists_isometry_pair {u1 u2 v1 v2 : E3}
    (hu1 : ‖u1‖ = 1) (hu2 : ‖u2‖ = 1) (hv1 : ‖v1‖ = 1) (hv2 : ‖v2‖ = 1)
    (hc : ⟪u1, u2⟫ = ⟪v1, v2⟫) :
    ∃ ρ : E3 ≃ₗᵢ[ℝ] E3, ρ u1 = v1 ∧ ρ u2 = v2 := by
  set c : ℝ := ⟪u1, u2⟫ with hc_def
  have hcv : c = ⟪v1, v2⟫ := hc_def.trans hc
  have hc2le1 : c ^ 2 ≤ 1 := by
    have h := abs_real_inner_le_norm u1 u2
    rw [hu1, hu2, mul_one] at h
    nlinarith [abs_le.mp h]
  have collinear : ∀ {x y : E3}, ‖x‖ = 1 → ‖y‖ = 1 → ⟪x, y⟫ ^ 2 = 1 → y = ⟪x, y⟫ • x := by
    intro x y hx hy hxy2
    have hnormsq : ‖y - ⟪x, y⟫ • x‖ ^ 2 = 0 := by rw [norm_sq_sub_inner_smul hx hy, hxy2]; ring
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnormsq))
  rcases hc2le1.eq_or_lt with hc2eq | hc2lt
  · have hu2eq : u2 = ⟪u1, u2⟫ • u1 := collinear hu1 hu2 (hc_def ▸ hc2eq)
    have hv2eq : v2 = ⟪v1, v2⟫ • v1 := collinear hv1 hv2 (hcv ▸ hc2eq)
    obtain ⟨ρ, hρ⟩ := exists_isometry_of_unit hu1 hv1
    refine ⟨ρ, hρ, ?_⟩
    rw [hu2eq, ρ.map_smul, hρ, ← hc_def, hc, ← hv2eq]
  · set r : ℝ := ‖u2 - c • u1‖ with hr_def
    have hnormsq_u : r ^ 2 = 1 - c ^ 2 := by rw [hr_def]; exact norm_sq_sub_inner_smul hu1 hu2
    have hrpos : 0 < r := by
      have hr2pos : 0 < r ^ 2 := by rw [hnormsq_u]; linarith
      have hrnn : 0 ≤ r := hr_def ▸ norm_nonneg _
      rcases hrnn.eq_or_lt with h | h
      · exfalso; rw [← h] at hr2pos; norm_num at hr2pos
      · exact h
    set u2' : E3 := r⁻¹ • (u2 - c • u1) with hu2'_def
    have hu2'norm : ‖u2'‖ = 1 := by
      rw [hu2'_def, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hrpos, ← hr_def]
      exact inv_mul_cancel₀ hrpos.ne'
    have hu1u2'_orth : ⟪u1, u2'⟫ = 0 := by
      rw [hu2'_def, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hu1, ← hc_def]
      ring
    have hu2_decomp : u2 = c • u1 + r • u2' := by
      rw [hu2'_def, smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
      abel
    set r' : ℝ := ‖v2 - c • v1‖ with hr'_def
    have hnormsq_v : r' ^ 2 = 1 - c ^ 2 := by
      have h := norm_sq_sub_inner_smul hv1 hv2
      rw [← hcv] at h
      rw [hr'_def]; exact h
    have hr'r : r' = r := by
      have heq2 : r' ^ 2 = r ^ 2 := by rw [hnormsq_v, hnormsq_u]
      have hr'nn : 0 ≤ r' := norm_nonneg _
      have hrnn : 0 ≤ r := norm_nonneg _
      nlinarith [heq2, hr'nn, hrnn]
    have hr'pos : 0 < r' := hr'r ▸ hrpos
    set v2' : E3 := r'⁻¹ • (v2 - c • v1) with hv2'_def
    have hv2'norm : ‖v2'‖ = 1 := by
      rw [hv2'_def, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr'pos, ← hr'_def]
      exact inv_mul_cancel₀ hr'pos.ne'
    have hv1v2'_orth : ⟪v1, v2'⟫ = 0 := by
      rw [hv2'_def, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hv1, ← hcv]
      ring
    have hv2_decomp : v2 = c • v1 + r' • v2' := by
      rw [hv2'_def, smul_smul, mul_inv_cancel₀ hr'pos.ne', one_smul]
      abel
    obtain ⟨ρ, hρ1, hρ2⟩ := isometry_of_orthonormal_pair hu1 hu2'norm hu1u2'_orth
      hv1 hv2'norm hv1v2'_orth
    refine ⟨ρ, hρ1, ?_⟩
    rw [hu2_decomp, ρ.map_add, ρ.map_smul, ρ.map_smul, hρ1, hρ2, ← hr'r, ← hv2_decomp]

/-- **G1c.** `f ∘ ρ` (pour `ρ` une isométrie linéaire) est une frame function
du même poids : l'image d'une base orthonormée par `ρ` en est une
(`OrthonormalBasis.map`). -/
theorem IsFrameFunction.comp_isometry {f : E3 → ℝ} {W : ℝ} (hf : IsFrameFunction f W)
    (ρ : E3 ≃ₗᵢ[ℝ] E3) : IsFrameFunction (f ∘ ρ) W := by
  intro b
  have h := hf (b.map ρ)
  simpa [Function.comp, OrthonormalBasis.map_apply] using h

/-- **G1d.** Somme, négation et constante de frame functions. -/
theorem IsFrameFunction.add {f g : E3 → ℝ} {Wf Wg : ℝ}
    (hf : IsFrameFunction f Wf) (hg : IsFrameFunction g Wg) :
    IsFrameFunction (fun x => f x + g x) (Wf + Wg) := by
  intro b
  have h1 := hf b
  have h2 := hg b
  rw [Fin.sum_univ_three] at h1 h2 ⊢
  linarith

theorem IsFrameFunction.neg {f : E3 → ℝ} {W : ℝ} (hf : IsFrameFunction f W) :
    IsFrameFunction (fun x => -f x) (-W) := by
  intro b
  have h := hf b
  rw [Fin.sum_univ_three] at h ⊢
  linarith

theorem IsFrameFunction.const (c : ℝ) : IsFrameFunction (fun _ => c) (3 * c) := by
  intro b
  rw [Fin.sum_univ_three]
  ring

theorem IsFrameFunction.sub {f g : E3 → ℝ} {Wf Wg : ℝ}
    (hf : IsFrameFunction f Wf) (hg : IsFrameFunction g Wg) :
    IsFrameFunction (fun x => f x - g x) (Wf - Wg) := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

/- ═══════════════════════════════════════════════════════════════════
   G2. Rotation de 90° autour du pôle.
   ═══════════════════════════════════════════════════════════════════ -/

/-- **G2.** Isométrie de rotation de 90° autour de `p` : complète `p` en base
`(p,u1,u2)`, envoie `(p,u1,u2) ↦ (p,u2,-u1)` (G1a). Fixe `p` ; envoie
l'équateur de `p` dans lui-même ; pour `s` sur l'équateur, `s` et son image
sont orthogonaux (décomposition `s = ⟪u1,s⟫•u1+⟪u2,s⟫•u2`, image
`⟪u1,s⟫•u2-⟪u2,s⟫•u1`, produit scalaire croisé nul par `⟪u1,u2⟫=0` et
normes unitaires). `u1` (renommé `e0` par G3) est exposé pour que le
recentrage de G3 et la descente de G8/G9 travaillent dans le même plan
méridien que la rotation. -/
theorem exists_rotate90 {p : E3} (hp : ‖p‖ = 1) :
    ∃ (phat : E3 ≃ₗᵢ[ℝ] E3) (u1 u2 : E3), ‖u1‖ = 1 ∧ ‖u2‖ = 1 ∧
      ⟪p, u1⟫ = 0 ∧ ⟪p, u2⟫ = 0 ∧ ⟪u1, u2⟫ = 0 ∧
      phat p = p ∧ phat u1 = u2 ∧ phat u2 = -u1 ∧
      ∀ s ∈ equator p, phat s ∈ equator p ∧ ⟪s, phat s⟫ = 0 := by
  obtain ⟨b, hb0⟩ := exists_orthonormalBasis_fst p hp
  set u1 : E3 := b 1 with hu1_def
  set u2 : E3 := b 2 with hu2_def
  have hu1 : ‖u1‖ = 1 := b.norm_eq_one 1
  have hu2 : ‖u2‖ = 1 := b.norm_eq_one 2
  have hpu1 : ⟪p, u1⟫ = 0 := by rw [← hb0]; exact b.inner_eq_zero (by decide)
  have hpu2 : ⟪p, u2⟫ = 0 := by rw [← hb0]; exact b.inner_eq_zero (by decide)
  have hu1u2 : ⟪u1, u2⟫ = 0 := b.inner_eq_zero (by decide)
  have hu2u1 : ⟪u2, u1⟫ = 0 := by rw [real_inner_comm]; exact hu1u2
  have hpu1_neg : ⟪p, -u1⟫ = 0 := by rw [inner_neg_right, hpu1, neg_zero]
  have hu2u1_neg : ⟪u2, -u1⟫ = 0 := by rw [inner_neg_right, hu2u1, neg_zero]
  have hnegu1 : ‖(-u1 : E3)‖ = 1 := by rw [norm_neg]; exact hu1
  obtain ⟨ρ, hρp, hρu1, hρu2⟩ := isometry_of_orthonormal_triples hp hu1 hu2 hpu1 hpu2 hu1u2
    hp hu2 hnegu1 hpu2 hpu1_neg hu2u1_neg
  refine ⟨ρ, u1, u2, hu1, hu2, hpu1, hpu2, hu1u2, hρp, hρu1, hρu2, ?_⟩
  intro s hs
  have hsu : ‖s‖ = 1 := hs.1
  have hsp : ⟪p, s⟫ = 0 := hs.2
  have hpsnorm : ‖ρ s‖ = 1 := by rw [ρ.norm_map]; exact hsu
  have hpsp : ⟪p, ρ s⟫ = 0 := by rw [← hρp, ρ.inner_map_map]; exact hsp
  refine ⟨⟨hpsnorm, hpsp⟩, ?_⟩
  have hdecomp : ⟪u1, s⟫ • u1 + ⟪u2, s⟫ • u2 = s := by
    have h := b.sum_repr' s
    rw [Fin.sum_univ_three, hb0, hsp, zero_smul, zero_add, ← hu1_def, ← hu2_def] at h
    exact h
  set a : ℝ := ⟪u1, s⟫ with ha_def
  set d : ℝ := ⟪u2, s⟫ with hd_def
  have hrhos : ρ s = a • u2 - d • u1 := by
    rw [← hdecomp, ρ.map_add, ρ.map_smul, ρ.map_smul, hρu1, hρu2, smul_neg]
    abel
  rw [hrhos, ← hdecomp]
  simp only [inner_add_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hu1, hu2, hu1u2, hu2u1]
  ring

/- ═══════════════════════════════════════════════════════════════════
   G3. Recentrage.
   ═══════════════════════════════════════════════════════════════════ -/

/-- **G3 (définition).** Point du méridien `(p,e0)` de latitude (signée) `c'`. -/
def recenter (p e0 : E3) (c' : ℝ) : E3 := c' • p + Real.sqrt (1 - c' ^ 2) • e0

/-- **G3.** `recenter p e0 c'` est unitaire, de produit scalaire `c'` avec `p`,
pour `c' ∈ [0,1]` (le radicande `1-c'²` est alors `≥ 0`). -/
theorem recenter_prop {p e0 : E3} (hp : ‖p‖ = 1) (he0 : ‖e0‖ = 1) (hpe0 : ⟪p, e0⟫ = 0)
    {c' : ℝ} (hc'0 : 0 ≤ c') (hc'1 : c' ≤ 1) :
    ‖recenter p e0 c'‖ = 1 ∧ ⟪p, recenter p e0 c'⟫ = c' := by
  have hnn : (0 : ℝ) ≤ 1 - c' ^ 2 := by nlinarith
  have hinner : ⟪p, recenter p e0 c'⟫ = c' := by
    unfold recenter
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hpe0, mul_zero, add_zero,
      real_inner_self_eq_norm_sq, hp]
    ring
  refine ⟨?_, hinner⟩
  have hsq : ‖recenter p e0 c'‖ ^ 2 = 1 := by
    unfold recenter
    rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, hpe0, mul_zero, mul_zero]
    have h1 : ‖c' • p‖ ^ 2 = c' ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hp]; ring
    have h2 : ‖Real.sqrt (1 - c' ^ 2) • e0‖ ^ 2 = 1 - c' ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, he0, Real.sq_sqrt hnn]; ring
    rw [h1, h2]
    ring
  have heq0 : (‖recenter p e0 c'‖ - 1) * (‖recenter p e0 c'‖ + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp heq0 with h | h
  · linarith
  · linarith [norm_nonneg (recenter p e0 c')]

/-- **G3.** `recenter p e0 c'` est dans `northern p`, de latitude `c'²`. -/
theorem recenter_northern {p e0 : E3} (hp : ‖p‖ = 1) (he0 : ‖e0‖ = 1) (hpe0 : ⟪p, e0⟫ = 0)
    {c' : ℝ} (hc'0 : 0 ≤ c') (hc'1 : c' ≤ 1) :
    recenter p e0 c' ∈ northern p ∧ lat p (recenter p e0 c') = c' ^ 2 := by
  obtain ⟨hn, hi⟩ := recenter_prop hp he0 hpe0 hc'0 hc'1
  refine ⟨⟨hn, by rw [hi]; exact hc'0⟩, ?_⟩
  unfold lat; rw [hi]

/-- **G3 (assemblage).** Pour `q` unitaire avec `⟪p,q⟫ ∈ [0,1]`, il existe une
isométrie envoyant `recenter p e0 ⟪p,q⟫` sur `p` et `p` sur `q` :
`⟪recenter c', p⟫ = c' = ⟪p,q⟫` (G3, `real_inner_comm`), puis G1b. -/
theorem exists_recenter_isometry {p e0 q : E3} (hp : ‖p‖ = 1) (he0 : ‖e0‖ = 1)
    (hpe0 : ⟪p, e0⟫ = 0) (hq : ‖q‖ = 1) (hc'0 : 0 ≤ ⟪p, q⟫) :
    ∃ ρ : E3 ≃ₗᵢ[ℝ] E3, ρ (recenter p e0 ⟪p, q⟫) = p ∧ ρ p = q := by
  have hc'1 : ⟪p, q⟫ ≤ 1 := by
    have h := abs_real_inner_le_norm p q
    rw [hp, hq, mul_one] at h
    exact (abs_le.mp h).2
  obtain ⟨hrn, hri⟩ := recenter_prop hp he0 hpe0 hc'0 hc'1
  have hcomm : ⟪recenter p e0 ⟪p, q⟫, p⟫ = ⟪p, q⟫ := by rw [real_inner_comm]; exact hri
  exact exists_isometry_pair hrn hp hp hq hcomm

/- ═══════════════════════════════════════════════════════════════════
   G4. Symétrisation par la rotation de 90°.
   ═══════════════════════════════════════════════════════════════════ -/

/-- **G4a.** `g + g∘phat` est une frame function de poids `2W` (G1c + G1d). -/
theorem symmetrize_frame {g : E3 → ℝ} {W : ℝ} (hg : IsFrameFunction g W)
    (phat : E3 ≃ₗᵢ[ℝ] E3) : IsFrameFunction (fun x => g x + g (phat x)) (2 * W) := by
  have h2 : IsFrameFunction (fun x => g x + (g ∘ phat) x) (W + W) :=
    hg.add (hg.comp_isometry phat)
  have hWW : (2 : ℝ) * W = W + W := by ring
  rwa [hWW]

/-- **G4b.** Bornes héritées : `phat` préserve la norme. -/
theorem symmetrize_bounds {g : E3 → ℝ} {m M : ℝ} (phat : E3 ≃ₗᵢ[ℝ] E3)
    (hgm : ∀ t : E3, ‖t‖ = 1 → m ≤ g t) (hgM : ∀ t : E3, ‖t‖ = 1 → g t ≤ M)
    {t : E3} (ht : ‖t‖ = 1) :
    2 * m ≤ g t + g (phat t) ∧ g t + g (phat t) ≤ 2 * M := by
  have hphatt : ‖phat t‖ = 1 := by rw [phat.norm_map]; exact ht
  exact ⟨by linarith [hgm t ht, hgm (phat t) hphatt], by linarith [hgM t ht, hgM (phat t) hphatt]⟩

/-- **G4c.** Sur l'équateur de `p`, `g + g∘phat` vaut la constante `W - g p` :
`(p,s,phat s)` est un triplet orthonormé (G2), donc `g p + g s + g(phat s) = W`
(somme de trame). -/
theorem symmetrize_equator {g : E3 → ℝ} {W : ℝ} (hg : IsFrameFunction g W)
    {phat : E3 ≃ₗᵢ[ℝ] E3} {p : E3} (hp : ‖p‖ = 1)
    (hphat_equator : ∀ s ∈ equator p, phat s ∈ equator p ∧ ⟪s, phat s⟫ = 0)
    {s : E3} (hs : s ∈ equator p) :
    g s + g (phat s) = W - g p := by
  obtain ⟨hpsE, hspd⟩ := hphat_equator s hs
  have hsu : ‖s‖ = 1 := hs.1
  have hsp : ⟪p, s⟫ = 0 := hs.2
  have hpsu : ‖phat s‖ = 1 := hpsE.1
  have hpsp : ⟪p, phat s⟫ = 0 := hpsE.2
  obtain ⟨b, hb0, hb1, hb2⟩ := exists_orthonormalBasis_of_triple' p s (phat s) hp hsu hpsu
    hsp hpsp hspd
  have h := hg b
  rw [Fin.sum_univ_three, hb0, hb1, hb2] at h
  linarith

end
end Gleason
