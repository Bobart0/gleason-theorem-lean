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

end
end Gleason
