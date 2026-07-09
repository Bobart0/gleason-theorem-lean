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

/-- (Phase M) La frame function d'une mesure de projection est une frame function
complexe de poids 1. Indication : une base orthonormée découpe `⊤` en droites deux à
deux orthogonales ; itérer `add_isOrtho`. -/
theorem ProjMeasure.isCFrameFunction (m : ProjMeasure n) :
    IsCFrameFunction m.frameFunction 1 := by
  sorry

/-- Invariance de phase : `g (c • x) = g x` pour `‖c‖ = 1` — automatique pour les
frame functions issues de mesures, car `ℂ ∙ (c • x) = ℂ ∙ x`. -/
theorem ProjMeasure.frameFunction_phase (m : ProjMeasure n) (c : ℂ) (x : H n)
    (hc : ‖c‖ = 1) : m.frameFunction (c • x) = m.frameFunction x := by
  sorry

end
end Gleason
