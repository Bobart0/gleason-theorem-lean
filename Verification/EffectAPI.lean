import Gleason.EffectAPI

/-!
**FR.** # Audit de la façade `Gleason.EffectAPI`

Vérifie, indépendamment du reste du dépôt (import unique de la façade), que
les déclarations réexportées sont bien accessibles sous les noms attendus,
que la façade suffit à construire un témoin concret de `EffectMeasure` et à
appliquer `busch` / `busch_born_rule` sur ce témoin, et que la base de
confiance des deux théorèmes reste standard.

**EN.** # Audit of the `Gleason.EffectAPI` facade

Checks, independently of the rest of the repository (single facade import),
that the re-exported declarations are reachable under the expected names,
that the facade suffices to build a concrete `EffectMeasure` witness and to
apply `busch` / `busch_born_rule` to it, and that the trust base of both
theorems stays standard.
-/

open scoped InnerProductSpace

noncomputable section

-- ── Signatures réexportées ───────────────────────────────────────────
#check @Gleason.EffectAPI.H
#check @Gleason.EffectAPI.projL
#check @Gleason.EffectAPI.bornValue
#check @Gleason.EffectAPI.IsPositiveOp
#check @Gleason.EffectAPI.IsEffect
#check @Gleason.EffectAPI.IsDensityOperator
#check @Gleason.EffectAPI.EffectMeasure
#check @Gleason.EffectAPI.busch
#check @Gleason.EffectAPI.busch_born_rule
#check @Gleason.EffectAPI.isEffect_complexSmul
#check @Gleason.EffectAPI.map_zero
#check @Gleason.EffectAPI.mono
#check @Gleason.EffectAPI.isEffect_projL
#check @Gleason.EffectAPI.toProjMeasure

/--
**FR.** Témoin concret : mesure d'effets de l'état pur `|0⟩` sur `H 2`
(cible historique de Busch), construite uniquement à partir des noms exposés
par la façade.

**EN.** Concrete witness: pure-state `|0⟩` effect measure on `H 2` (Busch's
historical target), built solely from the names exposed by the facade.
-/
def sampleEffectMeasure : Gleason.EffectAPI.EffectMeasure 2 where
  f T := (⟪T (EuclideanSpace.single (0 : Fin 2) 1),
            EuclideanSpace.single (0 : Fin 2) 1⟫_ℂ).re
  nonneg T hT := hT.1.2 _
  map_one := by
    have hψ : ‖(EuclideanSpace.single (0 : Fin 2) 1 : Gleason.EffectAPI.H 2)‖ = 1 := by simp
    simp [inner_self_eq_norm_sq_to_K, hψ]
  additive S T _ _ _ := by simp [LinearMap.add_apply]

-- ── Application de `busch` ────────────────────────────────────────────
example :
    ∃! ρ : Gleason.EffectAPI.H 2 →ₗ[ℂ] Gleason.EffectAPI.H 2,
      Gleason.EffectAPI.IsDensityOperator ρ ∧
        ∀ T, Gleason.EffectAPI.IsEffect T →
          sampleEffectMeasure.f T =
            (LinearMap.trace ℂ (Gleason.EffectAPI.H 2) (ρ ∘ₗ T)).re :=
  Gleason.EffectAPI.busch (by norm_num) sampleEffectMeasure

-- ── Application de `busch_born_rule` ─────────────────────────────────
example :
    ∃ ρ : Gleason.EffectAPI.H 2 →ₗ[ℂ] Gleason.EffectAPI.H 2,
      Gleason.EffectAPI.IsDensityOperator ρ ∧
        ∀ A : Submodule ℂ (Gleason.EffectAPI.H 2),
          sampleEffectMeasure.toProjMeasure.μ A = Gleason.EffectAPI.bornValue ρ A :=
  Gleason.EffectAPI.busch_born_rule (by norm_num) sampleEffectMeasure

end

-- ── Base de confiance ─────────────────────────────────────────────────
#print axioms Gleason.busch
#print axioms Gleason.busch_born_rule
