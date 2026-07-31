import Gleason.Busch.Effects
import Gleason.Busch.Main
import Gleason.Operator

/-!
**FR.** # Façade publique stable des effets (Busch)

Ce module est une **façade publique stable** destinée aux développements aval
(mesure, dilatations de Naimark, représentations de chances, etc.). Il ne
démontre **aucun nouveau résultat mathématique** : il réexporte, sous le nom
`Gleason.EffectAPI`, un sous-ensemble stable des déclarations déjà publiques de
`Gleason.Busch.Effects` et `Gleason.Busch.Main`.

Points à retenir pour les consommateurs aval :
- le cadre est celui des espaces de Hilbert complexes de dimension finie
  `H n = EuclideanSpace ℂ (Fin n)` ;
- le théorème de Busch (`Gleason.busch`, `Gleason.busch_born_rule`) vaut dès
  `n ≥ 1` (hypothèse `1 ≤ n`, pas de restriction supplémentaire) ;
- la positivité d'un opérateur densité reste un **champ explicite** de la
  structure `IsDensityOperator` (`nonneg : ∀ x, 0 ≤ (⟪ρ x, x⟫_ℂ).re`), ce n'est
  pas une conséquence dérivée en aval de cette façade ;
- les modules de preuve internes (`Gleason.Busch.Main`, l'extension
  réelle-linéaire `EffectMeasure.extendSA`, la représentation de Riesz, etc.)
  restent **non contractuels** : seule cette façade et ses noms réexportés
  constituent l'interface stable pour les dépôts aval.

**EN.** # Stable public effect facade (Busch)

This module is a **stable public facade** for downstream developments
(measurement, Naimark dilations, chance representations, etc.). It proves
**no new mathematical result**: it re-exports, under the name
`Gleason.EffectAPI`, a stable subset of the already-public declarations of
`Gleason.Busch.Effects` and `Gleason.Busch.Main`.

Notes for downstream consumers:
- the setting is finite-dimensional complex Hilbert spaces
  `H n = EuclideanSpace ℂ (Fin n)`;
- Busch's theorem (`Gleason.busch`, `Gleason.busch_born_rule`) holds from
  `n ≥ 1` (hypothesis `1 ≤ n`, no further restriction);
- the positivity of a density operator remains an **explicit field** of the
  `IsDensityOperator` structure (`nonneg : ∀ x, 0 ≤ (⟪ρ x, x⟫_ℂ).re`); it is not
  a fact re-derived downstream of this facade;
- the internal proof modules (`Gleason.Busch.Main`, the real-linear extension
  `EffectMeasure.extendSA`, the Riesz representation, etc.) remain
  **non-contractual**: only this facade and its re-exported names constitute
  the stable interface for downstream repositories.
-/

namespace Gleason.EffectAPI

export Gleason (
  H
  projL
  bornValue
  IsPositiveOp
  IsEffect
  IsDensityOperator
  EffectMeasure
  busch
  busch_born_rule
  isEffect_complexSmul
)

export Gleason.EffectMeasure (
  map_zero
  mono
  isEffect_projL
  toProjMeasure
)

end Gleason.EffectAPI
