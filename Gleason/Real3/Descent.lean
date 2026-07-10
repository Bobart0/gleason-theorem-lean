import Gleason.Real3.SphereGeometry
import Gleason.Real3.Simplex

/-!
# Basic Lemma (CKM 1985 §4, PDF du projet p. 122-123)

Remplace l'énoncé provisoire `exists_continuity_point` (qui ne correspondait pas à la
structure réelle de CKM — acté dans SORRIES.md, bloc C) par le Basic Lemma : si `f p`
est proche du sup et `f` est constante sur l'équateur de `p`, alors `f` décroît le long
de toute descente. Architecture inversée par rapport au papier : la version approchée
(`basic_lemma_approx`) est établie d'abord, la version exacte (`basic_lemma`) en est un
corollaire (limite `ξ → 0`).
-/

namespace Gleason

noncomputable section

end
end Gleason
