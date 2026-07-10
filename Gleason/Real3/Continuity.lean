import Gleason.Real3.Descent

/-!
# (Historique) De la continuité en un point à la continuité partout

Ce fichier contenait un énoncé provisoire (M2, `frameFunction_continuousOn`,
jamais prouvé) supposant qu'on pourrait obtenir les valeurs extrémales d'une
frame function via un argument de continuité transportée le long des bases
orthonormées. Ce n'est PAS la structure réelle de CKM 1985 §6 : l'attention du
sup/inf s'obtient par un argument d'ULTRAFILTRE (l'espace produit `[2m,2M]^S`
n'étant pas métrisable, pas de sous-suites ni de continuité globale
nécessaire) — voir `Gleason.Real3.Attainment` (`frameFunction_attains_sup`,
`frameFunction_attains_inf`), qui remplace entièrement ce fichier. Conservé
comme point d'import intermédiaire (`Regular.lean` l'importe encore) ; acté
dans `SORRIES.md`, bloc G.
-/

namespace Gleason

noncomputable section

end
end Gleason
