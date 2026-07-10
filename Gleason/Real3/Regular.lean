import Gleason.Real3.Attainment

/-!
# Régularité des frame functions positives sur ℝ³ (CKM 1985 §7)

**Théorème central du cœur analytique réel** : toute frame function positive
sur S² est la restriction d'une forme quadratique. Chemin CKM : cadre extrémal
(p,q,r) via le bloc G (H1, lemme-pivot COMBLANT une lacune du papier), deux
rotations d'axe (p̂, r̂) et les identités qu'elles induisent (H3), un « Claim »
de coïncidence f=g sur six grands cercles (H4), puis un second passage du même
argument à h:=g−f (poids nul, H6-H8) conclu par un argument de dénombrement
(H9, six cercles / deux paires de zéros / pigeonhole) qui exclut h≠0.

`heven` (parité) n'est PAS une hypothèse de ce théorème : elle est dérivable de
`hf` seule via `frameFunction_even` (P2, bloc A) — retirée de l'énoncé
d'origine (acté dans SORRIES.md, cf. règle 3 de CLAUDE.md).
-/

namespace Gleason

open scoped RealInnerProductSpace Real

noncomputable section

/- ═══════════════════════════════════════════════════════════════════
   H1 (lemme-pivot, comble une lacune du papier CKM). Étant un pôle `P`
   réalisant le sup d'une frame function bornée `φ` et un point `R0`
   réalisant l'inf, construit un triple orthonormé `(P, S1, U)` avec
   `φ(S1) = Wφ - φ(P) - φ(R0)` et `φ(U) = φ(R0)`.
   ═══════════════════════════════════════════════════════════════════ -/

/-- **H1.** `S1` orthogonal à `P` et `R0` (existence garantie en dimension 3,
`exists_unit_orthogonal_to_pair`) ; deux frames `(P,S1,T1)` et `(R0,S1,T2)`
encadrent `φ(S1)` par les extrema globaux `φ(P)` (max) et `φ(R0)` (min) des
DEUX côtés à la fois, forçant l'égalité `φ(S1) = Wφ-φ(P)-φ(R0)` (double
encadrement). `U` complète `(P,S1)` en un troisième frame, donnant
`φ(U) = φ(R0)` par soustraction. -/
theorem exists_extremal_frame {φ : E3 → ℝ} {Wφ : ℝ} (hφ : IsFrameFunction φ Wφ)
    {P : E3} (hP : ‖P‖ = 1) (hPmax : ∀ t : E3, ‖t‖ = 1 → φ t ≤ φ P)
    {R0 : E3} (hR0 : ‖R0‖ = 1) (hR0lb : ∀ t : E3, ‖t‖ = 1 → φ R0 ≤ φ t)
    (_hne : φ P ≠ φ R0) :
    ∃ S1 U : E3, ‖S1‖ = 1 ∧ ‖U‖ = 1 ∧ ⟪P, S1⟫ = 0 ∧ ⟪P, U⟫ = 0 ∧ ⟪S1, U⟫ = 0 ∧
      φ S1 = Wφ - φ P - φ R0 ∧ φ U = φ R0 := by
  obtain ⟨S1, hS1, hS1P', hS1R0'⟩ := exists_unit_orthogonal_to_pair P R0
  have hPS1 : ⟪P, S1⟫ = 0 := by rw [real_inner_comm]; exact hS1P'
  have hR0S1 : ⟪R0, S1⟫ = 0 := by rw [real_inner_comm]; exact hS1R0'
  obtain ⟨T1, hT1, hPT1, hS1T1⟩ := exists_third_orthogonal P S1 hP hS1 hPS1
  obtain ⟨T2, hT2, hR0T2, hS1T2⟩ := exists_third_orthogonal R0 S1 hR0 hS1 hR0S1
  obtain ⟨b1, hb1_0, hb1_1, hb1_2⟩ :=
    exists_orthonormalBasis_of_triple' P S1 T1 hP hS1 hT1 hPS1 hPT1 hS1T1
  obtain ⟨b2, hb2_0, hb2_1, hb2_2⟩ :=
    exists_orthonormalBasis_of_triple' R0 S1 T2 hR0 hS1 hT2 hR0S1 hR0T2 hS1T2
  have hsum1 := hφ b1
  rw [Fin.sum_univ_three, hb1_0, hb1_1, hb1_2] at hsum1
  have hsum2 := hφ b2
  rw [Fin.sum_univ_three, hb2_0, hb2_1, hb2_2] at hsum2
  have hT1le : φ T1 ≤ φ P := hPmax T1 hT1
  have hT1ge : φ R0 ≤ φ T1 := hR0lb T1 hT1
  have hT2le : φ T2 ≤ φ P := hPmax T2 hT2
  have hT2ge : φ R0 ≤ φ T2 := hR0lb T2 hT2
  have hS1eq : φ S1 = Wφ - φ P - φ R0 := by linarith [hsum1, hsum2, hT1le, hT1ge, hT2le, hT2ge]
  obtain ⟨U, hU, hUP', hUS1'⟩ := exists_unit_orthogonal_to_pair P S1
  have hPU : ⟪P, U⟫ = 0 := by rw [real_inner_comm]; exact hUP'
  have hS1U : ⟪S1, U⟫ = 0 := by rw [real_inner_comm]; exact hUS1'
  obtain ⟨b3, hb3_0, hb3_1, hb3_2⟩ :=
    exists_orthonormalBasis_of_triple' P S1 U hP hS1 hU hPS1 hPU hS1U
  have hsum3 := hφ b3
  rw [Fin.sum_univ_three, hb3_0, hb3_1, hb3_2] at hsum3
  have hUeq : φ U = φ R0 := by linarith [hsum3, hS1eq]
  exact ⟨S1, U, hS1, hU, hPS1, hPU, hS1U, hS1eq, hUeq⟩

/-- **Régularité (Gleason réel, dimension 3).** Toute frame function positive
est quadratique sur la sphère (`heven` retirée : dérivable via
`frameFunction_even`, cf. le commentaire d'en-tête). -/
theorem frameFunction_regular (f : E3 → ℝ) (W : ℝ)
    (hf : IsFrameFunction f W) (hnn : ∀ x, ‖x‖ = 1 → 0 ≤ f x) :
    ∃ q : QuadraticForm ℝ E3, ∀ x, ‖x‖ = 1 → f x = q x := by
  sorry

end
end Gleason
