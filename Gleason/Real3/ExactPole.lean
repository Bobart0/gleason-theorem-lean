import Gleason.Real3.Descent

/-!
# Théorème principal du cœur analytique réel (CKM 1985 §5, PDF p. 124-125)

`frameFunction_exact_pole` : si une frame function `f` atteint son sup en `p`
et est constante sur l'équateur de `p`, alors `f` est EXACTEMENT quadratique :
`f(s) = c + (f(p) - c) · lat p s` pour tout `s` unitaire. Contrairement aux
blocs C/E (approché puis exact via une limite `ξ → 0`), ce bloc établit le
résultat sur la sphère ENTIÈRE (via la parité P2), pas seulement l'hémisphère
nord — le bloc G en aura besoin globalement.

Style : les lemmes F1c-F5 partagent le même paquet d'hypothèses
`(hf, hp, hmax, hmlb, hm, hconst)` (comme les blocs C/E) ; on les regroupe via
`variable` plutôt que de les répéter (contrairement à `Simplex.lean` où chaque
sous-lemme D1-D6 a un paquet distinct). Seule l'assemblage final F6 s'en
affranchit (il DÉRIVE `m₀, hmlb, hm` via F1b plutôt que de les recevoir).
-/

namespace Gleason

open scoped RealInnerProductSpace Real

noncomputable section

/-- **F2 (définitions).** Enveloppe sup/inf de `f` sur la classe de latitude
`l` de l'hémisphère nord de `p`. `f`, `p` explicites (sinon inférence
impossible : ils n'apparaissent pas dans le type de retour `ℝ`). -/
def latSup (f : E3 → ℝ) (p : E3) (l : ℝ) : ℝ :=
  sSup (f '' {s : E3 | s ∈ northern p ∧ lat p s = l})

def latInf (f : E3 → ℝ) (p : E3) (l : ℝ) : ℝ :=
  sInf (f '' {s : E3 | s ∈ northern p ∧ lat p s = l})

section ExactPoleSetup

variable {f : E3 → ℝ} {W m₀ c : ℝ} (hf : IsFrameFunction f W) {p : E3} (hp : ‖p‖ = 1)
  (hmax : ∀ t : E3, ‖t‖ = 1 → f t ≤ f p)
  (hmlb : ∀ t : E3, ‖t‖ = 1 → m₀ ≤ f t)
  (hm : ∀ ε > 0, ∃ x : E3, ‖x‖ = 1 ∧ f x < m₀ + ε)
  (hconst : ∀ e ∈ equator p, f e = c)

include hf hmax in
/-- **F1a.** `hmax` fournit gratuitement un minorant explicite (non optimal) :
compléter `t` en base donne `f t = W - f(b1) - f(b2) ≥ W - 2·f p`. -/
theorem crude_lower_bound : ∀ t : E3, ‖t‖ = 1 → W - 2 * f p ≤ f t := by
  intro t ht
  obtain ⟨b, hb0⟩ := exists_orthonormalBasis_fst t ht
  have hsum := hf b
  rw [Fin.sum_univ_three, hb0] at hsum
  have h1 : f (b 1) ≤ f p := hmax (b 1) (b.norm_eq_one 1)
  have h2 : f (b 2) ≤ f p := hmax (b 2) (b.norm_eq_one 2)
  linarith

include hf hp hmax in
/-- **F1b (existence de l'infimum approché).** `m₀ := sInf (f '' sphère)` est
à la fois un minorant (`csInf_le`) et approché (`exists_lt_of_csInf_lt`) —
borné inférieurement par F1a, sphère non vide (`p`). -/
theorem exists_inf_approx :
    ∃ m₀ : ℝ, (∀ t : E3, ‖t‖ = 1 → m₀ ≤ f t) ∧
      (∀ ε > 0, ∃ x : E3, ‖x‖ = 1 ∧ f x < m₀ + ε) := by
  set S : Set ℝ := f '' {x : E3 | ‖x‖ = 1} with hS_def
  have hSne : S.Nonempty := ⟨f p, p, hp, rfl⟩
  have hSbdd : BddBelow S := by
    refine ⟨W - 2 * f p, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact crude_lower_bound hf hmax x hx
  refine ⟨sInf S, ?_, ?_⟩
  · intro t ht
    exact csInf_le hSbdd ⟨t, ht, rfl⟩
  · intro ε hε
    obtain ⟨y, hyS, hylt⟩ := exists_lt_of_csInf_lt hSne (show sInf S < sInf S + ε by linarith)
    obtain ⟨x, hx, rfl⟩ := hyS
    exact ⟨x, hx, hylt⟩

include hf hp hconst in
/-- **F1c (poids).** `W = f p + 2c` : base `(p, e₁, e₂)` avec `e₁, e₂` à
l'équateur de `p`. -/
theorem weight_eq_pole_add_equator : W = f p + 2 * c := by
  obtain ⟨b, hb0⟩ := exists_orthonormalBasis_fst p hp
  have hsum := hf b
  rw [Fin.sum_univ_three, hb0] at hsum
  have he1 : b 1 ∈ equator p := by
    refine ⟨b.norm_eq_one 1, ?_⟩
    rw [← hb0]; exact b.inner_eq_zero (by decide)
  have he2 : b 2 ∈ equator p := by
    refine ⟨b.norm_eq_one 2, ?_⟩
    rw [← hb0]; exact b.inner_eq_zero (by decide)
  rw [hconst (b 1) he1, hconst (b 2) he2] at hsum
  linarith

include hf hp hmax hmlb hm hconst in
/-- **F1d.** `c` minore `f` globalement (réutilise `equator_value_le`, C5). -/
theorem c_le_f : ∀ t : E3, ‖t‖ = 1 → c ≤ f t :=
  equator_value_le hf hp hmax hmlb hm hconst

end ExactPoleSetup

end
end Gleason
