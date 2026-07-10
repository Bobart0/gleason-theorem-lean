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
  (hcm : c < f p)

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

include hp in
/-- **F2 (préliminaire).** Un point de l'équateur de `p` (utilisé pour la
non-vacuité de la classe de latitude `0`). -/
theorem equator_nonempty' : (equator p).Nonempty := by
  obtain ⟨b, hb0⟩ := exists_orthonormalBasis_fst p hp
  refine ⟨b 1, b.norm_eq_one 1, ?_⟩
  rw [← hb0]; exact b.inner_eq_zero (by decide)

include hp in
/-- **F2a.** Toute latitude `l ∈ [0,1]` est atteinte dans `northern p`
(`exists_frame_with_lat`, puis `exists_northern_rep` pour le signe). -/
theorem nonempty_latClass {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    {s : E3 | s ∈ northern p ∧ lat p s = l}.Nonempty := by
  have h2 : (0 : ℝ) ≤ (1 - l) / 2 := by linarith
  obtain ⟨b, hb0, -, -⟩ := exists_frame_with_lat hp hl0 h2 h2 (by ring)
  obtain ⟨s, hsN, hlseq, -⟩ := exists_northern_rep (p := p) (b.norm_eq_one 0)
  exact ⟨s, hsN, hlseq.trans hb0⟩

include hmax in
theorem bddAbove_latClass_image (l : ℝ) :
    BddAbove (f '' {s : E3 | s ∈ northern p ∧ lat p s = l}) := by
  refine ⟨f p, ?_⟩
  rintro y ⟨s, hs, rfl⟩
  exact hmax s hs.1.1

include hmlb in
theorem bddBelow_latClass_image (l : ℝ) :
    BddBelow (f '' {s : E3 | s ∈ northern p ∧ lat p s = l}) := by
  refine ⟨m₀, ?_⟩
  rintro y ⟨s, hs, rfl⟩
  exact hmlb s hs.1.1

include hf hp hmax hmlb hm hconst in
/-- **F2b (monotonie croisée, cœur de F2).** `l < l' → latSup l ≤ latInf l'` :
pour `s` de latitude `l`, `s'` de latitude `l'`, `f s ≤ f s'`. Cas `l' = 1`
(`s' = p` par `eq_pole_of_lat_eq_one`) via `hmax` directement ; cas `l' < 1`
via `frameFunction_le_of_lat_lt` (E5, `s ≠ p` toujours car `l < l' ≤ 1`
force `l < 1` donc `lat p s ≠ lat p p = 1`, et `s' ≠ p` car `l' < 1`). -/
theorem latSup_le_latInf_of_lt {l l' : ℝ} (hl0 : 0 ≤ l) (hl'1 : l' ≤ 1) (hlt : l < l') :
    latSup f p l ≤ latInf f p l' := by
  have hl1 : l ≤ 1 := hlt.le.trans hl'1
  unfold latSup latInf
  refine csSup_le (Set.Nonempty.image f (nonempty_latClass hp hl0 hl1)) ?_
  rintro y ⟨s, ⟨hsN, hls⟩, rfl⟩
  refine le_csInf (Set.Nonempty.image f (nonempty_latClass hp (by linarith) hl'1)) ?_
  rintro y' ⟨s', ⟨hs'N, hl's'⟩, rfl⟩
  rcases hl'1.lt_or_eq with hl'lt | hl'eq
  · have hsp : s ≠ p := by
      intro heq; rw [heq, lat_self p hp] at hls; linarith
    have hs'p : s' ≠ p := by
      intro heq; rw [heq, lat_self p hp] at hl's'; linarith
    exact frameFunction_le_of_lat_lt hf hp hmax hmlb hm hconst hs'N.1 hs'N hs'p hsN.1 hsN hsp
      (by rw [hls, hl's']; exact hlt)
  · have hs'p : s' = p := eq_pole_of_lat_eq_one hp hs'N.1 hs'N (hl's'.trans hl'eq)
    rw [hs'p]
    exact hmax s hsN.1

/-- **F2c (préliminaire).** La classe de latitude `0` de `northern p` est
exactement l'équateur de `p` (pas de nouvelle hypothèse : déroulement pur des
définitions). -/
theorem latClass_zero_eq_equator : {s : E3 | s ∈ northern p ∧ lat p s = 0} = equator p := by
  ext s
  constructor
  · rintro ⟨hsN, hl⟩
    exact (mem_equator_iff_lat_eq_zero p s).mpr ⟨hsN.1, hl⟩
  · intro hs
    have h := (mem_equator_iff_lat_eq_zero p s).mp hs
    exact ⟨equator_subset_northern p hs, h.2⟩

include hp in
/-- **F2c (préliminaire).** La classe de latitude `1` de `northern p` est le
singleton `{p}` (`eq_pole_of_lat_eq_one`). -/
theorem latClass_one_eq_singleton : {s : E3 | s ∈ northern p ∧ lat p s = 1} = {p} := by
  ext s
  constructor
  · rintro ⟨hsN, hl⟩
    exact eq_pole_of_lat_eq_one hp hsN.1 hsN hl
  · intro hsp
    rw [Set.mem_singleton_iff] at hsp
    rw [hsp]
    refine ⟨⟨hp, ?_⟩, lat_self p hp⟩
    rw [real_inner_self_eq_norm_sq, hp]; norm_num

include hp hconst in
/-- **F2d (extrémité `l = 0`).** `latSup 0 = latInf 0 = c` : l'image de
l'équateur par `f` est le singleton `{c}` (`hconst`). -/
theorem latSup_zero : latSup f p 0 = c := by
  unfold latSup
  rw [latClass_zero_eq_equator]
  have himg : f '' equator p = {c} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · obtain ⟨e, he⟩ := equator_nonempty' hp
      exact ⟨e, he, hconst e he⟩
    · rintro y ⟨e, he, hey⟩
      rw [← hey]; exact hconst e he
  rw [himg, csSup_singleton]

include hp hconst in
theorem latInf_zero : latInf f p 0 = c := by
  unfold latInf
  rw [latClass_zero_eq_equator]
  have himg : f '' equator p = {c} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · obtain ⟨e, he⟩ := equator_nonempty' hp
      exact ⟨e, he, hconst e he⟩
    · rintro y ⟨e, he, hey⟩
      rw [← hey]; exact hconst e he
  rw [himg, csInf_singleton]

include hp in
/-- **F2e (extrémité `l = 1`).** `latSup 1 = latInf 1 = f p`. -/
theorem latSup_one : latSup f p 1 = f p := by
  unfold latSup
  rw [latClass_one_eq_singleton hp, Set.image_singleton, csSup_singleton]

include hp in
theorem latInf_one : latInf f p 1 = f p := by
  unfold latInf
  rw [latClass_one_eq_singleton hp, Set.image_singleton, csInf_singleton]

include hf hp hmax hmlb hm hconst in
/-- **F3 (dénombrabilité de l'écart).** `C := {l ∈ (0,1) | latInf l < latSup l}`
est dénombrable : pour `l ∈ C`, choisir un rationnel `q(l)` dans l'intervalle
`(latInf l, latSup l)` (`exists_rat_btwn`) ; par la monotonie croisée (F2b),
ces intervalles sont deux-à-deux ordonnés-disjoints, donc `q` est injective sur
`C`, qui s'injecte ainsi dans `ℚ` (dénombrable). -/
theorem countable_latGap :
    {l ∈ Set.Ioo (0 : ℝ) 1 | latInf f p l < latSup f p l}.Countable := by
  classical
  set C : Set ℝ := {l ∈ Set.Ioo (0 : ℝ) 1 | latInf f p l < latSup f p l} with hC_def
  have hchoice : ∀ l, l ∈ C → ∃ q : ℚ, latInf f p l < (q : ℝ) ∧ (q : ℝ) < latSup f p l := by
    intro l hl
    exact exists_rat_btwn hl.2
  choose! q hqP using hchoice
  have hInj : Set.InjOn q C := by
    intro l₁ hl₁ l₂ hl₂ heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hmono : latSup f p l₁ ≤ latInf f p l₂ :=
        latSup_le_latInf_of_lt hf hp hmax hmlb hm hconst hl₁.1.1.le hl₂.1.2.le hlt
      have h1 := (hqP l₁ hl₁).2
      have h2 := (hqP l₂ hl₂).1
      have hlt' : (q l₁ : ℝ) < (q l₂ : ℝ) := by linarith
      exact (by exact_mod_cast hlt' : q l₁ < q l₂).ne heq
    · have hmono : latSup f p l₂ ≤ latInf f p l₁ :=
        latSup_le_latInf_of_lt hf hp hmax hmlb hm hconst hl₂.1.1.le hl₁.1.2.le hlt
      have h1 := (hqP l₂ hl₂).2
      have h2 := (hqP l₁ hl₁).1
      have hlt' : (q l₂ : ℝ) < (q l₁ : ℝ) := by linarith
      exact (by exact_mod_cast hlt' : q l₂ < q l₁).ne heq.symm
  exact Set.MapsTo.countable_of_injOn (Set.mapsTo_univ q C) hInj Set.countable_univ

include hp hmax hmlb in
/-- **F4a (préliminaire).** `latInf l ≤ latSup l` toujours (`csInf_le_csSup`). -/
theorem latInf_le_latSup {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    latInf f p l ≤ latSup f p l := by
  unfold latInf latSup
  exact csInf_le_csSup (Set.Nonempty.image f (nonempty_latClass hp hl0 hl1))
    (bddBelow_latClass_image hmlb l) (bddAbove_latClass_image hmax l)

include hp hmax hmlb in
/-- **F4b.** Hors de l'écart (`¬(latInf l < latSup l)`), tous les points de la
classe de latitude `l` ont la même valeur de `f`, encadrée par `latInf l` et
`latSup l` qui coïncident (antisymétrie). -/
theorem latClass_const_of_not_mem_gap {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hlC : ¬(latInf f p l < latSup f p l)) {s : E3} (hsN : s ∈ northern p) (hls : lat p s = l) :
    f s = latInf f p l := by
  have hle : latInf f p l ≤ latSup f p l := latInf_le_latSup hp hmax hmlb hl0 hl1
  have heq : latInf f p l = latSup f p l := le_antisymm hle (not_lt.mp hlC)
  have h1 : latInf f p l ≤ f s := csInf_le (bddBelow_latClass_image hmlb l) ⟨s, ⟨hsN, hls⟩, rfl⟩
  have h2 : f s ≤ latSup f p l := le_csSup (bddAbove_latClass_image hmax l) ⟨s, ⟨hsN, hls⟩, rfl⟩
  linarith

include hf hp hmax hmlb in
/-- **F4c (additivité-à-1 hors de l'écart).** Pour `l₁+l₂+l₃ = 1` tous hors de
l'écart, `latInf l₁ + latInf l₂ + latInf l₃ = W` : base de B7
(`exists_frame_with_lat`) réalisant ces latitudes, représentants nord
(`exists_northern_rep`), parité (`frameFunction_even`, P2) pour ramener la
somme de trame à ces représentants, puis F4b pour identifier chaque terme. -/
theorem latInf_additive_of_not_mem_gap {l₁ l₂ l₃ : ℝ}
    (h1 : 0 ≤ l₁) (h2 : 0 ≤ l₂) (h3 : 0 ≤ l₃) (hsum : l₁ + l₂ + l₃ = 1)
    (h1C : ¬(latInf f p l₁ < latSup f p l₁))
    (h2C : ¬(latInf f p l₂ < latSup f p l₂))
    (h3C : ¬(latInf f p l₃ < latSup f p l₃)) :
    latInf f p l₁ + latInf f p l₂ + latInf f p l₃ = W := by
  have hl1le : l₁ ≤ 1 := by linarith
  have hl2le : l₂ ≤ 1 := by linarith
  have hl3le : l₃ ≤ 1 := by linarith
  obtain ⟨b, hb0, hb1, hb2⟩ := exists_frame_with_lat hp h1 h2 h3 hsum
  obtain ⟨s0, hs0N, hls0, hs0eq⟩ := exists_northern_rep (p := p) (b.norm_eq_one 0)
  obtain ⟨s1, hs1N, hls1, hs1eq⟩ := exists_northern_rep (p := p) (b.norm_eq_one 1)
  obtain ⟨s2, hs2N, hls2, hs2eq⟩ := exists_northern_rep (p := p) (b.norm_eq_one 2)
  have hfs0 : f s0 = f (b 0) := by
    rcases hs0eq with h | h
    · rw [h]
    · rw [h]; exact frameFunction_even hf (b 0) (b.norm_eq_one 0)
  have hfs1 : f s1 = f (b 1) := by
    rcases hs1eq with h | h
    · rw [h]
    · rw [h]; exact frameFunction_even hf (b 1) (b.norm_eq_one 1)
  have hfs2 : f s2 = f (b 2) := by
    rcases hs2eq with h | h
    · rw [h]
    · rw [h]; exact frameFunction_even hf (b 2) (b.norm_eq_one 2)
  have hsum_f : f s0 + f s1 + f s2 = W := by
    have hb := hf b
    rw [Fin.sum_univ_three] at hb
    rw [hfs0, hfs1, hfs2]
    exact hb
  have e0 : f s0 = latInf f p l₁ :=
    latClass_const_of_not_mem_gap hp hmax hmlb h1 hl1le h1C hs0N (hls0.trans hb0)
  have e1 : f s1 = latInf f p l₂ :=
    latClass_const_of_not_mem_gap hp hmax hmlb h2 hl2le h2C hs1N (hls1.trans hb1)
  have e2 : f s2 = latInf f p l₃ :=
    latClass_const_of_not_mem_gap hp hmax hmlb h3 hl3le h3C hs2N (hls2.trans hb2)
  rw [← e0, ← e1, ← e2]
  exact hsum_f

/-- **F5 (préliminaire, cardinalité).** Un sous-ensemble dénombrable de ℝ ne
peut couvrir un intervalle `(a,b)` non vide (`Cardinal.mk_Ioo_real` = continuum
`> ℵ₀`). Fait général, indépendant du paquet d'hypothèses de la section. -/
theorem exists_not_mem_of_countable {D : Set ℝ} (hD : D.Countable) {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Set.Ioo a b, x ∉ D := by
  have hUncount : ¬ (Set.Ioo a b).Countable := by
    intro hcount
    have h1 : Cardinal.mk (Set.Ioo a b) ≤ Cardinal.aleph0 :=
      Cardinal.le_aleph0_iff_set_countable.mpr hcount
    rw [Cardinal.mk_Ioo_real hab] at h1
    exact absurd h1 (not_le.mpr Cardinal.aleph0_lt_continuum)
  have hnotsub : ¬ Set.Ioo a b ⊆ D := fun hsub => hUncount (hD.mono hsub)
  exact Set.not_subset.mp hnotsub

include hp hconst in
/-- **F5 (préliminaire).** `l ∉ C` entraîne `¬(latInf l < latSup l)` : cas
`l = 0`, `l = 1` (F2d/F2e, égalité directe) ou `l ∈ (0,1)` (extraction directe
depuis `l ∉ C`). -/
theorem not_gap_of_not_mem_C {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hlC : l ∉ {l ∈ Set.Ioo (0 : ℝ) 1 | latInf f p l < latSup f p l}) :
    ¬(latInf f p l < latSup f p l) := by
  rcases hl0.eq_or_lt with h0 | h0
  · rw [← h0, latInf_zero hp hconst, latSup_zero hp hconst]; exact lt_irrefl c
  rcases hl1.eq_or_lt with h1 | h1
  · rw [h1, latInf_one hp, latSup_one hp]; exact lt_irrefl (f p)
  · intro hcon
    exact hlC ⟨⟨h0, h1⟩, hcon⟩

include hf hp hmax hmlb hm hconst in
/-- **F5 (monotonie globale de `latInf`).** `l ≤ l' → latInf l ≤ latInf l'`
(sans restriction hors-`C` : `latInf l ≤ latSup l ≤ latInf l'` par F4a puis
F2b). -/
theorem latInf_mono {l l' : ℝ} (hl0 : 0 ≤ l) (hl'1 : l' ≤ 1) (hle : l ≤ l') :
    latInf f p l ≤ latInf f p l' := by
  rcases hle.eq_or_lt with heq | hlt
  · rw [heq]
  · have h1 := latInf_le_latSup hp hmax hmlb hl0 (hlt.le.trans hl'1)
    have h2 := latSup_le_latInf_of_lt hf hp hmax hmlb hm hconst hl0 hl'1 hlt
    linarith

include hf hp hmax hmlb hm hconst in
/-- **F5 (monotonie globale de `latSup`, symétrique).** -/
theorem latSup_mono {l l' : ℝ} (hl0 : 0 ≤ l) (hl'1 : l' ≤ 1) (hle : l ≤ l') :
    latSup f p l ≤ latSup f p l' := by
  rcases hle.eq_or_lt with heq | hlt
  · rw [heq]
  · have hl'0 : 0 ≤ l' := hl0.trans hle
    have h1 := latSup_le_latInf_of_lt hf hp hmax hmlb hm hconst hl0 hl'1 hlt
    have h2 := latInf_le_latSup hp hmax hmlb hl'0 hl'1
    linarith

include hf hp hmax hmlb hm hconst hcm in
/-- **F5 (Warmup II).** Hors de `C` (l'écart dénombrable, F3), `latInf` est
exactement affine : application de `warmup_II` (bloc D) à
`G(l) := (latInf l - c)/(f p - c)`, avec `G 0 = 0` (F2d), monotonie (F4a+F2b)
et additivité-à-1 (F4c + F5-not_gap). -/
theorem latInf_eq_affine_of_not_mem_C :
    ∀ l ∈ Set.Icc (0 : ℝ) 1 \ {l ∈ Set.Ioo (0 : ℝ) 1 | latInf f p l < latSup f p l},
      latInf f p l = c + (f p - c) * l := by
  have hne : f p - c ≠ 0 := by linarith
  set C : Set ℝ := {l ∈ Set.Ioo (0 : ℝ) 1 | latInf f p l < latSup f p l} with hC_def
  set G : ℝ → ℝ := fun l => (latInf f p l - c) / (f p - c) with hG_def
  have hG0 : G 0 = 0 := by simp only [hG_def, latInf_zero hp hconst, sub_self, zero_div]
  have hGmono : ∀ a b, a ∈ Set.Icc (0 : ℝ) 1 \ C → b ∈ Set.Icc (0 : ℝ) 1 \ C → a ≤ b →
      G a ≤ G b := by
    intro a b ha hb hab
    have hle := latInf_mono hf hp hmax hmlb hm hconst ha.1.1 hb.1.2 hab
    have hcm' : 0 < f p - c := by linarith
    simp only [hG_def]
    gcongr
  have hGtriple : ∀ a b d, a ∈ Set.Icc (0 : ℝ) 1 \ C → b ∈ Set.Icc (0 : ℝ) 1 \ C →
      d ∈ Set.Icc (0 : ℝ) 1 \ C → a + b + d = 1 → G a + G b + G d = 1 := by
    intro a b d ha hb hd hsum
    have hadd := latInf_additive_of_not_mem_gap hf hp hmax hmlb ha.1.1 hb.1.1 hd.1.1 hsum
      (not_gap_of_not_mem_C hp hconst ha.1.1 ha.1.2 ha.2)
      (not_gap_of_not_mem_C hp hconst hb.1.1 hb.1.2 hb.2)
      (not_gap_of_not_mem_C hp hconst hd.1.1 hd.1.2 hd.2)
    have hweight := weight_eq_pole_add_equator hf hp hconst
    simp only [hG_def]
    rw [← add_div, ← add_div, div_eq_one_iff_eq hne]
    linarith [hadd, hweight]
  have hwarm := warmup_II C (countable_latGap hf hp hmax hmlb hm hconst)
    (fun l hl => hl.1) G hG0 hGmono hGtriple
  intro l hl
  have hG := hwarm l hl
  simp only [hG_def] at hG
  rw [div_eq_iff hne] at hG
  linear_combination hG

include hf hp hmax hmlb hm hconst hcm in
/-- **F5 (densité, direction basse).** `target l ≤ latInf l` pour tout
`l ∈ [0,1]` : approche par `l₁ < l` hors de `C` (`exists_not_mem_of_countable`),
`latInf l₁ = target l₁` (F5 précédent), `latInf l₁ ≤ latInf l` (monotonie),
`target l₁ → target l` quand `l₁ → l`. -/
theorem target_le_latInf {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    c + (f p - c) * l ≤ latInf f p l := by
  rcases hl0.eq_or_lt with hl00 | hlpos
  · rw [← hl00, latInf_zero hp hconst, mul_zero, add_zero]
  refine le_of_forall_pos_lt_add (fun ε hε => ?_)
  set η : ℝ := min (ε / (2 * (f p - c))) (l / 2) with hη_def
  have hηpos : 0 < η := lt_min (by positivity) (by linarith)
  have hηl : η < l := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hηε : (f p - c) * η ≤ ε / 2 := by
    have h1 : η ≤ ε / (2 * (f p - c)) := min_le_left _ _
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ f p - c)
    have h3 : (f p - c) * (ε / (2 * (f p - c))) = ε / 2 := by
      have hcm'' : f p - c ≠ 0 := by linarith
      field_simp
    linarith [h2, h3]
  obtain ⟨l₁, hl₁mem, hl₁notC⟩ :=
    exists_not_mem_of_countable (countable_latGap hf hp hmax hmlb hm hconst)
      (show l - η < l by linarith)
  have hl₁0 : 0 ≤ l₁ := by linarith [hl₁mem.1]
  have hl₁1 : l₁ ≤ 1 := by linarith [hl₁mem.2]
  have hl₁C : l₁ ∈ Set.Icc (0 : ℝ) 1 \ {l ∈ Set.Ioo (0 : ℝ) 1 | latInf f p l < latSup f p l} :=
    ⟨⟨hl₁0, hl₁1⟩, hl₁notC⟩
  have haffine := latInf_eq_affine_of_not_mem_C hf hp hmax hmlb hm hconst hcm l₁ hl₁C
  have hmono : latInf f p l₁ ≤ latInf f p l :=
    latInf_mono hf hp hmax hmlb hm hconst hl₁0 hl1 hl₁mem.2.le
  have hcm' : 0 < f p - c := by linarith
  nlinarith [haffine, hmono, hηε, hl₁mem.1, hcm']

include hf hp hmax hmlb hm hconst hcm in
/-- **F5 (densité, direction haute, symétrique).** `latSup l ≤ target l`. -/
theorem latSup_le_target {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    latSup f p l ≤ c + (f p - c) * l := by
  rcases hl1.eq_or_lt with hl11 | hlpos
  · rw [hl11, latSup_one hp, mul_one]; linarith
  refine le_of_forall_pos_lt_add (fun ε hε => ?_)
  set η : ℝ := min (ε / (2 * (f p - c))) ((1 - l) / 2) with hη_def
  have hηpos : 0 < η := lt_min (by positivity) (by linarith)
  have hηl : η < 1 - l := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hηε : (f p - c) * η ≤ ε / 2 := by
    have h1 : η ≤ ε / (2 * (f p - c)) := min_le_left _ _
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ f p - c)
    have h3 : (f p - c) * (ε / (2 * (f p - c))) = ε / 2 := by
      have hcm'' : f p - c ≠ 0 := by linarith
      field_simp
    linarith [h2, h3]
  obtain ⟨l₂, hl₂mem, hl₂notC⟩ :=
    exists_not_mem_of_countable (countable_latGap hf hp hmax hmlb hm hconst)
      (show l < l + η by linarith)
  have hl₂0 : 0 ≤ l₂ := by linarith [hl₂mem.1]
  have hl₂1 : l₂ ≤ 1 := by linarith [hl₂mem.2]
  have hl₂C : l₂ ∈ Set.Icc (0 : ℝ) 1 \ {l ∈ Set.Ioo (0 : ℝ) 1 | latInf f p l < latSup f p l} :=
    ⟨⟨hl₂0, hl₂1⟩, hl₂notC⟩
  have haffine := latInf_eq_affine_of_not_mem_C hf hp hmax hmlb hm hconst hcm l₂ hl₂C
  have hle₂ : latSup f p l₂ = latInf f p l₂ := by
    have h1 := latInf_le_latSup hp hmax hmlb hl₂0 hl₂1
    have h2 := not_gap_of_not_mem_C hp hconst hl₂0 hl₂1 hl₂notC
    linarith [not_lt.mp h2]
  have hmono : latSup f p l ≤ latSup f p l₂ :=
    latSup_mono hf hp hmax hmlb hm hconst hl0 hl₂1 hl₂mem.1.le
  have hcm' : 0 < f p - c := by linarith
  nlinarith [haffine, hmono, hle₂, hηε, hl₂mem.2, hcm']

include hf hp hmax hmlb hm hconst hcm in
/-- **F5 (assemblage).** `latInf l = latSup l = c + (f p - c)·l` pour tout
`l ∈ [0,1]` (sandwich `target l ≤ latInf l ≤ latSup l ≤ target l`). -/
theorem latInf_eq_latSup_eq_affine {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    latInf f p l = c + (f p - c) * l ∧ latSup f p l = c + (f p - c) * l := by
  have h1 := target_le_latInf hf hp hmax hmlb hm hconst hcm hl0 hl1
  have h2 := latInf_le_latSup hp hmax hmlb hl0 hl1
  have h3 := latSup_le_target hf hp hmax hmlb hm hconst hcm hl0 hl1
  exact ⟨by linarith, by linarith⟩

end ExactPoleSetup

end
end Gleason
