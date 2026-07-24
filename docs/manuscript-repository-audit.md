# Manuscript–repository audit

This report audits every locally verifiable claim in the submission manuscript
[`busch_gleason_JAR_repositioned_v8_audited_beginning.tex`](../busch_gleason_JAR_repositioned_v8_audited_beginning.tex)
against the actual state of this repository. It was produced as part of the
pre-submission audit for the *Journal of Automated Reasoning* and follows the
verdict scheme:

- **CONFIRMED** — the claim matches the repository exactly.
- **TO CORRECT** — the claim was wrong and has been corrected (diff shown).
- **TO QUALIFY** — the claim is true but imprecise or could mislead; documented,
  not silently rewritten.
- **NOT LOCALLY VERIFIABLE** — depends on an external service (DOI resolution,
  GitHub visibility) that was checked online where possible, or cannot be
  checked from the repository alone.
- **DEPENDS ON A FUTURE RELEASE** — correct as a placeholder; must be filled in
  once the final commit/tag/DOI exist.

Audit date: 2026-07-24. Repository HEAD at the time of this audit:
`4fb363ca1c7fc5a16f64e3414c1904464faad993` (tag `v1.0.4-jar-audit`), with the
uncommitted working-tree changes listed in the final report on top.

## 1. Declarations, dimensions, and formal conclusions

| Manuscript claim | Evidence in repository | Verdict |
| --- | --- | --- |
| `Gleason.busch`, `n ≥ 1`, unique density operator represents every effect measure on all effects | `Gleason/Busch/Main.lean:972` — `theorem busch {n : ℕ} (hn : 1 ≤ n) (F : EffectMeasure n) : ∃! ρ, IsDensityOperator ρ ∧ ∀ T, IsEffect T → F.f T = (LinearMap.trace ℂ (H n) (ρ ∘ₗ T)).re` | CONFIRMED |
| `Gleason.busch_born_rule`, `n ≥ 1`, **existence** (not uniqueness) of a Born-form representative on projections | `Gleason/Busch/Main.lean:1041` — `theorem busch_born_rule {n} (hn : 1 ≤ n) (F : EffectMeasure n) : ∃ ρ, IsDensityOperator ρ ∧ ∀ A, F.toProjMeasure.μ A = bornValue ρ A` — note `∃`, not `∃!`, matching the manuscript's Corollary 1 wording ("there exists a density operator", no uniqueness claimed) | CONFIRMED |
| `Gleason.gleason`, `n ≥ 3`, unique density operator represents every projection measure | `Gleason/Main.lean:42` — `theorem gleason {n} (hn : 3 ≤ n) (m : ProjMeasure n) : ∃! ρ, IsDensityOperator ρ ∧ ∀ A, m.μ A = bornValue ρ A` | CONFIRMED |
| `Gleason.no_dispersion_free`, `n ≥ 3`, no globally `{0,1}`-valued projection measure | `Gleason/Main.lean:75` — `theorem no_dispersion_free {n} (hn : 3 ≤ n) (m : ProjMeasure n) : ¬ (∀ A, m.μ A = 0 ∨ m.μ A = 1)`, and its proof at lines 76–197 genuinely calls `gleason hn m` (line 78) to obtain the representing operator — it is derived from the representation theorem itself, not from a separate or stronger hidden hypothesis | CONFIRMED |
| Appendix ASCII transcriptions of the four theorems (lines 699–719) | Byte-level comparison against the real Unicode signatures above, modulo the documented Unicode→ASCII substitutions (`ℕ`→`Nat`, `ℂ`→`C`, `→ₗ[ℂ]`→`->l[C]`, `⟪·,·⟫_ℂ`→`inner`, etc.) | CONFIRMED |

## 2. Structures and additivity hypotheses

| Manuscript claim | Evidence | Verdict |
| --- | --- | --- |
| `ProjMeasure` additivity is on **orthogonal** pairs (`Submodule.IsOrtho`), not lattice-disjoint pairs; the stronger dimension-valuation principle is inconsistent with pure-state Born assignments but not with dimension≥2 per se | `Gleason/Defs.lean:76-90` (`add_isOrtho : ∀ A B, A ⟂ B → μ (A ⊔ B) = μ A + μ B`) and its extensive doc comment (lines 9-22) making exactly this point | CONFIRMED |
| `EffectMeasure` additivity is **binary**, only required when the sum remains an effect; finite additivity follows by iteration; this is weaker than Busch's original sequence/countable formulation | `Gleason/Busch/Effects.lean:62-71` (`additive : ∀ S T, IsEffect S → IsEffect T → IsEffect (S + T) → f (S + T) = f S + f T`) and doc comment lines 47-60 | CONFIRMED |
| `IsPositiveOp`/`IsEffect` definitions (`0 ≤ T ≤ 1` in Loewner order) | `Gleason/Busch/Effects.lean:40-45` | CONFIRMED |
| `IsDensityOperator` (symmetric, nonneg quadratic form, trace 1) | `Gleason/Defs.lean:97-100` | CONFIRMED |
| `bornValue(ρ, A) := Re tr(ρ ∘ P_A)` | `Gleason/Defs.lean:121-122` | CONFIRMED |

## 3. File/module correspondence (Tables 3 and 5 of the manuscript)

| Manuscript row | Claimed file | Actual file | Verdict |
| --- | --- | --- | --- |
| Effects and scalar extension | `Gleason/Busch/Effects.lean`, `Gleason/Busch/Main.lean` | Confirmed present, contents match description | CONFIRMED |
| Real frame functions on ℝ³ | `Gleason/Real3/*` | Confirmed (`FrameFunction.lean`, `SphereGeometry.lean`, `Descent.lean`, `Simplex.lean`, `ExactPole.lean`, `Attainment.lean`, `Continuity.lean`, `Regular.lean`) | CONFIRMED |
| Complex patching | `Gleason/Complex/*` | Confirmed (`RealSections.lean`, `Patching.lean`) | CONFIRMED |
| Operator assembly | `Gleason/Operator.lean`, `Gleason/Main.lean` | Confirmed | CONFIRMED |
| `frameFunction_regular` | `Real3/Regular.lean` | `Gleason/Real3/Regular.lean` — confirmed by grep | CONFIRMED |
| `cFrameFunction_regular` | `Complex/Patching.lean` | `Gleason/Complex/Patching.lean` — confirmed by grep | CONFIRMED |
| `isDensityOperator_of_represents`, `born_of_quadratic` | `Operator.lean` | `Gleason/Operator.lean` — confirmed by grep | CONFIRMED |
| **`ProjMeasure.frameFunction` and related lemmas** | ~~`FrameFunction.lean`~~ | Actually defined in **`Gleason/Complex/RealSections.lean:94`** (`def ProjMeasure.frameFunction`). `Gleason/Real3/FrameFunction.lean` is a *different* file: it defines the real-valued `IsFrameFunction` predicate on ℝ³ (the analytic core), not the complex `ProjMeasure.frameFunction` the table row describes. | **TO CORRECT — fixed.** The manuscript table cell was updated from `FrameFunction.lean` to `Gleason/Complex/RealSections.lean` (single-cell edit, no other text touched; see diff below). |

Diff applied for the row above:

```diff
-\passthrough{\lstinline!ProjMeasure.frameFunction!} and related lemmas & \passthrough{\lstinline!FrameFunction.lean!} & Converts a projection measure into a complex frame function. \\
+\passthrough{\lstinline!ProjMeasure.frameFunction!} and related lemmas & \passthrough{\lstinline!Gleason/Complex/RealSections.lean!} & Converts a projection measure into a complex frame function. \\
```

This is a path correction under the repository's stated exception rule ("a path, file
name, or declaration name has become false"); no mathematical content, hypothesis, or
architecture was changed.

## 4. Provenance and no-priority claims

| Manuscript claim | Evidence | Verdict |
| --- | --- | --- |
| "The present source tree contains no import from, or code dependency on, either [Soares] repository" | `grep -RIn "^import "` over all tracked `.lean` files shows only `import Mathlib` and `import Gleason.*`; a case-insensitive search for `soares` in Lean source returns no matches | CONFIRMED |
| Soares effects DOI `10.5281/zenodo.19739805` and projections DOI `10.5281/zenodo.21301925` | Cited as related work only, not as a dependency; not independently re-verified online in this audit (out of scope — third-party artifacts) | NOT LOCALLY VERIFIABLE (third-party) |
| Manuscript preprint DOI `10.5281/zenodo.21323681` | Resolved online: title "Mechanized Proofs of Busch's (2003) and Gleason's Theorems in Lean 4", author Bertrand Dalimier, dated 2026-07-12, subject matter matches. (The preprint title differs from the current manuscript title, which is expected — preprint titles commonly precede the final submitted title.) | CONFIRMED (resolves, correct author/subject) |
| Repository URL `https://github.com/Bobart0/gleason-theorem-lean` | Resolved online: public, active, description and README content consistent with this local repository | CONFIRMED |

## 5. Verification, trust boundary, and axioms

| Manuscript claim | Evidence | Verdict |
| --- | --- | --- |
| No admitted proof, no project-specific axiom; verification script rejects `sorry`, `admit`, `sorryAx`, `axiom`, `postulate`, `native_decide` in active source | Re-ran `scripts/verify.sh` on 2026-07-24 on HEAD `4fb363c` plus the pending working-tree changes: full `lake build` (8662 jobs) succeeded with **no warnings**; `scripts/check_lean_source.py` scanned all 19 tracked `.lean` files and reported no forbidden active-source token | CONFIRMED |
| `#print axioms` on the four public results equals exactly `[propext, Classical.choice, Quot.sound]` | Re-ran `lake env lean Verification/Axioms.lean` on 2026-07-24: all four theorems report exactly `[propext, Classical.choice, Quot.sound]`, matching `Verification/axioms.expected` byte-for-byte after normalizing line endings (see §6) | CONFIRMED |
| Reviewer reproduction sequence (`git clone`, `git checkout TAG`, `./setup.sh`, `./scripts/verify.sh`, `git status --short`) | Tested end-to-end in a clean local clone of tag `v1.0.4-jar-audit` (the last real tag) in a short path with `core.longpaths=true`; see §7 for the full result and a genuine, unrelated Windows-specific finding | CONFIRMED for the existing tag; the manuscript's own `FINAL-RELEASE-TAG` cannot be tested until it is created |

## 6. A genuine, non-scientific bug found and fixed: CRLF sensitivity in `scripts/verify.sh`

Running `scripts/verify.sh` unmodified on this Windows checkout (where the user's
global `core.autocrlf` is `true`) made the script's final `diff` step report a
spurious mismatch between `Verification/axioms.expected` (checked out with CRLF line
endings) and the freshly generated, CR-stripped `axioms.normalized`. The **axiom
content compared identical**; only line endings differed. Since the outer shell
invocation piped the script's output to `tail`, the failure was easy to miss (the
reported process exit code was `tail`'s, not the script's) — this is called out
explicitly here so it is not silently glossed over.

This is a portability bug in the script, not a scientific or reproducibility problem
with the proofs. It was fixed by normalizing both sides of the axiom diff:

```diff
 "$PYTHON" scripts/normalize_axioms.py "$tmp_dir/axioms.log" | tr -d '\r' > "$tmp_dir/axioms.normalized"
-diff -u Verification/axioms.expected "$tmp_dir/axioms.normalized"
+tr -d '\r' < Verification/axioms.expected > "$tmp_dir/axioms.expected.normalized"
+diff -u "$tmp_dir/axioms.expected.normalized" "$tmp_dir/axioms.normalized"
```

After this fix, `scripts/verify.sh` exits `0` and prints "Verification succeeded"
on this checkout. GitHub Actions CI (`ubuntu-latest`) was never affected, because
Linux runners do not have `core.autocrlf` conversion. See `REPRODUCIBILITY.md` for
the recommended Windows-specific `git config` note this episode also surfaced.

## 7. Clean-clone reproducibility test

See `REPRODUCIBILITY.md` for the full procedure and the exact commands/output. Summary:

- A first attempt, cloning into a deeply nested path
  (`...\AppData\Local\Temp\claude\...\scratchpad\review-copy\...`), failed with
  `error: unable to create file ...: Filename too long` while checking out
  Mathlib. This is the classic Windows `MAX_PATH` (260 characters) limitation
  interacting with Mathlib's long file paths — **not a defect in this
  repository**. It reproduces for any sufficiently deep clone path on Windows
  without long-path support enabled.
- A second attempt, cloning to a short path (`C:\glt\review-copy`) with
  `git -c core.longpaths=true clone ...`, succeeded.
- `./setup.sh` and `./scripts/verify.sh` were then run in that clean clone; see
  `REPRODUCIBILITY.md` for the outcome recorded at the time this report was
  written.

This finding is recorded in `REPRODUCIBILITY.md` as a documented Windows
prerequisite (`git config --global core.longpaths true` before cloning), rather
than as a repository defect.

## 8. Bilingual comment/docstring preservation

Per the mandatory pre-modification control: a baseline of SHA-256 hashes was
computed for the 22 tracked files carrying bilingual (French/English) comments or
docstrings (19 `.lean` files plus `README.md`, `AGENTS.md`, `MILESTONES.md`)
before any edit in this session. No edit in this session touched a `/-- ... -/`
docstring, a `/- ... -/` block comment, or a `-- ...` line comment in any `.lean`
file, and no bilingual passage in `README.md`, `AGENTS.md`, or `MILESTONES.md` was
altered, translated, merged, reordered, or shortened.

| File | Zone | English preserved | French preserved | Modification | Justification |
| --- | --- | ---: | ---: | --- | --- |
| All 19 tracked `.lean` files | docstrings/comments | yes | yes | none | not touched |
| `README.md` | bilingual body (FR block, then EN block) | yes | yes | **addition only**: one new "Relation avec le manuscrit" / "Relation to the manuscript" section appended after "Citer ce travail" / "Citing this work" in each language block | New content needed to satisfy the review requirement that the README state the manuscript's relation to the code; added symmetrically in both languages, in the same order, without touching any existing sentence |
| `AGENTS.md` | bilingual body | yes | yes | none | not touched |
| `MILESTONES.md` | bilingual body | yes | yes | none | not touched |

A post-modification hash re-check (excluding the one documented README addition)
confirmed no unintended change. See the final report for the exact
before/after hash table.

## 9. Items that remain open (deliberately not resolved by this audit)

| Item | Manuscript location | Status |
| --- | --- | --- |
| `FINAL-RELEASE-TAG` | throughout | DEPENDS ON A FUTURE RELEASE — no tag has been created for the current audited state; do not replace with a prior tag |
| `FINAL-COMMIT-SHA` | throughout | DEPENDS ON A FUTURE RELEASE — the current changes are uncommitted; replacing this with `HEAD`'s SHA now would point to a commit that does not contain these fixes |
| final/version-specific software DOI | `sec:verification`, `Data and code availability`, bibliography | DEPENDS ON A FUTURE RELEASE — requires a real Zenodo deposit tied to the final tag |
| release date in `dalimier2026` bibliography entry | bibliography | DEPENDS ON A FUTURE RELEASE |

No blocking placeholder was resolved by fabricating a value. See the final report,
§7 "Release proposée", for the exact recommended next steps.
