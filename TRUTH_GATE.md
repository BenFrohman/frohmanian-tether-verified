# TRUTH GATE — the GOD gate. Read this first.

Author: Benjamin Stanley Frohman. This file is the root instruction for every person and every
automated agent (every bot) that touches this repository. Load it before any other file.

**Only truth and honest, kernel-proved theorems pass this gate. Nothing from this repository is
published, released, deposited on Zenodo, cited or claimed unless the `truth-gate` check is green
on the exact commit being cited.** That is why it is the GOD gate: it sits above every other
check, and no other green check can stand in for it.

## The issue this gate fixes

A paper states its claim in English. Lean can only prove `formal_claim ↔ paper_claim` once
`paper_claim` is itself written in Lean. If `paper_claim` were simply *defined to be*
`formal_claim` (or an alias of it, or something that unfolds to it), the theorem
`intended_correspondence` would be `Iff.rfl`: it would be empty and prove nothing about the
paper. A green certificate could then "certify" a statement different from the one the paper
makes (drift), whether by accident or by an injected instruction.

## The fix rule (binding, permanent)

1. `paper_claim` is an **independent Lean transcription of the paper's exact claim**, written in
   the paper's own terms, with every hypothesis the paper states. The verbatim English quote,
   the paper path, its sha256 and the section are recorded in the doc comment of
   `Semantics.lean` **and** in this file (below).
2. `paper_claim` must **not** be defined as, reference, or trivially alias `formal_claim`.
3. `intended_correspondence : formal_claim ↔ paper_claim` must have a **substantive proof**. It
   may not be `Iff.rfl`, `rfl`, `exact Iff.rfl` or similar, and it may not use the main theorem
   (it is a statement-level equivalence, not "both sides happen to be provable").
4. `formal_claim` is exactly the statement of the repository's main theorem, and
   `paper_claim_holds` is the main theorem transported across the correspondence.
5. Only `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, `admit`, `native_decide` or
   new `axiom` anywhere outside the draft directories in `TRUTH_GATE.lock`.
6. If the paper's English claim cannot be faithfully transcribed, or is not what Lean proves,
   the gate stays **red** and the mismatch is reported. Never patch over it: never weaken
   `paper_claim`, drop a hypothesis, or redefine it to match the formal side. If the
   formalization drifted, rewrite the formalization so it transports across the lock again.
7. Open problems stay hypotheses. No Millennium Prize problem is claimed solved; the gate only
   ensures the certificate proves precisely the locked claim and nothing else.
8. The locked region of `Semantics.lean`, the quote and `TRUTH_GATE.lock` change only with the
   author's explicit sign-off, as a PR that says "new lock" in its title.
9. Commits are authored by Benjamin Stanley Frohman only, with no AI co-author trailers. No
   force-push and no history rewriting.

## What `scripts/verify-lock.sh` checks mechanically

* `lake build` succeeds, with no `sorry` warning outside the draft directories;
* no `sorry` / `admit` / `native_decide` / `axiom` token outside the draft directories
  (comments and strings excluded);
* `Semantics.lean` has `PAPER_PATH`, `PAPER_SHA256`, `PAPER_SECTION` and a verbatim
  `PAPER_QUOTE`; the hash matches the paper file and the quote occurs in it; this file carries
  the same path, hash and quote;
* the lock region hash matches `TRUTH_GATE.lock`;
* `paper_claim`'s body does not mention `formal_claim`; the correspondence is not proved by
  `Iff.rfl`/`rfl`;
* in Lean: the bodies of `formal_claim` and `paper_claim` differ, the two are not
  definitionally equal, the correspondence proof does not reach the main theorem, the main
  theorem's statement is `formal_claim`, `paper_claim_holds` goes through the correspondence,
  and `#print axioms` shows only the three standard axioms.

What it cannot check: whether the transcription is the right reading of the English. That
reading is fixed once, in writing, below and in `Semantics.lean`, and is the author's sign-off.

## Running the gate locally

```
lake exe cache get
bash scripts/verify-lock.sh
```

Reports are written to `truth-gate-report/`.

## Failure classes (what a red Truth Gate means)

A red Truth Gate is not automatically a math failure. Since 2026-11-17, `scripts/verify-lock.sh`
runs every phase even after one fails. `scripts/truth_gate_classify.py` then sorts each failure
into exactly one class and prints a `TRUTH GATE VERDICT` block at the end of the log. The block
also goes to the job summary and to `truth-gate-report/classification.json`.

This exists because of frohmanian-tether-sdiff PR #13 (run 44039231121). That PR changed only CI,
but its merge ref was built on a main whose lock still had the old `paper_claim` form. The gate
printed `TRUTH GATE FAIL: this lock is NOT certifying` and `TRUTH GATE STATIC FAIL`, which read like
a proof failure, though every kernel check was green.

| Class | Raised by | What the verdict prints | What fixes it |
|---|---|---|---|
| **KERNEL/PROOF** | `lake build` fails; `sorry`/`admit`/`native_decide`/`axiom` outside the draft dirs; nonstandard axioms; a missing or ill-typed locked declaration; `intended_correspondence` fails to check | `KERNEL/PROOF FAILURE (a proof does not check)` and `This is a proof failure`, with the failing lines | Fix the proof. **This is the only class ever described as a proof failure.** |
| **LOCK-FORM** | `paper_claim` reuses a repository Prop or definition; a vacuous alias of `formal_claim`; an `rfl` correspondence; a partial lock; a lock marked `"certifying": false`; an edited lock region; missing `PAPER_*` fields | `LOCK-FORM: lock wording/form problem, not a math failure`, each offending identifier with `file:line` in the Semantics file and the `file:line` of its repository declaration, then the independent transcription that is required | Rewrite the paper side from the paper's own definition, in the paper's symbols, and prove `intended_correspondence` with real reasoning. A new lock needs the author's sign-off. |
| **PAPER-HASH** | the paper's sha256 differs from the lock | `PAPER-HASH: the paper changed after the lock (not a math failure)`, the commit whose bytes match the lock, every changed line, whether only copyright/license/attribution lines changed, and whether the locked quote is still verbatim | If the edit is intended, update `paper_sha256` in `TRUTH_GATE.lock`, the `PAPER_SHA256:` line in the Semantics file and the hash in this file, all in one commit. If the quote changed, that is a statement change and needs sign-off. |
| **STALE-BASE** | a PR's merge ref was built on an older main, and main has since changed the lock, a Semantics file, a paper or a gate script | `STALE-BASE: branch is behind main's lock; update branch (not a math failure)` | The workflow re-merges the PR head onto the current main and judges that merge, which is what would actually land. It goes red only if that merge conflicts, and then it says to update the branch. |

Two more labels can appear in the verdict:

* **`[INHERITED]`** appears when the PR touches no lock, vocabulary, Semantics or paper file but a
  LOCK-FORM or PAPER-HASH failure remains. The failure comes from main, so it has to be fixed on
  main.
* **`UNCLASSIFIED`** appears when a checker crashed or printed a message no rule recognises. It is
  shown verbatim and is never presumed to be a math failure.

The last line always states the classes, for example
`VERDICT: FAIL (LOCK-FORM). Kernel checks passed: no math was found false.`

### Lock-form lint (runs on every PR, no Lean needed)

The `lock-form-lint` job in `.github/workflows/truth-gate.yml` runs
`python3 scripts/truth_gate_classify.py lint --fetch-deps`. It collects every declaration in
`lean_roots` and in the author's own Lake dependencies (every non-Mathlib package in
`lake-manifest.json`), then reads `paper_claim` and any paper-side helper defined in the Semantics
file. It rejects:

1. any Prop that is a whole hypothesis or the conclusion of `formal_claim` (for example the old
   sdiff form `(∀ ν > 0, PeriodicTetherClosingBound ν) → …`). This is never allowed, with or without
   a vocabulary entry;
2. any other repository name that is not listed, with a reason, in `TRUTH_GATE.vocabulary.json`
   (basic notions such as the velocity-field type);
3. any name in `paper_forbidden_names`, and any mention of `formal_claim`.

`TRUTH_GATE.vocabulary.json` is lint configuration. It cannot change the locked claim, because the
lock region hash still pins `paper_claim`. For an existing author-approved lock, it records only the
basic names that the approved claim already uses. Any new name on the paper side goes into the
new-lock PR together with the author's sign-off.

### Tests

`scripts/tests/test_truth_gate_classify.py` has one throw-away fixture repository per class:

* KERNEL/PROOF: build error, sorry, nonstandard axioms;
* LOCK-FORM: named hypothesis Prop, unlisted repository name, alias, non-certifying,
  partial lock, vacuous lock;
* PAPER-HASH: copyright-only change, and a change to the quote;
* STALE-BASE: re-merge onto the current main, and a merge conflict;
* `[INHERITED]` label.

The `lock-form-lint` job runs them on every PR:

```
python3 -m unittest discover -s scripts/tests -p 'test_truth_gate_classify.py' -v
```

## The locked claim of this repository

* Paper: `paper/frohmanian-tether-verified.tex`
* sha256: `9653476e11264bfbc49db8b9ca99615e1ac9ed004b5357de0430126bf4fd2500`
* Section: Proved results (C1/C3, C2) and the energy-budget refutation; uniqueness and the comparison bound as recorded in Conditional results
* Main theorem(s): `energy_damping_iff_not_degenerate`, `frohmanianTether_self_nonpos_of_mul_nonneg`, `frohmanianTether_invariant`, `frohmanianTether_degenerate`, `tetherKernel_self_nonpos`, `tetherKernel_degenerates_on_kinetic_energy`, `uniqueness_of_minimal_metric_tether`, `comparison_bound`, `CE.d2_d1`, `CE.cocycle_of_coboundary`, `CE.symPart_not_cochain`
* Lock file: `TRUTH_GATE.lock`; semantics: `FTVerified/Semantics.lean`

Verbatim quote:

```
\item \textbf{The tether damps the energy budget.} This is refuted. Let $B$ be a symmetric bilinear form on a real vector space $V$ with $B(x,x)\le0$ for all $x\in V$ (C3), and let $h\in V$ stand for $\delta H$. Then $B(h,h)<0$ if and only if $B(m,h)\neq0$ for some $m\in V$. Consequently, if $B(m,h)=0$ for all $m$ (C2), then $B(h,h)=0$, so the tether contributes nothing to $dH/dt$; and if $B(h,h)=0$, then $B(m,h)=0$ for all $m$
```

```lean
def formal_claim : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ x, B x x ≤ 0) → ∀ h : V,
      (B h h < 0 ↔ ∃ m, B m h ≠ 0)

def paper_claim : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ x, B x x ≤ 0) → ∀ h : V,
      (B h h < 0 ↔ ∃ m, B m h ≠ 0) ∧
      ((∀ m, B m h = 0) → B h h = 0) ∧
      (B h h = 0 → ∀ m, B m h = 0)
```

See the doc comment of `FTVerified/Semantics.lean` for the fixed reading of the paper's terms and the scope.

## Status (2026-11-23): still NOT certifying

`TRUTH_GATE.lock` keeps `"certifying": false`, so the gate stays red on purpose.

Fixed on 2026-11-23: the 2026-11-16 re-audit found the lock was a tautology (`flow_contribution_zero_of_C2` is the term `hC2 M ω`, C2 read back). It is no longer cited. The paper item now states, and the lock certifies, `energy_damping_iff_not_degenerate`: for a symmetric bilinear form with `B(x,x) ≤ 0`, `B(h,h) < 0` iff `B(m,h) ≠ 0` for some `m`. The nontrivial direction is Cauchy–Schwarz for semidefinite forms (`bilin_kernel_of_nonpos_of_self_zero`); C2 is never the hypothesis that yields the conclusion. The lint findings (`CoadjointOrbit`, `Functional`, `KineticEnergyHamiltonian`, `DegenerateWRTKineticEnergy`) are gone: `paper_claim` uses Mathlib only. `scripts/TruthGateAudit.lean` now instantiates universe parameters before comparing the main theorem with `formal_claim` (same check as the sibling repositories).

Extended on 2026-11-23: the paper wording was corrected to the kernel (kernel C2 only under its three hypotheses; `frohmanian_symplectic_tether_theorem` is Route-A uniqueness, not a smoothness theorem; `tethered_jacobi_identity` assumes vanishing; self-pairing is locked under `κ w ≥ 0`). The lock now also covers abstract C1/C3/C2, both kernel self-pairing and kernel C2 (with those hypotheses), uniqueness relative to a coefficient-fixing `C3` in finite dimension at least 3, the ODE comparison bound, and the low-degree Chevalley–Eilenberg facts.

Still open (why the gate is red): the nine-term Jacobi expansion and field-model Jacobi identities; Jacobi special cases and the remaining refutations; Route-A feedback; Riccati blow-up and the maximum-principle lemmas; the global-regularity package; and every open item in Section 5.

The history of the 2026-11-16 re-audit is in git (`git log -p TRUTH_GATE.md`).
