# TRUTH GATE — read this first

Author: Benjamin Stanley Frohman. This file is the root instruction for every person and every
automated agent that changes this repository. Load it before any other file.

## What the gate guarantees, and what it does not

The gate ties the Lean certificate to one fixed, quoted claim of the paper. A green
`truth-gate` check means exactly this:

1. `lake build` succeeds;
2. no `sorry`, `admit`, `native_decide` or `axiom` declaration occurs outside the draft
   directories listed in `TRUTH_GATE.lock`;
3. `Semantics.lean` contains `TruthGate.formal_claim` (the statement of the repository's main
   theorem), `TruthGate.paper_claim` (an independent Lean transcription of a sentence quoted
   verbatim from the paper, whose file hash is recorded) and the fixed theorem
   `TruthGate.intended_correspondence : formal_claim ↔ paper_claim`;
4. the correspondence is not vacuous: `formal_claim` and `paper_claim` are not definitionally
   equal, and the proof of the correspondence does not use the main theorem (it is a
   statement-level equivalence, not "both sides happen to be provable");
5. `paper_claim_holds` is obtained by transporting the main theorem across the correspondence;
6. all of these depend only on `propext`, `Classical.choice` and `Quot.sound`;
7. the locked region of `Semantics.lean` and the paper file are byte-identical to the hashes in
   `TRUTH_GATE.lock`.

It does **not** mean that the transcription is the only reasonable reading of the paper (that
reading is fixed once, by the author, in the docstring of `Semantics.lean`), that any
hypothesis named in the claim is true, or that any open problem is solved. No Millennium
Prize problem is claimed solved by any result in this repository.

## Rules

* No commit, PR or merge to `main` proceeds unless the `truth-gate` CI check is green.
* Never edit the region between `-- TRUTH-GATE LOCK BEGIN` and `-- TRUTH-GATE LOCK END`, the
  quoted paper text, or `TRUTH_GATE.lock`, except with the author's explicit sign-off; such a
  change is a new lock and must say so in the PR title.
* Never define `paper_claim` as `formal_claim`, never weaken `paper_claim`, never drop a
  hypothesis the paper states. Open problems stay hypotheses.
* If the formalization drifts so that the correspondence no longer holds, rewrite the
  formalization so that it transports across the lock again; do not patch the lock.
  If that is impossible, say so in the PR and leave the gate red.
* Work in progress that needs `sorry` lives only in a draft directory listed in
  `TRUTH_GATE.lock` and must not be imported by the library.
* Commits are authored by Benjamin Stanley Frohman only, with no AI co-author trailers.
* No force-push and no history rewriting.

## Running the gate locally

```
lake exe cache get
bash scripts/verify-lock.sh
```

Reports are written to `truth-gate-report/`.
