/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import FTVerified.Sdiff.ObstructionAudit

/-!
# Truth Gate: semantics lock (see `TRUTH_GATE.md`)

PAPER_PATH: paper/frohmanian-tether-verified.tex
PAPER_SHA256: 93bde1b66ac8ee68e33935c77c95a7a76e7a1bd5badd9b66f6663f110886cef9

Locked paper claim (Section "Refuted claims", first item), quoted verbatim:

PAPER_QUOTE_BEGIN
\item \textbf{The tether damps the energy budget.} This is refuted. C2 forces $B(M,H)=0$, so the tether contributes nothing to $dH/dt$
PAPER_QUOTE_END

Reading of the paper's terms (fixed here, once):
* "C2" is condition (C2) of the compilation, `DegenerateWRTKineticEnergy B`;
* `B(M,H)` is the tether correction `B ω M H` at the state `ω`, `H` the kinetic energy
  `KineticEnergyHamiltonian`, `M` an arbitrary functional;
* "contributes nothing to `dH/dt`" means the tether term in `dH/dt`, namely `B ω H H`, is `0`.

`formal_claim` is the statement of the repository theorem
`FrohmanianTether.ObstructionAudit.flow_contribution_zero_of_C2`. `paper_claim` transcribes the
paper sentence: for every kernel satisfying C2, both `B(M,H) = 0` for all `M` and the `dH/dt`
contribution vanishes. `intended_correspondence` is a statement-level equivalence: its proof
does not use any theorem of the library.

Scope: this certifies only the locked sentence. It does not claim anything about global
regularity; the paper's Clay-standard regularity claim stays open.
-/

namespace TruthGate

open FrohmanianTether ArnoldGeometric

-- TRUTH-GATE LOCK BEGIN
/-- The repository's main statement (`flow_contribution_zero_of_C2`). -/
def formal_claim : Prop :=
  ∀ (B : CoadjointOrbit → Functional → Functional → ℝ),
    DegenerateWRTKineticEnergy B → ∀ (ω : CoadjointOrbit) (M : Functional),
      B ω M KineticEnergyHamiltonian = 0

/-- The paper's sentence: C2 forces `B(M,H) = 0`, so the tether contributes nothing to `dH/dt`. -/
def paper_claim : Prop :=
  ∀ (B : CoadjointOrbit → Functional → Functional → ℝ),
    DegenerateWRTKineticEnergy B → ∀ ω : CoadjointOrbit,
      (∀ M : Functional, B ω M KineticEnergyHamiltonian = 0) ∧
        B ω KineticEnergyHamiltonian KineticEnergyHamiltonian = 0

/-- The fixed correspondence between the formal statement and the paper's claim. -/
theorem intended_correspondence : formal_claim ↔ paper_claim := by
  constructor
  · intro h B hB ω
    exact ⟨fun M => h B hB ω M, h B hB ω KineticEnergyHamiltonian⟩
  · intro h B hB ω M
    exact (h B hB ω).1 M
-- TRUTH-GATE LOCK END

/-- The main theorem proves `formal_claim`. -/
theorem formal_claim_holds : formal_claim :=
  fun B hB ω M => ObstructionAudit.flow_contribution_zero_of_C2 B hB ω M

/-- The paper's claim, transported across the correspondence. -/
theorem paper_claim_holds : paper_claim :=
  intended_correspondence.mp formal_claim_holds

end TruthGate
