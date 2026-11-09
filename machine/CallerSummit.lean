import MinPlusCaller
import MachineAdapter
import CoreCompatibility
import ConservativeAdapter
import TwinRaceBound

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the summit.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  landed `Race.bound` (2.995560766) is the root sibling.
- Joshua Wharton (QFEX) — the canonical adapter arrangement, the checked
  selection round / restart-loop driver, and the machine-obligations record.
- Hrishik Sai Bojnal — the verified frontier being refined and the refined
  numerical certificate this summit targets.

# FILL 3: the summit — the caller's slots as one existence claim

The campaign's named remainder (MACHINE_OBLIGATIONS): the actual min-plus
caller — a fixed Light program `P` whose solver body invokes the certified
stage, cache and restore procedures (the INSIDE shape pinned in STMTS.md),
with its execution derivation over the mpRounds schedule and its
`completeCost` step-count bound. Neither upstream nor the port closes it
on this route: upstream's own final theorem is conditional on an oracle
solver (`Filter2/Final.lean`'s `apsp_2995560766_of_oracle` takes the
`oracleTask` solver as a premise), and `Light.Solves.append` cannot create
a solver.

This module does NOT fake the body. It lands the summit's packaging — the
content that is real today — so the remainder is ONE named existence slot:

- `twin_of_summit` — the twin filing statement from the summit's mere
  EXISTENCE: if some fixed program carries the three canonical slots
  (`hs`, `hn`, `hdom`), the conservative `Race.bound` form
  (2.994999) follows. The twin's three named premises collapse into one
  slot; when the caller's body lands, this is the filing theorem.
- `realized_of_summit` — the canonical target's existence form: the
  summit's `hs` + `hn` realize the APSP end-statement on the upstream
  host's lifted clock (`MachineAdapter.realizedFromMinPlus`).

BOUNDARY (unchanged): no (min,+) product is constructed or claimed here;
the product-round body and the `completeCost` step-count bound remain the
campaign's named remainder. D7's boundary stands.
-/

namespace ThinMatrix.Summit

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.WordRam
  ThinMatrix.MinPlusReduction ThinMatrix.ConservativeAdapter

/-- The summit slot: a fixed program carries the canonical adapter's three
hypotheses — the actual min-plus solver, its polynomial need, and the
eventual `completeCost` domination of the host's exact lifted runtime.
One existence claim; the caller's product-round body is its content. -/
def SummitSlot : Prop :=
  ∃ (P : Light.Program) (p : ℕ) (Tn : ℕ → ℕ → ℕ) (need : ℕ → ℕ → Light.Need),
    Light.Solves Light.mpTask P p Tn need ∧
    Light.PolyNeed need ∧
    (∀ κ : Nat, ∃ (k : Nat) (C : Real), ∀ᶠ n : Nat in atTop,
      Light.timeUpTo (Light.Sec3.apTime Tn) n
        ((n : Real) ^ (κ : Real)) ≤
        C * AsymptoticCosts.completeCost k n)

/-- The twin filing statement from the summit's existence: the
conservative `Race.bound` form (2.994999) follows from the single slot.
When the caller's product-round body lands, this is the filing theorem —
no further composition. -/
theorem twin_of_summit (hsummit : SummitSlot) :
    EndStatement.APSP.SolvedInTime ((2994999 : Rat) / 1000000) := by
  obtain ⟨P, p, Tn, need, hs, hn, hdom⟩ := hsummit
  exact ThinMatrix.Twin.race_bound hs hn hdom

/-- The canonical target's existence form: the summit's solver and its
polynomial need realize the APSP end-statement on the upstream host's
lifted clock (`apTime`), via `MachineAdapter.realizedFromMinPlus`. -/
theorem realized_of_summit (hsummit : SummitSlot) :
    ∃ (Tn : ℕ → ℕ → ℕ),
      Realized EndStatement.APSP (Light.timeUpTo (Light.Sec3.apTime Tn)) := by
  obtain ⟨P, p, Tn, need, hs, hn, -⟩ := hsummit
  exact ⟨Tn, MachineAdapter.realizedFromMinPlus hs hn⟩

#print axioms twin_of_summit
#print axioms realized_of_summit

end ThinMatrix.Summit
