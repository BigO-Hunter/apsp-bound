import MachineAdapter
import CoreCompatibility
import ConservativeAdapter

/-!
Copyright (c) 2026. APSP port campaign: the twin filing statement.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  landed `Race.bound` (exponent 2.995560766) is this module's root sibling,
  not its substitute.
- Joshua Wharton (QFEX) — the conservative adapter arrangement this module
  states, and the numerical refinement lineage.
- Hrishik Sai Bojnal — the verified frontier being refined.

# The twin: the conservative `Race.bound` form

The owner's twin form of the filing statement: `Race.bound` at the
conservative exponent `2994999/1000000` (= 2.994999; the conservative
row's exponent, M3e/M3f), closed VIA
`ThinMatrix.ConservativeAdapter.conservativeStatementOfLedger` from the
three canonical slots (`hs`, `hn`, `hdom` — byte-identical to the upstream
adapters' hypotheses). This module is a separate statement module: the
landed root `Race.bound` (exponent 2.995560766, Li Xuanji's proof with the
Wharton refinement) is untouched — no root swap; the filing call is the
owner's.

It closes NOTHING by itself: `hs` awaits the actual min-plus Light program
and `hdom` awaits that program's `completeCost` step-count bound
(MACHINE_OBLIGATIONS' two named remainders; `hn`'s PolyNeed side rides the
need need of the same future program). D7's boundary stands: no (min,+)
product is constructed or claimed here.
-/

namespace ThinMatrix.Twin

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.WordRam
  ThinMatrix.ConservativeAdapter

/-- The twin filing statement: the conservative `Race.bound` form —
`EndStatement.APSP.SolvedInTime (2994999/1000000)` — from the canonical
adapter's three slots. Conditional on `hs`/`hn`/`hdom` exactly as the
upstream `rationalStatementOfMinPlusExecution` chain is; the slots are the
campaign's named remainders. -/
theorem race_bound {P : Light.Program} {p : ℕ} {Tn : ℕ → ℕ → ℕ}
    {need : ℕ → ℕ → Light.Need}
    (hs : Light.Solves Light.mpTask P p Tn need)
    (hn : Light.PolyNeed need)
    (hdom : ∀ κ : Nat, ∃ (k : Nat) (C : Real), ∀ᶠ n : Nat in atTop,
      Light.timeUpTo (Light.Sec3.apTime Tn) n
        ((n : Real) ^ (κ : Real)) ≤
        C * AsymptoticCosts.completeCost k n) :
    EndStatement.APSP.SolvedInTime ((2994999 : Rat) / 1000000) :=
  conservativeStatementOfLedger hs hn hdom

#print axioms race_bound

end ThinMatrix.Twin
