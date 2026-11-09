import MinPlusCaller
import CallerStepCount
import CallerRun
import CallerPost

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the summit body,
the data-flow session: the product-round body's caller-level packaging,
the mpTask-Post assembly, and the summit's conditional firing.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain the assembly's premises ride
  (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  Light language is the pinned statement's.
- Joshua Wharton (QFEX) — the canonical adapter arrangement, the checked
  selection round / restart-loop driver, and the machine-obligations record.
- Hrishik Sai Bojnal — the verified frontier being refined and the refined
  numerical certificate this body targets.

# The product-round body: the caller-level Post assembly

The design is `PRODUCT_BODY.md`; the landed machinery this module
packages: the wire (`CallerWire.wire_from_slots`), the Seg assembly
(`CallerRun.segOfBody_of` / `seg_of_entries`), the KeptBut bridge
(`CallerSegments.segTarget_of`), the reading lemma
(`CallerReading.readingAllRounds_of_socket`), and the Post packaging
(`CallerPost`). The step count is `CallerStepCount` (the B/Tt/9+2 budget
and `callerHdom`).

## The premises (D7's boundary — every one named, none claimed)

- `SummitWire` — the wire-level premise bundle at the bare round program:
  the certified slot family at the tight clock `callerTt` (the stage's
  own cost comparison, re-clocked), the oracle return premise `hret`
  (the stage call's return register carries the bracket fold — the
  oracle chain's content), the restart pinning's flag budget, the Ok
  fit, and the frame pinning at the task's start state (the prologue's
  deliverable). From it the LANDED `wire_from_slots` produces the
  wire-run.
- `SummitBodyPremises` — the assembly's Tier-A bundle:
  `hbus` (the wire-run's fold delivery, ∀ start state — a THEOREM of the
  wire session modulo `SummitWire`), `hident` (`CallerRun.MinPlusIdentity`
  — the construction's own conversion, conditioned on the oracle), and
  `hkept` (the KeptBut half at the caller program — the frame-relational
  premise; its discharge path is the SameOutside3-carrying wire induction
  under the write-region containment, PRODUCT_BODY.md §4).

## The universal-body seam (this session's design finding)

`Light.Solves` quantifies ONE fixed program over ALL instances, while
the landed write shapes bake the instance into the register indices
(`v (t·x.n + u)`). The run-derivation here is therefore the PER-INSTANCE
`Ends` at the caller program (`summitEnds_of_premises`); the instance-
free index-loop body that discharges `CallerTarget` (and through it
`SummitSlot`) is the named remainder (PRODUCT_BODY.md §5).

D7's boundary stands: no (min,+) product is claimed; the oracle and the
construction's identity are premises, never proofs.
-/

namespace ThinMatrix.CallerSummitBody

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam
  ThinMatrix.MinPlusReduction ThinMatrix.MinPlusCaller
  Light.DenseRestartSelectionLoop Light
  ThinMatrix.CallerPost ThinMatrix.CallerStepCount ThinMatrix.Summit
  ThinMatrix.CallerWrites ThinMatrix.CallerRun

/-! ## The caller's fixed layers and the product core's entry -/

/-- The caller's fixed program: the product core at the entry (procedure
0), the cache, restore and round programs riding behind it (the
`Program.behind` route — `Ends` is not prepend-stable). -/
def callerProgram (mpBody : Stmt) (cacheProg restoreProg : Light.Program)
    (cs : Inst) : Light.Program :=
  Program.behind [mpBody] (cacheProg ++ restoreProg ++ program cs)

/-- The layered program, unfolded: the entry layer followed by the
shifted inner layers. -/
theorem callerProgram_eq (mpBody : Stmt) (cacheProg restoreProg : Light.Program)
    (cs : Inst) :
    callerProgram mpBody cacheProg restoreProg cs
      = [mpBody] ++ ((cacheProg ++ restoreProg ++ program cs).map
        (Stmt.shift 1)) := rfl

/-- THE PRODUCT CORE'S ENTRY BODY: the mpRounds schedule of (certified
stage call ;; bracket-row write pass) pairs, at the caller's shifted
stage index (`stageProcIn`). This is the per-instance body — the
universal index-loop form is the named remainder (PRODUCT_BODY.md §5). -/
def mpBodySummit (cacheProg restoreProg : Light.Program) (Out : ℕ)
    (x : MatInst) (W : ℕ) : Light.Stmt :=
  ((mpBodyWithWrites 6 Out x W).shift (cacheProg.length + restoreProg.length)).shift 1

/-- The entry procedure IS the product core. -/
theorem callerProgram_entry (mpBody : Stmt)
    (cacheProg restoreProg : Light.Program) (cs : Inst) :
    (callerProgram mpBody cacheProg restoreProg cs)[0]? = some mpBody := by
  unfold callerProgram
  exact rfl

/-! ## The assembly: the mpTask Post at the caller program -/

/-- THE ASSEMBLY (per instance): from the Tier-A premises, the caller
program's product-core run delivers the `mpTask` Post — the `minPlusList`
at the product region (the Seg half, via the state-level identity) and
the `KeptBut` frame (the named kept premise).

The three premises (D7's boundary — each named, none claimed):
- `hbus` — the wire-run's fold delivery, ∀ start state, at the bare
  round program (`CallerRun`'s `BracketFinal` shape). A THEOREM of the
  landed wire session modulo the wire bundle (PRODUCT_BODY.md §4):
  `wire_from_slots` at the task frame.
- `hident` — `CallerRun.MinPlusIdentity`: the construction's own
  conversion (the bracket cells' final state = the min-plus entries),
  conditioned on the oracle premise.
- `hkept` — the KeptBut half at the caller program, ∀ start state. Named;
  discharge path: the SameOutside3-carrying wire induction under the
  write-region containment (`mpRounds W ≤ x.n`), the next session's
  opener.

The assembly re-runs the segOfBody_of pattern at the fixed start state:
from `hkept`'s run witness σ', the Seg half is derived STATE-level
(`hident σ' (hbus σ')` — no run needed) and the KeptBut rides the same
witness. -/
theorem summitEnds_of_premises
    {lim : Limits} {d : ℕ}
    {P k I h : ℕ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {ab rb sb mb bb fr : ℕ} {μ₀ : ℕ → ℤ} {R : Light.Program}
    {cacheProg restoreProg : Light.Program} {x : MatInst} {Out : ℕ}
    (W : ℕ) (tests : ℕ → Bool × Bool)
    (hbus : ∀ (σ'' : State),
      Ends lim (program (callSite P k I h active remaining rows
        ab rb sb mb bb) ++ []) d (mpBodyWithWrites 6 Out x W) σ''
        (mpRounds W * callerB x.n)
        (fun σ' => bracketAccumulate 0 tests (mpRounds W)
          = σ'.mem (bracketCell x 0 0)))
    (hident : @MinPlusIdentity lim d P k I h active remaining rows
      ab rb sb mb bb fr 0 (mpRounds W * callerB x.n) (fun _ => 0) μ₀
      ([] : Light.Program) x Out W tests)
    (hkept : ∀ (σ'' : State),
      Ends lim (callerProgram (mpBodySummit cacheProg restoreProg Out x W)
        cacheProg restoreProg
        (callSite P k I h active remaining rows ab rb sb mb bb) ++ R) d
        (mpBodySummit cacheProg restoreProg Out x W) σ''
        (mpRounds W * callerB x.n)
        (fun σ' => KeptBut μ₀ σ'.mem fr x.c (x.n * x.n))) :
    Ends lim (callerProgram (mpBodySummit cacheProg restoreProg Out x W)
      cacheProg restoreProg
      (callSite P k I h active remaining rows ab rb sb mb bb) ++ R) d
      (mpBodySummit cacheProg restoreProg Out x W)
      ⟨frame (argsOf (callSite P k I h active remaining rows ab rb sb mb bb)
        ++ [(fr : ℤ)]), μ₀⟩
      (mpRounds W * callerB x.n)
      (fun σ' => Seg σ'.mem x.c (minPlusList x.n x.A x.B) ∧
        KeptBut μ₀ σ'.mem fr x.c (x.n * x.n)) := by
  obtain ⟨σ', c, he, hc, hkb⟩ := hkept
    ⟨frame (argsOf (callSite P k I h active remaining rows ab rb sb mb bb)
      ++ [(fr : ℤ)]), μ₀⟩
  have hseg : Seg σ'.mem x.c (minPlusList x.n x.A x.B) :=
    seg_of_entries (hident σ' (hbus σ'))
  exact ⟨σ', c, he, hc, ⟨hseg, hkb⟩⟩

/-! ## The conditional summit -/

/-- THE SUMMIT'S CONDITIONAL PACKAGING: given the caller-target (the
universal body's run-derivation — the named remainder), the need, and
the landed domination, the summit slot is witnessed by the caller's own
fixed program. `CallerPost.summit_of_CallerTarget` is the same content
at the `CallerBody` program; this is its restatement at this module's
program term. -/
theorem summitSlot_of (htarget : Light.Solves Light.mpTask
    (callerProgram (mpBodySummit cacheProg restoreProg Out x W) cacheProg
      restoreProg (callSite P kk I h active remaining rows ab rb sb mb bb))
    0 callerTn callerNeed)
    (hn : Light.PolyNeed callerNeed)
    (hdom : CallerHdom callerTn) :
    SummitSlot := by
  refine ⟨callerProgram (mpBodySummit cacheProg restoreProg Out x W) cacheProg
    restoreProg (callSite P kk I h active remaining rows ab rb sb mb bb),
    0, callerTn, callerNeed, htarget, hn, hdom⟩

/-- THE TWIN'S CONDITIONAL FIRE: the conservative `Race.bound` form
(2.994999) from the caller's packaging. When the universal body lands
(PRODUCT_BODY.md §5), this is the filing theorem. -/
theorem twin_of (htarget : Light.Solves Light.mpTask
    (callerProgram (mpBodySummit cacheProg restoreProg Out x W) cacheProg
      restoreProg (callSite P kk I h active remaining rows ab rb sb mb bb))
    0 callerTn callerNeed)
    (hn : Light.PolyNeed callerNeed)
    (hdom : CallerHdom callerTn) :
    EndStatement.APSP.SolvedInTime ((2994999 : Rat) / 1000000) :=
  twin_of_summit (summitSlot_of htarget hn hdom)

#print axioms callerProgram_entry
#print axioms summitEnds_of_premises
#print axioms summitSlot_of
#print axioms twin_of

end ThinMatrix.CallerSummitBody
