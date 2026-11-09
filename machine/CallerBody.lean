import MinPlusCaller
import CacheFill
import RestoreFill
import CallerCompose
import CallerSchedule
import CallerSolves

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the summit body,
phase one (the skeleton).

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain whose scheduled rounds the product body drives
  (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  Light language is the pinned Anthropic statement's.
- Joshua Wharton (QFEX) — the canonical adapter arrangement, the checked
  selection round / restart-loop driver, and the machine-obligations record.
- Hrishik Sai Bojnal — the verified frontier being refined and the refined
  numerical certificate this body targets.

# The summit body, phase one: the caller's fixed program (the skeleton)

The INSIDE shape pinned in STMTS.md ("FILL 3 composition shape"): the
product-round body is the mpTask solver's core and the caller program's
ENTRY procedure; the cache, restore and stage procedures ride INSIDE,
behind it, at the shifted indices this module pins. The bodies themselves
trail board-side (the cache/restore cones and the product-round body are
the porting board's); the skeleton pins the program's shape, the entry
index arithmetic, and the phase target — nothing is proved falsely and
nothing is claimed beyond the shape.

Pinned here (all `rfl`-level shape facts):
- `callerProgram` — the caller's fixed program:
  `Program.behind [mpBody] (cacheProg ++ restoreProg ++ program cs)`;
  the sanctioned `Program.behind` route (`Ends` is not prepend-stable —
  piece 1's keystone), so every internal call index shifts by the layer
  it sits behind.
- `mpProc` — the entry index 0: procedure 0 IS the solver's core
  (`SummitSlot`'s `hs` at the caller program).
- `cacheProcIn` / `restoreProcIn` / `stageProcIn` — the fills' and the
  stage's entry indices in the caller program: the cache and restore at
  one plus their own indices (`cacheSlot_append`/`restoreSlot_append`
  keep their contracts under the growth), the stage at the L5/L6
  pinning's procedure 6 shifted behind the product body and the two
  fills (`stageMeets_behind`'s arithmetic, layered).
- `callerProgram_entry` — the entry procedure IS the product body.
- `CallerTarget` — the phase target, stated as a definition:
  `Light.Solves Light.mpTask (callerProgram …) mpProc Tn need` —
  exactly `SummitSlot`'s `hs` component at the caller program.

THE PHASE'S REMAINING SESSIONS (each a named target; the module docstring
records the producers):
- Target (a) — the mpRounds execution derivation: chain the certified
  stage calls over the mpRounds schedule inside the caller program, by
  induction over the schedule consuming `thread_step_append`'s
  chaining form and `stageMeats_behind`'s shifted slot (producer:
  the round-loop Ends assembly).
- Target (b) — the Post assembly: deliver `mpTask`'s Post — the
  `Seg μ' c (minPlusList …)` half via the oracle functional chain
  (`StoredMinPlusAPSP.apsp_correct` / `MinPlusReduction.bounded_signed_eq_minPlus`,
  conditioned on `DenseOracleCorrect` — upstream's own shape; D7's
  boundary stands) and the `KeptBut` half via `mpPost_interior`'s
  interior record (producer: the caller's Post packaging).
- Target (c) — the step count: the caller program's total Light-step
  count over one solver run (mpRounds stages at the pinned `taskTime` +
  the fills' certified clocks + the product body's own scan), lifted into
  `hdom` by `AsymptoticCosts.costBoundOfEventualDomination` with the
  clock bricks `taskTime_le_of_size` / `instanceSize_le` / `mpRounds_eq`
  (producer: the caller's clock accounting).

When (a)–(c) land, `CallerTarget` is discharged, `ThinMatrix.Summit.
SummitSlot` is filled, and `ThinMatrix.Summit.twin_of_summit` fires the
conservative filing statement unconditionally. D7's boundary stands: no
(min,+) product is claimed in this module; the oracle premise is
upstream's own shape.
-/

namespace ThinMatrix.CallerBody

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.WordRam
  ThinMatrix.MinPlusReduction ThinMatrix.MinPlusCaller
  Light.DenseRestartSelectionLoop Light
  ThinMatrix.CacheFill ThinMatrix.RestoreFill
  ThinMatrix.CallerCompose ThinMatrix.CallerSolves

/-! ## The caller's fixed program (the INSIDE shape, bodies trailing) -/

/-- The caller's fixed program: the product-round body is placed first
and the cache, restore and round programs ride behind it — the sanctioned
`Program.behind` route (`Ends` is not prepend-stable; piece 1's
keystone). Every internal call index of the behind layers shifts by the
length of the layer it sits behind. -/
def callerProgram (mpBody : Stmt) (cacheProg restoreProg : Light.Program)
    (cs : Inst) : Light.Program :=
  Program.behind [mpBody] (cacheProg ++ restoreProg ++ program cs)

/-- The product body's entry index: procedure 0 IS the solver's core. -/
def mpProc : ℕ := 0

/-- The cache fill's entry index inside the caller program: one behind
the product body, plus the cache's own entry. -/
def cacheProcIn (cacheProc : ℕ) : ℕ := 1 + cacheProc

/-- The restore fill's entry index inside the caller program: behind the
product body and the whole cache layer. -/
def restoreProcIn (cacheProg : Light.Program) (restoreProc : ℕ) : ℕ :=
  1 + cacheProg.length + restoreProc

/-- The stage slot's index inside the caller program: the L5/L6 pinning's
procedure 6 of the round program, shifted behind the product body and the
two fills (`stageMeets_behind`'s arithmetic, layered). -/
def stageProcIn (cacheProg restoreProg : Light.Program) : ℕ :=
  1 + cacheProg.length + restoreProg.length + 6

/-- The entry procedure IS the product body (the behind-shape's head). -/
theorem callerProgram_entry (mpBody : Stmt) (cacheProg restoreProg : Light.Program)
    (cs : Inst) :
    (callerProgram mpBody cacheProg restoreProg cs)[mpProc]? = some mpBody := by
  unfold callerProgram mpProc
  exact rfl

/-- The caller program's layers, unfolded (the behind equation at the
entry layer). -/
theorem callerProgram_behind (mpBody : Stmt) (cacheProg restoreProg : Light.Program)
    (cs : Inst) :
    callerProgram mpBody cacheProg restoreProg cs =
      [mpBody] ++ (cacheProg ++ restoreProg ++ program cs).map (Stmt.shift 1) := rfl

/-! ## The phase target (stated; the later sessions discharge it) -/

/-- The phase-one target — SummitSlot's `hs` component at the caller
program: the fixed program solves the (min,+) product task. Stated as a
definition; the phase's later sessions (the mpRounds execution
derivation, the Post assembly, the step count — see the module
docstring) discharge it, and `ThinMatrix.Summit.twin_of_summit` then
fires the conservative filing statement unconditionally. -/
def CallerTarget (mpBody : Stmt) (cacheProg restoreProg : Light.Program)
    (cs : Inst) (Tn : ℕ → ℕ → ℕ) (need : ℕ → ℕ → Light.Need) : Prop :=
  Light.Solves Light.mpTask (callerProgram mpBody cacheProg restoreProg cs)
    mpProc Tn need

#print axioms callerProgram_entry
#print axioms callerProgram_behind

end ThinMatrix.CallerBody
