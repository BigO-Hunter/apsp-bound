import MinPlusCaller
import CallerStepCount
import CallerRun
import CallerWire
import CallerPost

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the summit body,
the UNIVERSAL-BODY session (PRODUCT_BODY.md §5): the instance-free program
term, the while-controlled round schedule, and the wire induction re-run
over the while semantics.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain whose scheduled rounds the universal body drives
  (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  Light language, its `pass` combinator and `Ends.shift` renumbering are the
  pinned statement's.
- Joshua Wharton (QFEX) — the canonical adapter arrangement, the checked
  selection round / restart-loop driver, and the machine-obligations record.
- Hrishik Sai Bojnal — the verified frontier being refined and the refined
  numerical certificate this body targets.

# The universal body: one fixed program over all instances

`Light.Solves` quantifies ONE fixed program over ALL instances, while the
per-instance skeleton (`CallerRun.mpBodyWithWrites`) bakes the instance
into the register indices (`v (t·x.n + u)` — a different register per
`x.n`). This module lands the universal form (PRODUCT_BODY.md §5):

- **The computed index registers**: `IdxR` (≠ `Tmp`, ≠ the frame registers
  0–8) is set per round to `t·x.n` by `.set` (`univRowPass`), and the
  per-entry addressing rides the upstream canonical pass combinator
  (`Light.pass`): `pass J (v Nreg) (v DstR) (v Tmp)` — store `Tmp`'s
  delivered value into `DstR + J` for `J < Nreg`. No register index in the
  program text depends on the instance.
- **The while-controlled schedule**: the round schedule is driven by the
  level-doubling loop `univWhile` — test `Lvl ≤ 2·U` (`Cond.le`), body =
  two certified rounds (both adaptive tests at every signed level) plus the
  counter updates. The loop runs exactly `signedLevels W` iterations, i.e.
  `mpRounds W = 2 · signedLevels W` rounds — ALL in one term.
- **The wire induction over the while semantics**: `univWire` re-runs the
  per-round wire induction (the landed `CallerWire.aux_wire_from_slots`'s
  round blocks: the slot family → `reads_carry`'s mask evolution → `hret`'s
  fold delivery → the row pass) under `Ends.while`, carrying the pins, the
  reads and the cell-(0,0) fold through the loop.

D7's boundary stands: the oracle return premise (`hret`), the certified
slot family (`hslots`), the flag budget, the KeptBut half and the
construction's identity are NAMED PREMISES throughout — no (min,+) product
is claimed, nothing here proves the oracle.
-/

namespace ThinMatrix.CallerUniversalBody

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam
  ThinMatrix.MinPlusReduction ThinMatrix.MinPlusCaller
  Light.DenseRestartSelectionLoop Light
  ThinMatrix.CallerPost ThinMatrix.CallerStepCount ThinMatrix.Summit
  ThinMatrix.CallerWrites ThinMatrix.CallerRun ThinMatrix.CallerBodyStep

/-! ## The register map (fixed, instance-free) -/

/-- The product base register: holds `x.c`. -/
abbrev Out : ℕ := 11
/-- The row-length register: holds `x.n`. -/
abbrev Nreg : ℕ := 12
/-- The loop-bound register: holds `2·x.U`. -/
abbrev U2 : ℕ := 13
/-- The level register: the while's doubling counter. -/
abbrev Lvl : ℕ := 14
/-- The flat round counter: holds `t` inside round `t`. -/
abbrev Rt : ℕ := 15
/-- THE FIXED INDEX REGISTER: set per round to `t·x.n` by `.set` —
replaces the per-instance skeleton's baked `v (t·x.n + u)` indices. -/
abbrev IdxR : ℕ := 16
/-- The write base register: holds `x.c + t·x.n` (the pass's `dst`). -/
abbrev DstR : ℕ := 17
/-- The pass counter: the entry index `j` inside the row. -/
abbrev J : ℕ := 18

/-- Every scratch register misses the stage frame (0–8), the result
register `Tmp = 10`, and each other. -/
theorem scratch_facts : Out ≠ Tmp ∧ Nreg ≠ Tmp ∧ U2 ≠ Tmp ∧ Lvl ≠ Tmp ∧ Rt ≠ Tmp ∧
    IdxR ≠ Tmp ∧ DstR ≠ Tmp ∧ J ≠ Tmp ∧ Nreg ≠ J ∧ DstR ≠ J ∧ Out ≠ J ∧ IdxR ≠ J ∧
    Lvl ≠ Rt ∧ Out ≠ Nreg ∧ U2 ≠ Lvl ∧ Rt ≠ Lvl ∧ Nreg ≠ IdxR ∧ Out ≠ IdxR ∧
    DstR ≠ IdxR ∧ Out ≠ DstR ∧ Nreg ≠ DstR ∧ U2 ≠ Rt ∧ Out ≠ Lvl ∧ Nreg ≠ Lvl ∧
    IdxR ≠ Lvl ∧ DstR ≠ Lvl ∧ Nreg ≠ Rt ∧ Out ≠ Rt ∧ IdxR ≠ Rt ∧ DstR ≠ Rt ∧
    U2 ≠ Nreg ∧ U2 ≠ IdxR ∧ U2 ≠ DstR ∧ U2 ≠ Out := by
  simp only [Out, Nreg, U2, Lvl, Rt, IdxR, DstR, J, Tmp]
  omega

/-! ## The universal body -/

/-- The prologue: the register-convention bridge from the `mpTask` frame
`[n, U, a, b, c, fr]` to the stage's nine-value frame at the caller's
layout (`CallerBodyStep`'s five buffers stacked from `fr`), the two
initialization passes (the active bits and the remaining flags — all
true), and the loop counters' seeding. Instance-free: every stored value
is computed from the frame registers. -/
def univPrologue : Light.Stmt :=
  .set Height (v 1) ;;                                  -- h := U
  .set U2 (k 2 *' v 1) ;;                               -- U2 := 2·U
  .set Out (v 4) ;;                                     -- Out := x.c
  .set Nreg (v 0) ;;                                    -- Nreg := n
  .set Len (v 0) ;;                                     -- I := n
  .set Active (v 5) ;;                                  -- ab := fr
  .set Rows (v Active +' v Nreg) ;;                     -- rb := fr + n
  .set Scores (v Rows +' (v Nreg *' v Nreg)) ;;         -- sb := rb + n²
  .set Base (v Scores +' v Nreg) ;;                     -- bb := sb + n
  .set Remaining (v Base +' v Nreg) ;;                  -- mb := bb + n
  .set Free (v Remaining +' v Nreg) ;;                  -- the stage's fr := mb + n
  pass J (v Nreg) (v Active) (k 1) ;;                   -- the active bits := 1
  pass J (v Nreg) (v Remaining) (k 1) ;;                -- the flags := 1
  .set Lvl (k 1) ;;                                     -- Lvl := 1
  .set Rt (k 0)                                         -- Rt := 0

/-- The per-round write pass: THE FIXED INDEX REGISTER (`IdxR := t·n` by
`.set` — the design's computed index), the write base (`DstR := x.c +
t·n`), and the row's stores through the upstream canonical pass — entry
`j` storing the delivered value `v Tmp` into `DstR + j` for `j < n`.
SHAPE NOTE (PRODUCT_BODY.md §5, pinned): the design sketch's per-entry
`set IdxR (t·n+j)` advance is realized by the canonical pass's counter
(`dst + c` addressing with `dst` in a register) — the same computed-index
content, with the inner while's induction owned by the library's proved
`Ends.pass` rule. The stored VALUE is the call's single delivery register
`Tmp` (a Light call updates only `Tmp`); the per-instance skeleton's
value-base registers `Tmp + u` are not expressible with a computed index,
and no landed conclusion consumes them (only entry 0's value reaches a
proved fact — the cell-(0,0) fold). -/
def univRowPass : Light.Stmt :=
  .set IdxR (v Rt *' v Nreg) ;;
  .set DstR (v Out +' v IdxR) ;;
  pass J (v Nreg) (v DstR) (v Tmp)

/-- The universal round: the certified stage call (the L5/L6 restart-loop
slot at the composed program's procedure index `stage`) followed by the
row's write pass. -/
def univRound (stage : ℕ) : Light.Stmt :=
  Light.Stmt.call stage callArgs Tmp ;; univRowPass

/-- The level body: BOTH adaptive rounds at the current signed level
(the schedule's two-call blocks), then the counter updates — the round
counter advances by two, the level register doubles. -/
def univLevelBody (stage : ℕ) : Light.Stmt :=
  univRound stage ;;
  .set Rt (v Rt +' k 1) ;;
  univRound stage ;;
  .set Rt (v Rt +' k 1) ;;
  .set Lvl (k 2 *' v Lvl)

/-- THE WHILE CONTROL: the level-doubling loop — test `Lvl ≤ 2·U`, one
certified round pair per level. Exactly `signedLevels W` iterations:
`mpRounds W` rounds in ONE fixed term (PRODUCT_BODY.md §5). -/
def univWhile (stage : ℕ) : Light.Stmt :=
  .while (v Lvl ≤' v U2) (univLevelBody stage)

/-- THE UNIVERSAL BODY: the prologue then the while-controlled schedule —
the entry procedure's fixed statement, one text over all instances. -/
def mpBodyUniv (stage : ℕ) : Light.Stmt :=
  univPrologue ;; univWhile stage

/-- The stage slot's procedure index inside the caller's composed
program (the landed `CallerBody.stageProcIn`'s arithmetic: the entry
layer, then the cache, restore, and the driver's six). -/
def stageProcIn (cacheProg restoreProg : Light.Program) : ℕ :=
  1 + cacheProg.length + restoreProg.length + 6

/-- THE CALLER'S FIXED PROGRAM: the universal body at the entry, the
cache/restore/stage procedures behind it — composed by NESTED
`Program.behind` (each layer shifts the next's internal call indices by
its own length, so the driver's internal round/loop indices resolve:
the latent flat-`++` composition of the per-instance skeleton is not
renumbering-consistent for cache/restore layers of length > 0). -/
def callerProgramUniv (stage : ℕ) (cacheProg restoreProg : Light.Program)
    (cs : Inst) : Light.Program :=
  Program.behind [mpBodyUniv stage]
    (Program.behind cacheProg (Program.behind restoreProg (program cs)))

/-- The entry procedure IS the universal body. -/
theorem callerProgramUniv_entry (stage : ℕ) (cacheProg restoreProg : Light.Program)
    (cs : Inst) :
    (callerProgramUniv stage cacheProg restoreProg cs)[0]? = some (mpBodyUniv stage) := by
  unfold callerProgramUniv
  exact rfl

/-- The caller program, unfolded: the entry layer, then the nested-behind
layers. -/
theorem callerProgramUniv_behind (stage : ℕ) (cacheProg restoreProg : Light.Program)
    (cs : Inst) :
    callerProgramUniv stage cacheProg restoreProg cs
      = [mpBodyUniv stage] ++ ((Program.behind cacheProg
          (Program.behind restoreProg (program cs))).map (Stmt.shift 1)) := rfl

/-- The shift composes: two behind-layers shift by the summed depth. -/
theorem shift_shift (s : Stmt) (m n : ℕ) :
    Stmt.shift n (Stmt.shift m s) = Stmt.shift (m + n) s := by
  induction s with
  | skip => rfl
  | set x e => rfl
  | store a e => rfl
  | seq s t ihs iht => simp only [Stmt.shift, ihs, iht]
  | ite c s t ihs iht => simp only [Stmt.shift, ihs, iht]
  | «while» c s ih => simp only [Stmt.shift, ih]
  | call p args x => simp only [Stmt.shift, Nat.add_assoc]

/-- The stage's body inside the caller program: the driver's loop
procedure, shifted by the full behind-depth (the restore layer, then the
cache layer, then the entry layer). -/
theorem callerProgramUniv_stage (stage : ℕ) (cacheProg restoreProg : Light.Program)
    (cs : Inst) (hstage : stage = stageProcIn cacheProg restoreProg)
    {body : Stmt} (hb : (program cs)[6]? = some body) :
    (callerProgramUniv stage cacheProg restoreProg cs)[stage]?
      = some (body.shift (restoreProg.length + (cacheProg.length + 1))) := by
  unfold callerProgramUniv stageProcIn at *
  rw [hstage]
  generalize (mpBodyUniv (1 + cacheProg.length + restoreProg.length + 6)) = q
  have h1 := Program.getElem?_behind_right restoreProg hb
  have h2 := Program.getElem?_behind_right cacheProg h1
  have h3 := Program.getElem?_behind_right [q] h2
  have hid : (1 + cacheProg.length + restoreProg.length + 6 : ℕ)
      = 6 + restoreProg.length + cacheProg.length + List.length [q] := by
    rw [List.length_singleton]; omega
  rw [hid, h3]
  congr 1
  rw [shift_shift, shift_shift]
  congr 1

/-! ## The universal pins -/

/-- The universal body's register contract at any state: the stage's
nine-value frame in registers 0–8, the computed registers holding the
caller's layout values, and the static address bookkeeping (every row
write's base in range; every per-round index within a word). -/
def UnivPins (lim : Limits) (vals : List ℤ) (x : MatInst) (W : ℕ) (σ : State) :
    Prop :=
  (∀ k' : ℕ, k' < 9 → σ.loc k' = vals.getD k' 0) ∧
  σ.loc Out = (x.c : ℤ) ∧
  σ.loc Nreg = (x.n : ℤ) ∧
  σ.loc U2 = (2 * x.U : ℤ) ∧
  (∀ t : ℕ, t < mpRounds W →
    ((x.c + t * x.n : ℕ) + x.n ≤ lim.space) ∧ |(t * x.n : ℤ)| ≤ lim.word)

/-- The pins' register half survives the stage call (the call updates
only `Tmp`, and every pinned register misses `Tmp`). -/
theorem UnivPins_update {lim : Limits} {vals : List ℤ} {x : MatInst} {W : ℕ}
    {l : ℕ → ℤ} {μ : ℕ → ℤ} {r : ℤ}
    (hp : UnivPins lim vals x W ⟨l, μ⟩) :
    UnivPins lim vals x W ⟨Function.update l Tmp r, μ⟩ := by
  unfold UnivPins at hp ⊢
  simp only [State.loc] at *
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k' hk'
    have hu : Function.update l Tmp r k' = l k' :=
      dif_neg (by have hT : Tmp = (10 : ℕ) := rfl; omega)
    rw [hu]
    exact h1 k' hk'
  · have hu : Function.update l Tmp r Out = l Out :=
      dif_neg (by norm_num [Out, Tmp])
    rw [hu]
    exact h2
  · have hu : Function.update l Tmp r Nreg = l Nreg :=
      dif_neg (by norm_num [Nreg, Tmp])
    rw [hu]
    exact h3
  · have hu : Function.update l Tmp r U2 = l U2 :=
      dif_neg (by norm_num [U2, Tmp])
    rw [hu]
    exact h4
  · intro t ht
    exact h5 t ht

/-- The pins are loc-only: they transfer along any state whose registers
agree. -/
theorem UnivPins_congr {lim : Limits} {vals : List ℤ} {x : MatInst} {W : ℕ}
    {σ σ' : State} (h : σ'.loc = σ.loc) (hp : UnivPins lim vals x W σ) :
    UnivPins lim vals x W σ' := by
  unfold UnivPins at hp ⊢
  simp only [h]
  exact hp

/-! ## The clock: the universal budget and its domination shape -/

/-- The per-store pass cost: the value expression `v Tmp` costs 1, and
the canonical pass takes `e.cost + 12` per entry. -/
def univRowBw : ℕ := 13

/-- The row pass's fixed overhead: the two `.set`s (4 + 4) and the
pass's tail (6). -/
def univRowFix : ℕ := 14

/-- The row pass's budget. -/
def univRowB (n : ℕ) : ℕ := univRowBw * n + univRowFix

/-- The round budget: the call's argument cost 9, the call overhead 2,
the tight stage clock, and the row pass. -/
def univRoundB (n : ℕ) : ℕ := 9 + 2 + callerTt n + univRowB n

/-- The level body's budget: two rounds and the three counter `.set`s
(4 + 4 + 4) with slack. -/
def univLevelB (n : ℕ) : ℕ := 2 * univRoundB n + 16

/-- The prologue's budget: the twelve `.set`s (40 steps) and the two
initialization passes (`2·(13n + 6)`), with slack. -/
def univProB (n : ℕ) : ℕ := 27 * n + 64

/-- The while's per-iteration test-plus-overhead: the test
`v Lvl ≤' v U2` costs 5; the loop rule adds it per iteration and once at
the exit. -/
def univTestB : ℕ := 6

/-- The per-round unit budget: the round itself, the level body's
counter updates, and the while's per-iteration test overhead. -/
def univUnitB (n : ℕ) : ℕ := univRoundB n + univLevelB n + univTestB

/-- THE UNIVERSAL CLOCK: `mpRounds U` rounds at the per-round unit
budget, plus the prologue. -/
def univTn (n U : ℕ) : ℕ :=
  mpRounds U * univUnitB n + univProB n

/-- The schedule's factor: `mpRounds W = 2 · signedLevels W`. -/
theorem mpRounds_eq_signed (W : ℕ) : mpRounds W = 2 * signedLevels W := by
  rw [mpRounds_eq]
  unfold signedLevels
  ring

/-- The schedule's level count is positive. -/
theorem signedLevels_pos (U : ℕ) : 1 ≤ signedLevels U := by
  unfold signedLevels
  omega

/-- The round budget is positive. -/
theorem univRoundB_pos (n : ℕ) : 1 ≤ univRoundB n := by
  simp only [univRoundB, univRowB, univRowBw, univRowFix, callerTt]
  omega

/-- The while's cost fits the schedule's unit budget: the level loop's
per-iteration overhead rides the round budget's slack. -/
theorem univWhile_cost (n U : ℕ) (hn : 1 ≤ n) :
    signedLevels U * (univTestB + univLevelB n) + univTestB
      ≤ mpRounds U * univUnitB n := by
  have hur := univRoundB_pos n
  have hul : 1 ≤ univLevelB n := by
    have := univRoundB_pos n
    unfold univLevelB
    omega
  rw [mpRounds_eq_signed]
  unfold univUnitB univTestB
  nlinarith [signedLevels_pos U, hur, hul]

/-- The universal budget is quadratic. -/
theorem univRoundB_le (n : ℕ) (hn : 1 ≤ n) : univRoundB n ≤ 250 * (n * n) := by
  have h1 : n ≤ n * n := Nat.le_mul_of_pos_right n (by omega)
  have hA : n * n + 6 * n + n ≤ 8 * (n * n) := by nlinarith
  have hB : 25 * (n * n + 6 * n + n) ≤ 200 * (n * n) := by nlinarith [hA]
  have hC : 13 * n ≤ 13 * (n * n) := Nat.mul_le_mul_left 13 h1
  have hD : (25 : ℕ) ≤ 25 * (n * n) :=
    Nat.mul_le_mul_left 25 (show (1 : ℕ) ≤ n * n from by nlinarith)
  simp only [univRoundB, univRowB, univRowBw, univRowFix, callerTt]
  omega

/-- The level body's budget is quadratic. -/
theorem univLevelB_le (n : ℕ) (hn : 1 ≤ n) : univLevelB n ≤ 510 * (n * n) := by
  have h1 : n ≤ n * n := Nat.le_mul_of_pos_right n (by omega)
  have hA : n * n + 6 * n + n ≤ 8 * (n * n) := by nlinarith
  have hB : 25 * (n * n + 6 * n + n) ≤ 200 * (n * n) := by nlinarith [hA]
  have hC : 13 * n ≤ 13 * (n * n) := Nat.mul_le_mul_left 13 h1
  have hD : (25 : ℕ) ≤ 25 * (n * n) :=
    Nat.mul_le_mul_left 25 (show (1 : ℕ) ≤ n * n from by nlinarith)
  unfold univLevelB univRoundB univRowB univRowBw univRowFix callerTt
  omega

/-- The unit budget is quadratic. -/
theorem univUnitB_le (n : ℕ) (hn : 1 ≤ n) : univUnitB n ≤ 770 * (n * n) := by
  have h2 := univRoundB_le n hn
  have h3 := univLevelB_le n hn
  have h6 : (6 : ℕ) ≤ 6 * (n * n) :=
    Nat.mul_le_mul_left 6 (show (1 : ℕ) ≤ n * n from by nlinarith)
  unfold univUnitB univTestB
  omega

/-- The whole universal budget is the schedule at the unit budget plus
the prologue (the definition, re-stated). -/
theorem univTn_eq (n U : ℕ) :
    univTn n U = mpRounds U * univUnitB n + univProB n := rfl

/-- The universal budget, bounded: `univTn n U ≤ (2·log₂U + 6)·770·n² +
27n + 64`. -/
theorem univTn_le (n U : ℕ) (hn : 1 ≤ n) :
    univTn n U ≤ (2 * Nat.log2 U + 6) * (770 * (n * n)) + 27 * n + 64 := by
  have hmp : mpRounds U ≤ 2 * Nat.log2 U + 6 := mpRounds_le_two_log_succ U
  have hU := univUnitB_le n hn
  have hAC : mpRounds U * univUnitB n ≤ (2 * Nat.log2 U + 6) * univUnitB n :=
    Nat.mul_le_mul_right _ hmp
  have hCB : (2 * Nat.log2 U + 6) * univUnitB n
      ≤ (2 * Nat.log2 U + 6) * (770 * (n * n)) :=
    Nat.mul_le_mul_left (2 * Nat.log2 U + 6) hU
  calc univTn n U
      = mpRounds U * univUnitB n + 27 * n + 64 := by
        unfold univTn univProB; ring
    _ ≤ (2 * Nat.log2 U + 6) * univUnitB n + 27 * n + 64 := by omega
    _ ≤ (2 * Nat.log2 U + 6) * (770 * (n * n)) + 27 * n + 64 := by omega

#print axioms scratch_facts
#print axioms shift_shift
#print axioms callerProgramUniv_entry
#print axioms callerProgramUniv_behind
#print axioms callerProgramUniv_stage
#print axioms UnivPins_update
#print axioms UnivPins_congr
#print axioms mpRounds_eq_signed
#print axioms univWhile_cost
#print axioms univRoundB_le
#print axioms univLevelB_le
#print axioms univUnitB_le
#print axioms univTn_le

end ThinMatrix.CallerUniversalBody
