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
def univRowFix : ℕ := 16

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

/-! ## The row pass's run (the computed-index write semantics) -/

/-- The pins read only the frame registers 0–8 and the three pinned
computed registers — they transfer along any register map agreeing
outside the three scratch registers. -/
theorem UnivPins_loc {lim : Limits} {vals : List ℤ} {x : MatInst} {W : ℕ}
    {σ σ' : State}
    (hloc : ∀ i : ℕ, i ≠ IdxR → i ≠ DstR → i ≠ J → σ'.loc i = σ.loc i)
    (hp : UnivPins lim vals x W σ) : UnivPins lim vals x W σ' := by
  have hO : Out = (11 : ℕ) := rfl
  have hN : Nreg = (12 : ℕ) := rfl
  have hU : U2 = (13 : ℕ) := rfl
  have hl : IdxR = (16 : ℕ) := rfl
  have hld : DstR = (17 : ℕ) := rfl
  have hlj : J = (18 : ℕ) := rfl
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k' hk'
    rw [hloc k' (by rw [hl]; omega) (by rw [hld]; omega) (by rw [hlj]; omega)]
    exact h1 k' hk'
  · rw [hloc Out (by rw [hO, hl]; norm_num) (by rw [hO, hld]; norm_num)
      (by rw [hO, hlj]; norm_num)]
    exact h2
  · rw [hloc Nreg (by rw [hN, hl]; norm_num) (by rw [hN, hld]; norm_num)
      (by rw [hN, hlj]; norm_num)]
    exact h3
  · rw [hloc U2 (by rw [hU, hl]; norm_num) (by rw [hU, hld]; norm_num)
      (by rw [hU, hlj]; norm_num)]
    exact h4
  · intro t ht
    exact h5 t ht

/-- THE ROW PASS'S RUN: from a pinned state whose round counter reads `t`
and whose `Tmp` holds the delivered value `r`, the pass writes `r` into
every cell of row `t` (the first entry's write is the cell fact the wire
consumes), keeps every cell outside the row, and preserves the pins. The
inner while's induction is owned by the library's proved `Ends.pass` rule
— the per-entry bookkeeping (counter, addressing, safety) is upstream's. -/
theorem univRowPass_runs
    {lim : Limits} {P : Light.Program} {d : ℕ} {x : MatInst} {W : ℕ}
    {vals : List ℤ} {ll : ℕ → ℤ} {μ : ℕ → ℤ} {r : ℤ} {t : ℕ} {T : ℕ}
    (hxn : 1 ≤ x.n)
    (hpins : UnivPins lim vals x W ⟨ll, μ⟩)
    (hspace : (lim.space : ℤ) ≤ lim.word)
    (hRt : ll Rt = (t : ℤ)) (hTmp : ll Tmp = r)
    (htW : t < mpRounds W)
    (hT : univRowB x.n ≤ T) :
    Ends lim P d univRowPass ⟨ll, μ⟩ T
      (fun σ' => σ'.mem (x.c + t * x.n) = r ∧
        UnivPins lim vals x W σ' ∧
        (∀ b' : ℕ, (b' < x.c + t * x.n ∨ x.c + t * x.n + x.n ≤ b') →
          σ'.mem b' = μ b')) := by
  obtain ⟨hframe, hOut, hNreg, hU2, haddr⟩ := hpins
  obtain ⟨harea, hidx⟩ := haddr t htW
  have h10 : Tmp = (10 : ℕ) := rfl
  have h11 : Out = (11 : ℕ) := rfl
  have h12 : Nreg = (12 : ℕ) := rfl
  have h13 : U2 = (13 : ℕ) := rfl
  have h16 : IdxR = (16 : ℕ) := rfl
  have h17 : DstR = (17 : ℕ) := rfl
  have h18 : J = (18 : ℕ) := rfl
  simp only [State.loc, State.mem] at hframe hOut hNreg hU2
  have hposB : (0 : ℤ) ≤ ((x.c + t * x.n : ℕ) : ℤ) := by omega
  have hwordB : ((x.c + t * x.n : ℕ) : ℤ) + (x.n : ℤ) ≤ lim.space := by
    have hcast : (((x.c + t * x.n : ℕ) + x.n : ℕ) : ℤ)
        = ((x.c + t * x.n : ℕ) : ℤ) + (x.n : ℤ) := by push_cast; ring
    have := harea
    omega
  have hwordC : ((x.c : ℤ)) + ((t * x.n : ℕ) : ℤ) ≤ lim.word := by
    have hcast : ((x.c + t * x.n : ℕ) : ℤ) = (x.c : ℤ) + ((t * x.n : ℕ) : ℤ) := by
      push_cast; ring
    have := hspace
    have := hwordB
    have hpos : (0 : ℤ) ≤ ((x.c + t * x.n : ℕ) : ℤ) := by omega
    have hxn' : (0 : ℤ) ≤ (x.n : ℤ) := by omega
    omega
  have hwordCA : |(x.c : ℤ) + ((t * x.n : ℕ) : ℤ)| ≤ lim.word := by
    rw [abs_of_nonneg (by have := hwordC; omega : (0 : ℤ) ≤ (x.c : ℤ) + ((t * x.n : ℕ) : ℤ))]
    exact hwordC
  -- the registers after the two sets
  set ll₂ : ℕ → ℤ := fun i =>
    if i = DstR then ((x.c + t * x.n : ℕ) : ℤ) else
    if i = IdxR then ((t * x.n : ℕ) : ℤ) else ll i with hll₂def
  have hll₂ : ∀ i : ℕ, i ≠ IdxR → i ≠ DstR → ll₂ i = ll i := by
    intro i h1 h2
    rw [hll₂def]
    simp only [h2, h1, if_false]
  have hll₂Idx : ll₂ IdxR = ((t * x.n : ℕ) : ℤ) := by rw [hll₂def]; simp
  have hll₂Dst : ll₂ DstR = ((x.c + t * x.n : ℕ) : ℤ) := by rw [hll₂def]; simp
  have hll₂Nreg : ll₂ Nreg = (x.n : ℤ) := by
    rw [hll₂ Nreg (by norm_num [Nreg, IdxR]) (by norm_num [Nreg, DstR])]
    exact hNreg
  have hll₂Tmp : ll₂ Tmp = r := by
    rw [hll₂ Tmp (by norm_num [Tmp, IdxR]) (by norm_num [Tmp, DstR])]
    exact hTmp
  -- the pass's own run at the sets' post
  have hpass : Ends lim P d (pass J (v Nreg) (v DstR) (v Tmp)) ⟨ll₂, μ⟩
      (13 * x.n + 6)
      (fun σ' => σ'.mem (x.c + t * x.n) = r ∧
        UnivPins lim vals x W σ' ∧
        (∀ b' : ℕ, (b' < x.c + t * x.n ∨ x.c + t * x.n + x.n ≤ b') →
          σ'.mem b' = μ b')) := by
    refine Ends.pass (fun _ => r) ?_ ?_ hspace harea hll₂Nreg
      (show ll₂ DstR = ((x.c + t * x.n : ℕ) : ℕ) from by
        rw [hll₂def]; simp)
      (by norm_num [Nreg, J]) (by norm_num [DstR, J]) ?_
    · -- round j: the value expression is the delivery register
      intro j hj
      refine ⟨trivial, ?_⟩
      show Function.update ll₂ J j Tmp = (fun _ => r) j
      have hu : Function.update ll₂ J j Tmp = ll₂ Tmp :=
        dif_neg (by rw [h18, h10]; norm_num)
      rw [hu]
      exact hll₂Tmp
    · -- done: the write conclusion at the pass's post
      refine ⟨?_, ?_, ?_⟩
      · have hw := wrote_done (μ := μ) (dst := (x.c + t * x.n : ℕ))
          (f := fun _ => r) (i := 0) (j := x.n) (by omega)
        simpa using hw
      · refine UnivPins_loc (σ := ⟨ll, μ⟩) ?_ ⟨hframe, hOut, hNreg, hU2, haddr⟩
        intro i hi1 hi2 hi3
        show Function.update ll₂ J (x.n : ℤ) i = ll i
        have hu2 : Function.update ll₂ J (x.n : ℤ) i = ll₂ i :=
          dif_neg (by rw [h18]; omega)
        rw [hu2]
        exact hll₂ i hi1 hi2
      · intro b' hb'
        show wrote μ (x.c + t * x.n) (fun _ => r) x.n b' = μ b'
        exact wrote_rest hb'
    · -- the pass's cost
      simp only [Expr.cost]
      have huniv : univRowB x.n = 13 * x.n + 16 := by
        simp only [univRowB, univRowBw, univRowFix]
      omega
  -- the second set + the pass, at any register map holding the computed values
  have key : ∀ ll' : ℕ → ℤ,
      ll' IdxR = ((t * x.n : ℕ) : ℤ) →
      (∀ i : ℕ, i ≠ IdxR → ll' i = ll i) →
      Ends lim P d (.set DstR (v Out +' v IdxR) ;;
        pass J (v Nreg) (v DstR) (v Tmp)) ⟨ll', μ⟩
        (Expr.cost (v Out +' v IdxR) + 1 + (13 * x.n + 6))
        (fun σ' => σ'.mem (x.c + t * x.n) = r ∧
          UnivPins lim vals x W σ' ∧
          (∀ b' : ℕ, (b' < x.c + t * x.n ∨ x.c + t * x.n + x.n ≤ b') →
            σ'.mem b' = μ b')) := by
    intro ll' hI hne
    refine Ends.seq (Expr.cost (v Out +' v IdxR) + 1) (13 * x.n + 6) ?_
      (by simp only [Expr.cost]; omega)
    refine Ends.set ?_ (by simp only [Expr.cost]; omega) ?_
    · show True ∧ True ∧ |ll' Out + ll' IdxR| ≤ lim.word
      rw [hne Out (by rw [h11, h16]; norm_num), hOut, hI]
      exact ⟨trivial, trivial, hwordCA⟩
    · show (fun σ'' => Ends lim P d (pass J (v Nreg) (v DstR) (v Tmp)) σ''
          (13 * x.n + 6)
          (fun σ' => σ'.mem (x.c + t * x.n) = r ∧
            UnivPins lim vals x W σ' ∧
            (∀ b' : ℕ, (b' < x.c + t * x.n ∨ x.c + t * x.n + x.n ≤ b') →
              σ'.mem b' = μ b')))
        ⟨Function.update ll' DstR (ll' Out + ll' IdxR), μ⟩
      have hu : Function.update ll' DstR (ll' Out + ll' IdxR) = ll₂ := by
        funext i
        by_cases hi : i = IdxR
        · subst hi
          have hu1 : Function.update ll' DstR (ll' Out + ll' IdxR) IdxR
              = ll' IdxR := dif_neg (by rw [h17, h16]; norm_num)
          rw [hu1, hI, hll₂Idx]
        · by_cases hi2 : i = DstR
          · subst hi2
            simp only [Function.update_self]
            rw [hne Out (by rw [h11, h16]; norm_num), hOut, hI, ← Nat.cast_add,
              hll₂Dst]
          · have hu3 : Function.update ll' DstR (ll' Out + ll' IdxR) i = ll' i :=
              dif_neg hi2
            rw [hu3]
            have hu4 : ll' i = ll i := hne i hi
            rw [hu4]
            exact (hll₂ i hi hi2).symm
      rw [hu]
      exact hpass
  -- the first set, then key
  refine Ends.seq (Expr.cost (v Rt *' v Nreg) + 1)
    (Expr.cost (v Out +' v IdxR) + 1 + (13 * x.n + 6)) ?_ ?_
  · refine Ends.set ?_ (by simp only [Expr.cost]; omega) ?_
    · show True ∧ True ∧ |ll Rt * ll Nreg| ≤ lim.word
      rw [hRt, hNreg]
      exact ⟨trivial, trivial, hidx⟩
    · exact key (Function.update ll IdxR (ll Rt * ll Nreg))
        (by simp only [Function.update_self, hRt, hNreg, Nat.cast_mul])
        (fun i hi => dif_neg hi)
  · simp only [Expr.cost]
    have huniv : univRowB x.n = 13 * x.n + 16 := by
      simp only [univRowB, univRowBw, univRowFix]
    omega

#print axioms univRowPass_runs

/-! ## The certified slot family at the caller program -/

/-- THE UNIVERSAL SLOT FAMILY: the certified stage slot (the L5/L6
restart-loop wrapper's `Meets`, byte-identical premises to the landed
wire's `hslots`) re-keyed to the caller program's stage index — the
per-round socket the universal body consumes. -/
def UnivSlot {lim : Limits} {d : ℕ} {P k I h : ℕ} {active : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr : ℕ}
    (stage : ℕ) (cacheProg restoreProg : Light.Program) (cs : Inst)
    (R : Light.Program) (Tt : ℕ → ℕ) : Prop :=
  ∀ (mask : ℕ → Bool) (kt : ℕ) (μ : ℕ → ℤ),
    ThinMatrix.CallerChain.StageReads P I active mask rows ab rb mb μ →
    kt ≤ (flagged P mask).card →
    (Light.DenseRestartSelectionLoop.need
      (instanceSize (callSite P kt I h active mask rows ab rb sb mb bb))
      (callSite P kt I h active mask rows ab rb sb mb bb).height).Ok lim fr (d + 1) →
    Meets lim (callerProgramUniv stage cacheProg restoreProg cs ++ R)
      stage (d + 1)
      (argsOf (callSite P k I h active mask rows ab rb sb mb bb) ++ [(fr : ℤ)]) μ
      (Tt kt)
      (pinnedPost (callSite P kt I h active mask rows ab rb sb mb bb) μ fr)

/-- THE ROUND SLICE'S RUN: one certified stage call followed by the
row's write pass, at the caller program. Round 0 writes the delivered
fold into the product's cell (0,0); rounds ≥ 1 keep the carried value;
every round preserves the pins and the reads at the evolved mask (the
stage's certified post clears one flag — `reads_carry`; the row's stores
miss the reads regions — the layout, the product region below the
stage's active base). -/
theorem univRound_runs
    {lim : Limits} {d : ℕ} {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr : ℕ}
    {cacheProg restoreProg : Light.Program} {cs : Inst}
    {stage : ℕ} {Tt : ℕ → ℕ} {R : Light.Program}
    {x : MatInst} {W : ℕ} {tests : ℕ → Bool × Bool}
    {vals : List ℤ} {ll : ℕ → ℤ} {μ : ℕ → ℤ} {mask : ℕ → Bool}
    {t : ℕ} {w : ℤ} {T : ℕ}
    (hxn : 1 ≤ x.n)
    (hvals : vals = argsOf (callSite P k I h active remaining rows ab rb sb mb bb)
      ++ [(fr : ℤ)])
    (hslot : @UnivSlot lim d P k I h active rows ab rb sb mb bb fr
      stage cacheProg restoreProg cs R Tt)
    (hret : ∀ (t' : ℕ) (mask' : ℕ → Bool) (μ' μ'' : ℕ → ℤ) (r' : ℤ),
      t' < mpRounds W →
      Light.DenseRestartSelectionLoop.Post
        (callSite P k I h active mask' rows ab rb sb mb bb) μ' μ'' →
      r' = bracketAccumulate (μ' (x.c + t' * x.n)) tests (mpRounds W))
    (hflag : ∀ mask' : ℕ → Bool, k ≤ (flagged P mask').card)
    (hok : ∀ (mask' : ℕ → Bool) (kt : ℕ),
      (Light.DenseRestartSelectionLoop.need
        (instanceSize (callSite P kt I h active mask' rows ab rb sb mb bb))
        (callSite P kt I h active mask' rows ab rb sb mb bb).height).Ok lim fr (d + 1))
    (hpins : UnivPins lim vals x W ⟨ll, μ⟩)
    (hRt : ll Rt = (t : ℤ))
    (hreads : ThinMatrix.CallerChain.StageReads P I active mask rows ab rb mb μ)
    (hlay : InOrder (callerFr fr P I) [(callerAb fr I, I), (callerRb fr I, P * I),
      (callerSb fr P I, P), (callerBb fr P I, I), (callerMb fr P I, P)])
    (haway : (x.c < callerSb fr P I ∨ callerSb fr P I + P ≤ x.c) ∧
      (x.c < callerBb fr P I ∨ callerBb fr P I + I ≤ x.c) ∧
      (x.c < callerMb fr P I ∨ callerMb fr P I + P ≤ x.c))
    (hbelow : (x.c + x.n * x.n : ℕ) ≤ ab)
    (hlay' : ab = callerAb fr I ∧ rb = callerRb fr I ∧ sb = callerSb fr P I ∧
      bb = callerBb fr P I ∧ mb = callerMb fr P I)
    (hw : μ x.c = w)
    (hspace : (lim.space : ℤ) ≤ lim.word)
    (hregion : mpRounds W ≤ x.n)
    (htW : t < mpRounds W)
    (hdim : d < lim.depth)
    (hTtk : Tt k ≤ callerTt x.n)
    (hT : univRoundB x.n ≤ T) :
    Ends lim (callerProgramUniv stage cacheProg restoreProg cs ++ R) d (univRound stage)
      ⟨ll, μ⟩ (univRoundB x.n)
      (fun σ' => ∃ mask' : ℕ → Bool,
        ThinMatrix.CallerChain.StageReads P I active mask' rows ab rb mb σ'.mem ∧
        UnivPins lim vals x W σ' ∧
        σ'.mem x.c = (if t = 0 then bracketAccumulate (μ x.c) tests (mpRounds W) else w)) := by
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hlay'
  have hframe := hpins.1
  simp only [State.loc] at hframe
  have hcallcost : (callArgs.map Expr.cost).sum + 2 + Tt k
      + univRowB x.n ≤ univRoundB x.n := by
    have h9 : (callArgs.map Expr.cost).sum = 9 := callArgs_cost
    simp only [univRoundB, univRowB, univRowBw, univRowFix]
    omega
  have hrowT : univRowB x.n ≤ univRoundB x.n - ((callArgs.map Expr.cost).sum + 2 + Tt k) := by
    omega
  unfold univRound
  refine Ends.seq ((callArgs.map Expr.cost).sum + 2 + Tt k)
    (univRoundB x.n - ((callArgs.map Expr.cost).sum + 2 + Tt k)) ?_ (by omega)
  have hslot' := hslot (mask := mask) (kt := k) (μ := μ) hreads (hflag mask) (hok mask k)
  refine Ends.callLast hslot' ?_ ?_ hdim
    (by simp only [callArgs_cost, univRoundB, univRowB, univRowBw, univRowFix]
        omega)
  · -- the continuation: the evolved reads, the pins, and the cell fact
    intro r₁ μ₁ hR
    obtain ⟨cs₁, hlen, hnd, hmem, hmask, hsam, h0', hpos⟩ := id hR
    have hreads₁ :=
      ThinMatrix.CallerChain.reads_carry (P := P) (I := I) (h := h) hlay hreads hsam hmask
    have hpinsμ₁ : UnivPins lim vals x W ⟨ll, μ₁⟩ := UnivPins_congr rfl hpins
    have hpins₁ : UnivPins lim vals x W ⟨Function.update ll Tmp r₁, μ₁⟩ :=
      UnivPins_update hpinsμ₁
    have huR : Function.update ll Tmp r₁ Rt = ll Rt :=
      dif_neg (by have h15 : Rt = (15 : ℕ) := rfl; have h10 : Tmp = (10 : ℕ) := rfl; omega)
    have hRt₁ : Function.update ll Tmp r₁ Rt = (t : ℤ) := by rw [huR]; exact hRt
    have hTmp₁ : Function.update ll Tmp r₁ Tmp = r₁ := rfl
    refine (univRowPass_runs hxn hpins₁ hspace hRt₁ hTmp₁ htW hrowT).mono le_rfl ?_
    rintro σ' ⟨hW, hP', hK⟩
    -- the reads survive the row's stores (the reads regions sit at and
    -- above the stage's active base, the product region below it)
    have hrowaway : ∀ (b' : ℕ), ab ≤ b' → x.c + t * x.n + x.n ≤ b' := by
      intro b' hb'
      have h1 : x.c + x.n * x.n ≤ ab := hbelow
      have h2 : t * x.n + x.n ≤ x.n * x.n := by
        have h3 : t + 1 ≤ x.n := by omega
        have h4 : (t + 1) * x.n ≤ x.n * x.n := Nat.mul_le_mul h3 (Nat.le_refl x.n)
        have h5 : (t + 1) * x.n = t * x.n + x.n := by ring
        omega
      omega
    refine ⟨maskCleared cs₁.toFinset mask, ?_, hP', ?_⟩
    · refine ⟨fun i hi => ?_, fun p hp i hi => ?_, fun p hp => ?_⟩
      · have hk := hK (ab + i) (Or.inr (hrowaway (ab + i) (by omega)))
        rw [hk]; exact hreads₁.1 i hi
      · have hk := hK (callerRb ab I + p * I + i)
          (Or.inr (hrowaway _ (show ab ≤ callerRb ab I + p * I + i from by
            simp only [callerRb]; omega)))
        rw [hk]; exact hreads₁.2.1 p hp i hi
      · have hk := hK (callerMb ab P I + p)
          (Or.inr (hrowaway _ (show ab ≤ callerMb ab P I + p from by
            simp only [callerMb]; omega)))
        rw [hk]; exact hreads₁.2.2 p hp
    · by_cases h0 : t = 0
      · subst h0
        have hfold := hret 0 mask μ μ₁ r₁ htW
          ⟨cs₁, hlen, hnd, hmem, hmask, hsam, h0', hpos⟩
        simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero] at hfold
        show σ'.mem x.c = bracketAccumulate (μ x.c) tests (mpRounds W)
        have hW' : σ'.mem x.c = r₁ := by simpa using hW
        rw [hW', hfold]
      · have ht1 : 1 ≤ t := by omega
        have hk := hK x.c (Or.inl (show x.c < x.c + t * x.n from
          Nat.lt_add_of_pos_right (Nat.mul_pos ht1 hxn)))
        rw [hk, hsam x.c haway, if_neg h0]
        exact hw
  · -- the call's arguments: safe, with the pinned frame values
    refine ⟨fun e he => ?_, ?_⟩
    · simp only [callArgs, List.mem_cons] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
      · exact trivial
      · exact trivial
      · exact trivial
      · exact trivial
      · exact trivial
      · exact trivial
      · exact trivial
      · exact trivial
      · exact trivial
      · exact absurd h (by simp)
    · have hlits : callArgs.map (fun x => Expr.val ⟨ll, μ⟩ x) =
        [ll 0, ll 1, ll 2, ll 3, ll 4, ll 5, ll 6, ll 7, ll 8] := rfl
      rw [hlits, hframe 0 (by omega), hframe 1 (by omega), hframe 2 (by omega),
        hframe 3 (by omega), hframe 4 (by omega), hframe 5 (by omega),
        hframe 6 (by omega), hframe 7 (by omega), hframe 8 (by omega), hvals]
      rfl

#print axioms univRound_runs

/-- The pins survive a register write outside the pinned registers
(the frame 0–8, Out, Nreg, U2). -/
theorem UnivPins_set {lim : Limits} {vals : List ℤ} {x : MatInst} {W : ℕ}
    {l : ℕ → ℤ} {μ : ℕ → ℤ} {i : ℕ} {v : ℤ}
    (hp : UnivPins lim vals x W ⟨l, μ⟩)
    (hfr : ∀ k' : ℕ, k' < 9 → i ≠ k') (hO : i ≠ Out) (hN : i ≠ Nreg) (hU : i ≠ U2) :
    UnivPins lim vals x W ⟨Function.update l i v, μ⟩ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  simp only [State.loc] at h1 h2 h3 h4 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k' hk'
    show Function.update l i v k' = vals.getD k' 0
    have hu : Function.update l i v k' = l k' := dif_neg (fun h => hfr k' hk' h.symm)
    rw [hu]
    exact h1 k' hk'
  · show Function.update l i v Out = (x.c : ℤ)
    have hu : Function.update l i v Out = l Out := dif_neg (fun h => hO h.symm)
    rw [hu]
    exact h2
  · show Function.update l i v Nreg = (x.n : ℤ)
    have hu : Function.update l i v Nreg = l Nreg := dif_neg (fun h => hN h.symm)
    rw [hu]
    exact h3
  · show Function.update l i v U2 = (2 * x.U : ℤ)
    have hu : Function.update l i v U2 = l U2 := dif_neg (fun h => hU h.symm)
    rw [hu]
    exact h4
  · intro t ht
    exact h5 t ht

/-- The level-loop invariant: the pins, the doubling level, the flat
round counter, the reads at the evolved mask, and the cell-(0,0) state
(the seed before the first round; the delivered fold from round 1 on). -/
def UnivInv (lim : Limits) (vals : List ℤ) (x : MatInst) (W : ℕ)
    (P I : ℕ) (active : ℕ → Bool) (rows : ℕ → ℕ → ℕ) (ab rb mb : ℕ)
    (μ₀ : ℕ → ℤ) (tests : ℕ → Bool × Bool) (ell : ℕ) (σ : State) : Prop :=
  UnivPins lim vals x W σ ∧
  σ.loc Lvl = ((2 ^ ell : ℕ) : ℤ) ∧
  σ.loc Rt = ((2 * ell : ℕ) : ℤ) ∧
  (∃ mask' : ℕ → Bool,
    ThinMatrix.CallerChain.StageReads P I active mask' rows ab rb mb σ.mem) ∧
  σ.mem x.c = (if ell = 0 then μ₀ x.c else bracketAccumulate (μ₀ x.c) tests (mpRounds W))

/- (`WireUnivTarget` is DEFINED BELOW, immediately after `UnivInvAll` — see the
note there. Its hypothesis is the strengthened invariant `UnivInvAll`, which
cannot be referenced before that def exists, so the target moved rather than
being restated with a hypothesis the induction cannot close on.) -/

/-! ## The row pass's run, strengthened (the full row + the kept cells) -/

/-- THE ROW PASS'S RUN, STRENGTHENED: the landed `univRowPass_runs` plus
the full-row write — every entry `u < x.n` of row `t` receives the pass's
delivered value (the canonical pass's `wrote` semantics, `wrote_done` at
every entry, not only entry 0). The conclusion's shape serves the wire
induction's all-cells tracking. -/
theorem univRowPass_runs'
    {lim : Limits} {P : Light.Program} {d : ℕ} {x : MatInst} {W : ℕ}
    {vals : List ℤ} {ll : ℕ → ℤ} {μ : ℕ → ℤ} {r : ℤ} {t : ℕ} {T : ℕ}
    (hxn : 1 ≤ x.n)
    (hpins : UnivPins lim vals x W ⟨ll, μ⟩)
    (hspace : (lim.space : ℤ) ≤ lim.word)
    (hRt : ll Rt = (t : ℤ)) (hTmp : ll Tmp = r)
    (htW : t < mpRounds W)
    (hT : univRowB x.n ≤ T) :
    Ends lim P d univRowPass ⟨ll, μ⟩ T
      (fun σ' => UnivPins lim vals x W σ' ∧
        (∀ u : ℕ, u < x.n → σ'.mem (x.c + t * x.n + u) = r) ∧
        (∀ b' : ℕ, (b' < x.c + t * x.n ∨ x.c + t * x.n + x.n ≤ b') →
          σ'.mem b' = μ b') ∧
        (∀ i : ℕ, i ≠ IdxR → i ≠ DstR → i ≠ J → σ'.loc i = ll i)) := by
  obtain ⟨hframe, hOut, hNreg, hU2, haddr⟩ := hpins
  obtain ⟨harea, hidx⟩ := haddr t htW
  have h10 : Tmp = (10 : ℕ) := rfl
  have h11 : Out = (11 : ℕ) := rfl
  have h12 : Nreg = (12 : ℕ) := rfl
  have h13 : U2 = (13 : ℕ) := rfl
  have h16 : IdxR = (16 : ℕ) := rfl
  have h17 : DstR = (17 : ℕ) := rfl
  have h18 : J = (18 : ℕ) := rfl
  simp only [State.loc, State.mem] at hframe hOut hNreg hU2
  have hposB : (0 : ℤ) ≤ ((x.c + t * x.n : ℕ) : ℤ) := by omega
  have hwordB : ((x.c + t * x.n : ℕ) : ℤ) + (x.n : ℤ) ≤ lim.space := by
    have hcast : (((x.c + t * x.n : ℕ) + x.n : ℕ) : ℤ)
        = ((x.c + t * x.n : ℕ) : ℤ) + (x.n : ℤ) := by push_cast; ring
    have := harea
    omega
  have hwordC : ((x.c : ℤ)) + ((t * x.n : ℕ) : ℤ) ≤ lim.word := by
    have hcast : ((x.c + t * x.n : ℕ) : ℤ) = (x.c : ℤ) + ((t * x.n : ℕ) : ℤ) := by
      push_cast; ring
    have := hspace
    have := hwordB
    have hpos : (0 : ℤ) ≤ ((x.c + t * x.n : ℕ) : ℤ) := by omega
    have hxn' : (0 : ℤ) ≤ (x.n : ℤ) := by omega
    omega
  have hwordCA : |(x.c : ℤ) + ((t * x.n : ℕ) : ℤ)| ≤ lim.word := by
    rw [abs_of_nonneg (by have := hwordC; omega : (0 : ℤ) ≤ (x.c : ℤ) + ((t * x.n : ℕ) : ℤ))]
    exact hwordC
  set ll₂ : ℕ → ℤ := fun i =>
    if i = DstR then ((x.c + t * x.n : ℕ) : ℤ) else
    if i = IdxR then ((t * x.n : ℕ) : ℤ) else ll i with hll₂def
  have hll₂ : ∀ i : ℕ, i ≠ IdxR → i ≠ DstR → ll₂ i = ll i := by
    intro i h1 h2
    rw [hll₂def]
    simp only [h2, h1, if_false]
  have hll₂Idx : ll₂ IdxR = ((t * x.n : ℕ) : ℤ) := by rw [hll₂def]; simp
  have hll₂Dst : ll₂ DstR = ((x.c + t * x.n : ℕ) : ℤ) := by rw [hll₂def]; simp
  have hll₂Nreg : ll₂ Nreg = (x.n : ℤ) := by
    rw [hll₂ Nreg (by norm_num [Nreg, IdxR]) (by norm_num [Nreg, DstR])]
    exact hNreg
  have hll₂Tmp : ll₂ Tmp = r := by
    rw [hll₂ Tmp (by norm_num [Tmp, IdxR]) (by norm_num [Tmp, DstR])]
    exact hTmp
  have hpass : Ends lim P d (pass J (v Nreg) (v DstR) (v Tmp)) ⟨ll₂, μ⟩
      (13 * x.n + 6)
      (fun σ' => UnivPins lim vals x W σ' ∧
        (∀ u : ℕ, u < x.n → σ'.mem (x.c + t * x.n + u) = r) ∧
        (∀ b' : ℕ, (b' < x.c + t * x.n ∨ x.c + t * x.n + x.n ≤ b') →
          σ'.mem b' = μ b') ∧
        (∀ i : ℕ, i ≠ IdxR → i ≠ DstR → i ≠ J → σ'.loc i = ll i)) := by
    refine Ends.pass (fun _ => r) ?_ ?_ hspace harea hll₂Nreg
      (show ll₂ DstR = ((x.c + t * x.n : ℕ) : ℕ) from by
        rw [hll₂def]; simp)
      (by norm_num [Nreg, J]) (by norm_num [DstR, J]) ?_
    · -- round j: the value expression is the delivery register
      intro j hj
      refine ⟨trivial, ?_⟩
      show Function.update ll₂ J j Tmp = (fun _ => r) j
      have hu : Function.update ll₂ J j Tmp = ll₂ Tmp :=
        dif_neg (by rw [h18, h10]; norm_num)
      rw [hu]
      exact hll₂Tmp
    · -- done: the pins, the full-row write, the kept cells, and the loc
      refine ⟨UnivPins_loc (σ := ⟨ll, μ⟩) ?_ ⟨hframe, hOut, hNreg, hU2, haddr⟩, ?_, ?_, ?_⟩
      · intro i hi1 hi2 hi3
        show Function.update ll₂ J (x.n : ℤ) i = ll i
        have hu2 : Function.update ll₂ J (x.n : ℤ) i = ll₂ i :=
          dif_neg (by rw [h18]; omega)
        rw [hu2]
        exact hll₂ i hi1 hi2
      · intro u hu
        have hw := wrote_done (μ := μ) (dst := (x.c + t * x.n : ℕ))
          (f := fun _ => r) (i := u) (by omega)
        simpa using hw
      · intro b' hb'
        show wrote μ (x.c + t * x.n) (fun _ => r) x.n b' = μ b'
        exact wrote_rest hb'
      · intro i hi1 hi2 hi3
        show Function.update ll₂ J (x.n : ℤ) i = ll i
        have hu2 : Function.update ll₂ J (x.n : ℤ) i = ll₂ i :=
          dif_neg (by rw [h18]; omega)
        rw [hu2]
        exact hll₂ i hi1 hi2
    · -- the pass's cost
      simp only [Expr.cost]
      have huniv : univRowB x.n = 13 * x.n + 16 := by
        simp only [univRowB, univRowBw, univRowFix]
      omega
  have key : ∀ ll' : ℕ → ℤ,
      ll' IdxR = ((t * x.n : ℕ) : ℤ) →
      (∀ i : ℕ, i ≠ IdxR → ll' i = ll i) →
      Ends lim P d (.set DstR (v Out +' v IdxR) ;;
        pass J (v Nreg) (v DstR) (v Tmp)) ⟨ll', μ⟩
        (Expr.cost (v Out +' v IdxR) + 1 + (13 * x.n + 6))
        (fun σ' => UnivPins lim vals x W σ' ∧
          (∀ u : ℕ, u < x.n → σ'.mem (x.c + t * x.n + u) = r) ∧
          (∀ b' : ℕ, (b' < x.c + t * x.n ∨ x.c + t * x.n + x.n ≤ b') →
            σ'.mem b' = μ b') ∧
          (∀ i : ℕ, i ≠ IdxR → i ≠ DstR → i ≠ J → σ'.loc i = ll i)) := by
    intro ll' hI hne
    refine Ends.seq (Expr.cost (v Out +' v IdxR) + 1) (13 * x.n + 6) ?_
      (by simp only [Expr.cost]; omega)
    refine Ends.set ?_ (by simp only [Expr.cost]; omega) ?_
    · show True ∧ True ∧ |ll' Out + ll' IdxR| ≤ lim.word
      rw [hne Out (by rw [h11, h16]; norm_num), hOut, hI]
      exact ⟨trivial, trivial, hwordCA⟩
    · show (fun σ'' => Ends lim P d (pass J (v Nreg) (v DstR) (v Tmp)) σ''
          (13 * x.n + 6)
          (fun σ' => UnivPins lim vals x W σ' ∧
            (∀ u : ℕ, u < x.n → σ'.mem (x.c + t * x.n + u) = r) ∧
            (∀ b' : ℕ, (b' < x.c + t * x.n ∨ x.c + t * x.n + x.n ≤ b') →
              σ'.mem b' = μ b') ∧
            (∀ i : ℕ, i ≠ IdxR → i ≠ DstR → i ≠ J → σ'.loc i = ll i)))
        ⟨Function.update ll' DstR (ll' Out + ll' IdxR), μ⟩
      have hu : Function.update ll' DstR (ll' Out + ll' IdxR) = ll₂ := by
        funext i
        by_cases hi : i = IdxR
        · subst hi
          have hu1 : Function.update ll' DstR (ll' Out + ll' IdxR) IdxR
              = ll' IdxR := dif_neg (by rw [h17, h16]; norm_num)
          rw [hu1, hI, hll₂Idx]
        · by_cases hi2 : i = DstR
          · subst hi2
            simp only [Function.update_self]
            rw [hne Out (by rw [h11, h16]; norm_num), hOut, hI, ← Nat.cast_add,
              hll₂Dst]
          · have hu3 : Function.update ll' DstR (ll' Out + ll' IdxR) i = ll' i :=
              dif_neg hi2
            rw [hu3]
            have hu4 : ll' i = ll i := hne i hi
            rw [hu4]
            exact (hll₂ i hi hi2).symm
      rw [hu]
      exact hpass
  refine Ends.seq (Expr.cost (v Rt *' v Nreg) + 1)
    (Expr.cost (v Out +' v IdxR) + 1 + (13 * x.n + 6)) ?_ ?_
  · refine Ends.set ?_ (by simp only [Expr.cost]; omega) ?_
    · show True ∧ True ∧ |ll Rt * ll Nreg| ≤ lim.word
      rw [hRt, hNreg]
      exact ⟨trivial, trivial, hidx⟩
    · exact key (Function.update ll IdxR (ll Rt * ll Nreg))
        (by simp only [Function.update_self, hRt, hNreg, Nat.cast_mul])
        (fun i hi => dif_neg hi)
  · simp only [Expr.cost]
    have huniv : univRowB x.n = 13 * x.n + 16 := by
      simp only [univRowB, univRowBw, univRowFix]
    omega

#print axioms univRowPass_runs'

/-! ## The row-index arithmetic (the all-cells tracking's disjointness) -/

/-- Two rows' cells are disjoint: a cell of row `t'` (entry `u' < n`) lies
outside row `t` whenever the row indices differ (linear arithmetic after
distribution). -/
theorem row_disjoint {n t t' u' : ℕ} (hnt : t' ≠ t) (hu' : u' < n) :
    t' * n + u' < t * n ∨ t * n + n ≤ t' * n + u' := by
  rcases Nat.lt_or_ge t' t with h | h
  · exact Or.inl (by
      have h1 : (t' + 1) * n ≤ t * n := Nat.mul_le_mul_right n (by omega)
      have h2 : (t' + 1) * n = t' * n + n := by ring
      omega)
  · exact Or.inr (by
      have h1 : (t + 1) * n ≤ t' * n := Nat.mul_le_mul_right n (by omega)
      have h2 : (t + 1) * n = t * n + n := by ring
      omega)

/-! ## The round slice's run, corrected and strengthened -/

/-- THE ROUND SLICE'S RUN, CORRECTED AND STRENGTHENED (the wire
induction's brick; supersedes this module's earlier `univRound_runs`
bundle, which is kept): the layout premise is the RAW `InOrder` at the
layout's top `fr` — the convention of the landed chain and per-instance
wire (`chain_from`, `wire_from_slots`) — so `fr` is register 8's value
(the stage's own free pointer, the call's ninth argument), matching the
program's prologue, which sets `Free := mb + n` (the top). The earlier
bundle pinned the buffers at `callerAb fr I …` and the ninth argument at
the same `fr` — a base/top conflation that is not instantiable against
the actual program. The conclusion adds what the all-cells tracking
consumes: the full row written to the round's delivery `r`, the row's
disjointness (cells of other rows are unchanged), and the cells below the
caller's free pointer `frC` and outside the product region unchanged. -/
theorem univRound_runs'
    {lim : Limits} {d : ℕ} {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr frC : ℕ}
    {cacheProg restoreProg : Light.Program} {cs : Inst}
    {stage : ℕ} {Tt : ℕ → ℕ} {R : Light.Program}
    {x : MatInst} {W : ℕ} {tests : ℕ → Bool × Bool}
    {vals : List ℤ} {ll : ℕ → ℤ} {μ : ℕ → ℤ} {mask : ℕ → Bool}
    {t : ℕ} {w : ℤ} {T : ℕ}
    (hxn : 1 ≤ x.n)
    (hvals : vals = argsOf (callSite P k I h active remaining rows ab rb sb mb bb)
      ++ [(fr : ℤ)])
    (hslot : @UnivSlot lim d P k I h active rows ab rb sb mb bb fr
      stage cacheProg restoreProg cs R Tt)
    (hret : ∀ (t' : ℕ) (mask' : ℕ → Bool) (μ' μ'' : ℕ → ℤ) (r' : ℤ),
      t' < mpRounds W →
      Light.DenseRestartSelectionLoop.Post
        (callSite P k I h active mask' rows ab rb sb mb bb) μ' μ'' →
      r' = bracketAccumulate (μ' (x.c + t' * x.n)) tests (mpRounds W))
    (hflag : ∀ mask' : ℕ → Bool, k ≤ (flagged P mask').card)
    (hok : ∀ (mask' : ℕ → Bool) (kt : ℕ),
      (Light.DenseRestartSelectionLoop.need
        (instanceSize (callSite P kt I h active mask' rows ab rb sb mb bb))
        (callSite P kt I h active mask' rows ab rb sb mb bb).height).Ok lim fr (d + 1))
    (hpins : UnivPins lim vals x W ⟨ll, μ⟩)
    (hRt : ll Rt = (t : ℤ))
    (hreads : ThinMatrix.CallerChain.StageReads P I active mask rows ab rb mb μ)
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)])
    (hfrCle : frC ≤ ab)
    (haway : (x.c < sb ∨ sb + P ≤ x.c) ∧
      (x.c < bb ∨ bb + I ≤ x.c) ∧
      (x.c < mb ∨ mb + P ≤ x.c))
    (hbelow : (x.c + x.n * x.n : ℕ) ≤ ab)
    (hw : μ x.c = w)
    (hspace : (lim.space : ℤ) ≤ lim.word)
    (hregion : mpRounds W ≤ x.n)
    (htW : t < mpRounds W)
    (hdim : d < lim.depth)
    (hTtk : Tt k ≤ callerTt x.n)
    (hT : univRoundB x.n ≤ T) :
    Ends lim (callerProgramUniv stage cacheProg restoreProg cs ++ R) d (univRound stage)
      ⟨ll, μ⟩ (univRoundB x.n)
      (fun σ' => ∃ (mask' : ℕ → Bool) (r : ℤ),
        ThinMatrix.CallerChain.StageReads P I active mask' rows ab rb mb σ'.mem ∧
        UnivPins lim vals x W σ' ∧
        r = bracketAccumulate (μ (x.c + t * x.n)) tests (mpRounds W) ∧
        (∀ u : ℕ, u < x.n → σ'.mem (x.c + t * x.n + u) = r) ∧
        (∀ t' u' : ℕ, t' < mpRounds W → u' < x.n → t' ≠ t →
          σ'.mem (x.c + t' * x.n + u') = μ (x.c + t' * x.n + u')) ∧
        (∀ b' : ℕ, b' < frC → (b' < x.c ∨ x.c + x.n * x.n ≤ b') →
          σ'.mem b' = μ b') ∧
        (∀ i : ℕ, i ≠ Tmp → i ≠ IdxR → i ≠ DstR → i ≠ J → σ'.loc i = ll i)) := by
  have hframe := hpins.1
  simp only [State.loc] at hframe
  have hcallcost : (callArgs.map Expr.cost).sum + 2 + Tt k
      + univRowB x.n ≤ univRoundB x.n := by
    have h9 : (callArgs.map Expr.cost).sum = 9 := callArgs_cost
    simp only [univRoundB, univRowB, univRowBw, univRowFix]
    omega
  have hrowT : univRowB x.n ≤ univRoundB x.n - ((callArgs.map Expr.cost).sum + 2 + Tt k) := by
    omega
  -- the layout's ordering facts (InOrder unfolds conjunctively)
  have hlayc : ab + I ≤ rb ∧ rb + P * I ≤ sb ∧ sb + P ≤ bb ∧ bb + I ≤ mb ∧
      mb + P ≤ fr := hlay
  obtain ⟨h1l, h2l, h3l, h4l, h5l⟩ := hlayc
  have habsb : ab ≤ sb := by omega
  unfold univRound
  refine Ends.seq ((callArgs.map Expr.cost).sum + 2 + Tt k)
    (univRoundB x.n - ((callArgs.map Expr.cost).sum + 2 + Tt k)) ?_ (by omega)
  have hslot' := hslot (mask := mask) (kt := k) (μ := μ) hreads (hflag mask) (hok mask k)
  refine Ends.callLast hslot' ?_ ?_ hdim
    (by simp only [callArgs_cost, univRoundB, univRowB, univRowBw, univRowFix]
        omega)
  · -- the continuation: the evolved reads, the pins, and the tracked cells
    intro r₁ μ₁ hR
    obtain ⟨cs₁, hlen, hnd, hmem, hmask, hsam, h0', hpos⟩ := id hR
    have hreads₁ :=
      ThinMatrix.CallerChain.reads_carry (P := P) (I := I) (h := h) hlay hreads hsam hmask
    have hpinsμ₁ : UnivPins lim vals x W ⟨ll, μ₁⟩ := UnivPins_congr rfl hpins
    have hpins₁ : UnivPins lim vals x W ⟨Function.update ll Tmp r₁, μ₁⟩ :=
      UnivPins_update hpinsμ₁
    have huR : Function.update ll Tmp r₁ Rt = ll Rt :=
      dif_neg (by have h15 : Rt = (15 : ℕ) := rfl; have h10 : Tmp = (10 : ℕ) := rfl; omega)
    have hRt₁ : Function.update ll Tmp r₁ Rt = (t : ℤ) := by rw [huR]; exact hRt
    have hTmp₁ : Function.update ll Tmp r₁ Tmp = r₁ := rfl
    -- the delivery value's identity: the oracle premise at THIS round
    have hr_eq : r₁ = bracketAccumulate (μ (x.c + t * x.n)) tests (mpRounds W) :=
      hret t mask μ μ₁ r₁ htW ⟨cs₁, hlen, hnd, hmem, hmask, hsam, h0', hpos⟩
    refine (univRowPass_runs' hxn hpins₁ hspace hRt₁ hTmp₁ htW hrowT).mono le_rfl ?_
    rintro σ' ⟨hP', hRow, hK, hloc'⟩
    -- the round's loc-preservation: the call touched only Tmp, the pass
    -- only IdxR/DstR/J
    have hlocone : ∀ i : ℕ, i ≠ Tmp → i ≠ IdxR → i ≠ DstR → i ≠ J →
        σ'.loc i = ll i := by
      intro i hiT hi1 hi2 hi3
      have h1 := hloc' i hi1 hi2 hi3
      have h2 : Function.update ll Tmp r₁ i = ll i := dif_neg hiT
      rw [h1, h2]
    -- the row's stores stay inside the product region (the reads regions
    -- sit at and above the stage's active base, the product below it)
    have hrowaway : ∀ (b' : ℕ), ab ≤ b' → x.c + t * x.n + x.n ≤ b' := by
      intro b' hb'
      have h1 : x.c + x.n * x.n ≤ ab := hbelow
      have h2 : t * x.n + x.n ≤ x.n * x.n := by
        have h3 : t + 1 ≤ x.n := by omega
        have h4 : (t + 1) * x.n ≤ x.n * x.n := Nat.mul_le_mul h3 (Nat.le_refl x.n)
        have h5 : (t + 1) * x.n = t * x.n + x.n := by ring
        omega
      omega
    refine ⟨maskCleared cs₁.toFinset mask, r₁, ?_, hP', hr_eq, ?_, ?_, ?_, hlocone⟩
    · -- the evolved reads
      refine ⟨fun i hi => ?_, fun p hp i hi => ?_, fun p hp => ?_⟩
      · have hk := hK (ab + i) (Or.inr (hrowaway (ab + i) (by omega)))
        rw [hk]; exact hreads₁.1 i hi
      · have hk := hK (rb + p * I + i)
          (Or.inr (hrowaway _ (show ab ≤ rb + p * I + i from by omega)))
        rw [hk]; exact hreads₁.2.1 p hp i hi
      · have hk := hK (mb + p)
          (Or.inr (hrowaway _ (show ab ≤ mb + p from by omega)))
        rw [hk]; exact hreads₁.2.2 p hp
    · -- the full row carries the delivery value
      intro u hu
      exact hRow u hu
    · -- the other rows' cells are unchanged (pass keeps, call keeps)
      intro t' u' ht' hu' hne
      have hsam' : SameOutside3 μ μ₁ sb P bb I mb P := hsam
      have hbout := row_disjoint (n := x.n) hne hu'
      have hrowlt : t' * x.n + u' < x.n * x.n := by
        have h1 : (t' + 1) * x.n ≤ x.n * x.n :=
          Nat.mul_le_mul (by omega) (Nat.le_refl x.n)
        have h2 : (t' + 1) * x.n = t' * x.n + x.n := by ring
        omega
      have hk := hK (x.c + t' * x.n + u') (by omega)
      have hcell := hsam' (x.c + t' * x.n + u')
        ⟨Or.inl (by have := hbelow; have := habsb; have := hrowlt; omega),
          Or.inl (by have := hbelow; have := habsb; have := hrowlt; omega),
          Or.inl (by have := hbelow; have := habsb; have := hrowlt; omega)⟩
      rw [hk]
      exact hcell
    · -- the cells below the caller's free pointer and outside the product
      intro b' hb'c hb'out
      have hsam' : SameOutside3 μ μ₁ sb P bb I mb P := hsam
      have hk := hK b' (by
        rcases hb'out with h | h
        · exact Or.inl (by omega)
        · have hle : t * x.n + x.n ≤ x.n * x.n := by
            have h3 : t + 1 ≤ x.n := by omega
            have h4 : (t + 1) * x.n ≤ x.n * x.n := Nat.mul_le_mul h3 (Nat.le_refl x.n)
            have h5 : (t + 1) * x.n = t * x.n + x.n := by ring
            omega
          have hx : x.c + t * x.n + x.n ≤ x.c + x.n * x.n := by omega
          omega)
      have hcell := hsam' b'
        ⟨Or.inl (by have := hfrCle; have := h1l; have := h2l; omega),
          Or.inl (by have := hfrCle; have := h1l; have := h2l; have := h3l; omega),
          Or.inl (by have := hfrCle; have := h1l; have := h2l; have := h3l; have := h4l; omega)⟩
      rw [hk]
      exact hcell
  · -- the call's arguments: safe, with the pinned frame values
    refine ⟨fun e he => ?_, ?_⟩
    · simp only [callArgs, List.mem_cons] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
      · exact trivial
      · exact trivial
      · exact trivial
      · exact trivial
      · exact trivial
      · exact trivial
      · exact trivial
      · exact trivial
      · exact trivial
      · exact absurd h (by simp)
    · have hlits : callArgs.map (fun x => Expr.val ⟨ll, μ⟩ x) =
        [ll 0, ll 1, ll 2, ll 3, ll 4, ll 5, ll 6, ll 7, ll 8] := rfl
      rw [hlits, hframe 0 (by omega), hframe 1 (by omega), hframe 2 (by omega),
        hframe 3 (by omega), hframe 4 (by omega), hframe 5 (by omega),
        hframe 6 (by omega), hframe 7 (by omega), hframe 8 (by omega), hvals]
      rfl

#print axioms univRound_runs'

/-! ## The all-cells invariant and the level body's run -/

/-- The level-loop invariant, STRENGTHENED: the landed `UnivInv` plus the
all-rows tracking (written rows carry the delivered fold seeded at the
row's own head in `μ₀`; rows at/after the flat round counter still hold
their OWN initial values — the same-cell form: the prologue initializes
only the Active/Remaining bookkeeping arrays, so the product array keeps
the instance's values, which are not row-broadcast) plus the kept frame
(`KeptBut` below the caller's free pointer `frC`). The disjunctive
row-index form keeps every obligation inside omega's fragment. -/
def UnivInvAll (lim : Limits) (vals : List ℤ) (x : MatInst) (W : ℕ)
    (P I : ℕ) (active : ℕ → Bool) (rows : ℕ → ℕ → ℕ) (ab rb mb : ℕ)
    (μ₀ : ℕ → ℤ) (tests : ℕ → Bool × Bool) (frC ell : ℕ) (σ : State) : Prop :=
  UnivInv lim vals x W P I active rows ab rb mb μ₀ tests ell σ ∧
  (∀ t u : ℕ, t < 2 * ell → t < mpRounds W → u < x.n →
    σ.mem (x.c + t * x.n + u) =
      bracketAccumulate (μ₀ (x.c + t * x.n)) tests (mpRounds W)) ∧
  (∀ t u : ℕ, 2 * ell ≤ t → t < mpRounds W → u < x.n →
    σ.mem (x.c + t * x.n + u) = μ₀ (x.c + t * x.n + u)) ∧
  KeptBut μ₀ σ.mem frC x.c (x.n * x.n)

/-- The level-loop wire target, STATED — now at the hypothesis the induction
actually closes on. The loop rule is `Ends.while` at `signedLevels W`
iterations with the constant per-iteration budget `univTestB + univLevelB n`;
the invariant is `UnivInvAll`; the per-iteration body is `univLevelBody`
(two certified rounds at levels `2ℓ`, `2ℓ+1` — the second at the first's
evolved mask — plus the three pin-preserving counter `.set`s, brick
`univLevel_runs`); the exit needs `2^signedLevels W > 2·U`
(`Nat.lt_pow_succ_log_self` at the instance relation `x.U = W`) and yields
the fold identity at cell (0,0). The per-iteration cost is
`univWhile_cost`-bounded by the schedule's unit budget; the total is
`mpRounds W * univUnitB n`, i.e. `univTn`-shaped up to the prologue.

AMENDED HYPOTHESIS (disclosed, not silently weakened): as first stated this
carried `UnivInv … 0`. That is too weak for the induction — the loop's
all-cells tracking (other rows unchanged, and `KeptBut` below the free
pointer) is load-bearing for every later round's row pass and for the
cell-(0,0) fold's survival, and only the PROLOGUE establishes it. The
hypothesis is therefore the strengthened invariant, and supplying it is the
entry assembly's obligation. -/
def WireUnivTarget
    {lim : Limits} {d : ℕ} {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr frC : ℕ}
    (stage : ℕ) (cacheProg restoreProg : Light.Program) (cs : Inst)
    (R : Light.Program) (Tt : ℕ → ℕ)
    (x : MatInst) (W : ℕ) (tests : ℕ → Bool × Bool)
    (vals : List ℤ) (μ₀ : ℕ → ℤ) : Prop :=
  ∀ (l : ℕ → ℤ),
    UnivInvAll lim vals x W P I active rows ab rb mb μ₀ tests frC 0 ⟨l, μ₀⟩ →
    Ends lim (callerProgramUniv stage cacheProg restoreProg cs ++ R) d (univWhile stage)
      ⟨l, μ₀⟩ (mpRounds W * univUnitB x.n)
      (fun σ' => UnivPins lim vals x W σ' ∧
        σ'.mem x.c = bracketAccumulate (μ₀ x.c) tests (mpRounds W) ∧
        (∃ mask' : ℕ → Bool,
          ThinMatrix.CallerChain.StageReads P I active mask' rows ab rb mb σ'.mem))

/-- THE ENTRY ASSEMBLY'S TARGET — STATED (lane target-def pattern, no sorry).
`univPrologue`, started in the mpTask frame (registers 0..5 = `[n, U, a, b,
c, fr]`) over the instance memory `μ₀`, ends within `univProB x.n` in the
level loop's ZERO invariant. This is the sole missing premise of
`wireUnivTarget_of`, so discharging it closes the lane's run-derivation.

THE FRAME CORRESPONDENCE (derived by reading, not assumed). `UnivPins vals`
pins registers 0..8 to `vals.getD`, with `vals = argsOf callSite ++ [fr]`.
The prologue's writes realise exactly that PROVIDED the instance's fields sit
where the layout puts them:

  vals[0] candidates     = n               (register 0 is never written — it
                                            still holds the input n)
  vals[1] length         = n               (`Len := v 0`)
  vals[2] height         = U               (`Height := v 1`)
  vals[3] activeBase     = fr              (`Active := v 5`)
  vals[4] rowsBase       = fr + n          (`Rows := Active + Nreg`)
  vals[5] scoresBase     = fr + n + n²     (`Scores := Rows + Nreg*Nreg`)
  vals[6] remainingBase  = fr + 2n + n²    (`Remaining := Base + Nreg`)
  vals[7] baseBase       = fr + n + n²     (`Base := Scores + Nreg`)
  vals[8] fr                               (`Free := Remaining + Nreg`)

Three consequences the proof will consume:
- the writes land ONLY at `ab` (= `fr`) and `mb`; both are at or above
  `x.c + n*n` (`hbelow`), which is precisely why the product region is
  untouched and `KeptBut … frC x.c (n*n)` holds (with `hfrCle`);
- the ORDER of the def's sets is load-bearing: `Height := v 1` must read
  register 1 BEFORE `Len := v 0` overwrites it;
- the ROWS region is never written, so the level-0 stage reads are
  satisfiable by taking `rows p i := μ₀ (rb + p*I + i)` — the same
  "the array keeps the instance's own values" device the all-cells clause
  of `UnivInvAll` uses. -/
def PrologueTarget
    {lim : Limits} {d : ℕ} {P k I h : ℕ} {active : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr frC : ℕ}
    (stage : ℕ) (cacheProg restoreProg : Light.Program) (cs : Inst)
    (R : Light.Program) (Tt : ℕ → ℕ)
    (x : MatInst) (W : ℕ) (tests : ℕ → Bool × Bool)
    (vals : List ℤ) (μ₀ : ℕ → ℤ) : Prop :=
  Ends lim (callerProgramUniv stage cacheProg restoreProg cs ++ R) d univPrologue
    ⟨frame vals, μ₀⟩ (univProB x.n)
    (UnivInvAll lim vals x W P I active rows ab rb mb μ₀ tests frC 0)

/-- THE LEVEL BODY'S RUN: from the strengthened invariant at level `ell`,
the level body — two certified rounds (rounds `2·ell`, `2·ell+1`, the
second at the first's evolved mask) plus the three counter `.set`s —
lands the invariant at level `ell + 1` within `univLevelB x.n`. The
delivery identities ride the round lemma's `hret`-shaped conclusions; the
head-value bridges (`μ (x.c + t·n) = μ₀ (x.c + t·n)`) ride the
unwritten-rows clause; the counter sets ride `UnivPins_set` and the
counters' word bounds. -/
theorem univLevel_runs
    {lim : Limits} {d : ℕ} {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr frC : ℕ}
    {cacheProg restoreProg : Light.Program} {cs : Inst}
    {stage : ℕ} {Tt : ℕ → ℕ} {R : Light.Program}
    {x : MatInst} {W : ℕ} {tests : ℕ → Bool × Bool}
    {vals : List ℤ} {μ₀ : ℕ → ℤ}
    (hxn : 1 ≤ x.n)
    (hvals : vals = argsOf (callSite P k I h active remaining rows ab rb sb mb bb)
      ++ [(fr : ℤ)])
    (hslot : @UnivSlot lim d P k I h active rows ab rb sb mb bb fr
      stage cacheProg restoreProg cs R Tt)
    (hret : ∀ (t' : ℕ) (mask' : ℕ → Bool) (μ' μ'' : ℕ → ℤ) (r' : ℤ),
      t' < mpRounds W →
      Light.DenseRestartSelectionLoop.Post
        (callSite P k I h active mask' rows ab rb sb mb bb) μ' μ'' →
      r' = bracketAccumulate (μ' (x.c + t' * x.n)) tests (mpRounds W))
    (hflag : ∀ mask' : ℕ → Bool, k ≤ (flagged P mask').card)
    (hok : ∀ (mask' : ℕ → Bool) (kt : ℕ),
      (Light.DenseRestartSelectionLoop.need
        (instanceSize (callSite P kt I h active mask' rows ab rb sb mb bb))
        (callSite P kt I h active mask' rows ab rb sb mb bb).height).Ok lim fr (d + 1))
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)])
    (hfrCle : frC ≤ ab)
    (haway : (x.c < sb ∨ sb + P ≤ x.c) ∧
      (x.c < bb ∨ bb + I ≤ x.c) ∧
      (x.c < mb ∨ mb + P ≤ x.c))
    (hbelow : (x.c + x.n * x.n : ℕ) ≤ ab)
    (hspace : (lim.space : ℤ) ≤ lim.word)
    (hregion : mpRounds W ≤ x.n)
    (hdim : d < lim.depth)
    (hTtk : Tt k ≤ callerTt x.n)
    (hwordRt : ((mpRounds W : ℕ) : ℤ) ≤ lim.word)
    (hwordLvl : ((2 ^ signedLevels W : ℕ) : ℤ) ≤ lim.word)
    {ℓ : ℕ} {ll : ℕ → ℤ} {μ : ℕ → ℤ} {T : ℕ}
    (hℓ : ℓ < signedLevels W)
    (hinv : UnivInvAll lim vals x W P I active rows ab rb mb μ₀ tests frC ℓ ⟨ll, μ⟩)
    (hT : univLevelB x.n ≤ T) :
    Ends lim (callerProgramUniv stage cacheProg restoreProg cs ++ R) d
      (univLevelBody stage) ⟨ll, μ⟩ T
      (UnivInvAll lim vals x W P I active rows ab rb mb μ₀ tests frC (ℓ + 1)) := by
  obtain ⟨hinvU, hall1, hall2, hkept⟩ := hinv
  obtain ⟨hpins, hLvl, hRt, hreadsEx, hcell⟩ := hinvU
  obtain ⟨mask, hreads⟩ := hreadsEx
  have hmp : mpRounds W = 2 * signedLevels W := mpRounds_eq_signed W
  have h2lt : 2 * ℓ + 2 ≤ mpRounds W := by rw [hmp]; omega
  have h2ltW : 2 * ℓ < mpRounds W := by omega
  have h2lt1W : 2 * ℓ + 1 < mpRounds W := by omega
  have h0ltW : 0 < mpRounds W := by omega
  have hRt' : ll Rt = ((2 * ℓ : ℕ) : ℤ) := hRt
  have hLB : univLevelB x.n = 2 * univRoundB x.n + 16 := by
    unfold univLevelB univRoundB
    ring
  have hB1 : univRoundB x.n + (univLevelB x.n - univRoundB x.n)
      = univLevelB x.n := by omega
  have hB2 : 4 + (univLevelB x.n - univRoundB x.n - 4)
      = univLevelB x.n - univRoundB x.n := by omega
  have hB3 : univRoundB x.n + (univLevelB x.n - univRoundB x.n - 4 - univRoundB x.n)
      = univLevelB x.n - univRoundB x.n - 4 := by omega
  have hB4 : 4 + (univLevelB x.n - univRoundB x.n - 4 - univRoundB x.n - 4)
      = univLevelB x.n - univRoundB x.n - 4 - univRoundB x.n := by omega
  have hB5 : (Light.k 2 *' v Lvl).cost + 1
      + (univLevelB x.n - univRoundB x.n - 4 - univRoundB x.n - 4)
      = univLevelB x.n - univRoundB x.n - 4 - univRoundB x.n := by
    simp only [Expr.cost]
    omega
  have hLR : (Lvl : ℕ) ≠ Rt := by
    have hL : Lvl = (14 : ℕ) := rfl
    have hR' : Rt = (15 : ℕ) := rfl
    omega
  have hRL : (Rt : ℕ) ≠ Lvl := by
    have hL : Lvl = (14 : ℕ) := rfl
    have hR' : Rt = (15 : ℕ) := rfl
    omega
  have hword2 : (2 : ℤ) ≤ lim.word := by
    have hw := (hok mask k).word
    simp only [Light.DenseRestartSelectionLoop.need] at hw
    have hpos : (0 : ℤ) ≤
        ((((instanceSize (callSite P k I h active remaining rows ab rb sb mb bb) + 1) *
              ((callSite P k I h active remaining rows ab rb sb mb bb).height + 1) : ℕ) : ℤ)) :=
      by positivity
    omega
  have hwordRt1 : |(ll Rt + (1 : ℤ))| ≤ lim.word := by
    rw [hRt']
    push_cast
    have h2 : ((2 * ℓ + 1 : ℕ) : ℤ) ≤ ((mpRounds W : ℕ) : ℤ) := by omega
    have h3 : (0 : ℤ) ≤ 2 * ((ℓ : ℕ) : ℤ) + 1 := by push_cast; omega
    rw [abs_of_nonneg h3]
    have h5 : 2 * ((ℓ : ℕ) : ℤ) + 1 = ((2 * ℓ + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h5]
    omega
  have hwordRt2 : |((2 * ℓ + 1 : ℕ) : ℤ) + (1 : ℤ)| ≤ lim.word := by
    have h1 : (0 : ℤ) ≤ ((2 * ℓ + 1 : ℕ) : ℤ) + 1 := by push_cast; omega
    rw [abs_of_nonneg h1]
    have h2 : ((2 * ℓ + 2 : ℕ) : ℤ) ≤ ((mpRounds W : ℕ) : ℤ) := by omega
    calc ((2 * ℓ + 1 : ℕ) : ℤ) + 1 = ((2 * ℓ + 2 : ℕ) : ℤ) := by push_cast; ring
      _ ≤ ((mpRounds W : ℕ) : ℤ) := h2
      _ ≤ lim.word := hwordRt
  have hwordLvl' : |((2 : ℤ) * ((2 ^ ℓ : ℕ) : ℤ))| ≤ lim.word := by
    have h1 : (0 : ℤ) ≤ (2 : ℤ) * ((2 ^ ℓ : ℕ) : ℤ) := by positivity
    rw [abs_of_nonneg h1]
    have h2 : ((2 ^ (ℓ + 1) : ℕ) : ℤ) = (2 : ℤ) * ((2 ^ ℓ : ℕ) : ℤ) := by
      rw [Nat.pow_succ]
      push_cast
      ring
    have h3 : ((2 ^ (ℓ + 1) : ℕ) : ℤ) ≤ ((2 ^ signedLevels W : ℕ) : ℤ) :=
      Nat.cast_le.2 (Nat.pow_le_pow_right (by omega) (by omega))
    rw [← h2]
    exact h3.trans hwordLvl
  have hcostSet : (v Rt +' Light.k 1).cost + 1 = 4 := by
    simp only [Expr.cost]
  have hcostSetL : (Light.k 2 *' v Lvl).cost + 1 = 4 := by
    simp only [Expr.cost]
  -- the fixed-premise bundle for the two rounds
  have hround : ∀ (t : ℕ) (ll' : ℕ → ℤ) (μ' : ℕ → ℤ) (mask' : ℕ → Bool) (T' : ℕ),
      UnivPins lim vals x W ⟨ll', μ'⟩ →
      t < mpRounds W → ll' Rt = (t : ℤ) →
      ThinMatrix.CallerChain.StageReads P I active mask' rows ab rb mb μ' →
      univRoundB x.n ≤ T' →
      Ends lim (callerProgramUniv stage cacheProg restoreProg cs ++ R) d (univRound stage)
        ⟨ll', μ'⟩ (univRoundB x.n)
        (fun σ' => ∃ (mask'' : ℕ → Bool) (r : ℤ),
          ThinMatrix.CallerChain.StageReads P I active mask'' rows ab rb mb σ'.mem ∧
          UnivPins lim vals x W σ' ∧
          r = bracketAccumulate (μ' (x.c + t * x.n)) tests (mpRounds W) ∧
          (∀ u : ℕ, u < x.n → σ'.mem (x.c + t * x.n + u) = r) ∧
          (∀ t' u' : ℕ, t' < mpRounds W → u' < x.n → t' ≠ t →
            σ'.mem (x.c + t' * x.n + u') = μ' (x.c + t' * x.n + u')) ∧
          (∀ b' : ℕ, b' < frC → (b' < x.c ∨ x.c + x.n * x.n ≤ b') →
            σ'.mem b' = μ' b') ∧
          (∀ i : ℕ, i ≠ Tmp → i ≠ IdxR → i ≠ DstR → i ≠ J → σ'.loc i = ll' i)) :=
    fun t ll' μ' mask' T' hp' ht hRt' hr' hT' =>
      univRound_runs' hxn hvals hslot hret hflag hok hp' hRt' hr' hlay hfrCle haway hbelow
        rfl hspace hregion ht hdim hTtk hT'
  unfold univLevelBody
  -- step 1: round 2·ell
  refine Ends.seq (univRoundB x.n) (univLevelB x.n - univRoundB x.n) ?_
    (by rw [hB1]; exact hT)
  refine (hround (2 * ℓ) ll μ mask (univRoundB x.n) hpins h2ltW hRt hreads
    (le_refl (univRoundB x.n))).mono le_rfl ?_
  rintro ⟨llB, μ₁⟩ ⟨mask₁, r₁, hR1, hP1, hReq1, hRow1, hQ1, hK1, hlocB⟩
  -- the carried cell after round 2·ell: the fold, in both cases
  have hcell' : μ x.c =
      (if ℓ = 0 then μ₀ x.c
        else bracketAccumulate (μ₀ x.c) tests (mpRounds W)) := hcell
  have hcell1 : μ₁ x.c = bracketAccumulate (μ₀ x.c) tests (mpRounds W) := by
    by_cases hℓ0 : ℓ = 0
    · subst hℓ0
      have hrow := hRow1 0 (by omega)
      simp at hrow
      have hreq := hReq1
      simp at hreq
      rw [if_pos rfl] at hcell'
      rw [hrow, hreq, hcell']
    · have hq := hQ1 0 0 h0ltW hxn (by omega)
      simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero] at hq
      rw [if_neg hℓ0] at hcell'
      rw [hq, hcell']
  -- step 2: set Rt := 2·ell + 1
  refine Ends.seq 4
    (univLevelB x.n - univRoundB x.n - 4) ?_
    (by rw [hB2])
  have hRtB : llB Rt = ((2 * ℓ : ℕ) : ℤ) := by
    have h1 : llB Rt = ll Rt :=
      hlocB Rt (by simp only [Rt, Tmp]; omega) (by simp only [Rt, IdxR]; omega)
        (by simp only [Rt, DstR]; omega) (by simp only [Rt, J]; omega)
    rw [h1]
    exact hRt'
  have hLvlB : llB Lvl = ((2 ^ ℓ : ℕ) : ℤ) := by
    have h1 : llB Lvl = ll Lvl :=
      hlocB Lvl (by simp only [Lvl, Tmp]; omega) (by simp only [Lvl, IdxR]; omega)
        (by simp only [Lvl, DstR]; omega) (by simp only [Lvl, J]; omega)
    rw [h1]
    exact hLvl
  have habs1 : |llB Rt + (1 : ℤ)| ≤ lim.word := by
    rw [hRtB]
    push_cast
    have h2 : ((2 * ℓ + 1 : ℕ) : ℤ) ≤ ((mpRounds W : ℕ) : ℤ) := by omega
    have h3 : (0 : ℤ) ≤ 2 * ((ℓ : ℕ) : ℤ) + 1 := by push_cast; omega
    rw [abs_of_nonneg h3]
    have h5 : 2 * ((ℓ : ℕ) : ℤ) + 1 = ((2 * ℓ + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h5]
    omega
  have hsafe1 : Expr.Safe lim ⟨llB, μ₁⟩ (v Rt +' Expr.const 1) := by
    simp only [Expr.Safe, Expr.val, Op.eval]
    exact ⟨trivial, by omega, habs1⟩
  refine Ends.set hsafe1 (by have := hcostSet; omega) ?_
  · -- step 3: round 2·ell+1
    have hpinsC : UnivPins lim vals x W
        ⟨Function.update llB Rt (llB Rt + (1 : ℤ)), μ₁⟩ :=
      UnivPins_set hP1 (by intro k' hk'; simp only [Rt]; omega)
        (by simp only [Rt, Out]; omega) (by simp only [Rt, Nreg]; omega)
        (by simp only [Rt, U2]; omega)
    have hLvlC : Function.update llB Rt (llB Rt + (1 : ℤ)) Lvl = ((2 ^ ℓ : ℕ) : ℤ) := by
      rw [Function.update_of_ne hLR]
      exact hLvlB
    have hRtC : Function.update llB Rt (llB Rt + (1 : ℤ)) Rt = ((2 * ℓ + 1 : ℕ) : ℤ) := by
      simp only [Function.update_self]
      rw [hRtB]
      push_cast
      ring
    refine Ends.seq (univRoundB x.n)
      (univLevelB x.n - univRoundB x.n - 4 - univRoundB x.n) ?_
      (by rw [hB3])
    refine (hround (2 * ℓ + 1) (Function.update llB Rt (llB Rt + (1 : ℤ))) μ₁ mask₁
      (univRoundB x.n)
      hpinsC h2lt1W hRtC hR1 (le_refl _)).mono le_rfl ?_
    rintro ⟨llD, μ₂⟩ ⟨mask₂, r₂, hR2, hP2, hReq2, hRow2, hQ2, hK2, hlocD⟩
    -- the delivery identities for the two rows
    have hhead1 : μ (x.c + 2 * ℓ * x.n) = μ₀ (x.c + 2 * ℓ * x.n) := by
      have h1 := hall2 (2 * ℓ) 0 (by omega) h2ltW hxn
      simpa using h1
    have hhead2 : μ₁ (x.c + (2 * ℓ + 1) * x.n) = μ₀ (x.c + (2 * ℓ + 1) * x.n) := by
      have h1 := hQ1 (2 * ℓ + 1) 0 h2lt1W hxn (by omega)
      simp only [Nat.add_zero] at h1
      have h2 := hall2 (2 * ℓ + 1) 0 (by omega) h2lt1W hxn
      simp only [Nat.add_zero] at h2
      exact h1.trans h2
    -- the round-2 post's counter values, via its loc clause
    have hRtD : llD Rt = ((2 * ℓ + 1 : ℕ) : ℤ) := by
      have h1 : llD Rt = Function.update llB Rt (llB Rt + (1 : ℤ)) Rt :=
        hlocD Rt (by simp only [Rt, Tmp]; omega) (by simp only [Rt, IdxR]; omega)
          (by simp only [Rt, DstR]; omega) (by simp only [Rt, J]; omega)
      rw [h1, hRtC]
    have hLvlD : llD Lvl = ((2 ^ ℓ : ℕ) : ℤ) := by
      have h1 : llD Lvl = Function.update llB Rt (llB Rt + (1 : ℤ)) Lvl :=
        hlocD Lvl (by simp only [Lvl, Tmp]; omega) (by simp only [Lvl, IdxR]; omega)
          (by simp only [Lvl, DstR]; omega) (by simp only [Lvl, J]; omega)
      rw [h1, hLvlC]
    -- step 4: set Rt := 2·ell + 2
    refine Ends.seq 4
      (univLevelB x.n - univRoundB x.n - 4 - univRoundB x.n - 4) ?_
      (by rw [hB4])
    have habs4 : |llD Rt + (1 : ℤ)| ≤ lim.word := by
      rw [hRtD]
      push_cast
      have h3 : (0 : ℤ) ≤ 2 * ((ℓ : ℕ) : ℤ) + 1 + 1 := by push_cast; omega
      rw [abs_of_nonneg h3]
      have h5 : 2 * ((ℓ : ℕ) : ℤ) + 1 + 1 = ((2 * ℓ + 2 : ℕ) : ℤ) := by push_cast; ring
      rw [h5]
      have h2 : ((2 * ℓ + 2 : ℕ) : ℤ) ≤ ((mpRounds W : ℕ) : ℤ) := by omega
      omega
    have hsafe4 : Expr.Safe lim ⟨llD, μ₂⟩ (v Rt +' Expr.const 1) := by
      simp only [Expr.Safe, Expr.val, Op.eval]
      exact ⟨trivial, by omega, habs4⟩
    refine Ends.set hsafe4 (by have := hcostSet; omega) ?_
    · -- step 5: set Lvl := 2·2^ell
      set llE : ℕ → ℤ := Function.update llD Rt (llD Rt + (1 : ℤ)) with hllE
      have hLvlE : llE Lvl = ((2 ^ ℓ : ℕ) : ℤ) := by
        rw [hllE, Function.update_of_ne hLR, hLvlD]
      have habs5 : |(2 : ℤ) * llE Lvl| ≤ lim.word := by
        rw [hLvlE]
        exact hwordLvl'
      have hsafe5 : Expr.Safe lim ⟨llE, μ₂⟩ (Expr.const 2 *' v Lvl) := by
        simp only [Expr.Safe, Expr.val, Op.eval]
        exact ⟨hword2, trivial, habs5⟩
      have hPinsF : UnivPins lim vals x W
          ⟨Function.update llE Lvl ((2 : ℤ) * llE Lvl), μ₂⟩ :=
        UnivPins_set (UnivPins_set hP2
          (by intro k' hk'; simp only [Rt]; omega)
          (by simp only [Rt, Out]; omega) (by simp only [Rt, Nreg]; omega)
          (by simp only [Rt, U2]; omega))
          (by intro k' hk'; simp only [Lvl]; omega)
          (by simp only [Lvl, Out]; omega) (by simp only [Lvl, Nreg]; omega)
          (by simp only [Lvl, U2]; omega)
      have hLvlF : Function.update llE Lvl ((2 : ℤ) * llE Lvl) Lvl
          = ((2 ^ (ℓ + 1) : ℕ) : ℤ) := by
        rw [Function.update_self, hLvlE]
        have h2 : ((2 : ℤ) * ((2 ^ ℓ : ℕ) : ℤ)) = ((2 ^ (ℓ + 1) : ℕ) : ℤ) := by
          rw [Nat.pow_succ]
          push_cast
          ring
        rw [h2]
      have hRtF : Function.update llE Lvl ((2 : ℤ) * llE Lvl) Rt
          = ((2 * (ℓ + 1) : ℕ) : ℤ) := by
        rw [Function.update_of_ne hRL, hllE, Function.update_self, hRtD]
        push_cast
        ring
      have hrem5 : univLevelB x.n - univRoundB x.n - 4 - univRoundB x.n - 4 = 8 := by
        omega
      refine Ends.set hsafe5 (by rw [hrem5]; omega) ?_
      · refine ⟨⟨hPinsF, hLvlF, hRtF, ⟨mask₂, hR2⟩, ?_⟩, ?_, ?_, ?_⟩
        · -- the cell: kept by round 2·ell+1, it held the fold
          have hq : μ₂ x.c = μ₁ x.c := by
            have h0q := hQ2 0 0 h0ltW hxn (by omega)
            simpa only [Nat.zero_mul, Nat.zero_add, Nat.add_zero] using h0q
          show μ₂ x.c = (if ℓ + 1 = 0 then μ₀ x.c
            else bracketAccumulate (μ₀ x.c) tests (mpRounds W))
          rw [hq, hcell1, if_neg (by omega)]
        · intro t u ht htW hu
          rcases Nat.lt_or_ge t (2 * ℓ) with htl | htl
          · have h1 : μ₂ (x.c + t * x.n + u) = μ₁ (x.c + t * x.n + u) :=
              hQ2 t u htW hu (by omega)
            have h2 : μ₁ (x.c + t * x.n + u) = μ (x.c + t * x.n + u) :=
              hQ1 t u htW hu (by omega)
            have h3 := hall1 t u htl htW hu
            exact h1.trans (h2.trans h3)
          · rcases Nat.lt_or_ge t (2 * ℓ + 1) with htl1 | htl2
            · have ht2 : t = 2 * ℓ := by omega
              subst ht2
              have h1 : μ₂ (x.c + 2 * ℓ * x.n + u) = μ₁ (x.c + 2 * ℓ * x.n + u) :=
                hQ2 (2 * ℓ) u h2ltW hu (by omega)
              have h2 : μ₁ (x.c + 2 * ℓ * x.n + u) = r₁ := hRow1 u hu
              have h4 : bracketAccumulate (μ (x.c + 2 * ℓ * x.n)) tests (mpRounds W)
                  = bracketAccumulate (μ₀ (x.c + 2 * ℓ * x.n)) tests (mpRounds W) := by
                rw [hhead1]
              exact h1.trans (h2.trans (hReq1.trans h4))
            · have ht2 : t = 2 * ℓ + 1 := by omega
              subst ht2
              have h2 : μ₂ (x.c + (2 * ℓ + 1) * x.n + u) = r₂ := hRow2 u hu
              have h4 : bracketAccumulate (μ₁ (x.c + (2 * ℓ + 1) * x.n)) tests (mpRounds W)
                  = bracketAccumulate (μ₀ (x.c + (2 * ℓ + 1) * x.n)) tests (mpRounds W) := by
                rw [hhead2]
              exact h2.trans (hReq2.trans h4)
        · intro t u ht htW hu
          have h1 : μ₂ (x.c + t * x.n + u) = μ₁ (x.c + t * x.n + u) :=
            hQ2 t u htW hu (by omega)
          have h2 : μ₁ (x.c + t * x.n + u) = μ (x.c + t * x.n + u) :=
            hQ1 t u htW hu (by omega)
          have h3 := hall2 t u (by omega) htW hu
          exact h1.trans (h2.trans h3)
        · intro b' hb'
          have h1 : μ₂ b' = μ₁ b' := hK2 b' hb'.1 hb'.2
          have h2 : μ₁ b' = μ b' := hK1 b' hb'.1 hb'.2
          have h3 : μ b' = μ₀ b' := hkept b' hb'
          exact h1.trans (h2.trans h3)

#print axioms univLevel_runs

/-! ## The level bound's arithmetic (the loop's two sides) -/

/-- Below the top level the doubling fits the loop bound: the level at
`i < signedLevels W` is at most `2^(signedLevels W - 1) = 2^(log₂(2W)) ≤ 2W`
(`Nat.pow_log_le_self`). This is the HOLDS side of the while test. -/
theorem pow_pred_signed_levels_le (W : ℕ) (hW : W ≠ 0) :
    2 ^ (signedLevels W - 1) ≤ 2 * W := by
  have h1 : signedLevels W - 1 = Nat.log2 (2 * W) := by
    unfold signedLevels
    omega
  rw [h1, Nat.log2_eq_log_two]
  exact Nat.pow_log_le_self 2 (by omega)

/-- At the top level the doubling EXCEEDS the loop bound
(`Nat.lt_pow_succ_log_self`). This is the ¬HOLDS side — the while's exit. -/
theorem two_mul_lt_pow_signed_levels (W : ℕ) : 2 * W < 2 ^ signedLevels W := by
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (2 * W)
  have h1 : Nat.log2 (2 * W) = Nat.log 2 (2 * W) := Nat.log2_eq_log_two
  unfold signedLevels
  rw [h1]
  simpa [Nat.succ_eq_add_one] using h

/-- THE WIRE'S DISCHARGE (PRODUCT_BODY.md §5 — the lane's last named seam):
`WireUnivTarget`, by `Ends.while` at `signedLevels W` iterations, invariant
`UnivInvAll`, constant per-iteration budget `univLevelB n`, body
`univLevelBody` (the two-round-plus-three-sets brick `univLevel_runs`).
Exit `2^signedLevels W > 2·U`; total `univWhile_cost`-bounded by the
schedule's unit budget, i.e. exactly the target's `mpRounds W * univUnitB n`.

THE HYPOTHESES THE TARGET-DEF DOES NOT CARRY, named here rather than
silently assumed:
- `hWU : x.U = W` — the instance's word bound IS the schedule's. It cannot
  be weakened to `≤`: BOTH sides of the test move with it, so `≤` breaks
  the exit while `≥` breaks the entry. At the packaging call site they are
  the same number.
- `hWpos : 0 < W` — a nonzero schedule (at `W = 0` the level register's
  initial `1` already exceeds `2·0`).
- `hwordU2`, `hword1` — the loop bound and the constant `1` fit a word, so
  the test `v Lvl ≤' v U2` (cost 5, i.e. `univTestB - 1`) is safe. -/
theorem wireUnivTarget_of
    {lim : Limits} {d : ℕ} {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr frC : ℕ}
    (stage : ℕ) (cacheProg restoreProg : Light.Program) (cs : Inst)
    (R : Light.Program) (Tt : ℕ → ℕ)
    (x : MatInst) (W : ℕ) (tests : ℕ → Bool × Bool)
    (vals : List ℤ) (μ₀ : ℕ → ℤ)
    (hxn : 1 ≤ x.n)
    (hvals : vals = argsOf (callSite P k I h active remaining rows ab rb sb mb bb)
      ++ [(fr : ℤ)])
    (hslot : @UnivSlot lim d P k I h active rows ab rb sb mb bb fr
      stage cacheProg restoreProg cs R Tt)
    (hret : ∀ (t' : ℕ) (mask' : ℕ → Bool) (μ' μ'' : ℕ → ℤ) (r' : ℤ),
      t' < mpRounds W →
      Light.DenseRestartSelectionLoop.Post
        (callSite P k I h active mask' rows ab rb sb mb bb) μ' μ'' →
      r' = bracketAccumulate (μ' (x.c + t' * x.n)) tests (mpRounds W))
    (hflag : ∀ mask' : ℕ → Bool, k ≤ (flagged P mask').card)
    (hok : ∀ (mask' : ℕ → Bool) (kt : ℕ),
      (Light.DenseRestartSelectionLoop.need
        (instanceSize (callSite P kt I h active mask' rows ab rb sb mb bb))
        (callSite P kt I h active mask' rows ab rb sb mb bb).height).Ok lim fr (d + 1))
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)])
    (hfrCle : frC ≤ ab)
    (haway : (x.c < sb ∨ sb + P ≤ x.c) ∧
      (x.c < bb ∨ bb + I ≤ x.c) ∧
      (x.c < mb ∨ mb + P ≤ x.c))
    (hbelow : (x.c + x.n * x.n : ℕ) ≤ ab)
    (hspace : (lim.space : ℤ) ≤ lim.word)
    (hregion : mpRounds W ≤ x.n)
    (hdim : d < lim.depth)
    (hTtk : Tt k ≤ callerTt x.n)
    (hwordRt : ((mpRounds W : ℕ) : ℤ) ≤ lim.word)
    (hwordLvl : ((2 ^ signedLevels W : ℕ) : ℤ) ≤ lim.word)
    (hwordU2 : |2 * (x.U : ℤ) + 1| ≤ lim.word)
    (hword1 : (1 : ℤ) ≤ lim.word)
    (hWU : x.U = W)
    (hWpos : 0 < W) :
    WireUnivTarget (lim := lim) (d := d) (P := P) (k := k) (I := I) (h := h)
      (active := active) (remaining := remaining) (rows := rows)
      (ab := ab) (rb := rb) (sb := sb) (mb := mb) (bb := bb) (fr := fr) (frC := frC)
      stage cacheProg restoreProg cs R Tt x W tests vals μ₀ := by
  intro l h0
  have hWne : W ≠ 0 := by omega
  have hPowLe : 2 ^ (signedLevels W - 1) ≤ 2 * W := pow_pred_signed_levels_le W hWne
  have hPowGt : 2 * W < 2 ^ signedLevels W := two_mul_lt_pow_signed_levels W
  have hsum : (∑ i ∈ Finset.range (signedLevels W), (5 + 1 + univLevelB x.n)) + (5 + 1)
      = signedLevels W * (univTestB + univLevelB x.n) + univTestB := by
    simp only [univTestB]
    rw [Finset.sum_const, Finset.card_range]
    simp
  have hwhile : Ends lim (callerProgramUniv stage cacheProg restoreProg cs ++ R) d
      (.while (v Lvl ≤' v U2) (univLevelBody stage)) ⟨l, μ₀⟩
      ((∑ i ∈ Finset.range (signedLevels W), (5 + 1 + univLevelB x.n)) + (5 + 1))
      (fun σ' => UnivPins lim vals x W σ' ∧
        σ'.mem x.c = bracketAccumulate (μ₀ x.c) tests (mpRounds W) ∧
        (∃ mask' : ℕ → Bool,
          ThinMatrix.CallerChain.StageReads P I active mask' rows ab rb mb σ'.mem)) := by
    refine Ends.while
      (I := fun ell σ => UnivInvAll lim vals x W P I active rows ab rb mb μ₀ tests frC ell σ)
      (n := signedLevels W) (b := fun _ => univLevelB x.n)
      (c := (v Lvl ≤' v U2)) (s := univLevelBody stage) (σ := ⟨l, μ₀⟩) h0 ?_ ?_
    · -- the body at level i < signedLevels W
      intro i σ hi hinvAll
      obtain ⟨hpins, hLvl, hRt, hreads, hcell⟩ := hinvAll.1
      obtain ⟨hframe, hOut, hNreg, hU2, haddr⟩ := hpins
      refine ⟨?_, ?_, ?_⟩
      · -- the test is safe: the loop bound and 1 fit a word
        simp only [Cond.le, Cond.Safe, Expr.Safe, Expr.val, Op.eval]
        exact ⟨trivial, trivial, hword1, by rw [hU2]; exact hwordU2⟩
      · -- the test holds: 2^i ≤ 2·U
        rw [Cond.holds_le]
        simp only [Expr.val]
        rw [hLvl, hU2, hWU]
        have h2 : 2 ^ i ≤ 2 ^ (signedLevels W - 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        have hcast : ((2 ^ i : ℕ) : ℤ) ≤ ((2 ^ (signedLevels W - 1) : ℕ) : ℤ) := by
          exact_mod_cast h2
        have hcast2 : ((2 ^ (signedLevels W - 1) : ℕ) : ℤ) ≤ ((2 * W : ℕ) : ℤ) := by
          exact_mod_cast hPowLe
        push_cast at hcast2
        omega
      · -- the level body's run: two certified rounds + three counter sets
        exact univLevel_runs (lim := lim) (d := d) (P := P) (k := k) (I := I) (h := h)
          (active := active) (remaining := remaining) (rows := rows)
          (ab := ab) (rb := rb) (sb := sb) (mb := mb) (bb := bb) (fr := fr) (frC := frC)
          (cacheProg := cacheProg) (restoreProg := restoreProg) (cs := cs) (stage := stage)
          (Tt := Tt) (R := R) (x := x) (W := W) (tests := tests) (vals := vals) (μ₀ := μ₀)
          hxn hvals hslot hret hflag hok hlay hfrCle haway hbelow hspace hregion hdim hTtk
          hwordRt hwordLvl (ℓ := i) (ll := σ.loc) (μ := σ.mem) (T := univLevelB x.n)
          hi (by simpa using hinvAll) (le_refl _)
    · -- the exit: the level bound is exceeded, and the target's conclusion holds
      intro σ hinvAll
      have hpinsE : UnivPins lim vals x W σ := hinvAll.1.1
      have hLvlE : σ.loc Lvl = ((2 ^ signedLevels W : ℕ) : ℤ) := hinvAll.1.2.1
      have hreadsE : ∃ mask' : ℕ → Bool,
          ThinMatrix.CallerChain.StageReads P I active mask' rows ab rb mb σ.mem :=
        hinvAll.1.2.2.2.1
      have hcellE : σ.mem x.c = (if signedLevels W = 0 then μ₀ x.c
          else bracketAccumulate (μ₀ x.c) tests (mpRounds W)) := hinvAll.1.2.2.2.2
      have hU2E : σ.loc U2 = (2 * (x.U : ℤ)) := hpinsE.2.2.2.1
      refine ⟨?_, ?_, ?_⟩
      · simp only [Cond.le, Cond.Safe, Expr.Safe, Expr.val, Op.eval]
        exact ⟨trivial, trivial, hword1, by rw [hU2E]; exact hwordU2⟩
      · -- ¬ (2^signedLevels W ≤ 2·U)
        rw [Cond.holds_le]
        simp only [Expr.val]
        rw [hLvlE, hU2E, hWU]
        intro hle
        have hcast : ((2 * W : ℕ) : ℤ) < ((2 ^ signedLevels W : ℕ) : ℤ) := by
          exact_mod_cast hPowGt
        push_cast at hcast
        omega
      · refine ⟨hpinsE, ?_, hreadsE⟩
        rw [if_neg (by have := signedLevels_pos W; omega)] at hcellE
        exact hcellE
  refine hwhile.mono ?_ (fun _ h => h)
  rw [hsum]
  exact univWhile_cost x.n W hxn

#print axioms pow_pred_signed_levels_le

#print axioms two_mul_lt_pow_signed_levels

#print axioms wireUnivTarget_of

#print axioms UnivPins_set

end ThinMatrix.CallerUniversalBody