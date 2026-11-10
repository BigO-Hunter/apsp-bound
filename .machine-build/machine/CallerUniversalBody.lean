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

/-! ## `mpTaskRounds` — cure (a), SUPERSEDED by cure (b)

`mpTaskRounds` restricted the claimed instance class by `mpRounds U ≤ n` so
that the body's per-round ROW write stayed inside the product region. Cure
(b) — the write-shape rewrite in this module (`univRowPass` now writes the
single cell `x.c`, guarded to round 0) — deletes the reason the restriction
existed: the write set is `{x.c} ⊆ [x.c, x.c + n²)` for EVERY instance, so
`hregion` is never needed and `Solves mpTask` — the UNRESTRICTED task — is
what the chain proves. The def and its three trivial projection lemmas are
KEPT, unmodified, purely as the record of what cure (a) landed; nothing in
this module consumes them.

DOC CORRECTION (disclosed, 2026-11-10). The block this replaced asserted
that "THE RESTRICTION IS NECESSARY". That claim was TRUE OF THE ROW-BROADCAST
BODY and is FALSE OF THE BODY NOW LANDED. It is corrected here rather than
deleted, because a stale necessity claim in a proof file is the exact
doc-truth defect the lane has been bitten by before. -/

def mpTaskRounds : Task where
  Inst := MatInst
  size := mpTask.size
  bound := mpTask.bound
  args := mpTask.args
  Pre x μ fr := mpTask.Pre x μ fr ∧ mpRounds (mpTask.bound x) ≤ mpTask.size x
  Post := mpTask.Post

/-- The restricted task's precondition, unfolded: `mpTask`'s `Pre` plus the
round containment that the row pass needs. -/
theorem mpTaskRounds_pre {x : MatInst} {μ : ℕ → ℤ} {fr : ℕ} :
    mpTaskRounds.Pre x μ fr ↔ x.Pre μ fr ∧ mpRounds x.U ≤ x.n := Iff.rfl

/-- The restricted task's size is the side length (unchanged from
`mpTask`): `timeUpTo` reads the same parameter. -/
theorem mpTaskRounds_size (x : MatInst) : mpTaskRounds.size x = x.n := rfl

/-- The restricted task's bound is `U` (unchanged from `mpTask`). -/
theorem mpTaskRounds_bound (x : MatInst) : mpTaskRounds.bound x = x.U := rfl

/-- The restricted task's postcondition is `mpTask`'s, verbatim. -/
theorem mpTaskRounds_post (x : MatInst) (μ : ℕ → ℤ) (fr : ℕ) (v : ℤ) (μ' : ℕ → ℤ) :
    mpTaskRounds.Post x μ fr v μ' ↔ mpTask.Post x μ fr v μ' := Iff.rfl

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
  pass J (v Nreg) (v Active) (Light.k 1) ;;                   -- the active bits := 1
  pass J (v Nreg) (v Remaining) (Light.k 1) ;;                -- the flags := 1
  .set Lvl (Light.k 1) ;;                                     -- Lvl := 1
  .set Rt (k 0)                                         -- Rt := 0

/-- THE ROUND'S OUTPUT WRITE — cure (b) (wound R2125609577, decided
2026-11-10, superseding cure (a)'s task restriction).

WHAT THE OLD SHAPE WAS. `x.n` stores per round, row `t`'s cells at
`x.c + t·n + u` for `u < n` (the per-instance skeleton's broadcast, driven
by the computed index registers `IdxR`/`DstR` and the canonical `pass`).
That write set is `[x.c + t·n, x.c + t·n + n)` for `t < mpRounds W`, which
ESCAPES the product region `[x.c, x.c + n²)` as soon as `mpRounds W > n`.
`hregion : mpRounds W ≤ n` was then needed to keep the stores off the
stage's buffer stack (the certified post `SameOutside3` at `sb/bb/mb` and
the final `KeptBut`), and that containment is NOT derivable from
`mpTask.Pre` plus any polynomial `Need.Ok` — `Need` bounds the word, the
cells and the depth; `MatInst.Pre` bounds `U` only from below (`AbsLe`).
Counterexample: `n = 1, U = 100` gives `mpRounds 100 = 16 > 1`.

WHY THE ROW PASS WAS NEVER NEEDED. The row broadcast was an implementation
choice, not mathematics. The only cell ANY landed conclusion consumes is the
product's head `x.c`: the construction's identity premise
(`CallerRun.MinPlusIdentity`) takes the round-0 fold at `bracketCell x 0 0
= x.c` as its hypothesis and concludes EVERY cell's `minPlusEntry` value;
`bracketCell x 0 0 = x.c + 0·n + 0 = x.c`, and `mpTask.Post`'s `Seg` half
then follows from that premise via `seg_of_entries`. The other `n − 1`
cells of row `t` are read by nothing.

AND ONLY ROUND 0's DELIVERY REACHES THE HEAD. Round `t`'s delivery is
`bracketAccumulate (μ (x.c + t·n)) tests (mpRounds W)` — the fold seeded at
ROW `t`'s head, so rounds `t ≥ 1` carry DIFFERENT values and must not
clobber the head. Hence the `Rt = 0` guard.

THIS IS THE REGISTER ACCUMULATION, IN PLACE. Carrying the fold in a
dedicated register and storing it once after the loop is the same program up
to the observation that nothing between round 0 and the loop's exit reads or
writes the head: the guarded store lands round 0's delivery in `x.c`
immediately and every later round leaves it alone, so the register (and its
pin, and its final store) would carry no information the cell does not
already hold. Stated as the equivalence it is, not as a silent substitution.

WHAT THIS BUYS. The write set is now `{x.c}` — ONE cell, for every instance,
whatever `mpRounds W` is. `{x.c} ⊆ [x.c, x.c + n²)` for every `n ≥ 1`, so
the certified stage post and `KeptBut` hold for ALL instances, `hregion` is
never needed, and `Solves mpTask` — the UNRESTRICTED task — is what the
chain proves. The cost falls from `13n + 16` to a constant `7`
(`Cond.cost 3 + 1 + 3`). -/
def univRowPass : Light.Stmt :=
  .ite (v Rt =' k 0) (.store (v Out) (v Tmp)) .skip

/-- The universal round: the certified stage call (the L5/L6 restart-loop
slot at the composed program's procedure index `stage`) followed by the
round's single output write (`univRowPass`). -/
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

/-- The cache call's arguments: `cacheTask.args` with the free pointer LAST
(the task convention — `Task.args`, then `fr`). At the mpTask frame
(`v 0 = n`, `v 5 = fr`) these evaluate to `[n, n, fr + n, LTop x fr]`: the
cache's `rb` is the rows buffer, and its free pointer is the caller's stack
top, so the rows region `[fr + n, fr + n + n²)` and the whole buffer stack
lie below it (`cacheTask.Pre` is `rb + P·I ≤ fr`, i.e. `n ≤ 4n`). -/
def univCacheArgs : List Expr :=
  [v 0, v 0, v 5 +' v 0, v 5 +' k 4 *' v 0 +' (v 0 *' v 0)]

/-- The cache call's FOUR frame values, evaluated at the entry frame
(`l 0 = n`, `l 5 = fr`): `[n, n, fr + n, fr + 4n + n²]` — `cacheTask.args`
(`P, I, rb`), then the free pointer the call runs at, LAST (`Task.args`,
`fr` last — `Solves`'s frame convention). `fr + 4n + n²` is the caller's
stack top (`LTop`), so the rows region `[fr + n, fr + n + n²)` and every
buffer lie below the cache's free pointer. -/
theorem univCacheArgs_val {x : MatInst} {fr : ℕ} {l : ℕ → ℤ} {μ : ℕ → ℤ}
    (h0 : l 0 = (x.n : ℤ)) (h5 : l 5 = (fr : ℤ)) :
    univCacheArgs.map (·.val ⟨l, μ⟩) =
      [(x.n : ℤ), (x.n : ℤ), (fr : ℤ) + (x.n : ℤ),
        (fr : ℤ) + 4 * (x.n : ℤ) + (x.n : ℤ) * (x.n : ℤ)] := by
  simp [univCacheArgs, Expr.val, Op.eval, h0, h5]

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

/-- The cache procedure's index in the composed program: the entry body is
procedure 0, so the cache that sits at `cacheProc` of `cacheProg` sits at
`1 + cacheProc` of `callerProgramUniv` (the same arithmetic as the landed
`CallerBody.cacheProcIn`). -/
def cacheProcInP (cacheProc : ℕ) : ℕ := 1 + cacheProc

/-- THE CACHE SLOT AT THE COMPOSED PROGRAM — route (c)'s renumbering step,
PROVED: `Solves cacheTask cacheProg cacheProc` survives the entry body being
placed in front of it, with the procedure at `1 + cacheProc` and the body
shifted by one (`Solves` → `Ends.append` → `Ends.shift_append`, i.e. the
`stageMeets_behind` route). The entry body consumes exactly this: the cache
call it makes is at a composed index, and the contract it needs is this one.

`Solves` is at the program `callerProgramUniv` builds, so nothing below has
to carry a renumbering argument of its own. -/
theorem cacheSolves_composed (stage cacheProc : ℕ)
    (cacheProg restoreProg : Light.Program) (cs : Inst) (R : Light.Program)
    (cacheTime : ℕ → ℕ → ℕ) (cacheNeed : ℕ → ℕ → Light.Need)
    (hcache : Light.Solves cacheTask cacheProg cacheProc cacheTime cacheNeed) :
    Light.Solves cacheTask (callerProgramUniv stage cacheProg restoreProg cs ++ R)
      (cacheProcInP cacheProc) cacheTime cacheNeed := by
  obtain ⟨body, hb, hE⟩ := hcache
  refine ⟨body.shift 1, ?_, ?_⟩
  · -- the body's index: procedure `cacheProc` of `cacheProg`, one layer deeper
    rw [cacheProcInP, Nat.add_comm]
    have h1 : (Program.behind [mpBodyUniv stage] cacheProg)[cacheProc + 1]? =
        some (body.shift 1) := by
      simpa using Program.getElem?_behind_right [mpBodyUniv stage] hb
    have h2 : callerProgramUniv stage cacheProg restoreProg cs
        = Program.behind [mpBodyUniv stage] cacheProg
          ++ ((Program.behind restoreProg (program cs)).map
              (Stmt.shift cacheProg.length)).map (Stmt.shift 1) := by
      simp [callerProgramUniv, Program.behind, List.map_append, List.append_assoc]
    rw [h2, List.append_assoc]
    exact getElem?_append_of_eq_some h1 _
  · -- the run: `Ends.shift_append` at the procedure's own program, then the
    -- composed program is `callerProgramUniv` by definition
    intro R' lim d x μ fr hpre hok
    have hP : Ends lim
        (cacheProg ++ (Program.behind restoreProg (program cs)).map (Stmt.shift cacheProg.length))
        d body ⟨frame (cacheTask.args x ++ [(fr : ℤ)]), μ⟩
        (cacheTime (cacheTask.size x) (cacheTask.bound x))
        (fun σ' => cacheTask.Post x μ fr (σ'.loc 0) σ'.mem) :=
      hE ((Program.behind restoreProg (program cs)).map (Stmt.shift cacheProg.length))
        lim d x μ fr hpre hok
    have hsh := Ends.shift_append (Q := [mpBodyUniv stage]) (R := R ++ R') hP
    rw [List.append_assoc]
    exact hsh

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
caller's layout values, and the product head's address in range.

CURE (b) SIMPLIFICATION (2026-11-10): the old last conjunct was an
unbounded-index address bookkeeping (`∀ t < mpRounds W, (x.c + t·n) + n ≤
lim.space ∧ |t·n| ≤ lim.word`) because the row pass addressed cell
`x.c + t·n`. The round now writes ONE cell, `x.c` (`univRowPass`), so the
whole obligation collapses to `x.c < lim.space` — the address
`Ends.store` demands — and is instance-sizing-free. -/
def UnivPins (lim : Limits) (vals : List ℤ) (x : MatInst) (W : ℕ) (σ : State) :
    Prop :=
  (∀ k' : ℕ, k' < 9 → σ.loc k' = vals.getD k' 0) ∧
  σ.loc Out = (x.c : ℤ) ∧
  σ.loc Nreg = (x.n : ℤ) ∧
  σ.loc U2 = (2 * x.U : ℤ) ∧
  x.c < lim.space

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
  · exact h5

/-- The pins are loc-only: they transfer along any state whose registers
agree. -/
theorem UnivPins_congr {lim : Limits} {vals : List ℤ} {x : MatInst} {W : ℕ}
    {σ σ' : State} (h : σ'.loc = σ.loc) (hp : UnivPins lim vals x W σ) :
    UnivPins lim vals x W σ' := by
  unfold UnivPins at hp ⊢
  simp only [h]
  exact hp

/-! ## The clock: the universal budget and its domination shape -/

/-- The output write's budget: the test `v Rt =' k 0` costs `1 + 1 + 1 = 3`,
the `Ends.ite` rule adds 1, and the store's branch costs `1 + 1 + 1 = 3`;
the `skip` branch is free. `7` is therefore exact, and — this is the point
of cure (b) — CONSTANT in `n`, where the row pass cost `13n + 16`. -/
def univRowB : ℕ := 7

/-- The round budget: the call's argument cost 9, the call overhead 2,
the tight stage clock, and the output write. -/
def univRoundB (n : ℕ) : ℕ := 9 + 2 + callerTt n + univRowB

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

/-- The cache call's own step count: its four argument expressions
(`v 0`, `v 0`, `v 5 +' v 0`, `v 5 +' k 4 *' v 0 +' (v 0 *' v 0)` cost
`1 + 1 + 3 + 9 = 14`) plus the call rule's 2. Constant in `n`, like
`univRowB`. -/
def univCallB : ℕ := 16

/-- THE UNIVERSAL CLOCK: the cache call at the entry, `mpRounds U` rounds at
the per-round unit budget, plus the prologue.

The cache term is `cacheTime (n²) U`: `cacheTask.size` is `P·I = n²` and
`cacheTask.bound` is the word bound `U`, so the call's clock is the cache
solver's own clock at the instance the entry body builds. It is carried as
an ARGUMENT (the cache's clock is abstract — route (c)'s disclosed cost). -/
def univTn (cacheTime : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  univCallB + cacheTime (n * n) U + (univProB n + mpRounds U * univUnitB n)

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
  simp only [univRoundB, univRowB, callerTt]
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
  simp only [univRoundB, univRowB, callerTt]
  omega

/-- The level body's budget is quadratic. -/
theorem univLevelB_le (n : ℕ) (hn : 1 ≤ n) : univLevelB n ≤ 510 * (n * n) := by
  have h1 : n ≤ n * n := Nat.le_mul_of_pos_right n (by omega)
  have hA : n * n + 6 * n + n ≤ 8 * (n * n) := by nlinarith
  have hB : 25 * (n * n + 6 * n + n) ≤ 200 * (n * n) := by nlinarith [hA]
  have hC : 13 * n ≤ 13 * (n * n) := Nat.mul_le_mul_left 13 h1
  have hD : (25 : ℕ) ≤ 25 * (n * n) :=
    Nat.mul_le_mul_left 25 (show (1 : ℕ) ≤ n * n from by nlinarith)
  unfold univLevelB univRoundB univRowB callerTt
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
theorem univTn_eq (cacheTime : ℕ → ℕ → ℕ) (n U : ℕ) :
    univTn cacheTime n U =
      univCallB + cacheTime (n * n) U + (univProB n + mpRounds U * univUnitB n) := rfl

/-- The universal budget, bounded: the cache's clock and the two loop
terms each fit one `(2·log₂U + 6)·770·n²` arm, so `univTn ≤ 2·(that) +
27n + 64`. The cache's own clock is NOT derivable from the schedule —
`cacheTime` is abstract — so its budget is a HYPOTHESIS, and without it this
statement is false. -/
theorem univTn_le (cacheTime : ℕ → ℕ → ℕ) (n U : ℕ) (hn : 1 ≤ n)
    (hcT : univCallB + cacheTime (n * n) U ≤ (2 * Nat.log2 U + 6) * (770 * (n * n))) :
    univTn cacheTime n U ≤ 2 * ((2 * Nat.log2 U + 6) * (770 * (n * n))) + 27 * n + 64 := by
  have hmp : mpRounds U ≤ 2 * Nat.log2 U + 6 := mpRounds_le_two_log_succ U
  have hU := univUnitB_le n hn
  have h1 : mpRounds U * univUnitB n ≤ (2 * Nat.log2 U + 6) * (770 * (n * n)) :=
    le_trans (Nat.mul_le_mul_right _ hmp) (Nat.mul_le_mul_left _ hU)
  have h2 : univProB n = 27 * n + 64 := rfl
  simp only [univTn, univCallB] at hcT ⊢
  omega

#print axioms scratch_facts
#print axioms shift_shift
#print axioms callerProgramUniv_entry
#print axioms callerProgramUniv_behind
#print axioms callerProgramUniv_stage
#print axioms univCacheArgs_val
#print axioms cacheSolves_composed
#print axioms UnivPins_update
#print axioms UnivPins_congr
#print axioms mpRounds_eq_signed
#print axioms univWhile_cost
#print axioms univRoundB_le
#print axioms univLevelB_le
#print axioms univUnitB_le
#print axioms univTn_le

/-! ## The round's output write (cure (b): one guarded cell, no row pass) -/

/-- THE ROUND'S OUTPUT WRITE'S RUN: from a pinned state whose round counter
reads `t` and whose `Tmp` holds the delivered value `r`, the guarded write
installs `r` in the product's head `x.c` exactly when `t = 0` and leaves the
memory untouched otherwise; it touches no register.

THE WRITE SET IS THE SINGLETON `{x.c}` — that is the whole point of cure (b).
It lies inside the product region `[x.c, x.c + n²)` for every `n ≥ 1`, so the
certified stage post and the `KeptBut` frame hold for ALL instances and no
containment premise on `mpRounds W` (`hregion`) is ever needed. -/
theorem univRowPass_runs
    {lim : Limits} {P : Light.Program} {d : ℕ} {x : MatInst} {W : ℕ}
    {vals : List ℤ} {ll : ℕ → ℤ} {μ : ℕ → ℤ} {r : ℤ} {t : ℕ} {T : ℕ}
    (hpins : UnivPins lim vals x W ⟨ll, μ⟩)
    (hword : (0 : ℤ) ≤ lim.word)
    (hRt : ll Rt = (t : ℤ)) (hTmp : ll Tmp = r)
    (hT : univRowB ≤ T) :
    Ends lim P d univRowPass ⟨ll, μ⟩ T
      (fun σ' => UnivPins lim vals x W σ' ∧
        σ'.mem x.c = (if t = 0 then r else μ x.c) ∧
        (∀ b' : ℕ, b' ≠ x.c → σ'.mem b' = μ b') ∧
        σ'.loc = ll) := by
  obtain ⟨hframe, hOut, hNreg, hU2, haddr⟩ := hpins
  simp only [State.loc] at hframe hOut hNreg hU2
  have hword' : ((0 : ℕ) : ℤ) ≤ lim.word := by simpa using hword
  have hcost : (v Rt =' k 0).cost + 1 + 3 ≤ T := by
    have hc : (v Rt =' k 0).cost = 3 := rfl
    have hb : univRowB = 7 := rfl
    omega
  have hsafe : (v Rt =' k 0).Safe lim ⟨ll, μ⟩ := by
    show (v Rt).Safe lim ⟨ll, μ⟩ ∧ (k 0).Safe lim ⟨ll, μ⟩
    exact ⟨trivial, hword'⟩
  have haddr' : lim.Addr (Expr.val ⟨ll, μ⟩ (v Out)) := by
    show lim.Addr (ll Out)
    rw [hOut]
    exact ⟨by positivity, by exact_mod_cast haddr⟩
  have htoNat : (ll Out).toNat = x.c := by rw [hOut]; simp
  unfold univRowPass
  by_cases ht0 : t = 0
  · -- the test holds: the store runs and installs `r` at the head
    have hholds : (v Rt =' k 0).Holds ⟨ll, μ⟩ := by
      show ll Rt = ((0 : ℕ) : ℤ)
      rw [hRt, ht0]
    refine Ends.ite 3 hsafe (fun _ => ?_) (fun hc => absurd hholds hc) hcost
    refine Ends.store ?_ ?_ haddr' ?_ ?_
    · exact trivial
    · exact trivial
    · show (v Out).cost + (v Tmp).cost + 1 ≤ 3
      simp only [Expr.cost]; omega
    · refine ⟨⟨hframe, hOut, hNreg, hU2, haddr⟩, ?_, ?_, rfl⟩
      · simp [State.mem, State.loc, Expr.val, htoNat, hTmp, ht0]
      · intro b' hb'
        simp [State.mem, State.loc, Expr.val, htoNat, hb']
  · -- the test fails: the memory is untouched
    have hnholds : ¬ (v Rt =' k 0).Holds ⟨ll, μ⟩ := by
      intro hh
      have h1 : ((0 : ℕ) : ℤ) = ll Rt := hh.symm
      rw [hRt] at h1
      exact ht0 (by omega)
    refine Ends.ite 3 hsafe (fun hc => absurd hc hnholds) (fun _ => ?_) hcost
    refine Ends.skip ⟨⟨hframe, hOut, hNreg, hU2, haddr⟩, ?_, ?_, rfl⟩
    · show μ x.c = (if t = 0 then r else μ x.c)
      rw [if_neg ht0]
    · intro b' _
      rfl

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

/-- THE ROUND SLICE'S RUN — the wire induction's brick, cure-(b) shape.

One certified stage call followed by the round's guarded output write, at the
caller program. The round's delivery `r` is the oracle premise (`hret`):
`bracketAccumulate (μ (x.c + t·n)) tests (mpRounds W)` — the fold SEEDED AT
ROW `t`'s HEAD, so rounds `t ≥ 1` carry different values and the write must not
let them clobber the head. Round 0 installs the fold in the product's head
`x.c` — the one cell the construction's identity premise consumes
(`bracketCell x 0 0 = x.c`) — and every later round leaves it alone.

WHAT IS GONE AND WHY IT WAS NEVER MATHEMATICS (cure (b), R2125609577). The
row-broadcast form also carried "the full row written at `x.c + t·n`", "every
other row unchanged" and "the cells below the free pointer outside the product
unchanged", and it needed `hregion : mpRounds W ≤ n` to keep the `x.n` row
stores inside the product region. With the singleton write set `{x.c}` the
stage's certified post (`SameOutside3` at `sb/bb/mb`) and the `KeptBut` frame
hold for ALL instances, so `hregion` is gone and the task stays UNRESTRICTED
(`mpTask`, not `mpTaskRounds`). -/
theorem univRound_runs
    {lim : Limits} {d : ℕ} {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr frC : ℕ}
    {cacheProg restoreProg : Light.Program} {cs : Inst}
    {stage : ℕ} {Tt : ℕ → ℕ} {R : Light.Program}
    {x : MatInst} {W : ℕ} {tests : ℕ → Bool × Bool}
    {vals : List ℤ} {ll : ℕ → ℤ} {μ : ℕ → ℤ} {mask : ℕ → Bool}
    {t : ℕ}
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
    (hword : (0 : ℤ) ≤ lim.word)
    (hRt : ll Rt = (t : ℤ))
    (hreads : ThinMatrix.CallerChain.StageReads P I active mask rows ab rb mb μ)
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)])
    (hfrCle : frC ≤ ab)
    (haway : (x.c < sb ∨ sb + P ≤ x.c) ∧
      (x.c < bb ∨ bb + I ≤ x.c) ∧
      (x.c < mb ∨ mb + P ≤ x.c))
    (hbelow : (x.c + x.n * x.n : ℕ) ≤ ab)
    (htW : t < mpRounds W)
    (hdim : d < lim.depth)
    (hTtk : Tt k ≤ callerTt x.n) :
    Ends lim (callerProgramUniv stage cacheProg restoreProg cs ++ R) d (univRound stage)
      ⟨ll, μ⟩ (univRoundB x.n)
      (fun σ' => ∃ (mask' : ℕ → Bool) (r : ℤ),
        ThinMatrix.CallerChain.StageReads P I active mask' rows ab rb mb σ'.mem ∧
        UnivPins lim vals x W σ' ∧
        r = bracketAccumulate (μ (x.c + t * x.n)) tests (mpRounds W) ∧
        σ'.mem x.c = (if t = 0 then r else μ x.c) ∧
        KeptBut μ σ'.mem frC x.c (x.n * x.n) ∧
        (∀ i : ℕ, i ≠ Tmp → σ'.loc i = ll i)) := by
  have hframe := hpins.1
  have hOut := hpins.2.1
  have hNreg := hpins.2.2.1
  have hU2 := hpins.2.2.2.1
  have haddr := hpins.2.2.2.2
  simp only [State.loc] at hframe hOut hNreg hU2
  have hcallcost : (callArgs.map Expr.cost).sum + 2 + Tt k + univRowB ≤ univRoundB x.n := by
    have h9 : (callArgs.map Expr.cost).sum = 9 := callArgs_cost
    simp only [univRoundB, univRowB]
    omega
  have hlayc : ab + I ≤ rb ∧ rb + P * I ≤ sb ∧ sb + P ≤ bb ∧ bb + I ≤ mb ∧
      mb + P ≤ fr := hlay
  obtain ⟨h1l, h2l, h3l, h4l, h5l⟩ := hlayc
  unfold univRound
  refine Ends.seq ((callArgs.map Expr.cost).sum + 2 + Tt k) univRowB ?_ hcallcost
  have hslot' := hslot (mask := mask) (kt := k) (μ := μ) hreads (hflag mask) (hok mask k)
  refine Ends.callLast hslot' ?_ ?_ hdim ?_
  · -- the continuation: the evolved reads, the pins, the head's delivery
    intro r₁ μ₁ hR
    obtain ⟨cs₁, hlen, hnd, hmem, hmask, hsam, h0', hpos⟩ := id hR
    have hreads₁ :=
      ThinMatrix.CallerChain.reads_carry (P := P) (I := I) (h := h) hlay hreads hsam hmask
    have hr_eq : r₁ = bracketAccumulate (μ (x.c + t * x.n)) tests (mpRounds W) :=
      hret t mask μ μ₁ r₁ htW ⟨cs₁, hlen, hnd, hmem, hmask, hsam, h0', hpos⟩
    have hhead : μ₁ x.c = μ x.c := hsam x.c haway
    -- the call's frame, restricted to the cells `KeptBut` speaks about
    have hkept₁ : KeptBut μ μ₁ frC x.c (x.n * x.n) := by
      intro b hb
      obtain ⟨hlt, hout⟩ := hb
      have h1 : Outside sb P b := Or.inl (by omega)
      have h2 : Outside bb I b := Or.inl (by omega)
      have h3 : Outside mb P b := Or.inl (by omega)
      exact hsam b ⟨h1, h2, h3⟩
    have hpinsμ₁ : UnivPins lim vals x W ⟨ll, μ₁⟩ := UnivPins_congr rfl hpins
    have hpins₁ : UnivPins lim vals x W ⟨Function.update ll Tmp r₁, μ₁⟩ :=
      UnivPins_update hpinsμ₁
    have huR : Function.update ll Tmp r₁ Rt = ll Rt :=
      dif_neg (by have h15 : Rt = (15 : ℕ) := rfl; have h10 : Tmp = (10 : ℕ) := rfl; omega)
    have hRt₁ : Function.update ll Tmp r₁ Rt = (t : ℤ) := by rw [huR]; exact hRt
    have hTmp₁ : Function.update ll Tmp r₁ Tmp = r₁ := by simp
    refine (univRowPass_runs (T := univRowB) hpins₁ hword hRt₁ hTmp₁ le_rfl).mono le_rfl ?_
    rintro σ' ⟨hP', hEq, hOther, hloc'⟩
    -- the reads regions lie at and above the active base, the product head
    -- strictly below it, so the single-cell write leaves every read intact
    have hsq : 1 ≤ x.n * x.n := by simpa using Nat.mul_le_mul hxn hxn
    have hlt : x.c < ab := by omega
    have hreads₂ :
        ThinMatrix.CallerChain.StageReads P I active (maskCleared cs₁.toFinset mask)
          rows ab rb mb σ'.mem := by
      refine ⟨fun i hi => ?_, fun p hp i hi => ?_, fun p hp => ?_⟩
      · rw [hOther (ab + i) (by omega)]; exact hreads₁.1 i hi
      · rw [hOther (rb + p * I + i) (by omega)]; exact hreads₁.2.1 p hp i hi
      · rw [hOther (mb + p) (by omega)]; exact hreads₁.2.2 p hp
    refine ⟨maskCleared cs₁.toFinset mask, r₁, hreads₂, hP', hr_eq, ?_, ?_, ?_⟩
    · -- the product's head holds round 0's delivery
      rw [hEq]
      by_cases h0 : t = 0
      · simp only [if_pos h0]
      · simp only [if_neg h0]; exact hhead
    · -- `KeptBut`: the call's frame plus the write's single-cell exclusion
      intro b hb
      obtain ⟨hltb, houtb⟩ := hb
      have hbne : b ≠ x.c := by
        rcases houtb with h | h
        · omega
        · have hsq : 1 ≤ x.n * x.n := by simpa using Nat.mul_le_mul hxn hxn
          omega
      rw [hOther b hbne]
      exact hkept₁ b ⟨hltb, houtb⟩
    · -- the registers: only `Tmp` moved
      intro i hiT
      rw [hloc']
      exact dif_neg hiT
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
  · -- the call's own clock, inside the round's budget
    simp only [callArgs_cost]
    omega

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
  · exact h5

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

/-! ## The all-cells invariant and the level body's run -/

/-- The level-loop invariant: the landed `UnivInv` plus the kept frame
(`KeptBut` below the caller's free pointer `frC`, the product region
excepted).

CURE (b) SHRINK (2026-11-10, R2125609577). The bookkeeping had TWO
all-cells clauses — "written rows carry the delivered fold" and "rows at or
after the flat round counter still hold their own `μ₀` values". Both existed
to justify the ROW PASS: every round rewrote `n` cells, so the induction had
to track which rows had been written and what the untouched ones held. The
round now writes ONE cell (`x.c`, guarded to round 0 — `univRowPass`), so:
  * there is no row write to justify, and both clauses are dropped;
  * "rows at/after the counter are untouched" is `KeptBut`'s content
    restricted below `frC`, which the frame clause already carries;
  * the head's value — the only cell any landed conclusion consumes — is
    `UnivInv`'s last conjunct, unchanged.
Nothing is weakened: the wiring below never read either clause. It is the
write shape that stopped needing them. -/
def UnivInvAll (lim : Limits) (vals : List ℤ) (x : MatInst) (W : ℕ)
    (P I : ℕ) (active : ℕ → Bool) (rows : ℕ → ℕ → ℕ) (ab rb mb : ℕ)
    (μ₀ : ℕ → ℤ) (tests : ℕ → Bool × Bool) (frC ell : ℕ) (σ : State) : Prop :=
  UnivInv lim vals x W P I active rows ab rb mb μ₀ tests ell σ ∧
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
  ∀ (l : ℕ → ℤ) (μ : ℕ → ℤ),
    UnivInvAll lim vals x W P I active rows ab rb mb μ₀ tests frC 0 ⟨l, μ⟩ →
    Ends lim (callerProgramUniv stage cacheProg restoreProg cs ++ R) d (univWhile stage)
      ⟨l, μ⟩ (mpRounds W * univUnitB x.n)
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
where the layout puts them. Read off the real `.set` chain (the buffers are
stacked in the ORDER the def writes them: active, rows, scores, base,
remaining — so `Base := Scores + Nreg` at `fr + 2n + n²` and
`Remaining := Base + Nreg` at `fr + 3n + n²`):

  vals[0] candidates     = n               (register 0 is never written — it
                                            still holds the input n)
  vals[1] length         = n               (`Len := v 0`)
  vals[2] height         = U               (`Height := v 1`)
  vals[3] activeBase     = fr              (`Active := v 5`)
  vals[4] rowsBase       = fr + n          (`Rows := Active + Nreg`)
  vals[5] scoresBase     = fr + n + n²     (`Scores := Rows + Nreg*Nreg`)
  vals[6] remainingBase  = fr + 3n + n²    (`Remaining := Base + Nreg`)
  vals[7] baseBase       = fr + 2n + n²    (`Base := Scores + Nreg`)
  vals[8] fr + 4n + n²                     (`Free := Remaining + Nreg`)

CORRECTION (disclosed, 2026-11-10): the first STATED form of this table
placed `baseBase` at `fr + n + n²` and `remainingBase` at `fr + 2n + n²`,
i.e. one buffer early — it counted the scores region as if `Base` followed
`Rows`. `Base := Scores + Nreg` and `Remaining := Base + Nreg`, so both
lie one `n` higher, and the stage's free pointer is `fr + 4n + n²`. The
def was always right; only this prose was wrong. The proof below consumes
the corrected values (`univProloguePins`).

THE ENTRY FRAME (disclosed amendment): the first STATED form passed ONE
`vals` and used it both as the entry frame (`frame vals`) and as the pin
list. Those cannot coincide: the entry state is the mpTask frame
`[n, U, a, b, c, fr]` (six registers), while the pins are the nine-value
stage frame the prologue PRODUCES. The def now takes the entry frame
separately (`frameVals`); `prologue_runs` supplies the correspondence
(`hframe`, `hvals`).

Four consequences the proof consumes:
- the writes land ONLY at `ab` (= `fr`) and `mb`; both are at or above
  `x.c + n*n` (`hbelow`), which is precisely why the product region is
  untouched and `KeptBut … frC x.c (n*n)` holds (with `hfrCle`);
- the ORDER of the def's sets is load-bearing: `Height := v 1` must read
  register 1 BEFORE `Len := v 0` overwrites it;
- the ROWS region is never written, so the level-0 stage reads are
  satisfiable by taking `rows p i := μ₀ (rb + p*I + i)` — the same
  "the array keeps the instance's own values" device the all-cells clause
  of `UnivInvAll` uses;
- the two passes write ONLY at `ab` and `mb` (then a stride of `n`), and
  every op value is dominated by the buffer stack's top, so the stack's
  WORD FIT (`fr + 4n + n² ≤ space ≤ word`) is the only resource premise. -/
def PrologueTarget
    {lim : Limits} {d : ℕ} {P k I h : ℕ} {active : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr frC : ℕ}
    (stage : ℕ) (cacheProg restoreProg : Light.Program) (cs : Inst)
    (R : Light.Program) (Tt : ℕ → ℕ)
    (x : MatInst) (W : ℕ) (tests : ℕ → Bool × Bool)
    (vals frameVals : List ℤ) (μ₀ : ℕ → ℤ) : Prop :=
  Ends lim (callerProgramUniv stage cacheProg restoreProg cs ++ R) d univPrologue
    ⟨frame frameVals, μ₀⟩ (univProB x.n)
    (UnivInvAll lim vals x W P I active rows ab rb mb μ₀ tests frC 0)

/-- The prologue's output pins: the nine-value stage frame, each entry
traced to the `.set` that produces it (`argsOf`'s slot order — the stage's
free pointer last). -/
def univProloguePins (x : MatInst) (fr : ℕ) : List ℤ :=
  [(x.n : ℤ), (x.n : ℤ), (x.U : ℤ), (fr : ℤ),
   (fr : ℤ) + (x.n : ℤ),
   (fr : ℤ) + (x.n : ℤ) + (x.n : ℤ) * (x.n : ℤ),
   (fr : ℤ) + 3 * (x.n : ℤ) + (x.n : ℤ) * (x.n : ℤ),
   (fr : ℤ) + 2 * (x.n : ℤ) + (x.n : ℤ) * (x.n : ℤ),
   (fr : ℤ) + 4 * (x.n : ℤ) + (x.n : ℤ) * (x.n : ℤ)]

/-- THE FRAME CORRESPONDENCE AT THE COMPOSITION SEAM — the brick the entry
assembly consumes (named "the next brick" in the FILL-3 session's notes).

`argsOf` is the stage's EIGHT argument slots; the nine-value frame `UnivPins`
pins registers 0..8 to is `argsOf ++ [free pointer]`. The prologue PRODUCES
that frame from the `mpTask` frame (`univProloguePins`), so the two lists must
agree slot by slot. They agree on slots 0–7 under the lay-out equations — and
slot 8 is NOT the caller's `fr`:

  * `mpTask`'s free pointer `fr` is where the CALLER's buffers BEGIN
    (slot 3, `activeBase := fr`);
  * the STAGE's free pointer is where they END: `mb + P = fr + 4n + n²`,
    the ninth pin — which is exactly the `Free := v Remaining +' v Nreg`
    the prologue computes.

DISCLOSED CORRECTION (2026-11-10, found while composing the two green halves):
`wireUnivTarget_of` carries `hvals : vals = argsOf callSite ++ [fr]`, i.e.
slot 8 = `fr`. That is the PER-INSTANCE skeleton's convention (`CallerRun`'s
body IS the round program, so its stage frame starts at the task frame). It is
not the UNIVERSAL body's, whose prologue stacks the five buffers at `fr` and
hands the stage `mb + P`. Composing the halves therefore requires the seam at
`++ [(mb + P : ℕ)]`; the brick states it that way and the caller must supply
`h = x.U` (slot 2 is `height`) as well as the lay-out equations. -/
theorem univProloguePins_eq_argsOf
    {P k I h : ℕ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {ab rb sb mb bb fr : ℕ} (x : MatInst)
    (hP : P = x.n) (hI : I = x.n) (hU : h = x.U)
    (hab : ab = fr) (hrb : rb = fr + x.n) (hsb : sb = fr + x.n + x.n * x.n)
    (hbb : bb = fr + 2 * x.n + x.n * x.n) (hmb : mb = fr + 3 * x.n + x.n * x.n) :
    argsOf (callSite P k I h active remaining rows ab rb sb mb bb)
        ++ [((mb + P : ℕ) : ℤ)]
      = univProloguePins x fr := by
  subst hP
  subst hI
  subst hU
  subst hab
  subst hrb
  subst hsb
  subst hbb
  subst hmb
  simp [argsOf, callSite, univProloguePins]
  all_goals ring

/-- The prologue's locals after the eleven frame `.set`s: the nine pins
plus the computed registers the sets write (`Out`, `Nreg`, `U2`). The two
passes then write `J`; the counters close the list. -/
def univPrologueMid (x : MatInst) (fr : ℕ) : List ℤ :=
  univProloguePins x fr ++ [0, 0, (x.c : ℤ), (x.n : ℤ), 2 * (x.U : ℤ)]

/-- The prologue's locals at the end: the pins, then `Out`, `Nreg`, `U2`,
the two counters, the zeroed scratch and the pass counter `J`. -/
def univPrologueLocals (x : MatInst) (fr : ℕ) : List ℤ :=
  univProloguePins x fr ++
    [0, 0, (x.c : ℤ), (x.n : ℤ), 2 * (x.U : ℤ), 1, 0, 0, 0, (x.n : ℤ)]

/-- The two passes' and the two counters' writes, in `setLocal` form:
the end-of-prologue locals are the mid locals with `J` twice, `Lvl` and
`Rt` written. -/
theorem univPrologueLocals_eq (x : MatInst) (fr : ℕ) :
    setLocal (setLocal (setLocal (setLocal (univPrologueMid x fr) J (x.n : ℤ))
        J (x.n : ℤ)) Lvl 1) Rt 0 = univPrologueLocals x fr := by
  simp [univPrologueLocals, univPrologueMid, univProloguePins, J, Lvl, Rt, setLocal]

/-- THE LEVEL BODY'S RUN — cure-(b) shape.

From the invariant at level `ℓ`, the level body — two certified rounds
(rounds `2·ℓ` and `2·ℓ+1`, the second at the first's evolved mask) plus the
three counter `.set`s — lands the invariant at level `ℓ + 1` within
`univLevelB x.n`.

WHAT SIMPLIFIED (cure (b), R2125609577). The old brick threaded three extra
obligations per round — the full row written, every other row unchanged, the
cells below the free pointer outside the product unchanged — and needed
`hregion : mpRounds W ≤ n` so that the `x.n` row stores stayed inside the
product region. With a singleton write set `{x.c}` guarded to round 0
(`univRowPass`) all three collapse: the round's `KeptBut` frame is the ONLY
memory obligation, the head's value is `UnivInv`'s last conjunct, and the
only round whose write is visible is `t = 0` (i.e. `ℓ = 0`). `hregion` is
gone; the task stays unrestricted. -/
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
  obtain ⟨hinvU, hkept⟩ := hinv
  obtain ⟨hpins, hLvl, hRt, hreadsEx, hcell⟩ := hinvU
  simp only [State.loc] at hLvl hRt
  simp only [State.mem] at hcell
  obtain ⟨mask, hreads⟩ := hreadsEx
  have hmp : mpRounds W = 2 * signedLevels W := mpRounds_eq_signed W
  have h2ltW : 2 * ℓ < mpRounds W := by rw [hmp]; omega
  have h2lt1W : 2 * ℓ + 1 < mpRounds W := by rw [hmp]; omega
  have hword : (0 : ℤ) ≤ lim.word := by have := hspace; omega
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
  have hcostRt : (v Rt +' Light.k 1).cost + 1 = 4 := by simp only [Expr.cost]
  have hcostLvl : (Light.k 2 *' v Lvl).cost + 1 = 4 := by simp only [Expr.cost]
  -- the two counter writes' word bounds, at the state they are read in
  -- the constants `1` and `2` fit a word: the layout's head address does
  have hword2 : (2 : ℤ) ≤ lim.word := by
    have h2 : ((2 ^ 1 : ℕ) : ℤ) ≤ ((2 ^ signedLevels W : ℕ) : ℤ) :=
      Nat.cast_le.2 (Nat.pow_le_pow_right (by omega) (signedLevels_pos W))
    simpa using le_trans h2 hwordLvl
  have hword1 : (1 : ℤ) ≤ lim.word := by omega
  have hsafeRt : ∀ (l' : ℕ → ℤ) (μ' : ℕ → ℤ), |l' Rt + 1| ≤ lim.word →
      (v Rt +' Light.k 1).Safe lim ⟨l', μ'⟩ := by
    intro l' μ' h
    exact ⟨trivial, by simpa using hword1, h⟩
  have hsafeLvl : ∀ (l' : ℕ → ℤ) (μ' : ℕ → ℤ), |(2 : ℤ) * l' Lvl| ≤ lim.word →
      (Light.k 2 *' v Lvl).Safe lim ⟨l', μ'⟩ := by
    intro l' μ' h
    exact ⟨by simpa using hword2, trivial, h⟩
  have hRtN : ll Rt = ((2 * ℓ : ℕ) : ℤ) := hRt
  have hwordRt1 : |ll Rt + 1| ≤ lim.word := by
    rw [hRtN]
    have h1 : (0 : ℤ) ≤ ((2 * ℓ : ℕ) : ℤ) + 1 := by positivity
    rw [abs_of_nonneg h1]
    have h2 : ((2 * ℓ : ℕ) : ℤ) + 1 = ((2 * ℓ + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h2]
    exact le_trans (by exact_mod_cast Nat.le_of_lt h2lt1W) hwordRt
  have hwordLvl1 : |(2 : ℤ) * ll Lvl| ≤ lim.word := by
    have h1 : (0 : ℤ) ≤ (2 : ℤ) * ll Lvl := by rw [hLvl]; positivity
    rw [abs_of_nonneg h1, hLvl]
    have h2 : (2 : ℤ) * ((2 ^ ℓ : ℕ) : ℤ) = ((2 ^ (ℓ + 1) : ℕ) : ℤ) := by
      rw [Nat.pow_succ]; push_cast; ring
    rw [h2]
    exact le_trans (by exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega)) hwordLvl
  have hTmp15 : Tmp ≠ Rt := by
    have h15 : Rt = (15 : ℕ) := rfl
    have h10 : Tmp = (10 : ℕ) := rfl
    omega
  have hRtne : Rt ≠ Tmp := fun h => hTmp15 h.symm
  unfold univLevelBody
  -- round `2·ℓ`
  refine Ends.seq (univRoundB x.n) (univLevelB x.n - univRoundB x.n) ?_ (by rw [hB1]; exact hT)
  refine (univRound_runs hxn hvals hslot hret hflag hok hpins hword hRt hreads hlay hfrCle
    haway hbelow h2ltW hdim hTtk).mono le_rfl ?_
  rintro ⟨llB, μ₁⟩ ⟨mask₁, r₁, hR1, hP1, hReq1, hHead1, hKept1, hlocB⟩
  simp only [State.mem, State.loc] at hHead1 hlocB
  have hcell1 : μ₁ x.c = bracketAccumulate (μ₀ x.c) tests (mpRounds W) := by
    by_cases hℓ0 : ℓ = 0
    · subst hℓ0
      rw [if_pos (by omega : 2 * 0 = 0)] at hHead1
      rw [hHead1, hReq1]
      simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
      rw [if_pos rfl] at hcell
      rw [hcell]
    · rw [if_neg (by omega : ¬ (2 * ℓ = 0))] at hHead1
      rw [hHead1]
      rw [if_neg hℓ0] at hcell
      exact hcell
  have hRtB : llB Rt = ((2 * ℓ : ℕ) : ℤ) := by rw [hlocB Rt hRtne]; exact hRtN
  have hwordRtB : |llB Rt + 1| ≤ lim.word := by
    rw [hRtB]
    simpa only [hRtN] using hwordRt1
  -- `Rt := 2·ℓ + 1`
  refine Ends.seq 4 (univLevelB x.n - univRoundB x.n - 4) ?_ (by omega)
  refine Ends.set (hsafeRt llB μ₁ hwordRtB) (by rw [hcostRt]) ?_
  simp only [Expr.val, Op.eval]
  set ll₂ : ℕ → ℤ := Function.update llB Rt (llB Rt + 1) with hll₂
  have hll₂Rt : ll₂ Rt = ((2 * ℓ + 1 : ℕ) : ℤ) := by
    rw [hll₂, Function.update_self, hRtB]; push_cast; ring
  have hll₂Agree : ∀ i : ℕ, i ≠ Rt → ll₂ i = llB i := by
    intro i hi; rw [hll₂, Function.update_of_ne hi]
  have hll₂Lvl : ll₂ Lvl = ((2 ^ ℓ : ℕ) : ℤ) := by
    rw [hll₂Agree Lvl (by
      have h14 : Lvl = (14 : ℕ) := rfl
      have h15 : Rt = (15 : ℕ) := rfl
      omega)]
    rw [hlocB Lvl (by
      have h14 : Lvl = (14 : ℕ) := rfl
      have h10 : Tmp = (10 : ℕ) := rfl
      omega)]
    exact hLvl
  -- round `2·ℓ + 1`, at the first round's evolved mask
  refine Ends.seq (univRoundB x.n) (univLevelB x.n - univRoundB x.n - 4 - univRoundB x.n)
    ?_ (by omega)
  have hpins₂ : UnivPins lim vals x W ⟨ll₂, μ₁⟩ := by
    rw [hll₂]
    exact UnivPins_set hP1 (i := Rt)
      (by intro k' hk'; have h15 : Rt = (15 : ℕ) := rfl; omega)
      (by have h11 : Out = (11 : ℕ) := rfl; have h15 : Rt = (15 : ℕ) := rfl; omega)
      (by have h12 : Nreg = (12 : ℕ) := rfl; have h15 : Rt = (15 : ℕ) := rfl; omega)
      (by have h13 : U2 = (13 : ℕ) := rfl; have h15 : Rt = (15 : ℕ) := rfl; omega)
  refine (univRound_runs hxn hvals hslot hret hflag hok hpins₂ hword hll₂Rt hR1 hlay hfrCle
    haway hbelow h2lt1W hdim hTtk).mono le_rfl ?_
  rintro ⟨llC, μ₂⟩ ⟨mask₂, r₂, hR2, hP2, hReq2, hHead2, hKept2, hlocC⟩
  simp only [State.mem, State.loc] at hHead2 hlocC
  have hcell2 : μ₂ x.c = bracketAccumulate (μ₀ x.c) tests (mpRounds W) := by
    rw [hHead2, if_neg (by omega : ¬ (2 * ℓ + 1 = 0))]
    exact hcell1
  have hRtC : llC Rt = ((2 * ℓ + 1 : ℕ) : ℤ) := by rw [hlocC Rt hRtne]; exact hll₂Rt
  have hLvlC : llC Lvl = ((2 ^ ℓ : ℕ) : ℤ) := by
    rw [hlocC Lvl (by
      have h14 : Lvl = (14 : ℕ) := rfl
      have h10 : Tmp = (10 : ℕ) := rfl
      omega)]
    exact hll₂Lvl
  -- `Rt := 2·ℓ + 2`
  refine Ends.seq 4 (univLevelB x.n - univRoundB x.n - 4 - univRoundB x.n - 4)
    ?_ (by omega)
  refine Ends.set ?_ (by rw [hcostRt]) ?_
  · exact hsafeRt llC μ₂ (by
      rw [hRtC]
      have h1 : (0 : ℤ) ≤ ((2 * ℓ + 1 : ℕ) : ℤ) + 1 := by positivity
      rw [abs_of_nonneg h1]
      have h2 : ((2 * ℓ + 1 : ℕ) : ℤ) + 1 = ((2 * ℓ + 2 : ℕ) : ℤ) := by push_cast; ring
      rw [h2]
      exact le_trans (by exact_mod_cast (by rw [hmp]; omega : 2 * ℓ + 2 ≤ mpRounds W)) hwordRt)
  simp only [Expr.val, Op.eval]
  set ll₃ : ℕ → ℤ := Function.update llC Rt (llC Rt + 1) with hll₃
  have hll₃Rt : ll₃ Rt = ((2 * ℓ + 2 : ℕ) : ℤ) := by
    rw [hll₃, Function.update_self, hRtC]; push_cast; ring
  have hll₃Agree : ∀ i : ℕ, i ≠ Rt → ll₃ i = llC i := by
    intro i hi; rw [hll₃, Function.update_of_ne hi]
  have hll₃Lvl : ll₃ Lvl = ((2 ^ ℓ : ℕ) : ℤ) := by
    rw [hll₃Agree Lvl (by
      have h14 : Lvl = (14 : ℕ) := rfl
      have h15 : Rt = (15 : ℕ) := rfl
      omega)]
    exact hLvlC
  -- `Lvl := 2·Lvl`, closing at level `ℓ + 1`
  refine Ends.set (hsafeLvl ll₃ μ₂ (by
    rw [hll₃Lvl]
    have h1 : (0 : ℤ) ≤ (2 : ℤ) * ((2 ^ ℓ : ℕ) : ℤ) := by positivity
    rw [abs_of_nonneg h1]
    have h2 : (2 : ℤ) * ((2 ^ ℓ : ℕ) : ℤ) = ((2 ^ (ℓ + 1) : ℕ) : ℤ) := by
      rw [Nat.pow_succ]; push_cast; ring
    rw [h2]
    exact le_trans (by exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega)) hwordLvl))
    (by rw [hcostLvl]; omega) ?_
  simp only [Expr.val, Op.eval]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- the pins survive the two counter writes
    rw [hll₃, hll₂] at *
    refine UnivPins_set (UnivPins_set (UnivPins_congr rfl hP2)
      (i := Rt) (by intro k' hk'; have h15 : Rt = (15 : ℕ) := rfl; omega)
      (by have h11 : Out = (11 : ℕ) := rfl; have h15 : Rt = (15 : ℕ) := rfl; omega)
      (by have h12 : Nreg = (12 : ℕ) := rfl; have h15 : Rt = (15 : ℕ) := rfl; omega)
      (by have h13 : U2 = (13 : ℕ) := rfl; have h15 : Rt = (15 : ℕ) := rfl; omega))
      (i := Lvl)
      (by intro k' hk'; have h14 : Lvl = (14 : ℕ) := rfl; omega)
      (by have h11 : Out = (11 : ℕ) := rfl; have h14 : Lvl = (14 : ℕ) := rfl; omega)
      (by have h12 : Nreg = (12 : ℕ) := rfl; have h14 : Lvl = (14 : ℕ) := rfl; omega)
      (by have h13 : U2 = (13 : ℕ) := rfl; have h14 : Lvl = (14 : ℕ) := rfl; omega)
  · -- the level register: `2 · 2^ℓ = 2^(ℓ+1)`
    show Function.update ll₃ Lvl (2 * ll₃ Lvl) Lvl = ((2 ^ (ℓ + 1) : ℕ) : ℤ)
    rw [Function.update_self, hll₃Lvl]
    push_cast
    ring
  · -- the flat round counter: `2·ℓ + 2 = 2·(ℓ+1)`
    show Function.update ll₃ Lvl (2 * ll₃ Lvl) Rt = ((2 * (ℓ + 1) : ℕ) : ℤ)
    rw [Function.update_of_ne (by
      have h14 : Lvl = (14 : ℕ) := rfl
      have h15 : Rt = (15 : ℕ) := rfl
      omega), hll₃Rt]
    push_cast
    ring
  · -- the reads at the second round's evolved mask (the counters touch none)
    exact ⟨mask₂, hR2⟩
  · -- the head still carries the fold
    show μ₂ x.c = (if ℓ + 1 = 0 then μ₀ x.c else bracketAccumulate (μ₀ x.c) tests (mpRounds W))
    rw [if_neg (by omega : ¬ (ℓ + 1 = 0))]
    exact hcell2
  · -- the frame: three `KeptBut` links, none of them touching the product's head
    exact hkept.trans (hKept1.trans hKept2)

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
  intro l μ h0
  have hWne : W ≠ 0 := by omega
  have hPowLe : 2 ^ (signedLevels W - 1) ≤ 2 * W := pow_pred_signed_levels_le W hWne
  have hPowGt : 2 * W < 2 ^ signedLevels W := two_mul_lt_pow_signed_levels W
  have hsum : (∑ i ∈ Finset.range (signedLevels W), (5 + 1 + univLevelB x.n)) + (5 + 1)
      = signedLevels W * (univTestB + univLevelB x.n) + univTestB := by
    simp only [univTestB]
    rw [Finset.sum_const, Finset.card_range]
    simp
  have hwhile : Ends lim (callerProgramUniv stage cacheProg restoreProg cs ++ R) d
      (.while (v Lvl ≤' v U2) (univLevelBody stage)) ⟨l, μ⟩
      ((∑ i ∈ Finset.range (signedLevels W), (5 + 1 + univLevelB x.n)) + (5 + 1))
      (fun σ' => UnivPins lim vals x W σ' ∧
        σ'.mem x.c = bracketAccumulate (μ₀ x.c) tests (mpRounds W) ∧
        (∃ mask' : ℕ → Bool,
          ThinMatrix.CallerChain.StageReads P I active mask' rows ab rb mb σ'.mem)) := by
    refine Ends.while
      (I := fun ell σ => UnivInvAll lim vals x W P I active rows ab rb mb μ₀ tests frC ell σ)
      (n := signedLevels W) (b := fun _ => univLevelB x.n)
      (c := (v Lvl ≤' v U2)) (s := univLevelBody stage) (σ := ⟨l, μ⟩) h0 ?_ ?_
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
          hxn hvals hslot hret hflag hok hlay hfrCle haway hbelow hspace hdim hTtk
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

/-! ## The entry assembly's run: the prologue -/

/-- The mid-frame's row-length register holds `n` (the first pass's length). -/
theorem univPrologueMid_nreg (x : MatInst) (fr : ℕ) :
    frame (univPrologueMid x fr) Nreg = (x.n : ℤ) := by
  simp [univPrologueMid, univProloguePins, Nreg, frame]

/-- The mid-frame's active base holds `fr` (the first pass's destination). -/
theorem univPrologueMid_active (x : MatInst) (fr : ℕ) :
    frame (univPrologueMid x fr) Active = (fr : ℤ) := by
  simp [univPrologueMid, univProloguePins, Active, frame]

/-- The mid-frame's row-length register survives the first pass's counter
write (the counter is `J`, not `Nreg`). -/
theorem univPrologueMid_nreg' {x : MatInst} {fr : ℕ} :
    frame (setLocal (univPrologueMid x fr) J (x.n : ℤ)) Nreg = (x.n : ℤ) := by
  rw [frame_setLocal]
  simp [Nreg, J, univPrologueMid, univProloguePins, frame]

/-- The mid-frame's remaining base holds `fr + 3n + n²` — the second
pass's destination — and survives the first pass's counter write. -/
theorem univPrologueMid_remaining {x : MatInst} {fr : ℕ} :
    frame (setLocal (univPrologueMid x fr) J (x.n : ℤ)) Remaining
      = ((fr + 3 * x.n + x.n * x.n : ℕ) : ℤ) := by
  rw [frame_setLocal]
  simp [Remaining, J, univPrologueMid, univProloguePins, frame] <;> push_cast <;> ring

/-- THE ENTRY ASSEMBLY'S RUN: `univPrologue`, started in the `mpTask`
frame `[n, U, a, b, c, fr]` over the instance memory `μ₀`, ends within
`univProB x.n` in the level loop's ZERO invariant — the sole missing
premise of `wireUnivTarget_of`.

The budget is charged exactly: the thirteen `.set`s (forty steps), the
two all-ones passes (`13n + 6` each), and the two counter sets are all in
that forty — `40 + 2·(13n+6) = 26n + 52 ≤ 27n + 64 = univProB n`.

The hypothesis list is the frame correspondence (`hframe`, `hvals`) plus
the instance's own lay-out facts: the product region below the buffers
(`hbelow`), the buffer stack's fit (`hfit`), `space ≤ word`, the `2·U`
word bound, the active mask's truth (`hactive`), and the rows table's
memory image (`hrows`) — the level-0 stage reads' "the array keeps the
instance's own values" device. (The `hregion : mpRounds W ≤ n` premise that
stood here is GONE — cure (b) made the write set `{x.c}`, so no instance-
class containment is needed. Corrected, not silently dropped.) -/
theorem prologue_runs
    {lim : Limits} {d : ℕ} {P k I h : ℕ} {active : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr frC : ℕ}
    (stage : ℕ) (cacheProg restoreProg : Light.Program) (cs : Inst)
    (R : Light.Program) (Tt : ℕ → ℕ)
    (x : MatInst) (W : ℕ) (tests : ℕ → Bool × Bool)
    (vals frameVals : List ℤ) (μ₀ : ℕ → ℤ)
    (hxn : 1 ≤ x.n)
    (hframe : frameVals = [(x.n : ℤ), (x.U : ℤ), (x.a : ℤ), (x.b : ℤ),
      (x.c : ℤ), (fr : ℤ)])
    (hvals : vals = univProloguePins x fr)
    (hI : I = x.n) (hP : P = x.n)
    (hab : ab = fr) (hrb : rb = fr + x.n) (hsb : sb = fr + x.n + x.n * x.n)
    (hbb : bb = fr + 2 * x.n + x.n * x.n) (hmb : mb = fr + 3 * x.n + x.n * x.n)
    (hfrC : frC ≤ ab)
    (hbelow : x.c + x.n * x.n ≤ ab)
    (hfit : fr + 4 * x.n + x.n * x.n ≤ lim.space)
    (hspace : (lim.space : ℤ) ≤ lim.word)
    (hwordU2 : |2 * (x.U : ℤ)| ≤ lim.word)
    (hword1 : (1 : ℤ) ≤ lim.word)
    (hactive : ∀ i < I, active i = true)
    (hrows : ∀ p < P, ∀ i < I, rows p i = μ₀ (rb + p * I + i)) :
    PrologueTarget (lim := lim) (d := d) (P := P) (k := k) (I := I) (h := h)
      (active := active) (rows := rows) (ab := ab) (rb := rb) (sb := sb)
      (mb := mb) (bb := bb) (fr := fr) (frC := frC)
      stage cacheProg restoreProg cs R Tt x W tests vals frameVals μ₀ := by
  unfold PrologueTarget
  subst hvals
  subst hframe
  subst hI
  subst hP
  subst ab
  subst hrb
  subst hsb
  subst hbb
  subst hmb
  -- the numeric context: the buffer stack's fit, and the word's positivity
  have hw0 : (0 : ℤ) ≤ lim.word := by
    have h1 : (0 : ℤ) ≤ (lim.space : ℤ) := by exact_mod_cast Nat.zero_le lim.space
    linarith
  have hZ : (fr : ℤ) + 4 * (x.n : ℤ) + (x.n : ℤ) * (x.n : ℤ) ≤ lim.word := by
    have h1 : ((fr + 4 * x.n + x.n * x.n : ℕ) : ℤ) ≤ (lim.space : ℤ) := by
      exact_mod_cast hfit
    have h2 : (lim.space : ℤ) ≤ lim.word := hspace
    have h3 := le_trans h1 h2
    push_cast at h3
    linarith
  have hU2le : 2 * (x.U : ℤ) ≤ lim.word := (abs_le.mp hwordU2).2
  have hU2ge : -(lim.word) ≤ 2 * (x.U : ℤ) := (abs_le.mp hwordU2).1
  have hfr_space : fr + x.n ≤ lim.space := by
    have h1 : fr + x.n ≤ fr + 4 * x.n + x.n * x.n := by omega
    omega
  have hmb_space : fr + 3 * x.n + x.n * x.n + x.n ≤ lim.space := by
    omega
  have hn2_word : ((x.n * x.n : ℕ) : ℤ) ≤ lim.word := by
    have h1 : ((x.n * x.n : ℕ) : ℤ) ≤ ((fr + 4 * x.n + x.n * x.n : ℕ) : ℤ) := by
      exact_mod_cast (by omega : x.n * x.n ≤ fr + 4 * x.n + x.n * x.n)
    exact le_trans h1 (le_trans (by exact_mod_cast hfit) hspace)
  -- the two passes' writes, named
  let μ₁ : ℕ → ℤ := wrote μ₀ fr (fun _ => 1) x.n
  let μ₂ : ℕ → ℤ := wrote μ₁ (fr + 3 * x.n + x.n * x.n) (fun _ => 1) x.n
  -- the run
  have hcore : Ends lim (callerProgramUniv stage cacheProg restoreProg cs ++ R) d
      univPrologue
      ⟨frame [(x.n : ℤ), (x.U : ℤ), (x.a : ℤ), (x.b : ℤ), (x.c : ℤ), (fr : ℤ)],
        μ₀⟩ (26 * x.n + 52)
      (fun σ' => σ' = ⟨frame (univPrologueLocals x fr), μ₂⟩) := by
    unfold univPrologue
    -- the eleven frame sets
    refine Ends.setToThen ((x.U : ℤ)) ?_
    refine Ends.setToThen (2 * (x.U : ℤ)) ?_
    refine Ends.setToThen ((x.c : ℤ)) ?_
    refine Ends.setToThen ((x.n : ℤ)) ?_
    refine Ends.setToThen ((x.n : ℤ)) ?_
    refine Ends.setToThen ((fr : ℤ)) ?_
    refine Ends.setToThen ((fr : ℤ) + (x.n : ℤ)) ?_
    refine Ends.setToThen ((fr : ℤ) + (x.n : ℤ) + (x.n : ℤ) * (x.n : ℤ)) ?_
    refine Ends.setToThen ((fr : ℤ) + 2 * (x.n : ℤ) + (x.n : ℤ) * (x.n : ℤ)) ?_
    refine Ends.setToThen ((fr : ℤ) + 3 * (x.n : ℤ) + (x.n : ℤ) * (x.n : ℤ)) ?_
    refine Ends.setToThen ((fr : ℤ) + 4 * (x.n : ℤ) + (x.n : ℤ) * (x.n : ℤ)) ?_
    -- the two initialization passes
    have hpass1 : Ends lim (callerProgramUniv stage cacheProg restoreProg cs ++ R) d
        (Light.pass J (v Nreg) (v Active) (Light.k 1))
        ⟨frame (univPrologueMid x fr), μ₀⟩ (13 * x.n + 6)
        (fun σ' => σ' = ⟨frame (setLocal (univPrologueMid x fr) J (x.n : ℤ)), μ₁⟩) := by
      refine Ends.pass (n := x.n) (dst := fr) (fun _ => 1) ?_ ?_ hspace ?_ ?_ ?_ (by decide) (by decide) ?_
      · intro j hj
        exact ⟨hword1, rfl⟩
      · simp [update_frame_setLocal, μ₁]
      · exact hfr_space
      · exact univPrologueMid_nreg x fr
      · exact univPrologueMid_active x fr
      · simp only [Expr.cost]
        omega
    have hpass2 : Ends lim (callerProgramUniv stage cacheProg restoreProg cs ++ R) d
        (Light.pass J (v Nreg) (v Remaining) (Light.k 1))
        ⟨frame (setLocal (univPrologueMid x fr) J (x.n : ℤ)), μ₁⟩ (13 * x.n + 6)
        (fun σ' => σ' = ⟨frame (setLocal (setLocal (univPrologueMid x fr) J (x.n : ℤ))
          J (x.n : ℤ)), μ₂⟩) := by
      refine Ends.pass (n := x.n) (dst := fr + 3 * x.n + x.n * x.n) (fun _ => 1) ?_ ?_ hspace ?_ ?_ ?_ (by decide) (by decide) ?_
      · intro j hj
        exact ⟨hword1, rfl⟩
      · simp [update_frame_setLocal, μ₂]
      · exact hmb_space
      · exact univPrologueMid_nreg'
      · exact univPrologueMid_remaining
      · simp only [Expr.cost]
        omega
    refine Ends.pieceThen hpass1 ?_ (by light_time)
    intro σ' hσ'
    rw [hσ']
    refine Ends.pieceThen hpass2 ?_ (by light_time)
    intro σ'' hσ''
    rw [hσ'']
    -- the two counter sets
    refine Ends.setToThen (1 : ℤ) ?_ (by exact ⟨hword1, rfl⟩) (by simp only [Expr.cost]; omega)
    refine Ends.setTo (0 : ℤ) ?_ (by exact ⟨hw0, rfl⟩) (by simp only [Expr.cost]; omega)
    rw [univPrologueLocals_eq]
  -- the invariant at level zero
  refine hcore.mono (T' := univProB x.n) (by unfold univProB; omega) ?_
  intro σ' hσ'
  subst hσ'
  try dsimp only [State.mem, State.loc]
  refine ⟨?_, ?_⟩
  · -- UnivInv: pins, the two counters, the reads, the product cell
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- the nine frame pins
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro k' hk'
        interval_cases k' <;>
          simp [univPrologueLocals, univProloguePins, frame] <;> try ring
      · simp [univPrologueLocals, univProloguePins, Out, frame]
      · simp [univPrologueLocals, univProloguePins, Nreg, frame]
      · simp [univPrologueLocals, univProloguePins, U2, frame] <;> push_cast <;> ring
      · -- the product head's address: strictly inside the buffer stack
        omega
    · -- the level counter
      simp only [univPrologueLocals, univProloguePins, Lvl, frame]
      norm_num
    · -- the round counter
      simp only [univPrologueLocals, univProloguePins, Rt, frame]
      norm_num
    · -- the level-0 stage reads: the arrays keep the instance's own values
      refine ⟨fun _ => true, ?_, ?_, ?_⟩
      · intro i hi
        show μ₂ (fr + i) = DenseScorePass.bit (active i)
        have hai : active i = true := hactive i hi
        have hout : Outside (fr + 3 * x.n + x.n * x.n) x.n (fr + i) := Or.inl (by omega)
        have hwr : μ₂ (fr + i) = μ₁ (fr + i) :=
          wrote_rest (μ := μ₁) (f := fun _ => 1) hout
        have hdone : μ₁ (fr + i) = 1 :=
          wrote_done (μ := μ₀) (dst := fr) (f := fun _ => 1) (i := i) (j := x.n) hi
        rw [hwr, hdone, hai]
        simp [DenseScorePass.bit]
      · intro p hp i hi
        show μ₂ (fr + x.n + p * x.n + i) = ((rows p i : ℕ) : ℤ)
        have hout : Outside (fr + 3 * x.n + x.n * x.n) x.n (fr + x.n + p * x.n + i) :=
          Or.inl (by nlinarith)
        have hwr : μ₂ (fr + x.n + p * x.n + i) = μ₁ (fr + x.n + p * x.n + i) :=
          wrote_rest (μ := μ₁) (f := fun _ => 1) hout
        have hwr2 : μ₁ (fr + x.n + p * x.n + i) = μ₀ (fr + x.n + p * x.n + i) :=
          wrote_rest (μ := μ₀) (f := fun _ => 1) (Or.inr (by omega))
        rw [hwr, hwr2]
        exact (hrows p hp i hi).symm
      · intro p hp
        show μ₂ (fr + 3 * x.n + x.n * x.n + p) = DenseArgminPass.bit ((fun _ => true) p)
        have hdone : μ₂ (fr + 3 * x.n + x.n * x.n + p) = 1 :=
          wrote_done (μ := μ₁) (dst := fr + 3 * x.n + x.n * x.n)
            (f := fun _ => 1) (i := p) (j := x.n) hp
        rw [hdone]
        simp [DenseArgminPass.bit]
    · -- the product cell is untouched at level zero
      show μ₂ x.c = μ₀ x.c
      have h1 : μ₂ x.c = μ₁ x.c := wrote_rest (μ := μ₁) (f := fun _ => 1) (Or.inl (by omega))
      have h2 : μ₁ x.c = μ₀ x.c := wrote_rest (μ := μ₀) (f := fun _ => 1) (Or.inl (by nlinarith))
      rw [h1, h2]
  · -- the kept frame below the caller's free pointer
    intro b hb
    obtain ⟨hb1, _⟩ := hb
    show wrote (wrote μ₀ fr (fun _ => 1) x.n) (fr + 3 * x.n + x.n * x.n) (fun _ => 1) x.n b = μ₀ b
    have hout : Outside (fr + 3 * x.n + x.n * x.n) x.n b := Or.inl (by omega)
    have hout2 : Outside fr x.n b := Or.inl (by omega)
    rw [wrote_rest (μ := wrote μ₀ fr (fun _ => 1) x.n) (f := fun _ => 1) hout,
      wrote_rest (μ := μ₀) (f := fun _ => 1) hout2]

#print axioms univPrologueLocals_eq

#print axioms prologue_runs

/-! ## THE ENTRY ASSEMBLY — the two halves composed -/

/-- THE ENTRY ASSEMBLY'S TARGET AT THE COMPOSED PROGRAM (lane target-def
pattern: no sorry, no new axiom).

`mpBodyUniv stage` is BY DEFINITION `univPrologue ;; univWhile stage`, so the
composition is one `Ends.seq`: the prologue's `univProB x.n` and the while's
`mpRounds W * univUnitB x.n` ADD, and the while's precondition is exactly the
prologue's post-invariant (`UnivInvAll … frC 0`). The two halves were already
parametrised over the same `vals`, `μ₀`, `frC`, program and `R`, so nothing else
is needed — the clocks add, they do not have to be re-derived.

THE MEMORY BINDER IS THE WHOLE POINT. `WireUnivTarget` quantifies the while's
start state as `⟨l, μ⟩`: the LOCATION assignment free, the MEMORY bound by the
argument. The prologue's two initialisation passes WRITE memory (the active
bits at `ab` and the remaining flags at `mb`), so the while does not start at
`μ₀` — it starts at the prologue's end memory. Before 2026-11-10 the target
hard-wired `⟨l, μ₀⟩`, which made this composition unstatable; the def now
carries the memory as a bound variable (disclosed there) and `μ₀` keeps its
one job, the reference memory in `KeptBut` and in the cell-(0,0) seed. -/
theorem entryAssembly
    {lim : Limits} {d : ℕ} {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr frC : ℕ}
    (stage : ℕ) (cacheProg restoreProg : Light.Program) (cs : Inst)
    (R : Light.Program) (Tt : ℕ → ℕ)
    (x : MatInst) (W : ℕ) (tests : ℕ → Bool × Bool)
    (vals frameVals : List ℤ) (μ₀ : ℕ → ℤ)
    (hpro : PrologueTarget (lim := lim) (d := d) (P := P) (k := k) (I := I) (h := h)
      (active := active) (rows := rows) (ab := ab) (rb := rb) (sb := sb)
      (mb := mb) (bb := bb) (fr := fr) (frC := frC)
      stage cacheProg restoreProg cs R Tt x W tests vals frameVals μ₀)
    (hwire : WireUnivTarget (lim := lim) (d := d) (P := P) (k := k) (I := I) (h := h)
      (active := active) (remaining := remaining) (rows := rows)
      (ab := ab) (rb := rb) (sb := sb) (mb := mb) (bb := bb) (fr := fr) (frC := frC)
      stage cacheProg restoreProg cs R Tt x W tests vals μ₀) :
    Ends lim (callerProgramUniv stage cacheProg restoreProg cs ++ R) d
      (mpBodyUniv stage) ⟨frame frameVals, μ₀⟩
      (univProB x.n + mpRounds W * univUnitB x.n)
      (fun σ' => UnivPins lim vals x W σ' ∧
        σ'.mem x.c = bracketAccumulate (μ₀ x.c) tests (mpRounds W) ∧
        (∃ mask' : ℕ → Bool,
          ThinMatrix.CallerChain.StageReads P I active mask' rows ab rb mb σ'.mem)) := by
  unfold mpBodyUniv
  unfold PrologueTarget at hpro
  unfold WireUnivTarget at hwire
  refine Ends.seq (univProB x.n) (mpRounds W * univUnitB x.n) ?_ (le_refl _)
  exact hpro.mono (le_refl _) (fun σ' hinv => hwire σ'.loc σ'.mem hinv)

#print axioms entryAssembly

/-! ## THE BUNDLE, THE TWIN, AND THE FILING

`entryAssembly` is the universal body's RUN. What it does not contain is the
instance's DATA: the oracle's return premise, the certified stage socket, the
rows table, the construction's identity and the `KeptBut` frame. Those are
D7's boundary — NAMED PREMISES, never claimed — and this section states them
ONCE, universally closed, at the prologue's stacked layout, and then fires the
twin from them.

THE LAYOUT IS THE PROLOGUE'S, read off `univPrologue`'s `.set` chain and not
assumed: `ab = fr`, `rb = fr + n`, `sb = fr + n + n²`, `bb = fr + 2n + n²`,
`mb = fr + 3n + n²`, and the STAGE's free pointer is the stack top
`mb + n = fr + 4n + n²` (the `Free := v Remaining +' v Nreg` set). Instantiating
the stage sockets at that stack top is what makes the pins' ninth slot and the
`Meets` call row the SAME number, which is why `univRound_runs`' discharge
closes by `rfl` and why no theorem in this module had to move in order to
compose the two green halves.

TWO FILLS ARE NAMED, NOT FAKED:

* FILL 1 — the rows buffer. The level-0 stage reads the rows table, and
  NOTHING in the prologue copies the instance's matrix into the buffer the
  stack puts at `rb`. The body needs a fill that `mpTask.Pre` does not
  provide, so the row table here IS the memory image at `rb`
  (`rows p i = μ (rb + p·n + i)` — exactly the premise `prologue_runs`
  consumes); its instance-value side is left to the identity premise below.
  Stated, not claimed.
* the identity — `MinPlusIdentity`'s content (the construction's own
  conversion; D7's boundary): the head's delivery is every entry.
-/

/-- The prologue's scores-base register value (`sb`). -/
def LRow (x : MatInst) (fr : ℕ) : ℕ := fr + x.n + x.n * x.n

/-- The prologue's base-base register value (`bb`). -/
def LBase (x : MatInst) (fr : ℕ) : ℕ := fr + 2 * x.n + x.n * x.n

/-- The prologue's remaining-base register value (`mb`). -/
def LRem (x : MatInst) (fr : ℕ) : ℕ := fr + 3 * x.n + x.n * x.n

/-- THE STAGE'S FREE POINTER: the stack top, `mb + n`. -/
def LTop (x : MatInst) (fr : ℕ) : ℕ := fr + 3 * x.n + x.n * x.n + x.n

/-- THE BUNDLE — D7's named premises, universally closed at the stacked layout.

For every instance, oracle data (`tests`, the stage clock `Tt`) exists and:

1. the certified stage socket (`UnivSlot`, byte-identical premises to the
   landed wire's `hslots`) at the prologue's layout, stage free pointer = the
   stack top;
2. the oracle's return premise (`hret`: the delivery is the bracket fold seeded
   at row `t`'s head);
3. the flag budget (`hflag`);
4. the stage's own resource socket (`hok`) at the stack top;
5. the stage clock inside the certified per-candidate clock (`hTtk`);
6. THE IDENTITY (D7's boundary) — the head's delivery is every entry;
7. the frame half (`KeptBut`) — the named remainder. -/
def UnivBundle (stage : ℕ) (cacheProg restoreProg : Light.Program) (cs : Inst)
    (need : ℕ → ℕ → Light.Need) : Prop :=
  ∀ (R : Light.Program) (lim : Limits) (d : ℕ) (x : MatInst) (μ : ℕ → ℤ) (fr : ℕ),
    x.Pre μ fr → (need x.n x.U).Ok lim fr d →
    ∃ (tests : ℕ → Bool × Bool) (Tt : ℕ → ℕ) (rows : ℕ → ℕ → ℕ),
      -- FILL 1: the rows table is the memory image at the rows buffer (the
      -- prologue copies nothing into it; `mpTask.Pre` does not provide this).
      (∀ p < x.n, ∀ i < x.n, ((rows p i : ℕ) : ℤ) = μ (fr + x.n + p * x.n + i)) ∧
      @UnivSlot lim d x.n 0 x.n x.U (fun _ => true) (rows)
          fr (fr + x.n) (LRow x fr) (LRem x fr) (LBase x fr) (LTop x fr)
          stage cacheProg restoreProg cs R Tt ∧
      (∀ (t' : ℕ) (mask' : ℕ → Bool) (μ' μ'' : ℕ → ℤ) (r' : ℤ),
        t' < mpRounds x.U →
        Light.DenseRestartSelectionLoop.Post
          (callSite (P := x.n) (R := 0) (I := x.n) (h := x.U) (active := fun _ => true)
            (remaining := mask') (rows := rows) (ab := fr) (rb := fr + x.n)
            (sb := LRow x fr) (mb := LRem x fr) (bb := LBase x fr)) μ' μ'' →
        r' = bracketAccumulate (μ' (x.c + t' * x.n)) tests (mpRounds x.U)) ∧
      (∀ mask' : ℕ → Bool, 0 ≤ (flagged x.n mask').card) ∧
      (∀ (mask' : ℕ → Bool) (kt : ℕ),
        (Light.DenseRestartSelectionLoop.need (instanceSize (callSite (P := x.n) (R := kt) (I := x.n) (h := x.U)
            (active := fun _ => true) (remaining := mask') (rows := rows)
            (ab := fr) (rb := fr + x.n) (sb := LRow x fr) (mb := LRem x fr)
            (bb := LBase x fr)))
          (callSite (P := x.n) (R := kt) (I := x.n) (h := x.U) (active := fun _ => true)
            (remaining := mask') (rows := rows) (ab := fr) (rb := fr + x.n)
            (sb := LRow x fr) (mb := LRem x fr) (bb := LBase x fr)).height).Ok lim
          (LTop x fr) (d + 1)) ∧
      Tt 0 ≤ callerTt x.n ∧
      (∀ (σ' : State), UnivPins lim (univProloguePins x fr) x x.U σ' →
        σ'.mem x.c = bracketAccumulate (μ x.c) tests (mpRounds x.U) →
        ∀ i j : ℕ, σ'.mem (bracketCell x i j) = minPlusEntry x.n x.A x.B i j) ∧
      (∀ (σ' : State), UnivPins lim (univProloguePins x fr) x x.U σ' →
        σ'.mem x.c = bracketAccumulate (μ x.c) tests (mpRounds x.U) →
        KeptBut μ σ'.mem fr x.c (x.n * x.n))

/-- THE NEED'S COVERAGE — the six numeric facts `Need.Ok` alone does not carry:
it bounds what the caller DEMANDS, not what the body's stack needs. -/
def NeedCovers (need : ℕ → ℕ → Light.Need) : Prop :=
  ∀ x : MatInst,
    4 * x.n + x.n * x.n ≤ (need x.n x.U).cells ∧
    2 * x.U + 1 ≤ (need x.n x.U).word ∧
    1 ≤ (need x.n x.U).word ∧
    1 ≤ (need x.n x.U).depth ∧
    mpRounds x.U ≤ (need x.n x.U).word ∧
    2 ^ signedLevels x.U ≤ (need x.n x.U).word

/-- THE RUN BRIDGE: the bundle is the universal body's `Solves mpTask`.

Nothing here is arithmetic beyond the layout's own ring identities: the
prologue is `prologue_runs` at the stacked layout, the while is
`wireUnivTarget_of` at the same layout with the stage's free pointer at the
stack top, the composition is `entryAssembly`, and the two Post halves are
bundle conjuncts (6) and (7) through the landed `seg_of_entries`.

THE PIN SEAM. `wireUnivTarget_of`'s `hvals` is `vals = argsOf callSite ++ [↑fr]`
with `fr` the stage's free pointer, and the prologue produces
`univProloguePins x fr`, whose ninth slot is the stack top. `hvals` is
therefore `univProloguePins_eq_argsOf` read right-to-left — the brick restored
and corrected this session for exactly this consumer. -/
theorem univSolves (stage : ℕ) (cacheProg restoreProg : Light.Program) (cs : Inst)
    (need : ℕ → ℕ → Light.Need) (cacheTime : ℕ → ℕ → ℕ)
    (hb : UnivBundle stage cacheProg restoreProg cs need)
    (hcov : NeedCovers need) :
    Light.Solves Light.mpTask (callerProgramUniv stage cacheProg restoreProg cs) 0
      (univTn cacheTime) need := by
  refine ⟨mpBodyUniv stage, callerProgramUniv_entry stage cacheProg restoreProg cs, ?_⟩
  intro R lim d x μ fr hpre hok
  obtain ⟨tests, Tt, rows, hfill, hslot, hret, hflag, hokS, hTt, hident, hkept⟩ :=
    hb R lim d x μ fr hpre hok
  -- `mpTask.size`/`mpTask.bound` ARE `x.n`/`x.U`; normalise so the arithmetic
  -- below works over one term per quantity rather than two defeq atoms.
  have hok' : (need x.n x.U).Ok lim fr d := hok
  obtain ⟨hcells, hwU2, hw1, hdep, hwRt, hwLvl⟩ := hcov x
  have hfit : fr + 4 * x.n + x.n * x.n ≤ lim.space := by
    rw [Nat.add_assoc]
    exact le_trans (Nat.add_le_add_left hcells fr) hok'.cells
  have hwordU2 : |2 * (x.U : ℤ) + 1| ≤ lim.word := by
    have h1 : ((2 * x.U + 1 : ℕ) : ℤ) ≤ ((need x.n x.U).word : ℤ) := by
      exact_mod_cast hwU2
    rw [abs_of_nonneg (by positivity)]
    linarith [hok'.word]
  have hwordU2p : |2 * (x.U : ℤ)| ≤ lim.word := by
    have h2 : (2 * (x.U : ℤ)) ≤ |2 * (x.U : ℤ) + 1| := by
      have := le_abs_self (2 * (x.U : ℤ) + 1); linarith
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hword1 : (1 : ℤ) ≤ lim.word := by
    have h1 : ((1 : ℕ) : ℤ) ≤ ((need x.n x.U).word : ℤ) := by exact_mod_cast hw1
    linarith [hok'.word]
  have hdim : d < lim.depth := by have := hok'.depth; omega
  -- the product region sits strictly below the buffer stack: `Pre`'s own fact,
  -- hoisted so the linear arithmetic below sees it (it is a projection, and
  -- projections are invisible to `omega`).
  have hbC : x.c + x.n * x.n ≤ fr := hpre.belowC
  have hn1 : 1 ≤ x.n := hpre.n_pos
  have hpro : PrologueTarget (lim := lim) (d := d) (P := x.n) (k := 0) (I := x.n)
      (h := x.U) (active := fun _ => true) (rows := rows)
      (ab := fr) (rb := fr + x.n) (sb := LRow x fr) (mb := LRem x fr)
      (bb := LBase x fr) (fr := LTop x fr) (frC := fr)
      stage cacheProg restoreProg cs R Tt x x.U tests (univProloguePins x fr)
      (([(x.n : ℤ), (x.U : ℤ), (x.a : ℤ), (x.b : ℤ), (x.c : ℤ)] : List ℤ) ++ [(fr : ℤ)]) μ :=
    prologue_runs (lim := lim) (d := d) (P := x.n) (k := 0) (I := x.n) (h := x.U)
      (active := fun _ => true) (rows := rows) (ab := fr) (rb := fr + x.n)
      (sb := LRow x fr) (mb := LRem x fr) (bb := LBase x fr) (fr := fr) (frC := fr)
      stage cacheProg restoreProg cs R Tt x x.U tests (univProloguePins x fr)
      (([(x.n : ℤ), (x.U : ℤ), (x.a : ℤ), (x.b : ℤ), (x.c : ℤ)] : List ℤ) ++ [(fr : ℤ)]) μ
      (hxn := hpre.n_pos) (hframe := rfl) (hvals := rfl) (hI := rfl) (hP := rfl)
      (hab := rfl) (hrb := rfl) (hsb := rfl) (hbb := rfl) (hmb := rfl)
      (hfrC := le_refl fr) (hbelow := hbC) (hfit := hfit) (hspace := hok'.space)
      (hwordU2 := hwordU2p) (hword1 := hword1) (hactive := fun i hi => rfl)
      (hrows := hfill)
  have hseam : univProloguePins x fr =
      argsOf (callSite (P := x.n) (R := 0) (I := x.n) (h := x.U) (active := fun _ => true)
        (remaining := fun _ => true) (rows := rows) (ab := fr) (rb := fr + x.n)
        (sb := LRow x fr) (mb := LRem x fr) (bb := LBase x fr))
        ++ [((LTop x fr : ℕ) : ℤ)] :=
    (univProloguePins_eq_argsOf x (hP := rfl) (hI := rfl) (hU := rfl) (hab := rfl)
      (hrb := rfl) (hsb := rfl) (hbb := rfl) (hmb := rfl)).symm
  have hwire : WireUnivTarget (lim := lim) (d := d) (P := x.n) (k := 0) (I := x.n)
      (h := x.U) (active := fun _ => true) (remaining := fun _ => true)
      (rows := rows) (ab := fr) (rb := fr + x.n) (sb := LRow x fr)
      (mb := LRem x fr) (bb := LBase x fr) (fr := LTop x fr) (frC := fr)
      stage cacheProg restoreProg cs R Tt x x.U tests (univProloguePins x fr) μ :=
    wireUnivTarget_of (lim := lim) (d := d) (P := x.n) (k := 0) (I := x.n) (h := x.U)
      (active := fun _ => true) (remaining := fun _ => true) (rows := rows)
      (ab := fr) (rb := fr + x.n) (sb := LRow x fr) (mb := LRem x fr) (bb := LBase x fr)
      (fr := LTop x fr) (frC := fr)
      stage cacheProg restoreProg cs R Tt x x.U tests (univProloguePins x fr) μ
      (hxn := hpre.n_pos) (hvals := hseam) (hslot := hslot) (hret := hret)
      (hflag := hflag) (hok := hokS)
      (hlay := by simp only [InOrder, LRow, LBase, LRem, LTop]; omega)
      (hfrCle := le_refl fr)
      (haway := by
        refine ⟨Or.inl (by simp only [LRow]; omega), Or.inl (by simp only [LBase]; omega),
          Or.inl (by simp only [LRem]; omega)⟩)
      (hbelow := hbC) (hspace := hok'.space) (hdim := hdim) (hTtk := hTt)
      (hwordRt := by
        have h1 : ((mpRounds x.U : ℕ) : ℤ) ≤ ((need x.n x.U).word : ℤ) := by
          exact_mod_cast hwRt
        linarith [hok'.word])
      (hwordLvl := by
        have h1 : ((2 ^ signedLevels x.U : ℕ) : ℤ) ≤ ((need x.n x.U).word : ℤ) := by
          exact_mod_cast hwLvl
        linarith [hok'.word])
      (hwordU2 := hwordU2) (hword1 := hword1) (hWU := rfl) (hWpos := hpre.U_pos)
  refine (entryAssembly (lim := lim) (d := d) (P := x.n) (k := 0) (I := x.n) (h := x.U)
    (active := fun _ => true) (remaining := fun _ => true) (rows := rows)
    (ab := fr) (rb := fr + x.n) (sb := LRow x fr) (mb := LRem x fr) (bb := LBase x fr)
    (fr := LTop x fr) (frC := fr)
    stage cacheProg restoreProg cs R Tt x x.U tests (univProloguePins x fr)
    (([(x.n : ℤ), (x.U : ℤ), (x.a : ℤ), (x.b : ℤ), (x.c : ℤ)] : List ℤ) ++ [(fr : ℤ)]) μ
    (hpro := hpro) (hwire := hwire)).mono (by unfold univTn; exact Nat.le_add_left _ _) ?_
  intro σ' hσ'
  obtain ⟨hpins, hhead, _⟩ := hσ'
  exact ⟨seg_of_entries (hident σ' hpins hhead), hkept σ' hpins hhead⟩

#print axioms univSolves

/-- THE TWIN, FIRED FROM THE BUNDLE: the universal body's `Solves mpTask` plus
the need and domination sockets IS the conservative `Race.bound` form —
`EndStatement.APSP.SolvedInTime (2994999/1000000)`. This is the universal
body's `twin_of_CallerTarget`: when the bundle's premises are supplied, the
filing theorem is THIS one, with no further composition. -/
theorem twinUniv_of (stage : ℕ) (cacheProg restoreProg : Light.Program) (cs : Inst)
    (need : ℕ → ℕ → Light.Need) (cacheTime : ℕ → ℕ → ℕ)
    (hb : UnivBundle stage cacheProg restoreProg cs need)
    (hcov : NeedCovers need)
    (hn : Light.PolyNeed need)
    (hdom : ∀ κ : Nat, ∃ (k : Nat) (C : Real), ∀ᶠ n : Nat in atTop,
      Light.timeUpTo (Light.Sec3.apTime (univTn cacheTime)) n
        ((n : Real) ^ (κ : Real)) ≤
        C * AsymptoticCosts.completeCost k n) :
    EndStatement.APSP.SolvedInTime ((2994999 : Rat) / 1000000) :=
  ThinMatrix.Twin.race_bound (P := callerProgramUniv stage cacheProg restoreProg cs)
    (p := 0) (Tn := univTn cacheTime) (need := need)
    (univSolves stage cacheProg restoreProg cs need cacheTime hb hcov) hn hdom

#print axioms twinUniv_of

/-! ## Restored bricks

Two of the four bricks a previous session of this lane authored and lost
(the de-duplication incident — see the lane's REPRODUCE.md) survive the
cure-(b) rewrite unchanged, because they say nothing about the write shape:
`mpRounds_le_word` (the round counter fits a word) and
`UnivInvAll_zero_self` (at level zero the product's head still holds the
instance's own value). Two do not, and are named here rather than faked:

* `pow_signedLevels_le` — SURVIVES UNDER ITS LANDED NAME:
  `pow_pred_signed_levels_le` (the loop's exit, `2^(signedLevels W - 1) ≤
  2W`), together with `two_mul_lt_pow_signed_levels`. Both are already
  stated, proved and consumed by `wireUnivTarget_of`; re-introducing the
  old name would be an alias, not a brick.
* `univProloguePins_eq_argsOf` — RESTORED, CORRECTED, AND USED (2026-11-10).
  The lost form identified the prologue's nine pins with
  `argsOf (callSite …) ++ [fr]`; that is FALSE at slot 8. `argsOf`'s eight
  slots are candidates/length/height/activeBase/rowsBase/scoresBase/
  remainingBase/baseBase, and the NINTH frame value is the STAGE's free
  pointer, which the prologue computes as `Free := Remaining + Nreg =
  fr + 4n + n² = mb + n` — not the caller's `fr`, which is slot 3's base.
  The restored brick states the seam at `++ [(mb + P : ℕ)]` (equal to
  `mb + n` under `hP : P = x.n`) and carries `h = x.U` for slot 2.

  RESOLVED, AND THE DIAGNOSIS CORRECTED (2026-11-10, second session). The
  suggested cure — move `hvals` to `++ [(mb + x.n : ℕ)]` and close the
  discharge with `push_cast; ring` — was IMPLEMENTED AND MEASURED, and it
  CANNOT WORK. The obstruction at `univRound_runs`' discharge is not a term
  SHAPE but a VALUE IDENTITY: the goal there is
  `[…, ↑(mb + x.n)] = argsOf (callSite …) ++ [↑fr]`, whose right-hand side
  is the `Meets` call ROW fixed by `UnivSlot` (`argsOf … ++ [(fr : ℤ)]`).
  A `ring`/`push_cast` step cannot derive `mb + x.n = fr` because that is not
  true of the theorem's variables — it is a property of the LAYOUT, chosen by
  the caller. The two names for one number are reconciled at the CALLER:
  instantiate the stage's free pointer at the stack top, `fr := mb + x.n`
  (`= fr + 4n + n²`, the prologue's `Free := v Remaining +' v Nreg`), and then
  `hvals` is `argsOf … ++ [↑fr]` again by `univProloguePins_eq_argsOf` read
  right-to-left. `univSolves` below does exactly this and is GREEN with the
  standard axioms, with `univRound_runs`, `univLevel_runs` and
  `wireUnivTarget_of` UNMOVED from their landed form. The seam is therefore
  carried by the caller, not by the statement — recorded as MEASURED, with the
  compiler log as the witness. -/

/-- Brick: the round counter fits a word, so every round index is a legal
word-RAM value. Restored from the lost set (it is write-shape independent). -/
theorem mpRounds_le_word {lim : Limits} (W : ℕ)
    (h : ((mpRounds W : ℕ) : ℤ) ≤ lim.word) :
    ∀ t : ℕ, t < mpRounds W → |(t : ℤ)| ≤ lim.word := by
  intro t ht
  have h1 : (t : ℤ) ≤ ((mpRounds W : ℕ) : ℤ) := by exact_mod_cast Nat.le_of_lt ht
  have h2 : (0 : ℤ) ≤ (t : ℤ) := by positivity
  rw [abs_of_nonneg h2]
  omega

/-- Brick: at level zero the product's head still holds the instance's own
value — the prologue has written only the bookkeeping arrays, never the
product. Restored from the lost set (it is write-shape independent). -/
theorem UnivInvAll_zero_self {lim : Limits} {vals : List ℤ} {x : MatInst} {W : ℕ}
    {P I : ℕ} {active : ℕ → Bool} {rows : ℕ → ℕ → ℕ} {ab rb mb : ℕ}
    {μ₀ : ℕ → ℤ} {tests : ℕ → Bool × Bool} {frC : ℕ} {σ : State}
    (h : UnivInvAll lim vals x W P I active rows ab rb mb μ₀ tests frC 0 σ) :
    σ.mem x.c = μ₀ x.c := by
  have hc := h.1.2.2.2.2
  rw [if_pos rfl] at hc
  exact hc

#print axioms univProloguePins_eq_argsOf

#print axioms mpRounds_le_word

#print axioms UnivInvAll_zero_self

end ThinMatrix.CallerUniversalBody
