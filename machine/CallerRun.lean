import MinPlusCaller
import CallerWrites
import CallerEncoding
import CallerRounds
import CallerCount
import CallerSegments

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the summit body,
the run-derivation session: the body's write-inclusion, the wire-target,
the construction's identity-premise, and the Seg-assembly target.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  Light language is the pinned Anthropic statement's.
- Joshua Wharton (QFEX) — the canonical adapter arrangement, the refinement
  parameters, and the machine-obligations record.
- Hrishik Sai Bojnal — the verified frontier being refined and the refined
  numerical certificate this body targets.

# The run-derivation session: the body's write-inclusion and the Seg
assembly's decomposition

The Seg-half run-derivation's decomposition (each piece landed or named):

1. `roundSlice` / `mpBodyWithWrites` — THE BODY'S WRITE-INCLUSION: the
   mpRounds schedule of (stage-call + bracket-writes) pairs — the
   body's write-inclusion (the skeleton's refinement: the schedule +
   the per-round bracket-cell writes composed). The write shapes are
   landed (`CallerWrites.mpBodyWritesEntry`/`mpBodyWritesRow`).
2. `BracketFinal` — THE WIRE-TARGET: the body's run's bracket cells'
   final state = `bracketAccumulate`'s fold — the wire-lemma's
   statement (the next session's core: the chain's induction + the
   readings + the cell-updates).
3. `MinPlusIdentity` — THE CONSTRUCTION'S OWN IDENTITY-PREMISE: the
   bracket cells' final state = the min-plus entries — the
   construction's own conversion's content, conditioned on the oracle
   premise (D7's boundary — the premise, never claimed).
4. `SegOfBody` — THE SEG-ASSEMBLY'S TARGET: the body's run's Seg half
   (the `minPlusList` at the product region + the `KeptBut` frame).
   The assembly: the wire-target + the identity-premise + the landed
   `keptBut_of_chain` compose.

THE REMAINING SESSIONS: the wire-lemma's proof (the body's
write-inclusion's run-derivation — the chain's induction + the readings
+ the cell-updates); then the Seg-assembly (the wire + the identity +
the keptBut) discharging `SegOfBody` → `CallerTarget(Layered)`; then
the step count for `CallerHdom`. Until they land, `CallerTarget(Layered)`
and the twin stay conditional — honestly: no solver is postulated, no
(min,+) product is claimed. D7's boundary stands: the construction's
identity is a premise, never claimed as proved.
-/

namespace ThinMatrix.CallerRun

open ThreeSumApsp ThreeSumApsp.Spec ThinMatrix.CallerSegments
  Light.DenseRestartSelectionLoop Light
  ThinMatrix.MinPlusCaller
  ThinMatrix.CallerWrites ThinMatrix.CallerEncoding ThinMatrix.CallerRounds
  ThinMatrix.CallerCount

/-! ## The body's write-inclusion -/

/-- The per-round body-slice: the stage call followed by the bracket
cells' writes (the per-round cell-updates at the product region). The
stage at the caller's shifted index; the call's result lands in `Tmp`
and the row's stores read the value-base `Tmp` (the delivery register —
a Light call updates only `Tmp`); the address-base is `Out` (the
product base, pinned by the wire's pinning). -/
def roundSlice (stage Out : ℕ) (x : MatInst) (t : ℕ) : Light.Stmt :=
  Light.Stmt.call stage callArgs Tmp ;;
    mpBodyWritesRow Out Tmp x t

/-- THE CALLER'S BODY WITH WRITES: the mpRounds schedule of
(stage-call + bracket-writes) pairs — the body's write-inclusion (the
skeleton's refinement: the schedule + the per-round bracket-cell writes
composed). -/
def mpBodyWithWrites (stage Out : ℕ) (x : MatInst) (W : ℕ) : Light.Stmt :=
  (List.range (mpRounds W)).foldl
    (fun s t => Light.Stmt.seq s (roundSlice stage Out x t)) Light.Stmt.skip

/-! ## The wire-target and the identity-premise -/

/-- THE WIRE-TARGET: the body's run's bracket cells' final state = the
`bracketAccumulate`'s fold — the wire-lemma's statement (the next
session's core: the chain's induction + the readings + the
cell-updates). -/
def BracketFinal
    {lim : Limits} {d : ℕ} {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr : ℕ} {B T : ℕ} {Tt : ℕ → ℕ}
    {μ₀ : ℕ → ℤ} {R : Light.Program} {x : MatInst} {Out : ℕ}
    (W : ℕ) (tests : ℕ → Bool × Bool) :
    Prop :=
  ∀ (σ'' : State), Ends lim (program (callSite P k I h active remaining rows
      ab rb sb mb bb) ++ R) d (mpBodyWithWrites 6 Out x W) σ'' T
    (fun σ' => bracketAccumulate 0 tests (mpRounds W) = σ'.mem (bracketCell x 0 0))

/-- THE CONSTRUCTION'S OWN IDENTITY-PREMISE: the bracket cells' final
state = the min-plus entries — the construction's own conversion's
content, conditioned on the oracle premise (D7's boundary — the
premise, never claimed). -/
def MinPlusIdentity
    {lim : Limits} {d : ℕ} {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr : ℕ} {B T : ℕ} {Tt : ℕ → ℕ}
    {μ₀ : ℕ → ℤ} {R : Light.Program} {x : MatInst} {Out : ℕ}
    (W : ℕ) (tests : ℕ → Bool × Bool) :
    Prop :=
  ∀ (σ'' : State), Ends lim (program (callSite P k I h active remaining rows
      ab rb sb mb bb) ++ R) d (mpBodyWithWrites 6 Out x W) σ'' T
    (fun σ' => bracketAccumulate 0 tests (mpRounds W) = σ'.mem (bracketCell x 0 0)) →
    ∀ i j, σ''.mem (bracketCell x i j) =
      minPlusEntry x.n x.A x.B i j

/-! ## The Seg-assembly's target -/

/-- THE SEG-ASSEMBLY'S TARGET: the body's run's Seg half (the
`minPlusList` at the product region + the `KeptBut` frame) — the
assembly: the wire-target + the identity-premise + the landed
`keptBut_of_chain` compose. -/
def SegOfBody
    {lim : Limits} {d : ℕ} {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr : ℕ} {B T : ℕ} {Tt : ℕ → ℕ}
    {μ₀ : ℕ → ℤ} {R : Light.Program} {x : MatInst} {Out : ℕ}
    (W : ℕ) (tests : ℕ → Bool × Bool) :
    Prop :=
  ∀ (σ'' : State), Ends lim (program (callSite P k I h active remaining rows
      ab rb sb mb bb) ++ R) d (mpBodyWithWrites 6 Out x W) σ'' T
    (fun σ' => Seg σ'.mem x.c (minPlusList x.n x.A x.B) ∧
      KeptBut μ₀ σ'.mem fr x.c (x.n * x.n))

/-- THE SEG-BRIDGE: the construction's identity at a state delivers the
Seg half at that state. The region-index arithmetic: the bracket cells'
row-major layout (`bracketCell x i j = x.c + i * x.n + j`) meets
`minPlusList`'s row-major order (`q ↦ (q / n, q % n)`) — proved outright,
no premise beyond the entries themselves. The frame-start instance is
`CallerSegments.segTarget_of` (the bridge is inlined there — this module
sits above `CallerSegments`; the cycle would be downward). -/
theorem seg_of_entries {x : MatInst} {σ : State}
    (h : ∀ i j : ℕ, σ.mem (bracketCell x i j) = minPlusEntry x.n x.A x.B i j) :
    Seg σ.mem x.c (minPlusList x.n x.A x.B) := by
  intro i hi
  rw [length_minPlusList] at hi
  have hget : (minPlusList x.n x.A x.B)[i]
      = minPlusEntry x.n x.A x.B (i / x.n) (i % x.n) := by
    simp only [minPlusList, List.getElem_map, List.getElem_range]
  rw [hget, ← h (i / x.n) (i % x.n)]
  show σ.mem (x.c + i) = σ.mem (x.c + (i / x.n) * x.n + i % x.n)
  have hdm : (i / x.n) * x.n + i % x.n = i := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod i x.n
  rw [Nat.add_assoc, hdm]

/-- THE BODY-LEVEL ASSEMBLY: `SegOfBody` = the named identity-premise
(`MinPlusIdentity` — the 0-seeded wire-target's conversion; D7's
boundary: a premise, never claimed) fed by the 0-seeded wire-run
(`hbus` — the identity's own internal premise shape) + the KeptBut half.
The KeptBut half stays a premise because `SegOfBody` quantifies over
arbitrary start states while `KeptBut μ₀ σ'.mem …` compares against the
frame's initial memory — the discharge is frame-relational and rides the
caller's data-flow design (the named remainder); the frame-start
instance is `CallerSegments.segTarget_of`. -/
theorem segOfBody_of
    {lim : Limits} {d : ℕ} {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr : ℕ} {Bw B T : ℕ} {Tt : ℕ → ℕ}
    {μ₀ : ℕ → ℤ} {R : Light.Program} {x : MatInst} {Out : ℕ}
    (W : ℕ) (tests : ℕ → Bool × Bool)
    (hident : @MinPlusIdentity lim d P k I h active remaining rows ab rb sb mb bb
      fr B T Tt μ₀ R x Out W tests)
    (hbus : ∀ σ'' : State,
      Ends lim (program (callSite P k I h active remaining rows
        ab rb sb mb bb) ++ R) d (mpBodyWithWrites 6 Out x W) σ'' T
      (fun σ' => bracketAccumulate 0 tests (mpRounds W) = σ'.mem (bracketCell x 0 0)))
    (hkept : ∀ σ'' : State,
      Ends lim (program (callSite P k I h active remaining rows
        ab rb sb mb bb) ++ R) d (mpBodyWithWrites 6 Out x W) σ'' T
      (fun σ' => KeptBut μ₀ σ'.mem fr x.c (x.n * x.n))) :
    SegOfBody (lim := lim) (d := d) (P := P) (k := k) (I := I) (h := h)
      (active := active) (remaining := remaining) (rows := rows) (ab := ab)
      (rb := rb) (sb := sb) (mb := mb) (bb := bb) (fr := fr) (B := B) (T := T)
      (Tt := Tt) (μ₀ := μ₀) (R := R) (x := x) (Out := Out) W tests := by
  unfold SegOfBody
  intro σ''
  obtain ⟨σ', c, he, hc, hkb⟩ := hkept σ''
  exact ⟨σ', c, he, hc, ⟨seg_of_entries (hident σ' (hbus σ')), hkb⟩⟩

#print axioms roundSlice
#print axioms mpBodyWithWrites
#print axioms seg_of_entries
#print axioms segOfBody_of

end ThinMatrix.CallerRun
