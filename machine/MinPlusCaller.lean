import MinPlusReduction
import MachineAdapter
import DenseMinPlusPost

/-!
Copyright (c) 2026. APSP port campaign: D7(b) the min-plus caller skeleton.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain (`MinPlusReduction`: bit scaling, signed levels, the
  scheduled adaptive equality queries, sentinel encoding;
  thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  EndStatement.APSP target and `Realized` machinery are the pinned Anthropic
  statement's.
- Joshua Wharton (QFEX) — the canonical adapter arrangement and the checked
  selection round / restart-loop driver the scheduled rounds instantiate.
- Hrishik Sai Bojnal — the verified frontier being refined.

# D7(b): the min-plus caller program skeleton

`hs : Light.Solves Light.mpTask P p Tn need` — the hypothesis the canonical
adapters (D7(a)) consume — decomposes into the caller's call schedule and
per-slot contracts. This module pins what exists and names what trails:

- the schedule: `mpRounds W = 2·((2W).log2 + 1)` scheduled oracle calls
  (`mpRounds_eq`, bridged to upstream `scheduledCalls (signedLevels W)`);
- the stage slot, INHABITED at every round and any pinning: `stageSlot_any`
  certifies each scheduled stage call from the L5/L6(c) wrapper;
- the hdom-side bricks: the driver's pinned clock is size-monotone
  (`taskTime_le_of_size`) and the instance size is the pinning's polynomial
  (`instanceSize_le`) — the per-round step bound of the future `hdom`;
- the exact `hs` shape: `hsShape`.

THE NAMED FILLS (the machine port's remainder; none proved here, none
claimed):
- FILL 1 — the L2/L3 cache program: a `Light.Solves` contract for the
  polynomial query cache behind the oracle table's rows (score-table pass +
  BinaryArrayFFT cyclic path; upstream content contract `OracleCorrect`).
- FILL 2 — the finish/restore pass (upstream `restore_correct`).
- FILL 3 — the caller composition: chaining the `mpRounds W` certified stage
  calls over one fixed program into the single `hsShape` contract.

D7's boundary stands: the (min,+) product itself is never claimed; the
functional chain `bounded_signed_eq_minPlus` is upstream's, conditioned on
`OracleCorrect` — the cache-slot's content contract.
-/

namespace ThinMatrix.MinPlusCaller

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.WordRam
  ThinMatrix.MinPlusReduction
  Light.DenseRestartSelectionLoop Light.DenseCompositeCaller
  Light.DenseCompositeLedger Light.DenseMinPlusPost Light

/-! ## The schedule -/

/-- The caller's oracle-call schedule at word bound `W`: upstream
`scheduledCalls (signedLevels W)` — both adaptive equality tests at every
signed level. -/
def mpRounds (W : ℕ) : ℕ := scheduledCalls (signedLevels W)

/-- The schedule's closed form, bridged to the upstream functional chain. -/
theorem mpRounds_eq (W : ℕ) : mpRounds W = 2 * ((2 * W).log2 + 1) := by
  simp [mpRounds, signedLevels, scheduledCalls_eq]

/-! ## The stage slot — inhabited at every round and any pinning -/

/-- The stage slot, at any round's pinning: the restart-loop driver meets the
pinned composite-incidence certification within the pinned clock, in every
appended program. Byte-identical premises to `callSite_meets` — the stage
slot is the L5/L6(c) wrapper consumed at the caller's `(P, k)` pinning, so
every scheduled round's stage call is certified. -/
theorem stageSlot_any (P k I h : ℕ) (active remaining : ℕ → Bool)
    (rows : ℕ → ℕ → ℕ) (ab rb sb mb bb fr : ℕ) (lim : Limits) (d : ℕ)
    (μ : ℕ → ℤ) (Prog : Program)
    (hAR : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hRR : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hbound : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hfl : ∀ p < P, μ (mb + p) = DenseArgminPass.bit (remaining p))
    (hR : k ≤ (flagged P remaining).card)
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)])
    (hok : (need (instanceSize (callSite P k I h active remaining rows ab rb sb mb bb))
      (callSite P k I h active remaining rows ab rb sb mb bb).height).Ok lim fr d) :
    Meets lim (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ Prog) 6 d
      (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]) μ
      (taskTime (instanceSize (callSite P k I h active remaining rows ab rb sb mb bb))
        (callSite P k I h active remaining rows ab rb sb mb bb).height)
      (pinnedPost (callSite P k I h active remaining rows ab rb sb mb bb) μ fr) :=
  callSite_meets hAR hRR hbound hfl hR hlay hok

/-! ## The hdom-side bricks -/

/-- The driver's pinned clock is size-monotone: within an instance-size
bound `a`, the round costs at most `100·a² + 98·a` steps (the height bound
does not enter the pinned clock). -/
theorem taskTime_le_of_size (m u a : ℕ) (hm : m ≤ a) :
    taskTime m u ≤ 100 * a * a + 98 * a := by
  unfold taskTime
  have hsq : m * m ≤ a * a := Nat.mul_le_mul hm hm
  have h1 : 100 * m * m ≤ 100 * a * a := by
    calc 100 * m * m = 100 * (m * m) := by ring
      _ ≤ 100 * (a * a) := Nat.mul_le_mul_left 100 hsq
      _ = 100 * a * a := by ring
  nlinarith

/-- The pinned call site's instance size is the pinning's polynomial:
`P·I + 2P + 2I` under per-parameter bounds. -/
theorem instanceSize_le (P k I h aP aI : ℕ)
    (hP : P ≤ aP) (hI : I ≤ aI)
    (active remaining : ℕ → Bool) (rows : ℕ → ℕ → ℕ)
    (ab rb sb mb bb : ℕ) :
    instanceSize (callSite P k I h active remaining rows ab rb sb mb bb)
      ≤ aP * aI + 2 * aP + 2 * aI := by
  unfold instanceSize
  have h1 : P * I ≤ aP * aI := Nat.mul_le_mul hP hI
  have h2 : 2 * P ≤ 2 * aP := Nat.mul_le_mul_left 2 hP
  have h3 : 2 * I ≤ 2 * aI := Nat.mul_le_mul_left 2 hI
  simp only [callSite] at *
  omega

/-! ## The exact hs shape the fills close -/

/-- The `hs` hypothesis's exact shape, at the caller's schedule: what the
canonical adapters (D7(a)) consume once the fills close. -/
def hsShape (P : Light.Program) (p : ℕ) (Tn : ℕ → ℕ → ℕ)
    (need : ℕ → ℕ → Light.Need) : Prop :=
  Light.Solves Light.mpTask P p Tn need

#print axioms mpRounds
#print axioms mpRounds_eq
#print axioms stageSlot_any
#print axioms taskTime_le_of_size
#print axioms instanceSize_le
#print axioms hsShape

end ThinMatrix.MinPlusCaller
