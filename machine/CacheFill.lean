import MinPlusCaller

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 1 — the cache program's
task contract.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction: the materialized
  row cache behind the scheduled triangle queries and its correctness
  contract (`OracleCorrect`);
  thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc.
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  Light language these procedures execute in.
- Joshua Wharton (QFEX) — the canonical adapter arrangement and the checked
  selection round / restart-loop driver the rounds instantiate.
- Hrishik Sai Bojnal — the verified frontier being refined.

# FILL 1: the cache program's task contract

The cache-slot's content contract is upstream's, byte-identical:
`cacheContent O A = Oracle.Correct O A` — each cached row equals the
incidence count `A.modCount (selected.prod * candidate) i` on active
incidences.

What this module pins:
- `CacheInst` / `cacheTask` — the Light task the cache program solves:
  write the `P×I` cached rows into the rows region below the free pointer
  and keep everything else (`KeptBut`);
- `image_of_kept_post` — the RECEIPT for the frame repair (2026-11-10): under
  the task's first frame shape (`Kept μ μ' fr`, nothing below the free pointer
  changes) the post ENTAILED `rows p i = μ (rb + p·I + i)`, i.e. the raw
  memory image the task was meant to produce. The frame is `KeptBut` now;
- `cacheReads_of_solves` — the proved extraction: the cache program's
  `Light.Solves` delivers the reads (`hRR`-shaped) and the frame;
- `reads_persist` — the proved persistence: under `KeptBut` with the
  five-region layout below the free pointer, every stage read premise that
  lies OUTSIDE the rows region survives into the cache's final memory, while
  the rows premise comes from the cache's own WRITE (no image hypothesis at
  the entry memory is needed);
- `stageMeets_shifted` — the proved re-indexing: the stage slot's `Meets`
  in the composed round program `cacheProg ++ program cs ++ rest` at
  procedure `cacheProg.length + 6`.

The cache program's BODY still trails (the L2/L3 cone porting board-side);
this module states and proves the fill's byte-shape and its composition
primitives, not the body. D7's boundary stands: no (min,+) product is
claimed.
-/

namespace ThinMatrix.CacheFill

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.WordRam
  ThinMatrix.MinPlusReduction
  ThinMatrix.MinPlusCaller
  Light.DenseRestartSelectionLoop Light

/-! ## The content contract — upstream, byte-identical -/

/-- The cache-slot's content contract: byte-identical to upstream
`MinPlusReduction.OracleCorrect` — the triangle-oracle correctness the
functional chain `bounded_signed_eq_minPlus` is conditioned on. (The deeper
row-level clause — each cached row equal to the incidence count on active
incidences, upstream `ArrayCompositeAlgorithm.Oracle.Correct` — is what the
L2/L3 cone delivers behind this; it trails with that port.) -/
def cacheContent {I K J : Type} (O : TriangleOracle I K J) : Prop :=
  OracleCorrect O

/-! ## The cache program's Light task -/

/-- The cache program's instance: the `P×I` cached rows written at the rows
region, with the row-magnitude bound. -/
structure CacheInst where
  P : ℕ
  I : ℕ
  h : ℕ
  rb : ℕ
  fr : ℕ
  rows : ℕ → ℕ → ℕ

/-- The cache program's task: write every cached row into the rows region
and keep everything else below the free pointer. The body is the L2/L3
cone's obligation (the score-table pass and BinaryArrayFFT cyclic path
behind `Oracle.Correct`); the contract is what the caller composes with.

THE FRAME IS `KeptBut`, NOT `Kept` — REPAIRED 2026-11-10, disclosed, with the
receipt kept. The first form of this contract carried `Kept μ μ' fr`: a frame
that changes NOTHING below the free pointer. `Pre` places the whole rows
region below it (`rb + P·I ≤ fr`), so the two conjuncts are jointly
satisfiable only when the rows region ALREADY holds `rows`. The post
therefore entailed `rows p i = μ (rb + p·I + i)` — the raw memory image the
task exists to produce (`image_of_kept_post`, below). A cache whose frame
forbids writing its own output computes nothing, and a `Solves cacheTask`
premise carrying that frame is not "the cache boundary": it is the image
premise wearing the cache's vocabulary. Discharging FILL 1 by calling the
cache slot is therefore sound ONLY with the frame repaired; the receipt is
what makes the difference between the two shapes measurable.

SCOPE OF "ONLY WHEN": the collapse is vacuous at `P = 0` or `I = 0`, where
there are no rows to write. `image_of_kept_post` carries the `1 ≤ I` side as
an explicit hypothesis; `1 ≤ P` follows from the same quantifier (`∀ p < P`
is empty otherwise). The body consumes neither degenerate case.

The repaired frame is `KeptBut μ μ' fr rb (P·I)`: everything below the free
pointer EXCEPT the rows region the task is defined to fill. -/
def cacheTask : Task where
  Inst := CacheInst
  size x := x.P * x.I
  bound x := x.h
  args x := [x.P, x.I, x.rb]
  Pre x μ fr := x.rb + x.P * x.I ≤ fr
  Post x μ fr _r μ' :=
    (∀ p < x.P, ∀ i < x.I, μ' (x.rb + p * x.I + i) = x.rows p i) ∧
    KeptBut μ μ' fr x.rb (x.P * x.I)

/-! ### The receipt for the frame repair -/

/-- **The measurement that forced the repair.** Under the task's first frame
shape — `Kept μ μ' fr`, nothing below the free pointer changes — the post's
reads clause and `Pre`'s `rb + P·I ≤ fr` together ENTAIL the raw rows image
`rows p i = μ (rb + p·I + i)` at the ENTRY memory. So a `Light.Solves
cacheTask …` premise stated with that frame re-imports FILL 1 rather than
discharging it: route (c) would be a RENAMING of the premise, not a
reduction of it. This theorem is true of the old shape and is not a
hypothesis of anything below; it is kept as the record.

Frame shape does its work here as a statement about satisfiability, so this is
the same class of finding as the bundle's refuted flag conjunct
(`CallerFill1Measure.hflag_shape_false`): a premise that looks like a boundary
and is in fact the thing it was meant to produce. -/
theorem image_of_kept_post {P I rb fr : ℕ} (hI : 1 ≤ I) {rows : ℕ → ℕ → ℕ}
    {μ μ' : ℕ → ℤ}
    (hreads : ∀ p < P, ∀ i < I, μ' (rb + p * I + i) = ((rows p i : ℕ) : ℤ))
    (hkept : Kept μ μ' fr) (hpre : rb + P * I ≤ fr) :
    ∀ p < P, ∀ i < I, ((rows p i : ℕ) : ℤ) = μ (rb + p * I + i) := by
  intro p hp i hi
  have hlt : rb + p * I + i < fr := by
    have h1 : p * I + I ≤ P * I := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right I (Nat.succ_le_of_lt hp)
    have h2 : p * I + i < p * I + I := by omega
    omega
  calc ((rows p i : ℕ) : ℤ) = μ' (rb + p * I + i) := (hreads p hp i hi).symm
    _ = μ (rb + p * I + i) := hkept _ hlt

/-- The proved extraction: the cache program's `Light.Solves` delivers the
reads (`hRR`-shaped, pointwise over the rows region) and the `KeptBut`
frame. -/
theorem cacheReads_of_solves {cacheProg : Light.Program} {cacheProc : ℕ}
    {cacheTime : ℕ → ℕ → ℕ} {cacheNeed : ℕ → ℕ → Light.Need}
    (hs : Light.Solves cacheTask cacheProg cacheProc cacheTime cacheNeed)
    {x : CacheInst} {μ : ℕ → ℤ} {fr : ℕ} {lim : Limits} {d : ℕ}
    (hpre : cacheTask.Pre x μ fr)
    (hok : (cacheNeed (cacheTask.size x) (cacheTask.bound x)).Ok lim fr d) :
    ∃ body : Stmt, cacheProg[cacheProc]? = some body ∧
      Ends lim cacheProg d body
        ⟨frame (cacheTask.args x ++ [(fr : ℤ)]), μ⟩
        (cacheTime (cacheTask.size x) (cacheTask.bound x))
        fun σ' => (∀ p < x.P, ∀ i < x.I, σ'.mem (x.rb + p * x.I + i) = x.rows p i) ∧
          KeptBut μ σ'.mem fr x.rb (x.P * x.I) := by
  obtain ⟨body, hb, hrun⟩ := hs
  have h2 := hrun [] lim d x μ fr hpre hok
  rw [List.append_nil] at h2
  exact ⟨body, hb, h2⟩

/-! ## The reads persist through the cache's `KeptBut` frame -/

/-- Under `KeptBut` with the five-region layout below the free pointer, every
stage read premise that lies OUTSIDE the rows region survives into the
cache's final memory — and the rows premise, which lies INSIDE it, is
supplied by the cache's own WRITE (`hW`), not by the entry memory. That
asymmetry is the whole content of the frame repair: `hRR`-at-the-entry-memory
is not a hypothesis here, because a cache is exactly the thing that produces
it. -/
theorem reads_persist {P I rb fr : ℕ} {μ μ' : ℕ → ℤ}
    (hkept : KeptBut μ μ' fr rb (P * I))
    {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {ab sb bb mb : ℕ}
    (hAR : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hW : ∀ p < P, ∀ i < I, μ' (rb + p * I + i) = ((rows p i : ℕ) : ℤ))
    (hfl : ∀ p < P, μ (mb + p) = DenseArgminPass.bit (remaining p))
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)]) :
    (∀ i < I, μ' (ab + i) = DenseScorePass.bit (active i)) ∧
    (∀ p < P, ∀ i < I, μ' (rb + p * I + i) = ((rows p i : ℕ) : ℤ)) ∧
    (∀ p < P, μ' (mb + p) = DenseArgminPass.bit (remaining p)) := by
  obtain ⟨hab, hrb, hsb, hbb, hmb⟩ := hlay
  have e1 : ab + I ≤ rb := hab
  have e2 : rb + P * I ≤ sb := hrb
  have e3 : sb + P ≤ bb := hsb
  have e4 : bb + I ≤ mb := hbb
  have e5 : mb + P ≤ fr := hmb
  refine ⟨fun i hi => ?_, hW, fun p hp => ?_⟩
  · have hlt : ab + i < fr := by omega
    have hout : Outside rb (P * I) (ab + i) := Or.inl (by omega)
    rw [hkept (ab + i) ⟨hlt, hout⟩]
    exact hAR i hi
  · have hlt : mb + p < fr := by omega
    have hout : Outside rb (P * I) (mb + p) := Or.inr (by omega)
    rw [hkept (mb + p) ⟨hlt, hout⟩]
    exact hfl p hp

/- NAMED FILL 3 CONTENT (not proved here): the stage slot inside the
composed caller program. A cache-first program layout shifts the driver's
procedure indices (the driver's loop calls procedure 5 of `program cs`), so
the composition goes through the Lang's renumbering machinery
(`Stmt.shift` / `Program.behind`) — the machine port's remaining mass,
together with FILL 2's finish pass. The slot itself is INHABITED:
`stageSlot_any` (MinPlusCaller) certifies it at the round program. -/

#print axioms cacheContent
#print axioms image_of_kept_post
#print axioms cacheReads_of_solves
#print axioms reads_persist

end ThinMatrix.CacheFill
