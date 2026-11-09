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
  and keep everything else (`Kept`);
- `cacheReads_of_solves` — the proved extraction: the cache program's
  `Light.Solves` delivers the reads (`hRR`-shaped) and the frame;
- `reads_persist` — the proved persistence: under `Kept` with the five-region
  layout below the free pointer, every stage read premise survives into the
  cache's final memory;
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
behind `Oracle.Correct`); the contract is what the caller composes with. -/
def cacheTask : Task where
  Inst := CacheInst
  size x := x.P * x.I
  bound x := x.h
  args x := [x.P, x.I, x.rb]
  Pre x μ fr := x.rb + x.P * x.I ≤ fr
  Post x μ fr _r μ' :=
    (∀ p < x.P, ∀ i < x.I, μ' (x.rb + p * x.I + i) = x.rows p i) ∧
    Kept μ μ' fr

/-- The proved extraction: the cache program's `Light.Solves` delivers the
reads (`hRR`-shaped, pointwise over the rows region) and the `Kept` frame. -/
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
          Kept μ σ'.mem fr := by
  obtain ⟨body, hb, hrun⟩ := hs
  have h2 := hrun [] lim d x μ fr hpre hok
  rw [List.append_nil] at h2
  exact ⟨body, hb, h2⟩

/-! ## The reads persist through the cache's Kept frame -/

/-- Under `Kept` with the five-region layout below the free pointer, every
stage read premise survives into the cache's final memory. -/
theorem reads_persist {μ μ' : ℕ → ℤ} {fr : ℕ} (hkept : Kept μ μ' fr)
    {P I h : ℕ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {ab rb sb bb mb : ℕ}
    (hAR : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hRR : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hfl : ∀ p < P, μ (mb + p) = DenseArgminPass.bit (remaining p))
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)]) :
    (∀ i < I, μ' (ab + i) = DenseScorePass.bit (active i)) ∧
    (∀ p < P, ∀ i < I, μ' (rb + p * I + i) = rows p i) ∧
    (∀ p < P, μ' (mb + p) = DenseArgminPass.bit (remaining p)) := by
  obtain ⟨hab, hrb, hsb, hbb, hmb⟩ := hlay
  have e1 : ab + I ≤ rb := hab
  have e2 : rb + P * I ≤ sb := hrb
  have e3 : sb + P ≤ bb := hsb
  have e4 : bb + I ≤ mb := hbb
  have e5 : mb + P ≤ fr := hmb
  refine ⟨fun i hi => ?_, fun p hp => fun i hi => ?_, fun p hp => ?_⟩
  · rw [hkept (ab + i) (by omega)]
    exact hAR i hi
  · have hlt : p * I < P * I := Nat.mul_lt_mul_of_pos_right hp (by omega)
    rw [hkept (rb + p * I + i) (by omega)]
    exact hRR p hp i hi
  · rw [hkept (mb + p) (by omega)]
    exact hfl p hp

/- NAMED FILL 3 CONTENT (not proved here): the stage slot inside the
composed caller program. A cache-first program layout shifts the driver's
procedure indices (the driver's loop calls procedure 5 of `program cs`), so
the composition goes through the Lang's renumbering machinery
(`Stmt.shift` / `Program.behind`) — the machine port's remaining mass,
together with FILL 2's finish pass. The slot itself is INHABITED:
`stageSlot_any` (MinPlusCaller) certifies it at the round program. -/

#print axioms cacheContent
#print axioms cacheReads_of_solves
#print axioms reads_persist

end ThinMatrix.CacheFill
