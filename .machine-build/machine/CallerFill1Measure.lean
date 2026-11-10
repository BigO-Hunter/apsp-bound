import CacheFill
import CallerUniversalBody

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 1 — the measurement.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  Light language is the pinned statement's.
- Joshua Wharton (QFEX) — the canonical adapter arrangement, the checked
  selection round / restart-loop driver, and the machine-obligations record.
- Hrishik Sai Bojnal — the verified frontier being refined and the refined
  numerical certificate this body targets.

# FILL 1 — the measurement, and the census's blocking finding

`UnivBundle` (`CallerUniversalBody.lean`) carries the rows image as a raw
conjunct:

    ∀ p < x.n, ∀ i < x.n, ((rows p i : ℕ) : ℤ) = μ (fr + x.n + p * x.n + i)

The question this module MEASURES (it does not prescribe): can that conjunct
be discharged by a PROGRAM STEP of the body — (a) an `x.a → rows` copy pass in
`univPrologue`, or (b) an `rb := x.a` layout that makes the reads land on the
instance's own arrays — so that it follows from `MatInst.Pre` alone?

Both routes are measured below and BOTH FAIL, for reasons that are not
budget-bookkeeping:

* ROUTE (a) — the copy pass. Cost: an `n × n` copy is `n` applications of the
  `Ends.pass` shape at `13n + 6` each, i.e. `13n² + 6n`. The prologue's budget
  `univProB n = 27n + 64` has `26n + 52` spent, leaving `n + 12`; the overrun
  is `13n² + 5n − 12 > 0` for every `n ≥ 1`. (Repairable — the per-round term
  of `univTn` is `770n²·(2·log₂U + 6)`, so a quadratic prologue budget is
  asymptotically free — but it still does not discharge the conjunct: see the
  coercion obstruction below, which the copied values inherit.)
* ROUTE (b) — `rb := x.a`. The stage's own region order
  (`InOrder fr [(ab,I),(rb,P·I),(sb,P),(bb,I),(mb,P)]`, `Lang/Regions.lean:66`)
  requires `ab + I ≤ rb`, i.e. `fr + n ≤ x.a`, while
  `MatInst.Pre.belowA : x.a + n·n ≤ fr`. The two are incompatible, so the
  layout cannot be chosen at all. And the same coercion obstruction stands.

THE COERCION OBSTRUCTION (why neither route can be a copy of `x.A`).
`MatInst.Pre` pins the memory with `segA : Seg μ x.a x.A` over
`A : List ℤ` and bounds the magnitude with `leA : AbsLe x.A x.U`
(`|e| ≤ U`) — it does NOT bound the sign. The bundle's conjunct is a `ℕ`
coercion, so it asserts that the buffer's image is a nonnegative integer
table; no arrangement of `x.A`'s cells can produce that when an entry is
negative. So the rows buffer is NOT the instance's matrix: it is the CACHE's
output (a count table), whose contract is `CacheFill.cacheTask.Post`'s reads
clause — the shape `cacheReads_of_solves` + `reads_persist` already deliver.
That is D7's oracle/cache boundary, not instance arithmetic.

THE CENSUS'S BLOCKING FINDING. The bundle's flag-budget conjunct

    (∀ mask' : ℕ → Bool, x.n ≤ (flagged x.n mask').card)

is FALSE: `flagged P mask'` is `(range P).filter mask'`, so its card is `0` at
`mask' := fun _ => false`, while `x.Pre.n_pos` gives `1 ≤ x.n`. `UnivBundle`
is therefore UNSATISFIABLE at every `need` (the `∃` body carries a false
conjunct), so `univSolves`/`twinUniv_of` are VACUOUS as they stand — green,
and unfireable. `hflag_shape_false` and `univBundle_false` below are the
receipts. The repair is at the CALL SITE, not in the wire: the wire
(`wireUnivTarget_of`, `univRound_runs`) is generic over `k` and consumes
`k ≤ (flagged P mask).card` per round, while the schedule's masks lose one
flag per round (`maskCleared cs₁.toFinset`), so a mask-generic budget forces
`k = 0`; the bundle instantiates `k := x.n`.

D7's boundary stands: nothing here proves the oracle, the cache body, or the
(min,+) product. This module is a measurement and a refutation.
-/

namespace ThinMatrix.CallerFill1Measure

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam
  Light.DenseRestartSelectionLoop Light
  ThinMatrix.MinPlusCaller ThinMatrix.CacheFill
  ThinMatrix.CallerUniversalBody

/-! ## Route (a): the `x.a → rows` copy pass against the prologue's budget -/

/-- An `n × n` copy is `n` passes of the prologue's `Ends.pass` shape, each
costing `13n + 6` (the two initialisation passes' measured cost). -/
theorem routeA_copy_cost (n : ℕ) : n * (13 * n + 6) = 13 * n * n + 6 * n := by ring

/-- The prologue's `26n + 52` spent against `univProB n = 27n + 64` leaves
`n + 12`. -/
theorem routeA_slack (n : ℕ) (hn : 1 ≤ n) : 26 * n + 52 + (n + 12) = 27 * n + 64 := by
  omega

/-- The copy does NOT fit the landed budget, at any `n ≥ 1`: the overrun is
`13n² + 5n − 12 > 0`. -/
theorem routeA_overrun (n : ℕ) (hn : 1 ≤ n) :
    27 * n + 64 < 26 * n + 52 + n * (13 * n + 6) := by
  nlinarith

/-- The budget a copy pass WOULD need: `13n² + 32n + 64`. Recorded so the
alternative is priced, not dismissed — the per-round term of `univTn` is
`770n²·(2·log₂U + 6)`, so this is asymptotically free. -/
theorem routeA_budget_if_paid (n : ℕ) :
    26 * n + 52 + n * (13 * n + 6) ≤ 13 * n * n + 32 * n + 64 := by
  have h : n * (13 * n + 6) = 13 * n * n + 6 * n := by ring
  rw [h]
  nlinarith

/-! ## Route (b): `rb := x.a` — the layout is forbidden by the stage's order -/

/-- The stage's region order forces the rows buffer ABOVE the caller's `fr`:
`InOrder`'s first clause is `ab + I ≤ rb`, and the prologue's layout has
`ab = fr`, `I = n`. -/
theorem routeB_order_forces_rows_above (ab rb I : ℕ) (P sb bb mb : ℕ) (fr : ℕ)
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)]) :
    ab + I ≤ rb := by
  simp only [InOrder] at hlay
  exact hlay.1

/-- …while `MatInst.Pre.belowA` puts `x.a` BELOW `fr`. Together with
`ab = fr` they are incompatible, so `rb := x.a` cannot satisfy the stage's
layout: route (b) is not a cheaper layout, it is not a layout. -/
theorem routeB_contradicts_belowA {x : MatInst} {μ : ℕ → ℤ} {fr rb I P sb bb mb : ℕ}
    (hpre : x.Pre μ fr) (hab : fr = rb + 0 + 0) (hI : I = x.n) (hrb : rb = x.a)
    (hlay : InOrder fr [(fr, I), (rb, P * I), (sb, P), (bb, I), (mb, P)]) :
    False := by
  have horder : fr + I ≤ rb := routeB_order_forces_rows_above fr rb I P sb bb mb fr hlay
  have hbelow : x.a + x.n * x.n ≤ fr := hpre.belowA
  have hn : 1 ≤ x.n := hpre.n_pos
  omega

/-! ## The coercion obstruction — why NEITHER route can copy `x.A` -/

/-- No natural-number image exists for a negative cell, so the bundle's
`((rows p i : ℕ) : ℤ) = μ (…)` cannot hold at a negative memory cell. -/
theorem no_nat_image_of_neg (e : ℤ) (he : e < 0) : ¬ ∃ m : ℕ, (m : ℤ) = e := by
  rintro ⟨m, hm⟩
  have h : (0 : ℤ) ≤ (m : ℤ) := by exact_mod_cast Nat.zero_le m
  omega

/-- …and `MatInst.Pre`'s own entry bound admits a negative entry: it is
`AbsLe`, i.e. `|e| ≤ U`, which says nothing about the sign. So the rows buffer
is not the instance's matrix; it is the cache's count table. -/
theorem pre_entry_bound_admits_negative : AbsLe ([-1] : List ℤ) (1 : ℤ) := by
  intro z hz
  simp only [List.mem_singleton] at hz
  subst hz
  norm_num

/-! ## The fold: FILL 1 IS the cache task's post reads-clause

The honest discharge is not a program step and not a layout: it is
`cacheTask.Post`'s first conjunct at the cache's own pinning
(`P, I, rb, rows`). `cacheReads_of_solves` produces exactly this in the
cache's end memory, and `reads_persist` carries every stage read premise
through the cache's `Kept` frame — both landed in `CacheFill`. So FILL 1 is a
D7 boundary premise of the CACHE slot's shape, not instance arithmetic, and
"folding it out of the bundle" means replacing the raw image by that slot,
which the files already name. -/

/-- The cache task's post delivers the rows image: FILL 1's shape is
literally the first conjunct of `cacheTask.Post`. -/
theorem cachePost_reads {P I h rb fr : ℕ} {rows : ℕ → ℕ → ℕ} {μ μ' : ℕ → ℤ} {r : ℤ}
    (hp : cacheTask.Post ⟨P, I, h, rb, fr, rows⟩ μ fr r μ') :
    ∀ p < P, ∀ i < I, μ' (rb + p * I + i) = rows p i :=
  hp.1

/-! ## The census's blocking finding: the bundle's flag conjunct is false -/

/-- The bundle's flag budget, as stated, is UNSATISFIABLE: `∀ mask', k ≤
(flagged P mask').card` fails at the all-false mask for every `k ≥ 1`, and the
bundle instantiates it at `k = P = x.n` with `x.n ≥ 1` from `Pre.n_pos`. -/
theorem hflag_shape_false (k P : ℕ) (hk : 1 ≤ k) :
    ¬ ∀ mask' : ℕ → Bool, k ≤ (flagged P mask').card := by
  intro h
  have h0 : (flagged P (fun _ => false)).card = 0 := by
    simp [flagged]
  have := h (fun _ => false)
  omega

/-- The counterexample instance: `n = U = 1`, `A = B = [0]`, all-zero memory,
`fr = 8`. `MatInst.Pre` holds (each field by the definition it abbreviates). -/
def xInst : MatInst := { n := 1, U := 1, a := 0, b := 2, c := 4, A := [0], B := [0] }

theorem xInst_pre : MatInst.Pre xInst (fun _ => 0) 8 := by
  refine ⟨le_rfl, le_rfl, rfl, rfl, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
    Or.inl (by decide), Or.inl (by decide)⟩
  · intro i hi
    have hi0 : i = 0 := by
      simp only [xInst, List.length_singleton] at hi
      omega
    subst hi0
    simp [xInst]
  · intro i hi
    have hi0 : i = 0 := by
      simp only [xInst, List.length_singleton] at hi
      omega
    subst hi0
    simp [xInst]
  · intro z hz
    simp only [xInst, List.mem_singleton] at hz
    subst hz
    norm_num
  · intro z hz
    simp only [xInst, List.mem_singleton] at hz
    subst hz
    norm_num

/-- THE RECEIPT: `UnivBundle` is unsatisfiable at every `need`, hence
`univSolves`/`twinUniv_of` are vacuous as they stand. The `Ok` premise is
discharged by choosing limits large enough for any `need` — the bundle's `∀`
over `lim` makes that a legitimate instantiation, and the false conjunct
survives it. -/
theorem univBundle_false (stage : ℕ) (cacheProg restoreProg : Light.Program)
    (cs : Inst) (need : ℕ → ℕ → Light.Need) :
    ¬ UnivBundle stage cacheProg restoreProg cs need := by
  intro hb
  let lim : Limits :=
    { word := (((8 + (need 1 1).cells) + (need 1 1).word : ℕ) : ℤ),
      space := 8 + (need 1 1).cells, depth := (need 1 1).depth }
  have hok : (need 1 1).Ok lim 8 0 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [lim]
      exact_mod_cast Nat.le_add_left (need 1 1).word (8 + (need 1 1).cells)
    · dsimp only [lim]
      omega
    · dsimp only [lim]
      push_cast
      omega
    · dsimp only [lim]
      omega
  have hb' := hb [] lim 0 xInst (fun _ => 0) 8 xInst_pre hok
  obtain ⟨tests, Tt, rows, h1, h2, h3, hflag, h5, h6, h7, h8⟩ := hb'
  exact (hflag_shape_false 1 1 le_rfl) hflag

#print axioms routeA_copy_cost
#print axioms routeA_overrun
#print axioms routeB_order_forces_rows_above
#print axioms routeB_contradicts_belowA
#print axioms no_nat_image_of_neg
#print axioms pre_entry_bound_admits_negative
#print axioms cachePost_reads
#print axioms hflag_shape_false
#print axioms xInst_pre
#print axioms univBundle_false

end ThinMatrix.CallerFill1Measure
