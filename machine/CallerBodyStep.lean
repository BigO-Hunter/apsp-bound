import MinPlusCaller
import CallerBody
import CallerChain

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the summit body,
step session: the caller layout, the KeptBut bridge, and the oracle
premise.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  Light language is the pinned Anthropic statement's.
- Joshua Wharton (QFEX) — the canonical adapter arrangement, the checked
  selection round / restart-loop driver, and the machine-obligations record.
- Hrishik Sai Bojnal — the verified frontier being refined and the refined
  numerical certificate this body targets.

# The summit body, step session: layout, KeptBut bridge, oracle premise

The body's first construction slice. The caller's `mpTask` run needs, at
the matrix instance `x : MatInst`, a scratch region for the stage's five
buffers and a map from the stage's certified frame to the caller's
`KeptBut` obligation:

- `callerAb` … `callerMb` — the five stage buffers stacked from the
  caller's free pointer `fr` (active bits, rows cache, scores, replacement
  base, remaining flags — the sizes I, P*I, P, I, P at the pinning's
  `(P, I)`); `callerFr` — the stage's free pointer, the allocation top.
- `regions_inOrder` — the layout's `InOrder` derivation (each buffer
  starts where the previous ends; the top is the stage's free pointer).
- `keptBut_of_chain` — THE KEPTBUT HALF: the chain's certified frame
  (`SameOutside3` over the stage's three written regions) delivers the
  caller's `KeptBut μ μ₁ fr x.c (x.n * x.n)` — every cell below the
  caller's free pointer and outside the product region lies below the
  scores buffer, hence outside all three written regions (the layout,
  omega).
- the ORACLE PREMISE at the TriangleOracle level: the Seg half's
  functional consumption conditions on `MinPlusReduction.OracleCorrect O`
  — exactly the premise upstream's own construction lemmas take
  (`bounded_signed_eq_minPlus` and the stored-table chapter's
  `bitScale_value`/`apsp_correct`). When Fill 1's cache body lands, its
  content contract (`cacheContent O A = Oracle.Correct O A`) meets this
  premise through the stored chapter's `semanticOracle_correct`
  (`DenseOracleCorrect O → OracleCorrect (semanticOracle O)` — to be
  imported then; D7's boundary stands: the oracle premise is a premise,
  never claimed as proved).

THE BODY'S REMAINING SLICES (each the next session's target): the
product-round body's Light statement itself (the bit-scaled product
rounds over the caller layout, the stage/cache/restore invocations at
their pinned indices — the program term); the execution derivation
(ChainTarget's frame + the KeptBut bridge + the Seg half through the
oracle chain, discharging `CallerTarget`); the step count for
`CallerHdom` (the budget structure B / Tt / 9+2 over mpRounds). D7's
boundary stands: no (min,+) product is claimed in this module.
-/

namespace ThinMatrix.CallerBodyStep

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.WordRam
  ThinMatrix.MinPlusReduction ThinMatrix.MinPlusCaller
  Light.DenseRestartSelectionLoop Light
  ThinMatrix.CallerBody ThinMatrix.CallerRounds

/-! ## The caller's scratch layout (the five stage buffers) -/

/-- The stage's active-bits buffer: at the caller's free pointer. -/
abbrev callerAb (fr I : ℕ) : ℕ := fr

/-- The stage's rows cache: behind the active bits. -/
abbrev callerRb (fr I : ℕ) : ℕ := fr + I

/-- The stage's scores buffer: behind the rows cache. -/
abbrev callerSb (fr P I : ℕ) : ℕ := fr + I + P * I

/-- The stage's replacement base: behind the scores. -/
abbrev callerBb (fr P I : ℕ) : ℕ := fr + I + P * I + P

/-- The stage's remaining flags: behind the replacement base. -/
abbrev callerMb (fr P I : ℕ) : ℕ := fr + I + P * I + P + I

/-- The stage's free pointer: the caller's allocation top. -/
abbrev callerFr (fr P I : ℕ) : ℕ := fr + I + P * I + P + I + P

/-- The layout's `InOrder`: each buffer starts where the previous ends,
and the flags end at the stage's free pointer. -/
theorem regions_inOrder (fr P I : ℕ) :
    InOrder (callerFr fr P I)
      [(callerAb fr I, I), (callerRb fr I, P * I), (callerSb fr P I, P),
        (callerBb fr P I, I), (callerMb fr P I, P)] := by
  unfold InOrder callerFr callerAb callerRb callerSb callerBb callerMb
  repeat' constructor
  all_goals omega

/-! ## The KeptBut half: the chain's frame delivers the caller's frame -/

/-- THE KEPTBUT HALF: the chain's certified frame over the stage's three
written regions delivers the caller's `KeptBut μ μ₁ fr x.c (x.n * x.n)` —
every cell below the caller's free pointer and outside the product region
lies below the scores buffer (the layout), hence outside all three
written regions. -/
theorem keptBut_of_chain
    {x : MatInst} {μ : ℕ → ℤ} {fr : ℕ} (xpre : x.Pre μ fr)
    {P I : ℕ} {μ₁ : ℕ → ℤ}
    (hchain : SameOutside3 μ μ₁ (callerSb fr P I) P
      (callerBb fr P I) I (callerMb fr P I) P) :
    KeptBut μ μ₁ fr x.c (x.n * x.n) := by
  intro b' hb'
  have h1 : b' < callerSb fr P I := by
    simp only [callerSb]
    omega
  have h2 : b' < callerBb fr P I := by
    simp only [callerBb]
    omega
  have h3 : b' < callerMb fr P I := by
    simp only [callerMb]
    omega
  exact hchain b' ⟨Or.inl h1, Or.inl h2, Or.inl h3⟩

/-! ## The oracle premise in upstream's own shape -/

#print axioms regions_inOrder
#print axioms keptBut_of_chain

end ThinMatrix.CallerBodyStep
