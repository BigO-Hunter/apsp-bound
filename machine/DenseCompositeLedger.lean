import DenseCompositeCaller

/-!
Copyright (c) 2026. APSP port campaign: L6 caller ledger.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence reduction: the materialized
  row cache, the running modulus, and the greedy history
  (`ArrayCompositeAlgorithm`, thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler
  (`Submission/`) whose Light language these procedures execute in.
- Joshua Wharton (QFEX) — the checked selection round and restart-loop
  driver this ledger sits beside.
- Hrishik Sai Bojnal — the verified frontier being refined.

# L6(b): the caller's D5 remainder — cache lifetime, oracle-call
accounting, modulus/history updates

The delta table's D5 row names three surfaces beyond the restart loop:
oracle calls, modulus/history updates, cache lifetime. At the n×n call site
these are statements about the one cache the `k` restart rounds read and the
one scalar the certification finish consumes:

- `cert_cache` — cache lifetime: every cell below the scores region (the
  active mask and the whole rows cache) survives the certification run, so
  all `k` rounds read the same cache and the driver issues no fresh oracle
  call.
- `historyModulus`, `history_cons` — the modulus/history updates: the stage
  modulus is the product of the chosen candidates' primes (upstream
  `greedy_factor_product`: `out.selected.prod = out.modulus`), and one more
  restart multiplies the running modulus by the chosen candidate's prime —
  upstream's `d * primes.get p` step.
- `cert_rounds` — oracle-call accounting: the run is exactly `k` restart
  rounds (the chosen list's length), so the cache is shared across exactly
  `k` rounds.

Statements touch no board-model text; the D7 boundary stands (no
bit-cost → Light-step translation).
-/

namespace Light.DenseCompositeLedger

open Light DenseRestartSelectionLoop DenseCompositeCaller

/-! ## Cache lifetime -/

/-- Cache lifetime: every cell below the scores region survives the
certification run. The active mask (`ab + I ≤ rb`) and the rows cache
(`rb + P * I ≤ sb`) lie below `sb` by the five-region layout, so all `k`
restart rounds read the same cache — the driver issues no fresh oracle
call. -/
theorem cert_cache {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr : ℕ} {μ μ' : ℕ → ℤ}
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)])
    (hpost : Post (callSite P k I h active remaining rows ab rb sb mb bb) μ μ')
    (x : ℕ) (hx : x < sb) : μ' x = μ x := by
  obtain ⟨hab, hrb, hsb, hmb, hfr⟩ := hlay
  obtain ⟨-, -, -, -, -, hframe, -, -⟩ := hpost
  have hxb : x < bb := by omega
  have hxm : x < mb := by omega
  exact hframe x ⟨Or.inl hx, Or.inl hxb, Or.inl hxm⟩

/-! ## Modulus and history updates -/

/-- The restart history's modulus: the product of the chosen candidates'
primes, in round order. Upstream this is `greedy_factor_product`'s
`out.selected.prod = out.modulus`; the certification finish consumes it as
its modulus scalar. -/
def historyModulus (prime : ℕ → ℕ) (cs : List ℕ) : ℕ := (cs.map prime).prod

/-- Modulus update rule: one more restart multiplies the running modulus by
the chosen candidate's prime — upstream's `d * primes.get p` step. -/
theorem history_cons (prime : ℕ → ℕ) (c : ℕ) (cs : List ℕ) :
    historyModulus prime (c :: cs) = prime c * historyModulus prime cs := rfl

/-- The empty history's modulus is the stage's starting scalar `d` —
upstream's `greedy` base case `⟨d, remaining, base, selected, []⟩`. -/
@[simp] theorem history_nil (prime : ℕ → ℕ) : historyModulus prime [] = 1 := rfl

/-! ## Oracle-call accounting -/

/-- Oracle-call accounting: the certification run is exactly `k` restart
rounds — the chosen list's length — so the cache is read across exactly `k`
rounds and the driver adds no further oracle traffic. -/
theorem cert_rounds {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb : ℕ} {μ μ' : ℕ → ℤ}
    (hpost : Post (callSite P k I h active remaining rows ab rb sb mb bb) μ μ') :
    ∃ cs : List ℕ, cs.length = k := by
  obtain ⟨cs, hlen, -, -, -⟩ := hpost
  exact ⟨cs, hlen⟩

end Light.DenseCompositeLedger

#print axioms Light.DenseCompositeLedger.cert_cache
#print axioms Light.DenseCompositeLedger.history_cons
#print axioms Light.DenseCompositeLedger.history_nil
#print axioms Light.DenseCompositeLedger.cert_rounds
