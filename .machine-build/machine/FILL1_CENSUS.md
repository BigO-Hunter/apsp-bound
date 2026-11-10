# FILL 1 + the premise census (2026-11-10, the FILL-1 measurement session)

Working commit: `3e5a9f2` (branch `wip-summit-body`). Bench:
`.machine-build/machine`, Lean 4.33.1, mathlib `0df444a360eaa60`.

This file records TWO findings, both measured, neither prescribed:

1. **FILL 1 (the rows-buffer memory image) is not a program step and not a
   layout.** Both routes the brief named are refuted — one by budget, one by
   the stage's own region order — and BOTH by the same coercion obstruction.
   Receipts: `CallerFill1Measure.lean` (`routeA_overrun`,
   `routeB_contradicts_belowA`, `no_nat_image_of_neg`,
   `pre_entry_bound_admits_negative`).
2. **`UnivBundle` is UNSATISFIABLE**: its flag-budget conjunct is false, so
   `univSolves` and `twinUniv_of` are vacuous as they stand. Receipts:
   `hflag_shape_false`, `univBundle_false`.

## 1. FILL 1 — the measurement

The conjunct (`CallerUniversalBody.lean:1752`):

    ∀ p < x.n, ∀ i < x.n, ((rows p i : ℕ) : ℤ) = μ (fr + x.n + p * x.n + i)

### Route (a) — add an `x.a → rows` copy pass to `univPrologue`

| quantity | value |
|---|---|
| cost of one `Ends.pass` over `n` entries (measured, the two init passes) | `13n + 6` |
| an `n × n` copy = `n` such passes | `13n² + 6n` |
| `univProB n` (`:377`) / spent (`prologue_runs`, `:1449`) / slack | `27n + 64` / `26n + 52` / `n + 12` |
| overrun at every `n ≥ 1` | `13n² + 5n − 12 > 0` |
| budget that WOULD pay | `13n² + 32n + 64` (asymptotically free: the per-round term is `770n²·(2log₂U+6)`) |

So the copy does not fit the landed budget, and the repair is cheap — but the
copy is still the WRONG program: it copies `x.A`'s cells, and the conjunct
demands a `ℕ` image. `MatInst.Pre` pins the memory with
`segA : Seg μ x.a x.A` over `A : List ℤ` and bounds only the magnitude
(`leA : AbsLe x.A x.U`, i.e. `|e| ≤ U`). A negative entry admits no `rows`
(`no_nat_image_of_neg`), and `AbsLe` admits one
(`pre_entry_bound_admits_negative`). The rows buffer is a COUNT table — the
composite-incidence cache's output — not the instance's matrix.

### Route (b) — lay `rb := x.a` out, no copy

| quantity | value |
|---|---|
| steps added | 0 |
| the stage's region order (`Lang/Regions.lean:66`, `InOrder`) | `ab + I ≤ rb`, i.e. `fr + n ≤ rb` |
| `MatInst.Pre.belowA` | `x.a + n·n ≤ fr` |

`rb := x.a` makes the two incompatible — `routeB_contradicts_belowA`. Not a
cheaper layout: no layout. And it inherits the coercion obstruction.

### Route (c) — the one that works, and it is cheapest (RECOMMENDED, unlanded)

The image is exactly the CACHE task's post reads-clause
(`cachePost_reads`): `∀ p < P, ∀ i < I, μ' (rb + p·I + i) = rows p i`, which
`CacheFill.cacheReads_of_solves` produces from
`Light.Solves cacheTask cacheProg …` and `CacheFill.reads_persist` carries
through the cache's `Kept` frame. Both are LANDED. So the body's entry
statement should CALL the cache procedure before `univPrologue` (a 3-argument
call: `P, I, rb`) instead of copying anything:

* cost ≈ 5–9 steps + the cache's own clock, vs `13n² + 6n` for the copy;
* `MatInst.Pre` survives into the cache's end memory with NO extra premise:
  `Seg μ x.a x.A` re-derives by `Seg.of_kept` (`Lang/Tasks.lean:75`) from
  `belowA`, and every other `Pre` field is layout/magnitude, unaffected by a
  `Kept` write below `fr`;
* the conjunct becomes a THEOREM from the cache slot, i.e. it moves from a raw
  assumption to D7's cache boundary — the shape the lane already names.

Disclosed cost of route (c): `univTn` gains `cacheTime (n²) U` and `hdom` must
absorb it (poly clock ⇒ absorbed by the existing `log^{k+R+10}·n²` arm).

## 2. The premise census — every hypothesis of `twinUniv_of` (`:1909`)

Classes: **(i)** derivable from the challenge's own quantification (close it);
**(ii)** D7 oracle/cache-boundary shape — "upstream's own"; stays named;
**(iii)** instance arithmetic / domination — the board's model may carry it.
An (i) row states `landed` or `routed` — routed means the argument is given
and the proof is not yet written; nothing here is claimed as proved unless it
says landed.

| # | premise | site | class | verdict |
|---|---|---|---|---|
| 1 | FILL 1 rows image | `:1752` | **(ii)** cache boundary | NOT Pre-derivable (measured, §1). Producer: route (c). |
| 2 | `UnivSlot` (certified stage socket) | `:1753` | **(i) landed** | `stageSlot_any` is LANDED and is exactly this shape; its `hAR`/`hfl` follow from the prologue's two passes (`bit true = 1`), `hlay` from the layout ring, `hok` from `Ok`+`NeedCovers`. Its `hRR` IS premise 1. |
| 3 | `hret` (oracle return) | `:1756` | **(ii)** oracle boundary | stays named. |
| 4 | `hflag : ∀ mask', x.n ≤ (flagged x.n mask').card` | `:1763` | **FALSE** | `(range n).filter` ⇒ card `0` at the all-false mask; `Pre.n_pos` ⇒ `1 ≤ x.n`. `hflag_shape_false` + `univBundle_false`. **Repair: the call site, not the wire** — the wire is generic in `k` and the schedule clears one flag per round, so a mask-generic budget forces `k = 0`; the bundle instantiates `k := x.n`. |
| 5 | `hok` (`∀ mask kt`, the stage's own `need` fits the limits) | `:1764` | **(i) routed** | closes with the SAME witness `need` as rows 9/10, chosen with `word ≥ (n²+4n+1)(U+1)+1` (the stage's own need at `instanceSize = n²+4n`), `cells ≥ n²+4n+8`, `depth ≥ 1`; then `Need.Ok.mono`. |
| 6 | `hTt : Tt x.n ≤ callerTt x.n` | `:1773` | **(ii)** L5/L6(c) tight-clock wrapper | named; producer = the re-clocked selection round's `solvedIn`. Not derivable from `taskTime (instanceSize …)` (that is `~100n⁴ ≫ 25n²`). |
| 7 | `hident` (`MinPlusIdentity`) | `:1774` | **(ii)** D7 construction identity | stays named. |
| 8 | `hkept` (`KeptBut`) | `:1777` | **(i) routed** | derivable: write set `{x.c} ⊆ [x.c, x.c+n²)` by `Pre.belowC`, prologue writes at `ab = fr` and above (not `< fr`). Proof unlanded (`univRowPass_runs` frame + `KeptBut` composition). |
| 9 | `NeedCovers need` | `:1783` | **(i) routed** | close by CHOOSING `need := ⟨(n²+4n+1)(U+1)+8, n²+4n+8, 1⟩` (one witness also closes rows 5 and 10): `2^signedLevels U ≤ 4U` from `pow_pred_signed_levels_le` + `two_mul_lt_pow_signed_levels` (landed `:1244`, `:1254`); `mpRounds U ≤ 4U+2`; `2U+1 ≤ word`; `4n + n² ≤ cells`. |
| 10 | `hn : PolyNeed need` | `:1912` | **(i) routed** | `poly_need` at the same witness. |
| 11 | `hdom` (completeCost domination) | `:1913` | **(iii)** | `CallerHdom`/`callerHdom` landed at `callerTn`; the transfer to `univTn` is the same asymptotics (`O(n² log U)`), plus route (c)'s cache clock. |

### Result of the census

`(i)`-closure is NOT reached: four class-(ii) premises remain (FILL 1's cache
slot, `hret`, `hTt`, `hident`). So there is **no unconditional
`Race.bound 2994999/1000000`** at this commit — the root shape stays
conditional and the filing package is a CLAIMED route with disclosed
conditions.

And the route's conditions are not merely named: premise 4 is FALSE, which
makes the bundle unsatisfiable and the twin vacuous. **The filing is therefore
BLOCKED-ON-REPAIR, not merely CLAIMED**: repair `hflag` (one binder at the
call site — `k := 0`, or restate per round from the greedy's `enoughFlags`
with `k + mpRounds ≤ n`), then land route (c) + `hkept` + the `hdom`
transfer, then the honest label is CLAIMED-ROUTE-READY with premises
`{FILL 1 (cache slot), hret, hTt, hident}`.

D7's boundary stands throughout: no oracle, no cache body, no (min,+) product
is claimed here.
