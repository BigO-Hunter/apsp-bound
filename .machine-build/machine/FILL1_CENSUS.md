# FILL 1 + the premise census (2026-11-10, the FILL-1 measurement session)

Working commit: `ea7e86d` (branch `wip-summit-body`; the census was written at
`3e5a9f2`, the flag repair landed at `06a523e`, the cache-frame repair at
`ea7e86d`). Bench: `.machine-build/machine`, Lean 4.33.1, mathlib
`0df444a360eaa60`.

This file records THREE findings, all measured, none prescribed:

<!-- SUPERSEDED IN PART, 2026-11-10 (fifth pass, commit acd5612): the cache
     call IS wired (`9298c40`) and the bundle's hokC/hokS/hflag conjuncts are
     GONE (derived or tautological), and row 9's literal need witness was
     CORRECTED in two places — its `depth = 1` cannot close the nested stage
     socket (DenseRestartSelectionLoop.need has depth 4, asked at d+1) and its
     `(n²+4n+1)` bracket is false at n = 0 against `4U+2`. The tree's witness is
     `univNeed = ⟨(n²+4n+5)(U+1)+8, n²+4n+8, 5⟩`, with NeedCovers/PolyNeed now
     THEOREMS. Read this file as the dated measurement it is; the live premise
     list is FILING_DRAFT_CLAIMED.md. -->

1. **FILL 1 (the rows-buffer memory image) is not a program step and not a
   layout.** Both routes the brief named are refuted — one by budget, one by
   the stage's own region order — and BOTH by the same coercion obstruction.
   Receipts: `CallerFill1Measure.lean` (`routeA_overrun`,
   `routeB_contradicts_belowA`, `no_nat_image_of_neg`,
   `pre_entry_bound_admits_negative`).
2. **`UnivBundle` was UNSATISFIABLE**: its flag-budget conjunct was false, so
   `univSolves` and `twinUniv_of` were vacuous as they stood. Receipts:
   `hflag_shape_false`, `univBundle_false`. REPAIRED at `06a523e`.
3. **The cache task's frame hid the premise it was meant to remove.** Under
   `Kept` with `Pre`'s `rb + P·I ≤ fr`, `cacheTask.Post` entailed the raw rows
   image at the entry memory, so route (c) would have renamed FILL 1 rather
   than producing it. Receipt: `CacheFill.image_of_kept_post`. REPAIRED at
   `ea7e86d` (frame now `KeptBut`).

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

> **CORRECTED 2026-11-10 (later session), before any of it was written.** This
> route had a hidden premise, and it is the same class of defect as the
> bundle's flag conjunct. `cacheTask.Post` then carried `Kept μ μ' fr` (nothing
> below the free pointer changes) while its own `Pre` puts the whole rows
> region below that pointer, so the post **entailed** `rows p i =
> μ (rb + p·I + i)` at the entry memory: `Light.Solves cacheTask` would have
> **renamed** FILL 1, not produced it. The frame is now `KeptBut μ μ' fr rb
> (P·I)` (commit `ea7e86d`), receipt `CacheFill.image_of_kept_post`. Everything
> below is correct **only against the repaired frame** — see §"The frame
> repair" in `FILING_DRAFT_CLAIMED.md`. Two sub-claims in this section were also
> wrong as written and are corrected inline.

The image is exactly the CACHE task's post reads-clause
(`cachePost_reads`): `∀ p < P, ∀ i < I, μ' (rb + p·I + i) = rows p i`, which
`CacheFill.cacheReads_of_solves` produces from
`Light.Solves cacheTask cacheProg …` and `CacheFill.reads_persist` carries
through the cache's `Kept` frame. Both are LANDED. So the body's entry
statement should CALL the cache procedure before `univPrologue` (a 3-argument
call: `P, I, rb`) instead of copying anything:

* cost ≈ 5–9 steps + the cache's own clock, vs `13n² + 6n` for the copy;
* `MatInst.Pre` survives into the cache's end memory with NO extra premise:
  every `Pre` field other than `segA`/`segB` is layout/magnitude and unaffected
  by a write below the free pointer, and `Seg μ x.a x.A` re-derives from
  `belowA` — but **not** by `Seg.of_kept` (`Lang/Tasks.lean:75`) directly, as
  this section first said: `of_kept` needs `Kept`, and the repaired frame is
  `KeptBut`. The step that applies is `Seg.of_sameOn` on the sub-region
  `(· < x.a + n*n)`: `belowA` gives `x.a + n² ≤ fr` and the rows region begins
  at `rb = fr + n > fr`, so the whole `segA` region lies outside the written
  one. One step longer than claimed, no extra premise;
* the conjunct becomes a THEOREM from the cache slot, i.e. it moves from a raw
  assumption to D7's cache boundary — the shape the lane already names. This
  holds **because** the cache's post now writes the rows it reports; against
  the old frame it was a renaming (see the correction above).

Disclosed cost of route (c): `univTn` gains `cacheTime (n²) U` and `hdom` must
absorb it (poly clock ⇒ absorbed by the existing `log^{k+R+10}·n²` arm).

**PROGRESS 2026-11-10 (third pass) — route (c)'s MECHANICAL PREREQUISITES ARE
LANDED; THE CALL IS NOT.** Landed in `CallerUniversalBody` (green, no `sorryAx`,
each `#print axioms` = [propext, Classical.choice, Quot.sound]):
`univCacheArgs` + `univCacheArgs_val` — the call's frame EVALUATED, proved to be
`[n, n, fr + n, fr + 4n + n²]` (`P, I, rb, LTop` with the free pointer last);
`cacheSolves_composed` — `Solves cacheTask cacheProg cacheProc …` at
`callerProgramUniv`, procedure `1 + cacheProc`, body shifted, by `Solves` →
`Ends.append` → `Ends.shift_append`; and the clock — `univTn` takes
`cacheTime` as an ARGUMENT and `univTn_le` carries the cache's share as a
HYPOTHESIS (without it the bound is false). What is NOT done: `mpBodyUniv` does
not call the cache, so row 1 below is still the flat image, `UnivBundle`'s
conjunct 1 is unswapped, and `univSolves` still takes `hfill` from the bundle.
The obstruction (the prologue runs at the cache's END memory) and the cure for
the remaining step are written out in
`CallerUniversalBody.verification.txt` §"ROUTE (c)'s MECHANICAL
PREREQUISITES LANDED", items (a)–(d).

## 2. The premise census — every hypothesis of `twinUniv_of` (`:1909`)

Classes: **(i)** derivable from the challenge's own quantification (close it);
**(ii)** D7 oracle/cache-boundary shape — "upstream's own"; stays named;
**(iii)** instance arithmetic / domination — the board's model may carry it.
An (i) row states `landed` or `routed` — routed means the argument is given
and the proof is not yet written; nothing here is claimed as proved unless it
says landed.

| # | premise | site | class | verdict |
|---|---|---|---|---|
| 1 | FILL 1 rows image | `:1752` | **(ii)** cache boundary | NOT Pre-derivable (measured, §1). Producer: route (c) — **gated on the cache task's frame repair (`ea7e86d`); with the frame shape first carried, route (c) renamed this premise instead of producing it.** *Status 2026-11-10: the cache slot at the COMPOSED program (`cacheSolves_composed`) and the cache clock (`univTn`/`univTn_le`) are LANDED; the entry-body call, the `UnivBundle` shape swap and the derived `hfill` are NOT.* |
| 2 | `UnivSlot` (certified stage socket) | `:1753` | **(i) landed** | `stageSlot_any` is LANDED and is exactly this shape; its `hAR`/`hfl` follow from the prologue's two passes (`bit true = 1`), `hlay` from the layout ring, `hok` from `Ok`+`NeedCovers`. Its `hRR` IS premise 1. |
| 3 | `hret` (oracle return) | `:1756` | **(ii)** oracle boundary | stays named. |
| 4 | `hflag : ∀ mask', x.n ≤ (flagged x.n mask').card` | `:1763` | **FALSE — REPAIRED 2026-11-10** | `(range n).filter` ⇒ card `0` at the all-false mask; `Pre.n_pos` ⇒ `1 ≤ x.n`. `hflag_shape_false` (kept) records it. **The repair is at the CALL SITE, not the wire** — the wire is generic in `k` and the schedule clears one flag per round, so a mask-generic budget forces `k = 0`; the bundle instantiates `k := x.n`. Applied at `:1753` (slot), `:1759` (hret call site), `:1763` (conjunct), `:1773` (`hTt`) + six `univSolves` instantiations. **The conjunct is now a tautology** (`hflag_shape_true_zero`, `refuted_mask_now_satisfies`), so this premise LEAVES the list. |
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

~~And the route's conditions are not merely named: premise 4 is FALSE, which
makes the bundle unsatisfiable and the twin vacuous. **The filing is therefore
BLOCKED-ON-REPAIR, not merely CLAIMED**~~ — **SUPERSEDED 2026-11-10**: premise
4 was false and the bundle was unsatisfiable; the call-site repair above landed
and the bundle rebuilds green with the conjunct now a tautology. See
§"The repair" below. The filing is no longer BLOCKED-ON-REPAIR; it is CLAIMED
with four named premises, and **inhabitance is still unwitnessed** — the
bundle is consistent with its premises, not proved non-empty.

## The repair (2026-11-10, after this census)

Applied to `CallerUniversalBody.lean` (`:1753`, `:1759`, `:1763`, `:1773`, and
the six `univSolves` instantiations `:1841`, `:1847`, `:1858`, `:1864`,
`:1869`, `:1891`): `k := 0`. Ten lines, 20 characters, no other edit.

Verdicts, read from the logs (`log-never-the-wrapper`):

| build | log | verdict |
|---|---|---|
| `lake env lean -j1 CallerUniversalBody.lean` | `/private/tmp/apsp_univ_repair_130520.log` | **exit 0**, 0 errors, 0 `sorry`, olean written; `univSolves`/`twinUniv_of` axioms `[propext, Classical.choice, Quot.sound]` |
| `lake env lean -j1 CallerFill1Measure.lean` | `/private/tmp/apsp_fill1_repair_130815.log` | **exit 0**, 0 errors, 0 `sorry` |

Both ran detached behind `_build_lock.py` (fcntl, `/Volumes/Substrate-1/bigo/.build.lock`)
under host load 63.7/76.9/94.3 on 16 cores.

Receipts added to `CallerFill1Measure.lean`: `hflag_shape_true_zero` (the new
conjunct is a tautology) and `refuted_mask_now_satisfies` (the mask that
refuted the old conjunct satisfies the new one). `univBundle_false` is
**deleted, not weakened** — its proof consumed the conjunct at `k = 1`, which
the bundle no longer supplies, so it described a file state that no longer
exists. `hflag_shape_false` stays: still true for every `k ≥ 1`, and the record
of why `k = 0` is forced.

**Non-vacuity, stated at exactly the strength witnessed:** no provably-false
conjunct remains, so the old vacuity is gone; and no `tests, Tt, rows` are
exhibited, so inhabitance is *consistent with* the premises — not proved. The
filing label is CLAIMED-conditional, not Lean Verified.

Route (c) is still **UNLANDED**. What landed on 2026-11-10 is its PRECONDITION:
the cache task's frame repair (commit `ea7e86d`), without which the call would
have renamed FILL 1 instead of producing it — the same defect class as the flag
conjunct, caught by asking what the contract is *satisfiable* with rather than
what it *says*. The census's recommendation stands, with its seams now
enumerated in `FILING_DRAFT_CLAIMED.md` and two of them corrected here:
`mpBodyUniv` / `callerProgramUniv` gain the 3-argument cache call before
`univPrologue`, `univProB` and `univTn` gain `cacheTime (n²) U`, `hdom` must
absorb it, and `MatInst.Pre` is carried from the caller memory into the cache's
end memory by `Seg.of_sameOn` on the sub-region `(· < x.a + n*n)` off
`Pre.belowA` — not by `Seg.of_kept`, which needs the `Kept` shape the repaired
frame no longer gives.

EXACT REMAINDER (nothing else): (a) the cache call in `mpBodyUniv` plus the
`cacheProc` index and the arg expressions; (b) the `cacheTime (n²) U` term in
`univTn` and the matching hypothesis in `univTn_le`; (c) `entryAssembly` /
`univSolves` prepending a cache `Ends` obtained by `Solves` + `Ends.append` +
`Ends.shift_append`, and the `UnivBundle` conjunct swapped from the raw image to
`Solves cacheTask …` plus its `Ok` at the cache's own free pointer.



D7's boundary stands throughout: no oracle, no cache body, no (min,+) product
is claimed here.
