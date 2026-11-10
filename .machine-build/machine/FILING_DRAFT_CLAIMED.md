# FILING DRAFT — CLAIMED-conditional (ready to hand to the PR author, NOT posted) — FILED 2026-11-10: https://github.com/bigospeedrun/site/pull/22

Lane: `wip-summit-body` (apsp-l1), `/Volumes/Substrate-1/bigo/apsp-l1-work`.
Bench: `.machine-build/machine`, Lean 4.33.1, mathlib `0df444a360eaa60`.
Base of this draft: the commit that repairs `hflag` (parent `76605d0`).

## The label, stated first and honestly

**CLAIMED-conditional — upstream's own oracle-shape boundary. NOT Lean
Verified.**

The board's measured semantics are unconditional: a `Race.bound` row is
`Verified` only when the root statement is proved with no named premises. This
row is a **Claimed** row — site data supplied by the PR author, whose
conditions are disclosed in the premise list below. Nothing in this draft
asserts that the conditions hold; it asserts precisely what they are, and that
the reduction from them is proved.

Distinguish three things this lane can and cannot say:

| claim | status |
|---|---|
| `(premises) → EndStatement.APSP.SolvedInTime (2994999/1000000)` is PROVED | **yes** — `ThinMatrix.CallerUniversalBody.twinUniv_of`, axioms `[propext, Classical.choice, Quot.sound]` only, 0 `sorry` |
| the premise bundle is INHABITED | **no** — not witnessed. Post-repair it is *consistent with* the premises (no longer refuted); inhabitance is unproved |
| the row is `Verified` | **no** — four named premises remain, three of them D7's boundary |

The one thing that changed on 2026-11-10: the bundle is no longer
**UNSATISFIABLE**. Before the repair its flag conjunct was false and the
reduction was vacuous-as-green. After it, satisfiability is merely unproved.

## The root shape

```lean
theorem twinUniv_of (stage : ℕ) (cacheProg restoreProg : Light.Program) (cs : Inst)
    (need : ℕ → ℕ → Light.Need)
    (hb : UnivBundle stage cacheProg restoreProg cs need)
    (hcov : NeedCovers need)
    (hn : Light.PolyNeed need)
    (hdom : ∀ κ : Nat, ∃ (k : Nat) (C : Real), ∀ᶠ n : Nat in atTop,
      Light.timeUpTo (Light.Sec3.apTime univTn) n ((n : Real) ^ (κ : Real)) ≤
        C * AsymptoticCosts.completeCost k n) :
    EndStatement.APSP.SolvedInTime ((2994999 : Rat) / 1000000)
```

`EndStatement.APSP.SolvedInTime` is the root Submission shape
(`verified/Submission/EndStatement.lean`), the same statement class as the
landed `Race.bound (((1497780383 : Rat) / 500000000))` in
`verified/Submission.lean:25`. The composition is
`ThinMatrix.Twin.race_bound` (`TwinRaceBound.lean:48`) at
`P := callerProgramUniv stage cacheProg restoreProg cs`, `p := 0`,
`Tn := univTn`.

## The premise list — four named, everything else closed or routed

### Named, class (ii) — D7's oracle/cache/identity boundary ("upstream's own")

| # | premise | site | why it cannot be closed here |
|---|---|---|---|
| 1 | **FILL 1 rows image** — `∀ p < x.n, ∀ i < x.n, ((rows p i : ℕ) : ℤ) = μ (fr + x.n + p·x.n + i)` | `CallerUniversalBody.lean:1752` | **The CACHE-BOUNDARY route (c).** The image *is* `cacheTask.Post`'s first conjunct. Two direct routes were measured and both fail (`FILL1_CENSUS.md` §1): the copy pass costs `13n²+6n` against `n+12` slack, and `rb := x.a` contradicts `MatInst.Pre.belowA`. The producer is the cache call: `CacheFill.cacheReads_of_solves` (**landed**, `CacheFill.lean:149`) turns `Light.Solves cacheTask cacheProg …` into that reads clause, and `CacheFill.reads_persist` (**landed**, `CacheFill.lean:175`) carries it through the cache's frame. **The call itself is UNLANDED** — see route (c) state below. The cache slot is already pre-wired in the bundle's shape (`cacheProg : Light.Program` is a parameter). **This premise is producible only because the cache task's FRAME was repaired on 2026-11-10 — see "The frame repair" below; with the frame shape the lane first carried, route (c) renamed this premise instead of discharging it.** |
| 2 | `hret` — the oracle's return: the delivery is the bracket fold seeded at row `t`'s head | `:1756` | the oracle functional chain (shresh's construction) supplies it; not instance arithmetic |
| 3 | `hTt` — the tight clock: `Tt 0 ≤ callerTt x.n` | `:1773` | producer = the re-clocked selection round's `solvedIn`. Not derivable from `taskTime (instanceSize …)` (that is `~100n⁴ ≫ 25n²`). **Post-repair the index is `0`, not `x.n`** — see the repair note |
| 4 | `hident` — `MinPlusIdentity` (the head's delivery is every entry) | `:1774` | D7's construction identity |

### Closed or routed, class (i) — the argument is given, the proof is not all written

| premise | site | state |
|---|---|---|
| `UnivSlot` at `k := 0` (certified stage socket) | `:1753` | `stageSlot_any` is **landed**; `hAR`/`hfl` from the prologue's two passes, `hlay` from the layout ring, `hok` from `Ok`+`NeedCovers`. Its `hRR` is premise 1 |
| `hflag` — the flag budget | `:1763` | **REPAIRED and now a tautology**: `∀ mask', 0 ≤ (flagged x.n mask').card`. No longer a premise at all. Receipts `hflag_shape_true_zero`, `refuted_mask_now_satisfies` |
| `hok` — the stage's own `need` fits the limits | `:1764` | **routed**: closes with the witness `need` below + `Need.Ok.mono` |
| `hkept` — `KeptBut` frame | `:1777` | **routed**: write set `{x.c} ⊆ [x.c, x.c+n²)` by `Pre.belowC`; prologue writes at `ab = fr` and above |
| `NeedCovers need` | `:1783` | **routed, witness chosen**: see below |
| `PolyNeed need` | `:1913` | **routed**: the `poly_need []` tactic at the same witness |

### Class (iii) — image arithmetic / domination

| premise | state |
|---|---|
| `hdom` (completeCost domination for `univTn`) | `CallerHdom`/`callerHdom` are **landed** (`CallerStepCount.lean:524`) at `callerTn`. The transfer to `univTn` is the same asymptotics (`O(n² log U)`); **route (c) adds `cacheTime (n²) U`** to `univTn`, and the poly clock is absorbed by the existing `log^{k+R+10}·n²` arm |

## The need witness

One witness closes `NeedCovers`'s six numeric facts, `hok`, and `PolyNeed`:

```lean
need := fun n U => ⟨(n^2 + 4*n + 1) * (U + 1) + 8,   -- word
                     n^2 + 4*n + 8,                   -- cells
                     1⟩                               -- depth
```

`cells = n²+4n+8` covers `4n + n² ≤ cells`; `word ≥ (n²+4n+1)(U+1)+1` is the
stage's own `need` at `instanceSize = n²+4n`, comfortably above `2U+1`,
`mpRounds U ≤ 4U+2` and `2^signedLevels U ≤ 4U` (from the landed
`pow_pred_signed_levels_le` and `two_mul_lt_pow_signed_levels`); `depth = 1`
satisfies `1 ≤ depth`. Under `Need.Ok.mono` the same witness serves every
`kt`.

## The repair that unblocked this draft (2026-11-10)

`UnivBundle` instantiated the wire at `k := x.n`. The wire
(`UnivSlot`/`univRound_runs`/`wireUnivTarget_of`/`entryAssembly`) is **generic
in `k`**: `univRound_runs` calls the stage at a single fixed `kt := k` and
demands `hflag mask : k ≤ (flagged P mask).card` for every mask the schedule
reaches. The schedule clears one flag per round
(`maskCleared cs₁.toFinset`), so the reachable masks include the empty one —
a mask-generic budget therefore forces `k = 0`, and the bundle's `x.n` was the
wrong instantiation. `k := 0` at the slot, at `hret`'s call site, at the flag
conjunct and at `hTt`, plus the six `univSolves` instantiations that must
agree with them.

Consequences for the premise list, stated exactly:

* `hflag` leaves the list (a tautology at `k=0`).
* `hTt` **stays** a premise but re-indexes to `Tt 0 ≤ callerTt x.n`. It is not
  trivially discharged: `Tt` is existentially chosen inside the bundle, but
  `hslot` pins it at every `kt` the wire reaches, so the index-0 obligation on
  the *actual* stage clock survives.
* the bundle still contains no provably-false conjunct; nothing new is
  asserted about inhabitance.

## Credits (verbatim from the module header)

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

## The frame repair (2026-11-10, later session) — the step route (c) was missing

Route (c) rested on this: "the image is `cacheTask.Post`'s first conjunct, so
call the cache procedure and the conjunct becomes a theorem." Measured against
the contract the files actually carried, **that was not yet true**, and this is
the finding that had to land before any call could be written.

`cacheTask.Post` carried `Kept μ μ' fr` — "nothing below the free pointer
changes" — while its own `Pre` places the **whole rows region below that
pointer** (`Pre x μ fr := x.rb + x.P * x.I ≤ fr`). For the non-degenerate case
(`1 ≤ I`; `1 ≤ P` follows from the same quantifier) those two conjuncts are
jointly satisfiable **only when the rows region already holds `rows`**. So the
old post *entailed*

    rows p i = μ (rb + p·I + i)

at the entry memory — the very image it was supposed to produce. A
`Light.Solves cacheTask …` premise stated with that frame therefore puts the
image **inside the premise**: route (c) would have **renamed** FILL 1, not
discharged it. Receipt: `CacheFill.image_of_kept_post` (`CacheFill.lean:131`),
true of the old shape, kept so the two shapes stay distinguishable.

The repair (commit `ea7e86d`): the frame is
`KeptBut μ μ' fr x.rb (x.P * x.I)` — everything below the free pointer **except
the rows region the task is defined to fill**. That is the same class of defect
as the bundle's refuted flag conjunct (`hflag_shape_false`, repaired at
`06a523e`): a premise that looks like a boundary and is in fact the thing it was
meant to produce.

Two consequences, both verified rather than assumed:

* `reads_persist` no longer consumes an entry-memory rows image **at all**. It
  takes the cache's *write* (the post's first conjunct, at `μ'`) for the rows
  family, and the `KeptBut` frame for the active-bit and remaining-flag
  families — legitimate only because `InOrder` puts those two regions outside
  the rows region. The image is now **produced, not assumed**.
* `MatInst.Pre` still survives the cache's frame, but the reach is one step
  longer than the earlier draft said. The frame is `KeptBut`, not `Kept`, so
  `Seg.of_kept` does not apply directly. What applies is `Seg.of_sameOn` on the
  sub-region `(· < x.a + n*n)`: `Pre.belowA` gives `x.a + n² ≤ fr` and the rows
  region begins at `rb = fr + n > fr`, so the whole `segA` region is *outside*
  the written one. No extra premise is needed — but the step is named here
  rather than elided, because the elision is exactly what was wrong before.

## What route (c) buys — stated precisely, because it is easy to over-claim

Route (c) does **not** reduce the *count* of named premises. It replaces one
*shape* with another:

| | before | after (route (c)) |
|---|---|---|
| the rows image | a raw assertion about a memory image that **no program step can establish** (both direct routes measured refuted) | a **consequence** of `Light.Solves cacheTask cacheProg cacheProc cacheTime cacheNeed` + `cacheTask.Pre` + `Ok`, via the landed `cacheReads_of_solves` |
| premise kind | class (ii) "cache boundary", but asserted flatly | class (ii) "cache boundary", in the boundary's own vocabulary |

and only **after the frame repair above**. The sequencing is part of the claim:
the shape swap is sound because `cacheTask.Post` now writes the rows it reports,
not because the vocabulary changed.

So the honest framing is: the premise moves from a *flat memory-image
assertion* to a *cache-slot boundary premise* — the shape the lane already
names and the shape the board's D7 vocabulary recognises. Callers of the
bundle then owe `Light.Solves cacheTask …` rather than an
`∀ p < n, ∀ i < n, μ (…) = rows p i` they could not justify.

**LANDED SO FAR (2026-11-10, third pass — the swap itself is NOT landed).**
Green in `CallerUniversalBody`, no `sorryAx`, each `#print axioms` =
[propext, Classical.choice, Quot.sound]: `univCacheArgs` +
`univCacheArgs_val` (the call's four frame values `[n, n, fr + n,
fr + 4n + n²]`, evaluated and proved); `cacheSolves_composed` (the cache's
`Solves` at `callerProgramUniv`, procedure `1 + cacheProc`, body shifted —
`Solves` → `Ends.append` → `Ends.shift_append`); and the clock (`univTn`
takes `cacheTime`; `univTn_le` carries the cache's share as a hypothesis,
without which its conclusion is false). Not landed: the entry body's call,
`UnivBundle`'s conjunct-1 swap, and the derived `hfill`. The obstruction and
the cure are in `CallerUniversalBody.verification.txt`.

Verified signatures (read from the tree at `ea7e86d`, not assumed):

* `CacheFill.cacheTask` — `CacheFill.lean:106`; `Post`'s second conjunct is
  `KeptBut μ μ' fr x.rb (x.P * x.I)`.
* `CacheFill.image_of_kept_post` — `CacheFill.lean:131`; the receipt for the old
  frame shape.
* `CacheFill.cacheReads_of_solves` — `CacheFill.lean:149`; consumes
  `Light.Solves cacheTask cacheProg cacheProc cacheTime cacheNeed`,
  `cacheTask.Pre x μ fr`, `(cacheNeed (size x) (bound x)).Ok lim fr d`.
* `CacheFill.reads_persist` — `CacheFill.lean:175`; carries the two read
  families outside the rows region through `KeptBut μ μ' fr rb (P*I)`, and
  takes the rows family from the write. It has **no `hRR` hypothesis**: the
  rows image is the output, not an input.
* `Seg.of_kept` — `verified/Submission/ThreeSumApsp/Lang/Tasks.lean:75`;
  re-derives `Seg μ' a l` from `Seg μ a l` and `Kept μ μ' fr`. Used **via its
  weaker form** `Seg.of_sameOn` for the `KeptBut` frame (see above).

## What a reviewer should check before this becomes `Verified`

1. Inhabitance. Nobody has exhibited `tests, Tt, rows` discharging `hslot`,
   `hret`, `hident`, `hkept`. Until someone does, the twin is a conditional.
2. Route (c)'s call. The rows image is the only premise with a *cheap
   mechanical* producer left, and it is STILL not wired: `mpBodyUniv` does not
   call the cache, `UnivBundle`'s conjunct 1 is still the flat image, and
   `univSolves` still takes it from the bundle. What IS wired: the cache
   task's frame repair (`ea7e86d`) — without which the call would have renamed
   the premise rather than produced it — plus its three mechanical
   prerequisites (`univCacheArgs_val`, `cacheSolves_composed`, and the clock in
   `univTn`/`univTn_le`). A reviewer should check the frame and the clock's
   hypothesis, and should NOT read the three landed pieces as the call.
3. `hdom` under route (c)'s extra clock.
4. That this file's label is not quietly upgraded to `Verified` on the way to
   the board. It is a Claimed row.

D7's boundary stands throughout: no oracle, no cache body, no (min,+) product
is proved here.
