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
| 1 | **FILL 1 rows image** — `∀ p < x.n, ∀ i < x.n, ((rows p i : ℕ) : ℤ) = μ (fr + x.n + p·x.n + i)` | `CallerUniversalBody.lean:1752` | **The CACHE-BOUNDARY route (c).** The image *is* `cacheTask.Post`'s first conjunct. Two direct routes were measured and both fail (`FILL1_CENSUS.md` §1): the copy pass costs `13n²+6n` against `n+12` slack, and `rb := x.a` contradicts `MatInst.Pre.belowA`. The producer is the cache call: `CacheFill.cacheReads_of_solves` (**landed**, `CacheFill.lean`) turns `Light.Solves cacheTask cacheProg …` into `cachePost_reads`, and `CacheFill.reads_persist` (**landed**) carries it through the cache's `Kept` frame. **The call itself is UNLANDED** — see route (c) state below. The cache slot is already pre-wired in the bundle's shape (`cacheProg : Light.Program` is a parameter). |
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

## What route (c) buys — stated precisely, because it is easy to over-claim

Route (c) does **not** reduce the *count* of named premises. It replaces one
*shape* with another:

| | before | after (route (c)) |
|---|---|---|
| the rows image | a raw assertion about a memory image that **no program step can establish** (both direct routes measured refuted) | a **consequence** of `Light.Solves cacheTask cacheProg cacheProc cacheTime cacheNeed` + `cacheTask.Pre` + `Ok`, via the landed `cacheReads_of_solves` |
| premise kind | class (ii) "cache boundary", but asserted flatly | class (ii) "cache boundary", in the boundary's own vocabulary |

So the honest framing is: the premise moves from a *flat memory-image
assertion* to a *cache-slot boundary premise* — the shape the lane already
names and the shape the board's D7 vocabulary recognises. Callers of the
bundle then owe `Light.Solves cacheTask …` rather than an
`∀ p < n, ∀ i < n, μ (…) = rows p i` they could not justify.

Verified signatures (read, not assumed):

* `CacheFill.cacheReads_of_solves` — `CacheFill.lean:91`; consumes
  `Light.Solves cacheTask cacheProg cacheProc cacheTime cacheNeed`,
  `cacheTask.Pre x μ fr`, `(cacheNeed (size x) (bound x)).Ok lim fr d`.
* `CacheFill.reads_persist` — `CacheFill.lean:112`; carries the reads clause
  through `Kept μ μ' fr` given the `hAR`/`hRR`/`hfl` triple — its second
  conjunct is exactly `hRR`, i.e. the rows image FILL 1 wants.
* `Seg.of_kept` — `verified/Submission/ThreeSumApsp/Lang/Tasks.lean:75`;
  re-derives `Seg μ' a l` from `Seg μ a l` and `Kept μ μ' fr`, which is what
  keeps `MatInst.Pre` alive across the cache's frame using `Pre.belowA`.

## What a reviewer should check before this becomes `Verified`

1. Inhabitance. Nobody has exhibited `tests, Tt, rows` discharging `hslot`,
   `hret`, `hident`, `hkept`. Until someone does, the twin is a conditional.
2. Route (c)'s call. The rows image is the only premise with a *cheap
   mechanical* producer left, and it is not wired yet.
3. `hdom` under route (c)'s extra clock.
4. That this file's label is not quietly upgraded to `Verified` on the way to
   the board. It is a Claimed row.

D7's boundary stands throughout: no oracle, no cache body, no (min,+) product
is proved here.
