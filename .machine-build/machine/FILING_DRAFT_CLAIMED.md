# FILING DRAFT — CLAIMED-conditional (ready to hand to the PR author, NOT posted) — FILED 2026-11-10: https://github.com/bigospeedrun/site/pull/22

Lane: `wip-summit-body` (apsp-l1), `/Volumes/Substrate-1/bigo/apsp-l1-work`.
Bench: `.machine-build/machine`, Lean 4.33.1, mathlib `0df444a360eaa60`.
Base of this draft: `9298c40` (the cache call landed end to end), plus the fifth
pass on 2026-11-10 (the socket instantiated, the bundle un-over-named).

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
| `(premises) → EndStatement.APSP.SolvedInTime (2994999/1000000)` is PROVED | **yes** — `ThinMatrix.CallerUniversalBody.twinUniv_of`, and at the one witness term `twinUniv_socket`; axioms `[propext, Classical.choice, Quot.sound]` only, 0 `sorry`, 0 `sorryAx` |
| the premise bundle is INHABITED | **no** — not witnessed. Post-repair it is *consistent with* the premises (no longer refuted); inhabitance is unproved |
| the row is `Verified` | **no** — four named premises remain, three of them D7's boundary |

The one thing that changed on 2026-11-10: the bundle is no longer
**UNSATISFIABLE**. Before the repair its flag conjunct was false and the
reduction was vacuous-as-green. After it, satisfiability is merely unproved.

The second thing that changed later on 2026-11-10 (fifth pass): the bundle is
also no longer **OVER-NAMED**. Its flag conjunct is gone (a tautology at
`k := 0`) and its two resource sockets are DERIVED from one witness term
(`stackSocket_ok`), so the bundle states five things instead of nine, and the
`need` socket is instantiated rather than hypothesised (`twinUniv_socket`).

## The root shape

```lean
theorem twinUniv_of (stage cacheProc : ℕ) (cacheProg restoreProg : Light.Program)
    (cs : Inst) (need : ℕ → ℕ → Light.Need) (cacheTime : ℕ → ℕ → ℕ)
    (hb : UnivBundle stage cacheProc cacheProg restoreProg cs cacheTime need)
    (hcov : NeedCovers need)
    (hn : Light.PolyNeed need)
    (hdom : ∀ κ : Nat, ∃ (k : Nat) (C : Real), ∀ᶠ n : Nat in atTop,
      Light.timeUpTo (Light.Sec3.apTime (univTn cacheTime)) n ((n : Real) ^ (κ : Real)) ≤
        C * AsymptoticCosts.completeCost k n) :
    EndStatement.APSP.SolvedInTime ((2994999 : Rat) / 1000000)
```

and the FILING form, with the socket instantiated at the one witness term:

```lean
theorem twinUniv_socket (stage cacheProc : ℕ) (cacheProg restoreProg : Light.Program)
    (cs : Inst) (cacheTime : ℕ → ℕ → ℕ)
    (hb : UnivBundle stage cacheProc cacheProg restoreProg cs cacheTime univNeed)
    (hdom : ∀ κ : Nat, ∃ (k : Nat) (C : Real), ∀ᶠ n : Nat in atTop,
      Light.timeUpTo (Light.Sec3.apTime (univTn cacheTime)) n ((n : Real) ^ (κ : Real)) ≤
        C * AsymptoticCosts.completeCost k n) :
    EndStatement.APSP.SolvedInTime ((2994999 : Rat) / 1000000)
```

`EndStatement.APSP.SolvedInTime` is the root Submission shape
(`verified/Submission/EndStatement.lean`), the same statement class as the
landed `Race.bound (((1497780383 : Rat) / 500000000))` in
`verified/Submission.lean:25`. The composition is
`ThinMatrix.Twin.race_bound` (`TwinRaceBound.lean:48`) at
`P := callerProgramUniv stage cacheProc cacheProg restoreProg cs`, `p := 0`,
`Tn := univTn cacheTime`.

## The premise list — four named, everything else closed or routed

The four, stated as the ONE theorem that fires (`twinUniv_socket`):

1. **the cache boundary** — `Light.Solves cacheTask cacheProg cacheProc cacheTime univSocket`
   (`UnivBundle`'s conjunct 1). This is D7's cache slot, at the stack-shaped
   socket (see the fifth-pass section). It is the ONLY named premise that is a
   *solver contract* rather than an oracle fact.
2. `hret` — the oracle's return (bundle conjunct 3).
3. `hTt` — the tight clock, `Tt 0 ≤ callerTt x.n` (bundle conjunct 4). Index
   `0`, not `x.n`: `k := 0` is forced by the mask-generic flag budget.
4. `hident` — `MinPlusIdentity`, the head's delivery is every entry (bundle
   conjunct 5).

Plus `hdom` (class (iii)): the `completeCost` domination for `univTn`. It is
the fourth hypothesis of `twinUniv_socket` and is NOT a bundle conjunct.

Everything else is closed: `NeedCovers` and `PolyNeed` are THEOREMS at the
witness term, and the two resource sockets (`hokC`, `hokS`) and the flag budget
(`hflag`) are no longer named at all.

### Named, class (ii) — D7's oracle/cache/identity boundary ("upstream's own")

| # | premise | site | why it cannot be closed here |
|---|---|---|---|
| 1 | **the CACHE boundary** — `Solves cacheTask cacheProg cacheProc cacheTime univSocket` | `CallerUniversalBody.lean:1972` | **The CACHE-BOUNDARY route (c), now WIRED (commit `9298c40`).** The rows image *is* `cacheTask.Post`'s first conjunct, and the entry body CALLS the cache for it: `CacheFill.cacheReads_of_solves` (**landed**, `CacheFill.lean:149`) turns the `Solves` premise into that reads clause, and `reads_persist` (`CacheFill.lean:175`) carries it through the cache's `KeptBut` frame. What remains here is the cache's own body (the L2/L3 cone), which is upstream's — this lane composes against its contract and does not claim it. The socket is DISCLOSED in the fifth-pass section: `univSocket` = zero cells of its own, `(n²+1)(U+1)+1` word, four call levels. |
| 2 | `hret` — the oracle's return: the delivery is the bracket fold seeded at row `t`'s head | `:1967` | the oracle functional chain (shresh's construction) supplies it; not instance arithmetic |
| 3 | `hTt` — the tight clock: `Tt 0 ≤ callerTt x.n` | `:1967` | producer = the re-clocked selection round's `solvedIn`. Not derivable from `taskTime (instanceSize …)` (that is `~100n⁴ ≫ 25n²`). The index is `0`, not `x.n` |
| 4 | `hident` — `MinPlusIdentity` (the head's delivery is every entry) | `:1968` | D7's construction identity |

### Closed outright — the fifth pass turned these into theorems

| premise | site | state |
|---|---|---|
| `hflag` — the flag budget | — | **GONE from the bundle.** At `k := 0` it reads `0 ≤ (flagged _ _).card`; `univSolves` proves it by `fun _ => Nat.zero_le _`. The earlier draft's "no longer a premise at all" is now literally true of the tree |
| `hokC` — the cache's resource socket | — | **DERIVED.** `stackSocket_ok` at `s = n²` from the caller's own `Ok` + `NeedCovers` |
| `hokS` — the stage's resource socket | — | **DERIVED.** `stackSocket_ok` at `s = n² + 4n` — the same lemma, the same instance |
| `NeedCovers need` | — | **PROVED at the witness**: `needCovers_univNeed` (8 numeric facts) |
| `Light.PolyNeed need` | — | **PROVED at the witness**: `polyNeed_univNeed` (`unfold univNeed; poly_need []`) |

### Still argument, not all-written — the bundle's remaining conjuncts

| premise | site | state |
|---|---|---|
| `UnivSlot` at `k := 0` (certified stage socket) | `:1959` (bundle conjunct 2) | closed by the bundle's inhabitant: `stageSlot_any` is **landed**; `hAR`/`hfl` from the prologue's two passes, `hlay` from the layout ring. Its `hRR` was premise 1 and is now supplied by the cache call's post |
| `hkept` — `KeptBut` frame | `:1971` (bundle conjunct 6) | closed by the bundle's inhabitant: write set `{x.c} ⊆ [x.c, x.c+n²)` by `Pre.belowC`; prologue writes at `ab = fr` and above |

### Class (iii) — image arithmetic / domination

| premise | state |
|---|---|
| `hdom` (completeCost domination for `univTn`) | `CallerHdom`/`callerHdom` are **landed** (`CallerStepCount.lean:524`) at `callerTn`. The transfer to `univTn` is the same asymptotics (`O(n² log U)`); **route (c) adds `cacheTime (n²) U`** to `univTn`, and the poly clock is absorbed by the existing `log^{k+R+10}·n²` arm |

## The need witness

One term, and it closes `NeedCovers`'s eight numeric facts and `PolyNeed` — both
are theorems now, not routing notes:

```lean
def univNeed (n U : ℕ) : Light.Need where
  word  := (n*n + 4*n + 5) * (U + 1) + 8      -- the stage socket's word at n²+4n, with an n = 0 floor
  cells := n*n + 4*n + 8                      -- the prologue's five-region stack + 8 cells of slack
  depth := 5                                  -- this body's level + the nested socket's four
```

`cells = n²+4n+8` covers `4n + n² ≤ cells`; `word` dominates `2U+1`, `mpRounds U ≤ 2·log₂U + 6`,
`2^signedLevels U ≤ 4U+2` (from `pow_signedLevels_le`, i.e. the landed
`pow_pred_signed_levels_le` + `two_mul_lt_pow_signed_levels`), and the nested stage
socket's own word `(n²+4n+1)(U+1)+1`; `depth = 5` covers the stage's four levels
one call down.

**Two corrections to the census's literal term, disclosed because they are
corrections.** `FILL1_CENSUS.md` row 9 carries
`⟨(n²+4n+1)(U+1)+8, n²+4n+8, 1⟩`. Both differences matter:

* the `depth = 1` is WRONG for this bundle. The stage's socket is
  `Light.DenseRestartSelectionLoop.need` — `depth := 4` — asked at `d + 1`, so
  the caller's socket must satisfy `d + 1 + 4 ≤ lim.depth`; `depth = 1` gives
  only `d + 1`. (It was "1 ≤ depth" in the coverage list, which is what the
  census checked — the wrong question.)
* the `(n²+4n+1)` bracket is WRONG at `n = 0`: `NeedCovers` quantifies over
  every `MatInst`, and at `n = 0` the census word is `U + 9`, which does not
  dominate `4U + 2` for `U ≥ 3`. The `+5` bracket gives `5U + 13`, which does.
  The `+5` costs nothing (the slack was already there).

`polyNeed_univNeed` is `unfold univNeed; poly_need []` — the same tactic the
stage's own need uses.

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

**LANDED, FOURTH PASS (`9298c40`) — the swap itself IS landed.** The cache
call is in the entry body: `entryBodyUniv = call (cacheProcInP cacheProc)
univCacheArgs Tmp ;; .set Tmp (k 0) ;; mpBodyUniv stage`, `UnivBundle`'s
conjunct 1 is `Solves cacheTask cacheProg cacheProc cacheTime …`, and the rows
image is taken from the cache's post, not asserted on `μ`. The `Tmp` reset's two
steps fold into `univCallB := 16 + 2`. Earlier landed: `univCacheArgs` +
`univCacheArgs_val` (the call's four frame values `[n, n, fr + n, fr + 4n + n²]`,
evaluated and proved); `cacheSolves_composed` (the cache's `Solves` at
`callerProgramUniv`, procedure `1 + cacheProc`, body shifted — `Solves` →
`Ends.append` → `Ends.shift_append`); and the clock (`univTn` takes `cacheTime`;
`univTn_le` carries the cache's share as a hypothesis, without which its
conclusion is false).

## THE FIFTH PASS (2026-11-10, this one) — the socket instantiated, the bundle un-over-named

The bounded brick after the call: `need` and `cacheNeed` are no longer
hypotheses. What changed in `CallerUniversalBody.lean`:

| before | after |
|---|---|
| `UnivBundle … cacheTime cacheNeed need`, conjunct 1 at a free `cacheNeed` | `UnivBundle … cacheTime need`, conjunct 1 at `univSocket` |
| `cacheNeed` a parameter of `univSolves` / `twinUniv_of` | GONE — the socket is `univSocket` |
| `hokC` (cache socket) a bundle conjunct | **derived** by `stackSocket_ok` at `s = n²` |
| `hokS` (stage socket) a bundle conjunct | **derived** by `stackSocket_ok` at `s = n² + 4n` |
| `hflag` a bundle conjunct | **gone** — `0 ≤ card`, proved inline |
| `NeedCovers` a hypothesis, six facts | **theorem** `needCovers_univNeed`, eight facts |
| `PolyNeed` a hypothesis | **theorem** `polyNeed_univNeed` |
| — | **`twinUniv_socket`** — the twin at `need := univNeed`, with only the bundle + `hdom` |

So the bundle states FIVE things (the cache boundary, the stage slot, `hret`,
`hTt`, `hident`, `hkept` — six conjuncts, one of them the cache boundary) where
it stated nine, and the filing theorem's hypothesis list is
`bundle + hdom`.

**THE SOCKET IS DISCLOSED, because it is a claim about a body this lane does not
have.** `univSocket s U = Light.DenseRestartSelectionLoop.need s U` —
`word := (s+1)(U+1)+1`, `cells := 0`, `depth := 4`. `cells = 0` says the cache
writes only BELOW its own free pointer (`cacheTask.Pre` puts the whole rows
region there) and needs no stack of its own; `depth = 4` is the same nesting the
stage's driver has; the word covers the row counts. The caller's socket has
EIGHT cells of slack above the stack (`cells = n²+4n+8` against a stack of
`4n+n²`), so if the L2/L3 cache body needs scratch it can take up to eight cells
for free — that is the one socket adjustment this composition absorbs without
touching anything. Beyond that, the socket is D7's to raise, and raising it is
a visible edit to `univSocket`, not a hidden one.

Receipts: `CallerUniversalBody.verification.txt` (fifth-pass section);
`/private/tmp/apsp_univ7.log` (rc=0, `lake env lean -j1`, 0 errors, 0 `sorry`).

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
   `hret`, `hident`, `hkept`, nor a `cacheProg`/`cacheProc` discharging the
   cache boundary. Until someone does, the twin is a conditional. Note what is
   NO LONGER part of this: `hokC`/`hokS` (derived), `hflag` (tautology),
   `NeedCovers` and `PolyNeed` (proved at the witness).
2. Route (c)'s call. It IS wired now (`9298c40`): `entryBodyUniv` calls the
   cache, `UnivBundle`'s conjunct 1 is the cache's `Solves`, and `hrows`
   comes from the call's post. What a reviewer should check is the SEQUENCING,
   which is where the earlier version was wrong twice: the frame repair
   (`ea7e86d`) had to land first, or the call renames the premise instead of
   producing it. Also check the disclosed socket (fifth-pass section) — that is
   a claim about the cache body, which this lane does not have.
3. The two socket derivations. `stackSocket_ok` is one lemma applied twice; a
   reviewer should confirm that the STAGE's socket really is
   `DenseRestartSelectionLoop.need` at `instanceSize = n² + 4n` (the
   `depth := 4` is what forces `need.depth = 5`, and the census's `depth = 1`
   was wrong), and that `NeedCovers` really is closed at `n = 0`.
4. `hdom` under route (c)'s extra clock.
5. That this file's label is not quietly upgraded to `Verified` on the way to
   the board. It is a Claimed row.

D7's boundary stands throughout: no oracle, no cache body, no (min,+) product
is proved here.
