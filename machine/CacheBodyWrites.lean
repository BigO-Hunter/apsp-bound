import MinPlusCaller
import CallerWrites
import CallerFill1

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 1 — the cache body's
Light statements (the write-side slice).

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence construction and the oracle
  functional chain (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  Light language is the pinned Anthropic statement's.
- Joshua Wharton (QFEX) — the canonical adapter arrangement, the refinement
  parameters, and the machine-obligations record.
- Hrishik Sai Bojnal — the verified frontier being refined and the refined
  numerical certificate this body targets.

# Fill 1's cache-body statements: the count-writes at the cache registers

- `cacheWritesEntry` / `cacheWritesRow` — the per-(p, i) count-write
  statements at the cache's own register map: the store into the cache's
  row-base + entry-offset (the `mpBodyWritesEntry`/`mpBodyWritesRow`
  store-pattern from `CallerWrites`, byte-formed like the landed
  `DenseScoreTablePass.roundBody`'s store), the row-loop unrolled over
  the entry indices. Register map: `RbBase` = the cache's row base (the
  rb region, slice 1's `callerRb`), `Cand` = the candidate index p,
  `Cnt` = the count cell's source register.
- `CellContentTarget` — the named delivery target: the cache program's
  body run delivers `CellContent` — the per-cell contract whose
  correctness rides the `DenseOracleCorrect`-conditioned chain
  (upstream's own shape; the L2/L3 cone's content — the score-table pass
  + the BinaryArrayFFT cyclic path — is the board-side port's content,
  CacheFill's recorded deferral, unchanged). The cone-port's execution
  proof discharges this target.

THE REMAINING SLICES: the L2/L3 cone's cache-body port (board-side); the
writes' execution derivation (the Seg half of mpBody's run); the step
count for `CallerHdom`. Until they land, `CallerTarget(Layered)` and the
twin stay conditional — honestly: no solver is postulated, no (min,+)
product is claimed. D7's boundary stands: the oracle premise and the
content contracts are premises, never claimed as proved.
-/

namespace ThinMatrix.CacheBodyWrites

open ThreeSumApsp Light
  ThinMatrix.CallerWrites ThinMatrix.CallerFill1

/-! ## The count-writes at the cache's own register map -/

/-- The per-(p, i) count-write: store the count cell's value into the
cache's entry address `RbBase + p * I + i` — the `v Out +' v Idx`
addressing shape at the cache's register map. -/
def cacheWritesEntry (RbBase Idx Cnt : ℕ) : Light.Stmt :=
  mpBodyWritesEntry RbBase Idx Cnt

/-- The per-candidate count-write skeleton: the entries of one cache row
(candidate p), stored sequentially over the entry indices `p * I + j`
for `j < I` — the row-loop unrolled. Register map: `RbBase` = the
cache's row base, `CntBase` = the count cells' base. -/
def cacheWritesRow (RbBase CntBase : ℕ) (I : ℕ) (p : ℕ) : Light.Stmt :=
  (List.range I).foldl
    (fun s j => Light.Stmt.seq s
      (cacheWritesEntry RbBase (p * I + j) (CntBase + j))) Light.Stmt.skip

/-- The cache-body write skeleton: the count-writes for all P candidate
rows, sequenced — the p-loop unrolled over the row statements. SHAPE
ONLY: the count cells' COMPUTATION (the L2/L3 cone's score-table pass +
the BinaryArrayFFT cyclic path) is the board-side port's content —
CacheFill's recorded deferral; the cone-port's execution proof
discharges `CellContentTarget`. -/
def cacheBodyWrites (RbBase CntBase : ℕ) (P I : ℕ) : Light.Stmt :=
  (List.range P).foldl
    (fun s p => Light.Stmt.seq s (cacheWritesRow RbBase CntBase I p))
    Light.Stmt.skip

/-! ## The delivery target (the cone-port's execution proof discharges it) -/

/-- THE DELIVERY TARGET: the cache body's run (over the count-writes
with the cone's computed counts in the `CntBase` cells) delivers
`CellContent` — the per-cell contract the EncodingIdentity derivation
consumes. The cone-port's execution proof discharges this target. -/
def CellContentTarget (P I : ℕ) (active : ℕ → Bool) (rows : ℕ → ℕ → ℕ)
    (Opos : ℕ → ℕ → Prop) (RbBase CntBase : ℕ) (R : Light.Program) : Prop :=
  ∀ (lim : Limits) (d : ℕ) (μ : ℕ → ℤ) (fr : ℕ),
    Ends lim ([cacheBodyWrites RbBase CntBase P I] ++ R) d
      (cacheBodyWrites RbBase CntBase P I)
      ⟨frame (List.replicate 9 (fr : ℤ)), μ⟩ (I * P + 2 * P)
      (fun σ' => CellContent P I active rows Opos)

#print axioms cacheWritesEntry
#print axioms cacheWritesRow

end ThinMatrix.CacheBodyWrites
