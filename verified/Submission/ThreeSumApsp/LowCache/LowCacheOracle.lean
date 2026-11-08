/-
Copyright (c) 2026. APSP port campaign: L2 cache semantics and oracle.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the aligned-cache construction: the polynomial query
  cache and its dense lowering (`CacheDenseLowering`, thin-matrix-results at
  225c37476e31bdb27594953cc1f7738496fb4afc) are the functional spec of this
  layer.
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and the word-RAM compiler
  (`Submission/`) this layer executes in.
- Joshua Wharton (QFEX) — the checked low-row backend and constructor
  contracts this layer reads through; the rational retune.
- Hrishik Sai Bojnal — the verified frontier being refined.

# L2: the shared-cache read/write oracle

The physical cache is the `12 * n` coefficient cells at `base` that
`LowCacheConstructor` fills: block `i : Fin 12` occupies the `n = width * q`
cells from `base + i * n`, addressed inside the block by `degree * q + residue`.

This module lands the *semantics* of the oracle the later layers sit on:

- `addr` and its region bound: every cache cell lies strictly inside the
  `12 * n` region the constructor's precondition reserves.
- `CacheValid`: the cell-level invariant "block `i` at `(degree, residue)`
  holds the erased `rowBlock` payload value" — exactly the per-block values
  M1's constructor postcondition establishes.
- `ctor_valid`: M1's constructor postcondition implies `CacheValid`
  (definitional: the constructor's `blockAddr` plus offset *is* `addr`).
- `valid_read`: a valid cache answers a read with the `rowBlock` value.
- `valid_write_self` / `valid_write_other`: writing a block's cell with the
  value the invariant demands preserves validity everywhere;
  writing one block leaves every other block's cells untouched.
- Block-level disjointness: distinct blocks never share a cell.

Reads and writes are single `.load`/`.store` at `addr`; the physical Light
procedures with their `Solves` contracts live in `LowCacheOracle.lean`.
-/
import Submission.ThreeSumApsp.LowCache.LowCacheConstructor

namespace Light.LowCacheOracle

open Light

/-- Cache geometry: twelve blocks of `width × q` integer cells from `base`. -/
structure Layout where
  base : ℕ
  width : ℕ
  q : ℕ

/-- The length of one cache block: `width * q` cells. -/
def Layout.len (x : Layout) : ℕ := x.width * x.q

/-- The cell `(block i, degree, residue)` of the cache. -/
def addr (x : Layout) (i : Fin 12) (degree : Fin x.width) (residue : Fin x.q) : ℕ :=
  x.base + i.val * x.len + (degree.val * x.q + residue.val)

/-- The constructor's layout, as a cache geometry. -/
def layoutOf (x : LowCacheConstructor.Inst) : Layout :=
  { base := x.base, width := x.width, q := x.q }

/-- The constructor's block address plus an in-block offset is a cache address. -/
theorem addr_eq_block (x : Layout) (i : Fin 12) (degree : Fin x.width)
    (residue : Fin x.q) :
    addr x i degree residue = x.base + i.val * (x.width * x.q) + (degree.val * x.q + residue.val) :=
  rfl

/-- The in-block offset of a degree and a residue is below the block length. -/
theorem offset_lt_len (x : Layout) (degree : Fin x.width) (residue : Fin x.q) :
    degree.val * x.q + residue.val < x.len := by
  have hr := residue.isLt
  have hd := degree.isLt
  calc degree.val * x.q + residue.val < degree.val * x.q + x.q :=
        Nat.add_lt_add_left hr _
    _ = (degree.val + 1) * x.q := by ring
    _ ≤ x.width * x.q := Nat.mul_le_mul_right x.q (by omega)

/-- Every cache cell lies strictly inside the `12 * len` region from `base`. -/
theorem addr_lt (x : Layout) (i : Fin 12) (degree : Fin x.width) (residue : Fin x.q) :
    addr x i degree residue < x.base + 12 * x.len := by
  have hi : i.val + 1 ≤ 12 := by have := i.isLt; omega
  have hoff := offset_lt_len x degree residue
  have hblock : i.val * x.len + x.len ≤ 12 * x.len := by
    calc i.val * x.len + x.len = (i.val + 1) * x.len := by ring
      _ ≤ 12 * x.len := Nat.mul_le_mul_right x.len hi
  unfold addr
  omega

/-- Distinct blocks occupy disjoint cell ranges. -/
theorem blocks_disjoint (x : Layout) {i j : Fin 12} (hne : i ≠ j) :
    i.val * x.len + x.len ≤ j.val * x.len ∨ j.val * x.len + x.len ≤ i.val * x.len := by
  have hv : i.val ≠ j.val := fun h' => hne (Fin.ext h')
  rcases lt_or_gt_of_ne hv with hlt | hlt
  · left
    calc i.val * x.len + x.len = (i.val + 1) * x.len := by ring
      _ ≤ j.val * x.len := Nat.mul_le_mul_right x.len (by omega)
  · right
    calc j.val * x.len + x.len = (j.val + 1) * x.len := by ring
      _ ≤ i.val * x.len := Nat.mul_le_mul_right x.len (by omega)

/-- The cell invariant: every cache cell holds its erased `rowBlock` payload. -/
def CacheValid (x : Layout) (value : Fin 12 → Fin x.width → Fin x.q → ℤ)
    (μ : ℕ → ℤ) : Prop :=
  ∀ (i : Fin 12) (degree : Fin x.width) (residue : Fin x.q),
    μ (addr x i degree residue) = value i degree residue

/-- The constructor's payload, as a cache value table over the layout. -/
def ctorValue (x : LowCacheConstructor.Inst) :
    Fin 12 → Fin (layoutOf x).width → Fin (layoutOf x).q → ℤ :=
  fun i degree residue => LowCacheConstructor.blockValue x i degree residue

/-- M1's constructor postcondition is exactly cache validity. -/
theorem ctor_valid (x : LowCacheConstructor.Inst) (μ : ℕ → ℤ) (fr : ℕ) (r : ℤ)
    (μ' : ℕ → ℤ) (h : LowCacheConstructor.Post x μ fr r μ') :
    CacheValid (layoutOf x) (ctorValue x) μ' := by
  obtain ⟨-, hvals⟩ := h
  intro i degree residue
  show μ' (x.base + i.val * (x.width * x.q) +
    (degree.val * x.q + residue.val)) = LowCacheConstructor.blockValue x i degree residue
  rw [← x.shape]
  exact hvals i degree residue

/-- A valid cache answers a read with the `rowBlock` value. -/
theorem valid_read (x : Layout) (value : Fin 12 → Fin x.width → Fin x.q → ℤ)
    (μ : ℕ → ℤ) (h : CacheValid x value μ) (i : Fin 12)
    (degree : Fin x.width) (residue : Fin x.q) :
    μ (addr x i degree residue) = value i degree residue :=
  h i degree residue

/-- Writing a cell of another block leaves this cell untouched. -/
theorem other_block_untouched (x : Layout) {i j : Fin 12} (hne : i ≠ j)
    (μ : ℕ → ℤ) (v : ℤ) (degree : Fin x.width) (residue : Fin x.q) :
    Function.update μ (addr x j degree residue) v (addr x i degree residue) =
      μ (addr x i degree residue) := by
  apply Function.update_of_ne
  intro heq
  have ho := offset_lt_len x degree residue
  rcases blocks_disjoint x hne with h | h
  · unfold addr at heq
    omega
  · unfold addr at heq
    omega

/-- Two in-block offsets of the same block determine the degree and residue. -/
private theorem offset_inj (x : Layout) (hq : 0 < x.q) {a b r s : ℕ}
    (hr : r < x.q) (hs : s < x.q) (h : a * x.q + r = b * x.q + s) :
    a = b ∧ r = s := by
  have hdiv : (a * x.q + r) / x.q = (b * x.q + s) / x.q := by rw [h]
  rw [Nat.mul_comm a x.q, Nat.mul_comm b x.q,
    Nat.mul_add_div hq, Nat.mul_add_div hq,
    Nat.div_eq_of_lt hr, Nat.div_eq_of_lt hs, Nat.add_zero, Nat.add_zero] at hdiv
  refine ⟨hdiv, ?_⟩
  subst hdiv
  omega

/-- Writing a cell with the value the invariant demands preserves validity. -/
theorem valid_write_self (x : Layout) (value : Fin 12 → Fin x.width → Fin x.q → ℤ)
    (μ : ℕ → ℤ) (h : CacheValid x value μ) (i : Fin 12)
    (degree : Fin x.width) (residue : Fin x.q) :
    CacheValid x value (Function.update μ (addr x i degree residue) (value i degree residue)) := by
  intro i' degree' residue'
  by_cases hsame : i' = i ∧ degree' = degree ∧ residue' = residue
  · obtain ⟨rfl, rfl, rfl⟩ := hsame
    exact Function.update_self ..
  · have haddr : addr x i' degree' residue' ≠ addr x i degree residue := by
      intro heq
      apply hsame
      have hq : 0 < x.q := by
        rcases Nat.eq_zero_or_pos x.q with h0 | h0
        · exact absurd residue.isLt (by simp [h0])
        · exact h0
      have hoff : degree'.val * x.q + residue'.val = degree.val * x.q + residue.val := by
        rcases Nat.lt_trichotomy i'.val i.val with hlt | heq' | hgt
        · exfalso
          have hr := offset_lt_len x degree' residue'
          have hb : i'.val * x.len + x.len ≤ i.val * x.len := by
            calc i'.val * x.len + x.len = (i'.val + 1) * x.len := by ring
              _ ≤ i.val * x.len := Nat.mul_le_mul_right x.len (by omega)
          unfold addr at heq
          omega
        · have hii : i' = i := Fin.ext heq'
          subst hii
          unfold addr at heq
          omega
        · exfalso
          have hr := offset_lt_len x degree residue
          have hb : i.val * x.len + x.len ≤ i'.val * x.len := by
            calc i.val * x.len + x.len = (i.val + 1) * x.len := by ring
              _ ≤ i'.val * x.len := Nat.mul_le_mul_right x.len (by omega)
          unfold addr at heq
          omega
      obtain ⟨hdeg, hres⟩ := offset_inj x hq residue'.isLt residue.isLt hoff
      -- recover the block equality from the address equality's block term
      have hii : i' = i := by
        rcases Nat.lt_trichotomy i'.val i.val with hlt | heq' | hgt
        · exfalso
          have hr := offset_lt_len x degree' residue'
          have hb : i'.val * x.len + x.len ≤ i.val * x.len := by
            calc i'.val * x.len + x.len = (i'.val + 1) * x.len := by ring
              _ ≤ i.val * x.len := Nat.mul_le_mul_right x.len (by omega)
          unfold addr at heq
          omega
        · exact Fin.ext heq'
        · exfalso
          have hr := offset_lt_len x degree residue
          have hb : i.val * x.len + x.len ≤ i'.val * x.len := by
            calc i.val * x.len + x.len = (i.val + 1) * x.len := by ring
              _ ≤ i'.val * x.len := Nat.mul_le_mul_right x.len (by omega)
          unfold addr at heq
          omega
      exact ⟨hii, Fin.ext hdeg, Fin.ext hres⟩
    rw [Function.update_of_ne haddr]
    exact h i' degree' residue'

/-- Writing a cell of block `j` leaves block `i`'s cells (i ≠ j) valid. -/
theorem valid_write_other (x : Layout) (value : Fin 12 → Fin x.width → Fin x.q → ℤ)
    (μ : ℕ → ℤ) (h : CacheValid x value μ) {i j : Fin 12} (hne : i ≠ j)
    (degree : Fin x.width) (residue : Fin x.q) (v : ℤ) :
    Function.update μ (addr x j degree residue) v (addr x i degree residue) =
      value i degree residue := by
  rw [other_block_untouched x hne μ v degree residue]
  exact h i degree residue




/-- After the constructor, a cache read returns the erased `rowBlock` payload. -/
theorem ctor_read_eq_blockValue (x : LowCacheConstructor.Inst) (μ : ℕ → ℤ) (fr : ℕ)
    (r : ℤ) (μ' : ℕ → ℤ) (h : LowCacheConstructor.Post x μ fr r μ')
    (i : Fin 12) (degree : Fin x.width) (residue : Fin x.q) :
    μ' (addr (layoutOf x) i degree residue) = LowCacheConstructor.blockValue x i degree residue :=
  ctor_valid x μ fr r μ' h i degree residue

#print axioms addr_lt
#print axioms ctor_valid
#print axioms valid_read
#print axioms valid_write_self
#print axioms valid_write_other
#print axioms ctor_read_eq_blockValue

end Light.LowCacheOracle
