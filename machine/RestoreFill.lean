import MinPlusCaller
import MinPlusReduction

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 2 — the finish/restore
pass's task contract.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the sentinel-encoded min-plus assembly: `encode`,
  `encodeMatrix`, `restore`, `OptionalMinimizes`, `restore_correct`
  (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler; the
  Light language these procedures execute in.
- Joshua Wharton (QFEX) — the canonical adapter arrangement and the checked
  selection round / restart-loop driver the scheduled rounds instantiate.
- Hrishik Sai Bojnal — the verified frontier being refined.

# FILL 2: the finish/restore pass's task contract

The restore is pointwise: upstream `restore C W j = if 2*W < C j then none
else some (C j)`, and its sentinel encoding is `encode S (restore C W j) =
if 2*W < C j then S else C j` (`encode_restore`, proved here) — the exact
value the Light restore program writes. Under the caller's premises
(`FiniteBound` content and the `3W < S` sentinel gap, byte-shaped to
upstream `restore_correct`'s hypotheses), the functional chain closes
`OptionalMinimizes A B (restore C W)` — the (min,+) semantics — while the
Light task pins the machine execution side:

- `RestoreInst` / `restoreTask` — read the raw accumulated cells at `cin`,
  write their sentinel-encoded restores at `cout`, keep everything else
  (`Kept`). The BODY is the L2/L3 cone's obligation; the contract is what
  the caller composes with.
- `restoreReads_of_solves` — the proved extraction (FILL 1's clone): the
  program's `Light.Solves` delivers the restored-region post and the `Kept`
  frame.

D7's boundary stands: the (min,+) product itself is never claimed — the
`OptionalMinimizes` semantics ride upstream's `restore_correct`.
-/

namespace ThinMatrix.RestoreFill

open Filter Asymptotics ThreeSumApsp ThreeSumApsp.WordRam
  ThinMatrix.MinPlusReduction
  Light.DenseRestartSelectionLoop Light

/-! ## The restored cell value — bridged to upstream's pointwise restore -/

/-- The restored cell: the sentinel encoding of upstream's pointwise
`restore` — `encode S (restore C W j) = restoreVal W S (C j)`. -/
def restoreVal (W S : ℤ) (c : ℤ) : ℤ := if 2 * W < c then S else c

/-- The bridge to the functional chain: the Light cell value IS the sentinel
encoding of upstream's pointwise restore. -/
theorem encode_restore (S W : ℤ) (c : ℤ) :
    encode S (restore (fun _ : ℕ => c) W 0 0) = restoreVal W S c := by
  by_cases h : 2 * W < c
  · unfold restoreVal restore encode
    simp [h]
  · unfold restoreVal restore encode
    simp [h]

/-! ## The restore program's Light task -/

/-- The restore program's instance: `m` raw accumulated cells at `cin`,
their sentinel-encoded restores written at `cout`, everything else kept.
`W` is the content bound, `S` the sentinel (upstream `restore_correct`'s own
`3W < S` gap). -/
structure RestoreInst where
  m : ℕ
  W : ℕ
  S : ℕ
  cin : ℕ
  cout : ℕ
  fr : ℕ
  C : ℕ → ℤ

/-- The restore program's task: pointwise sentinel-encode the accumulated
cells into the output region and keep everything else. The body is the
L2/L3 cone's obligation; the contract is what the caller composes with. -/
def restoreTask : Task where
  Inst := RestoreInst
  size x := x.m
  bound x := x.m
  args x := [x.m, x.W, x.S, x.cin, x.cout]
  Pre x _μ fr := x.cin + x.m ≤ x.cout ∧ x.cout + x.m ≤ fr ∧
    (∀ j < x.m, -(x.W : ℤ) ≤ x.C j ∧ x.C j ≤ (x.W : ℤ))
  Post x μ fr _r μ' :=
    (∀ j < x.m, μ' (x.cout + j) = restoreVal (x.W : ℤ) (x.S : ℤ) (x.C j)) ∧
    Kept μ μ' fr

/-- The proved extraction: the restore program's `Light.Solves` delivers
the restored-region post and the `Kept` frame. -/
theorem restoreReads_of_solves {restoreProg : Light.Program} {restoreProc : ℕ}
    {restoreTime : ℕ → ℕ → ℕ} {restoreNeed : ℕ → ℕ → Light.Need}
    (hs : Light.Solves restoreTask restoreProg restoreProc restoreTime restoreNeed)
    {x : RestoreInst} {μ : ℕ → ℤ} {lim : Limits} {d : ℕ}
    (hpre : restoreTask.Pre x μ x.fr)
    (hok : (restoreNeed (restoreTask.size x) (restoreTask.bound x)).Ok lim x.fr d) :
    ∃ body : Stmt, restoreProg[restoreProc]? = some body ∧
      Ends lim restoreProg d body
        ⟨frame (restoreTask.args x ++ [(x.fr : ℤ)]), μ⟩
        (restoreTime (restoreTask.size x) (restoreTask.bound x))
        fun σ' => (∀ j < x.m, σ'.mem (x.cout + j) = restoreVal (x.W : ℤ) (x.S : ℤ) (x.C j)) ∧
          Kept μ σ'.mem x.fr := by
  obtain ⟨body, hb, hrun⟩ := hs
  have h2 := hrun [] lim d x μ x.fr hpre hok
  rw [List.append_nil] at h2
  exact ⟨body, hb, h2⟩

/-! ## The functional linkage — named, not claimed

Under the caller's premises the functional chain closes the (min,+)
semantics of the restored region: upstream `restore_correct` gives
`OptionalMinimizes A B (restore C W)` from `FiniteBound A W`, `FiniteBound
B W` and `Minimizes (encodeMatrix A S) (encodeMatrix B S) C`; each Light
cell the restore program writes is `encode S (restore C W j)`
(`encode_restore`). The scheduling of the accumulated cells into `A`/`B`/`T`
positions is FILL 3's composition content. -/

#print axioms restoreVal
#print axioms encode_restore
#print axioms restoreReads_of_solves

end ThinMatrix.RestoreFill
