import DenseCompositeLedger
import ThreeSumApsp.Lang.Lib.Seg

/-!
Copyright (c) 2026. APSP port campaign: L6(c) min-plus Post consumption.

Credits (constructions first, filer last):
- shresh (shreshth-s) — the composite-incidence reduction whose interior this
  module delivers to the min-plus caller
  (thin-matrix-results @ 225c37476e31bdb27594953cc1f7738496fb4afc).
- Josh Alman and Virginia Vassilevska Williams — source paper arXiv:2610.06783.
- Li Xuanji — the verified ten-term construction and word-RAM compiler
  (`Submission/`) whose Light language these procedures execute in.
- Joshua Wharton (QFEX) — the checked selection round, restart-loop driver,
  and caller this module sits under.
- Hrishik Sai Bojnal — the verified frontier being refined.

# L6(c): the composite-incidence consumption at the `mpTask` Post

`Light.mpTask`'s Post is `Seg μ' x.c (minPlusList x.n x.A x.B) ∧ KeptBut μ μ'
fr x.c (x.n * x.n)` — and the `hs` slot of the canonical adapter awaits a
solver for it. The min-plus caller composes that solver from interior
deliveries; the restart-loop certification is one interior. This module
states the delivery in the Post's own shapes, consumed from `cert_post`
(nothing re-proved):

- `cert_mask_seg` — the cleared mask as a `Seg` over its materialized list at
  the flag region (the `Seg` half of the Post's shapes);
- `cert_keptBut` — the memory frame in `KeptBut`'s `SameOn` form over the
  caller's composed regions: below the free pointer, nothing changes outside
  the three written regions;
- `cert_pop` — the pool scalar the certification finish consumes;
- `mpPost_interior` — the packaged interior record.

BOUNDARY (unchanged): the (min,+)-product output itself — `Seg μ' c
(minPlusList …)` — is the enclosing caller's obligation assembled over this
interior; no bit-cost → Light-step translation is claimed here (D7). The
`hs` slot is fed, not closed, by this file.
-/

namespace Light.DenseMinPlusPost

open Light DenseRestartSelectionLoop DenseCompositeCaller DenseCompositeLedger

/-! ## The mask as a Seg -/

/-- The cleared mask, materialized over the candidate range: the list the
`Seg` half of the consumption reads. -/
def maskList (P : ℕ) (remaining : ℕ → Bool) (cs : List ℕ) : List ℤ :=
  (List.range P).map fun p => DenseArgminPass.bit (maskCleared cs.toFinset remaining p)

/-- The cleared mask delivered in `Seg` shape: the certified post's flag
clause, read pointwise through the materialized list. -/
theorem cert_mask_seg_of {P : ℕ} {remaining : ℕ → Bool} {cs : List ℕ}
    {μ' : ℕ → ℤ} {mb : ℕ}
    (hflags : ∀ p < P, μ' (mb + p) = DenseArgminPass.bit (maskCleared cs.toFinset remaining p)) :
    Seg μ' mb (maskList P remaining cs) := by
  intro i hi
  have hmap : (maskList P remaining cs)[i] =
      DenseArgminPass.bit (maskCleared cs.toFinset remaining i) := by
    simp only [maskList, List.getElem_map, List.getElem_range]
  rw [hmap]
  have hP : i < P := by simpa [maskList] using hi
  exact hflags i hP

/-- The certified mask, packaged: the chosen restarts with their `Seg`-shaped
flag delivery. -/
theorem cert_mask_seg {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb : ℕ} {μ μ' : ℕ → ℤ}
    (hpost : Post (callSite P k I h active remaining rows ab rb sb mb bb) μ μ') :
    ∃ cs : List ℕ, cs.length = k ∧ cs.Nodup ∧
      (∀ c ∈ cs, c < P ∧ remaining c = true) ∧
      Seg μ' mb (maskList P remaining cs) := by
  obtain ⟨cs, hlen, hnd, hmem, hflags, -, -, -⟩ := hpost
  exact ⟨cs, hlen, hnd, hmem, cert_mask_seg_of hflags⟩

/-! ## The frame in the Post's shape -/

/-- The composite-incidence frame in the `mpTask`-Post shape (`KeptBut`'s
`SameOn` form, over the three regions the driver writes): below the free
pointer, nothing changes outside the scores, base and remaining regions. The
enclosing caller composes its output region with these three. -/
theorem cert_keptBut {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr : ℕ} {μ μ' : ℕ → ℤ}
    (hpost : Post (callSite P k I h active remaining rows ab rb sb mb bb) μ μ') :
    SameOn (fun x => x < fr ∧ Outside sb P x ∧ Outside bb I x ∧ Outside mb P x) μ μ' := by
  obtain ⟨cs, -, -, -, -, hframe, -, -⟩ := hpost
  intro x hx
  exact hframe x ⟨hx.2.1, hx.2.2.1, hx.2.2.2⟩

/-! ## The pool scalar -/

/-- The certification finish's pool scalar, packaged with the chosen list it
counts from. -/
theorem cert_pop {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb : ℕ} {μ μ' : ℕ → ℤ}
    (hpost : Post (callSite P k I h active remaining rows ab rb sb mb bb) μ μ') :
    ∃ cs : List ℕ, cs.length = k ∧ cs.Nodup ∧ (∀ c ∈ cs, c < P ∧ remaining c = true) ∧
      ((Finset.range P).filter (fun p => maskCleared cs.toFinset remaining p)).card
        = (flagged P remaining).card - k := by
  obtain ⟨cs, hlen, hnd, hmem, -, -, -, -⟩ := hpost
  exact ⟨cs, hlen, hnd, hmem, cert_pool hlen hnd hmem⟩

/-! ## The packaged interior record -/

/-- The composite-incidence consumption record at the n×n call site: the
interior delivery the min-plus caller's `hs` assembly composes. From the
caller's five physical reads, the greedy premise and the resource
clearance, the certified final memory carries the chosen restarts, the mask
as a `Seg`, the pool scalar, and the frame in the `KeptBut` shape. -/
theorem mpPost_interior {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr : ℕ} {lim : Limits} {d : ℕ}
    {μ : ℕ → ℤ} {Prog : Program}
    (hAR : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hRR : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hbound : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hfl : ∀ p < P, μ (mb + p) = DenseArgminPass.bit (remaining p))
    (hR : k ≤ (flagged P remaining).card)
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)])
    (hok : (need (instanceSize (callSite P k I h active remaining rows ab rb sb mb bb))
      (callSite P k I h active remaining rows ab rb sb mb bb).height).Ok lim fr d) :
    ∃ μ' : ℕ → ℤ, ∃ cs : List ℕ,
      cs.length = k ∧ cs.Nodup ∧ (∀ c ∈ cs, c < P ∧ remaining c = true) ∧
      Seg μ' mb (maskList P remaining cs) ∧
      ((Finset.range P).filter (fun p => maskCleared cs.toFinset remaining p)).card
        = (flagged P remaining).card - k ∧
      SameOn (fun x => x < fr ∧ Outside sb P x ∧ Outside bb I x ∧ Outside mb P x) μ μ' := by
  have hpost := cert_post (Prog := ([] : Program)) hAR hRR hbound hfl hR hlay hok
  obtain ⟨μ', cs, hlen, hnd, hmem, hflags, hsame, -, -⟩ := hpost
  exact ⟨μ', cs, hlen, hnd, hmem, cert_mask_seg_of hflags, cert_pool hlen hnd hmem,
    fun x hx => hsame x ⟨hx.2.1, hx.2.2.1, hx.2.2.2⟩⟩

#print axioms Light.DenseMinPlusPost.maskList
#print axioms Light.DenseMinPlusPost.cert_mask_seg_of
#print axioms Light.DenseMinPlusPost.cert_mask_seg
#print axioms Light.DenseMinPlusPost.cert_keptBut
#print axioms Light.DenseMinPlusPost.cert_pop
#print axioms Light.DenseMinPlusPost.mpPost_interior

end Light.DenseMinPlusPost
