import MinPlusCaller
import DenseScoreTablePass
import CallerCount
import CallerFill1

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the composition
session: the count-cell transport and the EncodingIdentity at the
FFT-table socket.

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

# The composition session: the count-cell transport and the FFT-table socket

- `countCell_of_roundtrip` — the socket-transport: the count-cell ↔
  recovered-entry socket (`hcell`, the exponential-encoding socket —
  DATAFLOW.md's named sub-design, upstream's own shape, never claimed)
  composed with the round-trip socket (`hrt`: the recovered entries = the
  FFT-computed table) yields the count-cell ↔ FFT-table socket —
  discharging `CountCellOfFft` GIVEN the two named sockets.
- `encodingIdentity_of_countCell` — the EncodingIdentity at the
  FFT-table socket: the derivation of `encodingIdentity_of_content`'s
  proof-shape with the rows-inequality socket swapped for the FFT-table
  nonzeroness socket — the count-vs-existence bridge at the ℕ level,
  identical route (the entries' nonnegativity by type).

THE REMAINING SESSIONS: the exponential×FFT composition at one cell (the
premise-shapes' production — DATAFLOW.md's named sub-design); the Seg-
half assembly (the bracket accumulation via `refineStep` — the writes'
shapes landed); the step count for `CallerHdom`. D7's boundary stands:
the encoding identity and the oracle premise are premises, never claimed
as proved; no (min,+) product is claimed in this module.
-/

namespace ThinMatrix.CallerCountCompose

open ThreeSumApsp Light.DenseScoreTablePass
  ThinMatrix.CallerCount ThinMatrix.CallerEncoding ThinMatrix.CallerFill1

/-- THE SOCKET-TRANSPORT: the exponential-encoding socket (`hcell` —
DATAFLOW.md's named sub-design, never claimed) composed with the
round-trip socket (`hrt` — the recovered entries = the FFT-computed
table) yields the count-cell ↔ FFT-table socket (`CountCellOfFft`'s
shape). -/
theorem countCell_of_roundtrip
    {P I : ℕ} {active : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {recov fftTable : ℕ → ℕ → ℕ}
    (hcell : ∀ p < P, ∀ i < I, (rows p i ≠ 0 ↔ recov p i ≠ 0))
    (hrt : ∀ p < P, ∀ i < I, recov p i = fftTable p i)
    (p : ℕ) (hp : p < P) (i : ℕ) (hi : i < I) :
    (rows p i ≠ 0 ↔ fftTable p i ≠ 0) := by
  rw [hcell p hp i hi, hrt p hp i hi]

/-- THE ENCODINGIDENTITY AT THE FFT-TABLE SOCKET: the derivation of
`encodingIdentity_of_content`'s proof-shape with the rows-inequality
socket swapped for the FFT-table nonzeroness socket — the
count-vs-existence bridge at the ℕ level, identical route (the entries'
nonnegativity by type). -/
theorem encodingIdentity_of_countCell
    {P I : ℕ} {active : ℕ → Bool} {answer : ℕ → Bool}
    {rows fftTable : ℕ → ℕ → ℕ}
    (hcell : ∀ p < P, ∀ i < I, (rows p i ≠ 0 ↔ fftTable p i ≠ 0))
    (hans : AnswerOr P I active answer
      (fun p i => fftTable p i ≠ 0)) :
    EncodingIdentity P I active rows answer := by
  intro p hp
  have hcell := hcell p hp
  have hans := hans p hp
  constructor
  · intro hne
    rw [scores_eq_sum] at hne
    obtain ⟨i, hi, hne'i⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hai : active i = true := by
      by_cases h : active i = true
      · exact h
      · rw [if_neg h] at hne'i
        exact absurd hne'i (by simp)
    have hfft : fftTable p i ≠ 0 := by
      rw [if_pos hai] at hne'i
      exact (hcell i (Finset.mem_range.mp hi)).1 hne'i
    exact hans.2 ⟨i, Finset.mem_range.mp hi, hai, hfft⟩
  · intro htrue
    obtain ⟨i, hi, hai, hfft⟩ := hans.1 htrue
    have hrne : rows p i ≠ 0 := (hcell i hi).2 hfft
    intro hzero
    rw [scores_eq_sum] at hzero
    have hge : (if active i then rows p i else 0) ≤
        ∑ j ∈ Finset.range I, (if active j then rows p j else 0) :=
      Finset.single_le_sum (f := fun j => (if active j then rows p j else 0))
        (fun j _ => Nat.zero_le _) (Finset.mem_range.2 hi)
    rw [if_pos hai, hzero] at hge
    omega

#print axioms countCell_of_roundtrip
#print axioms encodingIdentity_of_countCell

end ThinMatrix.CallerCountCompose
