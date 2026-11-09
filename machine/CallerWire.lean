import MinPlusCaller
import CallerWrites
import CallerRounds
import CallerRun
import CallerChain

/-!
Copyright (c) 2026. APSP port campaign: D7(b) FILL 3 — the wire-lemma's
session: the fold's equations, the schedule's round-splitting, the store
realization, the delivery socket, and the wire composition.

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

# The wire-lemma: what the machine semantics deliver, and what remains

The wire-lemma (`CallerRun.BracketFinal`) — the body's run's bracket cell
(0,0) = the `bracketAccumulate` fold — decomposes as:

1. THE PURE CORE (all proved here, axiom-free):
   - `bracketAccumulate_zero` / `bracketAccumulate_step` — the fold's
     recursion equations.
   - `bodyUpTo` / `bodyUpTo_succ` — the schedule's round-splitting;
     `mpBodyWithWrites` = the full-length prefix.
   - `rowUpTo` / `rowUpTo_succ` — the row's entry-splitting.
   - `store_writes` / `store_keeps` — the store's memory semantics: one
     store writes its own cell and keeps every other cell and every
     register (the `Exec.store` rule read off the state).
   - `rowUpTo_keep` / `rowUpTo_writesA` — the row's run keeps a pinned
     cell (every entry's address away from it), or writes it once at the
     first entry and keeps it after.
   - `roundZero_writes` / `roundKeeps` — the per-round slice: round 0
     writes the delivered fold into cell (0,0); every later round keeps
     it (the call keeps the cell, the row's stores are pinned away).
   - `wire_runs` / `wire_compose` / `bracketFinal_of_pins` — THE WIRE:
     the schedule's run threads the state and delivers the fold into
     cell (0,0) — `CallerRun.BracketFinal` at the pinned states.

2. THE DELIVERY SOCKET (named, never claimed):
   - `StageDelivers` — the stage call at round t delivers the row's
     refined value (the fold seeded by the row cell's current value)
     into the source register, keeps cell (0,0), and keeps the pinning.
     The body's per-round machine-computation contract (DATAFLOW.md's
     remaining sub-design). The min-plus identity of the delivered
     values rides the oracle premise — D7's boundary: the oracle is a
     premise, never claimed as proved. The socket's proof session is
     named, not landed.
   - The pinning (`WirePins`) and the budgets (`Bw`, `B`) are the
     layout's obligations — their discharge is the layout session
     (named). The start value (the cells at 0) is the initialization's
     obligation (named).

Until the socket and the pinning discharge, `CallerTarget(Layered)` and
the twin stay conditional — honestly: no solver is postulated, no
(min,+) product is claimed.
-/

namespace ThinMatrix.CallerWire

open ThreeSumApsp ThreeSumApsp.Spec
  Light.DenseRestartSelectionLoop Light
  ThinMatrix.MinPlusReduction ThinMatrix.MinPlusCaller
  ThinMatrix.CallerWrites ThinMatrix.CallerRounds ThinMatrix.CallerRun

/-! ## The fold's equations (pure) -/

theorem bracketAccumulate_zero (C : ℤ) (tests : ℕ → Bool × Bool) :
    bracketAccumulate C tests 0 = C := rfl

theorem bracketAccumulate_step (C : ℤ) (tests : ℕ → Bool × Bool) (t : ℕ) :
    bracketAccumulate C tests (t + 1) =
      refineWrite (bracketAccumulate C tests t) (tests t).1 (tests t).2 := by
  unfold bracketAccumulate
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-! ## The schedule's round-splitting (pure) -/

/-- The body's first-t-rounds prefix. -/
def bodyUpTo (stage Out : ℕ) (x : MatInst) (W t : ℕ) : Light.Stmt :=
  (List.range t).foldl
    (fun s u => Light.Stmt.seq s (roundSlice stage Out x u)) Light.Stmt.skip

theorem bodyUpTo_zero (stage Out : ℕ) (x : MatInst) (W : ℕ) :
    bodyUpTo stage Out x W 0 = Light.Stmt.skip := rfl

theorem bodyUpTo_succ (stage Out : ℕ) (x : MatInst) (W t : ℕ) :
    bodyUpTo stage Out x W (t + 1) =
      Light.Stmt.seq (bodyUpTo stage Out x W t) (roundSlice stage Out x t) := by
  unfold bodyUpTo
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem mpBodyWithWrites_eq (stage Out : ℕ) (x : MatInst) (W : ℕ) :
    mpBodyWithWrites stage Out x W = bodyUpTo stage Out x W (mpRounds W) := rfl

/-! ## The row's entry-splitting (pure) -/

/-- The row's first-j-entries prefix (the row-t entries of the
`mpBodyWritesRow Out Base x t` layout: store into `v Out +' v (t * x.n + u)`
the register `v (Base + u)` — the delivery register's family). -/
def rowUpTo (Out Base : ℕ) (x : MatInst) (t j : ℕ) : Light.Stmt :=
  (List.range j).foldl
    (fun s u => Light.Stmt.seq s
      (mpBodyWritesEntry Out (t * x.n + u) (Base + u))) Light.Stmt.skip

theorem rowUpTo_zero (Out Base : ℕ) (x : MatInst) (t : ℕ) :
    rowUpTo Out Base x t 0 = Light.Stmt.skip := rfl

theorem rowUpTo_succ (Out Base : ℕ) (x : MatInst) (t j : ℕ) :
    rowUpTo Out Base x t (j + 1) =
      Light.Stmt.seq (rowUpTo Out Base x t j)
        (mpBodyWritesEntry Out (t * x.n + j) (Base + j)) := by
  unfold rowUpTo
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem mpBodyWritesRow_eq (Out Base : ℕ) (x : MatInst) (t : ℕ) :
    mpBodyWritesRow Out Base x t = rowUpTo Out Base x t x.n := rfl

/-! ## The store's memory semantics (axiom-free) -/

/-- One store writes its own cell and keeps the registers. -/
theorem store_writes (lim : Limits) (P : Light.Program) (d : ℕ)
    (a e : Expr) (σ : State) (T : ℕ)
    (ha : a.Safe lim σ) (he : e.Safe lim σ) (haddr : lim.Addr (a.val σ))
    (hcost : a.cost + e.cost + 1 ≤ T) :
    Ends lim P d (Light.Stmt.store a e) σ T
      (fun σ' => σ'.mem (a.val σ).toNat = e.val σ ∧ σ'.loc = σ.loc) := by
  refine Ends.store ha he haddr hcost ⟨?_, rfl⟩
  simp

/-- One store keeps every other cell (the store's address distinct from
it) and keeps the registers. -/
theorem store_keeps (lim : Limits) (P : Light.Program) (d : ℕ)
    (a e : Expr) (σ : State) (T : ℕ) (A : ℕ)
    (ha : a.Safe lim σ) (he : e.Safe lim σ) (haddr : lim.Addr (a.val σ))
    (hcost : a.cost + e.cost + 1 ≤ T)
    (hne : A ≠ (a.val σ).toNat) :
    Ends lim P d (Light.Stmt.store a e) σ T
      (fun σ' => σ'.mem A = σ.mem A ∧ σ'.loc = σ.loc) := by
  refine Ends.store ha he haddr hcost ⟨?_, rfl⟩
  exact Function.update_of_ne hne _ _

/-! ## The pinning and the delivery socket -/

/-- THE WIRE'S PINNING at a state (all clauses mediated by the
registers): the base register holds the product base, register 0 holds
zero, the other entries' write addresses miss the (0,0) cell's register
source, the stores are safe (the address in the memory and its
absolute value in the word), and the frame holds: registers 0–8 carry
the call's argument list (the condition that survives the rounds — the
call updates only `Tmp`). -/
def WirePins (lim : Limits) (Out : ℕ) (vals : List ℤ) (x : MatInst) (N : ℕ)
    (σ : State) : Prop :=
  σ.loc Out = (x.c : ℤ) ∧
  σ.loc 0 = 0 ∧
  (∀ t : ℕ, t < N → ∀ j : ℕ, j < x.n → (t, j) ≠ (0, 0) →
    σ.loc (t * x.n + j) ≠ σ.loc 0) ∧
  (∀ t : ℕ, t < N → ∀ j : ℕ, j < x.n →
    lim.Addr (σ.loc Out + σ.loc (t * x.n + j)) ∧
    |σ.loc Out + σ.loc (t * x.n + j)| ≤ lim.word) ∧
  (∀ k' : ℕ, k' < 9 → σ.loc k' = vals.getD k' 0)

theorem WirePins_congr {lim : Limits} {Out : ℕ} {vals : List ℤ} {x : MatInst}
    {N : ℕ} {σ σ' : State} (h : σ'.loc = σ.loc)
    (hp : WirePins lim Out vals x N σ) : WirePins lim Out vals x N σ' := by
  unfold WirePins at hp ⊢
  simp only [h]
  exact hp

/-- The pins survive the stage call: the call's final state updates the
result register `Tmp` only, so every pinned register — the base, the
zero register, the write-address indices (excluded from `Tmp`), and the
frame registers 0–8 — is preserved. -/
theorem WirePins_update {lim : Limits} {Out : ℕ} {vals : List ℤ} {x : MatInst}
    {N : ℕ} {l : ℕ → ℤ} {μ : ℕ → ℤ} {r : ℤ}
    (hOutNe : Out ≠ Tmp)
    (hTtmp : ∀ t : ℕ, t < N → ∀ j : ℕ, j < x.n → t * x.n + j ≠ Tmp)
    (hp : WirePins lim Out vals x N ⟨l, μ⟩) :
    WirePins lim Out vals x N ⟨Function.update l Tmp r, μ⟩ := by
  unfold WirePins at hp ⊢
  simp only [State.loc] at *
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  have huOut : Function.update l Tmp r Out = l Out := dif_neg hOutNe
  have hu0 : Function.update l Tmp r 0 = l 0 := dif_neg (by norm_num [Tmp])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [huOut]; exact h1
  · rw [hu0]; exact h2
  · intro t ht j hj hne
    rw [show Function.update l Tmp r (t * x.n + j) = l (t * x.n + j) from
      dif_neg (hTtmp t ht j hj)]
    exact h3 t ht j hj hne
  · intro t ht j hj
    have h41 := h4 t ht j hj
    have huj : Function.update l Tmp r (t * x.n + j) = l (t * x.n + j) :=
      dif_neg (hTtmp t ht j hj)
    exact ⟨by rw [huOut, huj]; exact h41.1,
      by rw [huOut, huj]; exact h41.2⟩
  · intro k' hk'
    rw [show Function.update l Tmp r k' = l k' from
      dif_neg (by have hT : Tmp = (10 : ℕ) := rfl; omega)]
    exact h5 k' hk'

/-- SOCKET (never claimed): the stage call at round t delivers the row's
refined value — the fold seeded by the row cell's current value — into
the call's result register `Tmp` (a Light call updates only `Tmp`; the
address-base `Out` is a different register, pinned by the pinning), and
keeps cell (0,0), the pinning, and the memory frame. The body's
per-round machine-computation contract (DATAFLOW.md's remaining
sub-design); the min-plus identity of the delivered values rides the
oracle premise — D7's boundary: the oracle is a premise, never claimed
as proved. The socket's proof session is named, not landed. -/
def StageDelivers (lim : Limits) (P : Light.Program) (d Out Tcall : ℕ)
    (vals : List ℤ) (x : MatInst) (tests : ℕ → Bool × Bool) (N : ℕ) : Prop :=
  ∀ (t : ℕ) (l : ℕ → ℤ) (μ : ℕ → ℤ), t < N →
    (∀ k' : ℕ, k' < 9 → l k' = vals.getD k' 0) →
    Ends lim P d (Light.Stmt.call 6 callArgs Tmp) ⟨l, μ⟩ Tcall
      (fun σ₁ => σ₁.loc Tmp = bracketAccumulate (μ (x.c + t * x.n)) tests N ∧
        σ₁.mem x.c = μ x.c ∧ WirePins lim Out vals x N σ₁)

/-! ## The row's runs (axiom-free given the store semantics) -/

/-- The row's run keeps a pinned cell when every entry's address misses
it. -/
theorem rowUpTo_keep (lim : Limits) (P : Light.Program) (d Out Base : ℕ)
    (x : MatInst) (t : ℕ) (A : ℕ) (w : ℤ) (Bw : ℕ) :
    ∀ (j : ℕ) (σ : State),
      σ.mem A = w →
      (∀ u : ℕ, u < j → A ≠ (σ.loc Out + σ.loc (t * x.n + u) : ℤ).toNat) →
      (∀ u : ℕ, u < j →
        lim.Addr (σ.loc Out + σ.loc (t * x.n + u)) ∧
        (v Out +' v (t * x.n + u) : Expr).Safe lim σ ∧
        (v (Base + u) : Expr).Safe lim σ) →
      (∀ u : ℕ, u < j → (v Out +' v (t * x.n + u) : Expr).cost +
        (v (Base + u) : Expr).cost + 1 ≤ Bw) →
      ∀ T : ℕ, j * Bw ≤ T →
      Ends lim P d (rowUpTo Out Base x t j) σ T
        (fun σ' => σ'.mem A = w ∧ σ'.loc = σ.loc) := by
  intro j
  induction j with
  | zero =>
    intro σ hw _ _ _ T _
    rw [rowUpTo_zero]
    exact Ends.skip ⟨hw, rfl⟩
  | succ j ih =>
    intro σ hw hdist hsafe hcost T hT
    rw [rowUpTo_succ]
    have hmul : (j + 1) * Bw = j * Bw + Bw := by ring
    have hT1 : j * Bw ≤ T - Bw := by omega
    have hTsplit : (T - Bw) + Bw ≤ T := by omega
    refine Ends.seq (T - Bw) Bw ?_ hTsplit
    refine (ih σ hw (fun u hu => hdist u (by omega))
      (fun u hu => hsafe u (by omega)) (fun u hu => hcost u (by omega))
      (T - Bw) hT1).mono le_rfl (fun σ' hσ' => ?_)
    have hloc : σ'.loc = σ.loc := hσ'.2
    have haddr' : lim.Addr (σ'.loc Out + σ'.loc (t * x.n + j)) := by
      rw [hloc]; exact (hsafe j (by omega)).1
    have hne' : A ≠ (σ'.loc Out + σ'.loc (t * x.n + j)).toNat := by
      rw [hloc]; exact hdist j (by omega)
    have hsaf' : (v Out +' v (t * x.n + j) : Expr).Safe lim σ' := by
      show True ∧ True ∧ |σ'.loc Out + σ'.loc (t * x.n + j)| ≤ lim.word
      rw [hloc]
      exact (hsafe j (by omega)).2.1
    exact (store_keeps lim P d (v Out +' v (t * x.n + j)) (v (Base + j)) σ' Bw A
      hsaf' trivial haddr' (hcost j (by omega)) hne').mono le_rfl
      (fun σ'' h'' => ⟨h''.1.trans hσ'.1, h''.2.trans hσ'.2⟩)

/-- The row's run writes a pinned cell at the first entry and keeps it
after (every later entry's address away from it). The first entry's
value is the delivery register `Base`'s content. -/
theorem rowUpTo_writesA (lim : Limits) (P : Light.Program) (d Out Base : ℕ)
    (x : MatInst) (t : ℕ) (A : ℕ) (w : ℤ) (Bw : ℕ) :
    ∀ (j : ℕ), 1 ≤ j → ∀ (σ : State),
      (σ.loc Out + σ.loc (t * x.n) : ℤ).toNat = A →
      σ.loc Base = w →
      (∀ u : ℕ, 1 ≤ u → u < j →
        A ≠ (σ.loc Out + σ.loc (t * x.n + u) : ℤ).toNat) →
      (∀ u : ℕ, u < j →
        lim.Addr (σ.loc Out + σ.loc (t * x.n + u)) ∧
        (v Out +' v (t * x.n + u) : Expr).Safe lim σ ∧
        (v (Base + u) : Expr).Safe lim σ) →
      (∀ u : ℕ, u < j → (v Out +' v (t * x.n + u) : Expr).cost +
        (v (Base + u) : Expr).cost + 1 ≤ Bw) →
      ∀ T : ℕ, j * Bw ≤ T →
      Ends lim P d (rowUpTo Out Base x t j) σ T
        (fun σ' => σ'.mem A = w ∧ σ'.loc = σ.loc) := by
  intro j
  induction j with
  | zero =>
    intro hj _ _ _ _ _ _ _ _
    exact absurd hj (by omega)
  | succ j ih =>
    intro hj σ haddrA hval hdist hsafe hcost T hT
    rw [rowUpTo_succ]
    have hmul : (j + 1) * Bw = j * Bw + Bw := by ring
    have hT1 : j * Bw ≤ T - Bw := by omega
    have hTsplit : (T - Bw) + Bw ≤ T := by omega
    refine Ends.seq (T - Bw) Bw ?_ hTsplit
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      -- the single first entry: it writes A
      refine Ends.skip ?_
      refine (store_writes lim P d (v Out +' v (t * x.n + 0)) (v (Base + 0)) σ Bw
        ((hsafe 0 (by omega)).2.1) ((hsafe 0 (by omega)).2.2)
        ((hsafe 0 (by omega)).1)
        (hcost 0 (by omega))).mono le_rfl (fun σ' hσ' => ?_)
      have hAeq : ((v Out +' v (t * x.n + 0) : Expr).val σ).toNat = A := by
        have hsum : (v Out +' v (t * x.n + 0) : Expr).val σ =
            σ.loc Out + σ.loc (t * x.n) := rfl
        rw [hsum]; exact haddrA
      have hveq : (v (Base + 0) : Expr).val σ = w := by
        show σ.loc (Base + 0) = w
        rw [Nat.add_zero]; exact hval
      rw [hAeq, hveq] at hσ'
      exact ⟨hσ'.1, hσ'.2⟩
    · have hj' : 1 ≤ j := h0
      -- the prefix by ih; the last entry keeps A
      refine (ih hj' σ haddrA hval (fun u hu hu' => hdist u hu (by omega))
        (fun u hu => hsafe u (by omega)) (fun u hu => hcost u (by omega))
        (T - Bw) hT1).mono le_rfl (fun σ' hσ' => ?_)
      have hloc : σ'.loc = σ.loc := hσ'.2
      have haddr' : lim.Addr (σ'.loc Out + σ'.loc (t * x.n + j)) := by
        rw [hloc]; exact (hsafe j (by omega)).1
      have hne' : A ≠ (σ'.loc Out + σ'.loc (t * x.n + j)).toNat := by
        rw [hloc]; exact hdist j hj' (by omega)
      have hsaf' : (v Out +' v (t * x.n + j) : Expr).Safe lim σ' := by
        show True ∧ True ∧ |σ'.loc Out + σ'.loc (t * x.n + j)| ≤ lim.word
        rw [hloc]
        exact (hsafe j (by omega)).2.1
      exact (store_keeps lim P d (v Out +' v (t * x.n + j)) (v (Base + j)) σ' Bw A
        hsaf' trivial haddr' (hcost j (by omega)) hne').mono le_rfl
        (fun σ'' h'' => ⟨h''.1.trans hσ'.1, h''.2.trans hσ'.2⟩)

/-! ## The per-round slices (axiom-free given the delivery socket) -/

/-- Round 0's slice writes the delivered fold into cell (0,0) and keeps
the pinning. -/
theorem roundZero_writes (lim : Limits) (P : Light.Program) (d Out Tcall Bw T : ℕ)
    (x : MatInst) (tests : ℕ → Bool × Bool) (N : ℕ) (vals : List ℤ)
    (hxn : 1 ≤ x.n) (hN : 1 ≤ N)
    (σ : State)
    (hdeliv : StageDelivers lim P d Out Tcall vals x tests N)
    (hpins : WirePins lim Out vals x N σ)
    (hcost : ∀ u : ℕ, u < x.n → (v Out +' v (0 * x.n + u) : Expr).cost +
      (v (Tmp + u) : Expr).cost + 1 ≤ Bw)
    (hsplit : Tcall + x.n * Bw ≤ T) :
    Ends lim P d (roundSlice 6 Out x 0) σ T
      (fun σ' => σ'.mem (bracketCell x 0 0) =
        bracketAccumulate (σ.mem (bracketCell x 0 0)) tests N ∧
        WirePins lim Out vals x N σ') := by
  unfold roundSlice
  rw [mpBodyWritesRow_eq]
  refine Ends.seq Tcall (x.n * Bw) ?_ hsplit
  refine (hdeliv 0 σ.loc σ.mem (by omega)
    (fun k' hk' => hpins.2.2.2.2 k' hk')).mono le_rfl (fun σ₁ hσ₁ => ?_)
  obtain ⟨hdel, -, hpins₁⟩ := hσ₁
  -- the row-0 writes: entry 0 writes cell (0,0) = x.c with the delivered value
  have hA : (σ₁.loc Out + σ₁.loc (0 * x.n) : ℤ).toNat = x.c := by
    rw [hpins₁.1, Nat.zero_mul, hpins₁.2.1, Int.add_zero, Int.toNat_natCast]
  have hbound : ∀ u : ℕ, u < x.n →
      |σ₁.loc Out + σ₁.loc (0 * x.n + u)| ≤ lim.word :=
    fun u hu => (hpins₁.2.2.2.1 0 (by omega) u (by omega)).2
  refine (rowUpTo_writesA lim P d Out Tmp x 0 x.c (σ₁.loc Tmp) Bw
    x.n (by omega) σ₁ hA rfl
    (fun u hu hu' => ?_)
    (fun u hu => ⟨(hpins₁.2.2.2.1 0 (by omega) u (by omega)).1,
      ⟨trivial, trivial, hbound u (by omega)⟩, trivial⟩)
    (fun u hu => hcost u (by omega))
    (x.n * Bw) (by omega)).mono le_rfl (fun σ' hσ' => ?_)
  · -- the distance: entries u ≥ 1 of row 0 miss cell x.c
    have hp : σ₁.loc (0 * x.n + u) ≠ 0 := by
      have hp0 := hpins₁.2.2.1 0 (by omega) u (by omega) (by
        intro hcon
        simp only [Prod.mk.injEq] at hcon
        omega)
      rw [hpins₁.2.1] at hp0
      exact hp0
    have hzne : σ₁.loc Out + σ₁.loc (0 * x.n + u) ≠ (x.c : ℤ) := by
      rw [hpins₁.1]; omega
    have hpos : 0 ≤ σ₁.loc Out + σ₁.loc (0 * x.n + u) :=
      (hpins₁.2.2.2.1 0 (by omega) u (by omega)).1.1
    refine fun hcon => hzne ?_
    have hsum' : σ₁.loc Out + σ₁.loc (0 * x.n + u) = σ₁.loc Out := by
      rw [← Int.toNat_of_nonneg hpos, ← hcon, hpins₁.1]
    omega
  · -- the value: the written cell holds the delivered fold; the pins
    -- transfer through the row's loc-keeping
    have hw : σ₁.loc Tmp = bracketAccumulate (σ.mem x.c) tests N := by
      simpa [bracketCell, Nat.zero_mul, Nat.add_zero] using hdel
    simp only [bracketCell, Nat.zero_mul, Nat.add_zero] at hσ' ⊢
    exact ⟨by rw [hσ'.1, hw], WirePins_congr hσ'.2 hpins₁⟩

/-- Round t ≥ 1's slice keeps cell (0,0) and the pinning. -/
theorem roundKeeps (lim : Limits) (P : Light.Program) (d Out Tcall Bw T : ℕ)
    (x : MatInst) (tests : ℕ → Bool × Bool) (N t : ℕ) (vals : List ℤ)
    (σ : State) (w0 : ℤ)
    (ht : 1 ≤ t) (htN : t < N)
    (hdeliv : StageDelivers lim P d Out Tcall vals x tests N)
    (hpins : WirePins lim Out vals x N σ)
    (hval : σ.mem (bracketCell x 0 0) = w0)
    (hcost : ∀ u : ℕ, u < x.n → (v Out +' v (t * x.n + u) : Expr).cost +
      (v (Tmp + u) : Expr).cost + 1 ≤ Bw)
    (hsplit : Tcall + x.n * Bw ≤ T) :
    Ends lim P d (roundSlice 6 Out x t) σ T
      (fun σ' => σ'.mem (bracketCell x 0 0) = w0 ∧
        WirePins lim Out vals x N σ') := by
  unfold roundSlice
  rw [mpBodyWritesRow_eq]
  refine Ends.seq Tcall (x.n * Bw) ?_ hsplit
  refine (hdeliv t σ.loc σ.mem htN
    (fun k' hk' => hpins.2.2.2.2 k' hk')).mono le_rfl (fun σ₁ hσ₁ => ?_)
  obtain ⟨-, hkeep, hpins₁⟩ := hσ₁
  have hw : σ₁.mem x.c = w0 := by
    rw [hkeep]
    simpa [bracketCell, Nat.zero_mul, Nat.add_zero] using hval
  have hbound : ∀ u : ℕ, u < x.n →
      |σ₁.loc Out + σ₁.loc (t * x.n + u)| ≤ lim.word :=
    fun u hu => (hpins₁.2.2.2.1 t (by omega) u (by omega)).2
  refine (rowUpTo_keep lim P d Out Tmp x t x.c w0 Bw x.n σ₁ hw
    (fun u hu => ?_)
    (fun u hu => ⟨(hpins₁.2.2.2.1 t (by omega) u (by omega)).1,
      ⟨trivial, trivial, hbound u (by omega)⟩, trivial⟩)
    (fun u hu => hcost u (by omega))
    (x.n * Bw) (by omega)).mono le_rfl (fun σ' hσ' => ?_)
  · -- the distance: every entry of row t ≥ 1 misses cell x.c
    have hz : σ₁.loc (t * x.n + u) ≠ 0 := by
      have hp0 := hpins₁.2.2.1 t (by omega) u (by omega) (by
        intro hcon
        simp only [Prod.mk.injEq] at hcon
        have := ht
        omega)
      rw [hpins₁.2.1] at hp0
      exact hp0
    have hzne : σ₁.loc Out + σ₁.loc (t * x.n + u) ≠ (x.c : ℤ) := by
      rw [hpins₁.1]; omega
    have hpos : 0 ≤ σ₁.loc Out + σ₁.loc (t * x.n + u) :=
      (hpins₁.2.2.2.1 t (by omega) u (by omega)).1.1
    refine fun hcon => hzne ?_
    have hsum' : σ₁.loc Out + σ₁.loc (t * x.n + u) = σ₁.loc Out := by
      rw [← Int.toNat_of_nonneg hpos, ← hcon, hpins₁.1]
    omega
  · -- the target: the kept cell and the transferred pinning
    simp only [bracketCell, Nat.zero_mul, Nat.add_zero] at hσ' ⊢
    exact ⟨hσ'.1, WirePins_congr hσ'.2 hpins₁⟩

/-! ## The wire -/

/-- THE WIRE'S INDUCTION: the schedule's first-t-rounds prefix threads
the state; from round 1 on, cell (0,0) holds the delivered fold. -/
theorem wire_runs (lim : Limits) (P : Light.Program) (d Out Tcall Bw B : ℕ)
    (x : MatInst) (tests : ℕ → Bool × Bool) (N W : ℕ) (vals : List ℤ)
    (hxn : 1 ≤ x.n)
    (hdeliv : StageDelivers lim P d Out Tcall vals x tests N)
    (hcost : ∀ t : ℕ, t < N → ∀ u : ℕ, u < x.n →
      (v Out +' v (t * x.n + u) : Expr).cost + (v (Tmp + u) : Expr).cost + 1 ≤ Bw)
    (hround : Tcall + x.n * Bw ≤ B) :
    ∀ (t : ℕ), t ≤ N → ∀ (l : ℕ → ℤ) (μ₀ : ℕ → ℤ) (T : ℕ), t * B ≤ T →
      WirePins lim Out vals x N ⟨l, μ₀⟩ →
      Ends lim P d (bodyUpTo 6 Out x W t) ⟨l, μ₀⟩ T
        (fun σ' => (t = 0 → σ'.mem x.c = μ₀ x.c) ∧
          (1 ≤ t → σ'.mem x.c = bracketAccumulate (μ₀ x.c) tests N) ∧
          WirePins lim Out vals x N σ') := by
  intro t
  induction t with
  | zero =>
    intro hN l μ₀ T hT hpins
    rw [bodyUpTo_zero]
    exact Ends.skip ⟨fun _ => rfl, fun h => absurd h (by omega), hpins⟩
  | succ t ih =>
    intro hN l μ₀ T hT hpins
    rw [bodyUpTo_succ]
    have hmul : (t + 1) * B = t * B + B := by ring
    have hTB : t * B ≤ T - B := by omega
    have hTsplit : (T - B) + B ≤ T := by omega
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0
      have hN1 : 1 ≤ N := by omega
      refine Ends.seq 0 B (Ends.skip ?_) (by omega)
      refine (roundZero_writes lim P d Out Tcall Bw B x tests N vals hxn hN1 ⟨l, μ₀⟩
        hdeliv hpins (fun u hu => hcost 0 (by omega) u hu) hround).mono le_rfl
        (fun σ' hσ' => ?_)
      simp only [bracketCell, Nat.zero_mul, Nat.add_zero] at hσ'
      exact ⟨fun h => absurd h (by omega), fun _ => hσ'.1, hσ'.2⟩
    · have ht : 1 ≤ t := h0
      have htN : t < N := by omega
      refine Ends.seq (T - B) B ?_ hTsplit
      refine (ih (by omega) l μ₀ (T - B) hTB hpins).mono le_rfl
        (fun σ₁ hσ₁ => ?_)
      have hval : σ₁.mem (bracketCell x 0 0) =
          bracketAccumulate (μ₀ x.c) tests N := by
        simp only [bracketCell, Nat.zero_mul, Nat.add_zero]
        exact hσ₁.2.1 ht
      refine (roundKeeps lim P d Out Tcall Bw B x tests N t vals σ₁
        (bracketAccumulate (μ₀ x.c) tests N) ht htN hdeliv hσ₁.2.2 hval
        (fun u hu => hcost t htN u hu) hround).mono le_rfl
        (fun σ' hσ' => ?_)
      simp only [bracketCell, Nat.zero_mul, Nat.add_zero] at hσ'
      exact ⟨fun h => absurd h (by omega), fun _ => hσ'.1, hσ'.2⟩

/-- THE WIRE: the body's run delivers the fold into cell (0,0). -/
theorem wire_compose (lim : Limits) (P : Light.Program) (d Out Tcall Bw B T : ℕ)
    (x : MatInst) (tests : ℕ → Bool × Bool) (W : ℕ) (vals : List ℤ)
    (hxn : 1 ≤ x.n)
    (hdeliv : StageDelivers lim P d Out Tcall vals x tests (mpRounds W))
    (hcost : ∀ t : ℕ, t < mpRounds W → ∀ u : ℕ, u < x.n →
      (v Out +' v (t * x.n + u) : Expr).cost + (v (Tmp + u) : Expr).cost + 1 ≤ Bw)
    (hround : Tcall + x.n * Bw ≤ B) (hT : mpRounds W * B ≤ T)
    (l : ℕ → ℤ) (μ₀ : ℕ → ℤ)
    (hpins : WirePins lim Out vals x (mpRounds W) ⟨l, μ₀⟩) :
    Ends lim P d (mpBodyWithWrites 6 Out x W) ⟨l, μ₀⟩ T
      (fun σ' => σ'.mem (bracketCell x 0 0) =
        bracketAccumulate (μ₀ (bracketCell x 0 0)) tests (mpRounds W)) := by
  rw [mpBodyWithWrites_eq]
  have h2 : 2 ≤ mpRounds W := by
    rw [mpRounds_eq W]
    have hpos := Nat.succ_pos (2 * W).log2
    omega
  refine (wire_runs lim P d Out Tcall Bw B x tests (mpRounds W) W vals hxn hdeliv
    (fun t ht u hu => hcost t ht u hu) hround (mpRounds W) (le_refl _)
    l μ₀ T hT hpins).mono le_rfl (fun σ' hσ' => ?_)
  simp only [bracketCell, Nat.zero_mul, Nat.add_zero] at hσ' ⊢
  exact hσ'.2.1 (by omega)

/-- THE WIRE-TARGET: `CallerRun.BracketFinal` at the pinned states —
under the delivery socket, the pinning, the budgets, and the start
value (the cells at 0; the initialization's obligation). -/
theorem bracketFinal_of_pins
    {lim : Limits} {d : ℕ} {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr : ℕ} {Tcall Bw B T : ℕ}
    {μ₀ : ℕ → ℤ} {R : Light.Program} {x : MatInst} {Out : ℕ}
    (W : ℕ) (tests : ℕ → Bool × Bool)
    (hxn : 1 ≤ x.n)
    (hdeliv : StageDelivers lim
      (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
      d Out Tcall (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++
        [(fr : ℤ)]) x tests (mpRounds W))
    (hcost : ∀ t : ℕ, t < mpRounds W → ∀ u : ℕ, u < x.n →
      (v Out +' v (t * x.n + u) : Expr).cost + (v (Tmp + u) : Expr).cost + 1 ≤ Bw)
    (hround : Tcall + x.n * Bw ≤ B) (hT : mpRounds W * B ≤ T)
    (σ'' : State) (hpins : WirePins lim Out
      (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++
        [(fr : ℤ)]) x (mpRounds W) σ'')
    (hstart : σ''.mem (bracketCell x 0 0) = 0) :
    Ends lim
      (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
      d (mpBodyWithWrites 6 Out x W) σ'' T
      (fun σ' => bracketAccumulate 0 tests (mpRounds W) =
        σ'.mem (bracketCell x 0 0)) := by
  have hw := wire_compose lim
    (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
    d Out Tcall Bw B T x tests W
    (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)])
    hxn hdeliv hcost hround hT σ''.loc σ''.mem hpins
  refine hw.mono le_rfl (fun σ' hσ' => ?_)
  rw [hstart] at hσ'
  exact hσ'.symm

/-- THE SOCKET'S PROOF, at the call level: the certified slot family
consumed through `Ends.callLast`. The delivery-content is the named
return-premise `hret` (the construction's own machine-conversion —
`Post` ignores the return value, so it rides nowhere in the certified
contracts; D7's boundary: the oracle is a premise, never claimed). The
memory frame comes from `Post`'s `SameOutside3` + the layout (`x.c`
outside the three regions); the pinning from `WirePins_update` (the
call updates only `Tmp`; the frame registers 0–8 survive). The
reads-condition (`StageReads` at the round's memory) is explicit in the
statement — threading it through the schedule's rounds is the chain
machinery's work (the next assembly's piece). -/
theorem stageDelivers_of_slot
    {lim : Limits} {d : ℕ} {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr : ℕ} {Tcall : ℕ} {Tt : ℕ → ℕ}
    {R : Light.Program} {x : MatInst} {Out : ℕ}
    (tests : ℕ → Bool × Bool) (N : ℕ)
    (hOutNe : Out ≠ Tmp)
    (hTtmp : ∀ t : ℕ, t < N → ∀ j : ℕ, j < x.n → t * x.n + j ≠ Tmp)
    (haway : (x.c < sb ∨ sb + P ≤ x.c) ∧ (x.c < bb ∨ bb + I ≤ x.c) ∧
      (x.c < mb ∨ mb + P ≤ x.c))
    (hslots : ∀ (mask : ℕ → Bool) (kt : ℕ) (μ : ℕ → ℤ),
      ThinMatrix.CallerChain.StageReads P I active mask rows ab rb mb μ →
      kt ≤ (flagged P mask).card →
      (need (instanceSize (callSite P kt I h active mask rows ab rb sb mb bb))
        (callSite P kt I h active mask rows ab rb sb mb bb).height).Ok lim fr (d + 1) →
      Meets lim (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
        6 (d + 1) (argsOf (callSite P kt I h active mask rows ab rb sb mb bb) ++ [(fr : ℤ)]) μ
        (Tt kt)
        (pinnedPost (callSite P kt I h active mask rows ab rb sb mb bb) μ fr))
    (hflag : ∀ mask : ℕ → Bool, k ≤ (flagged P mask).card)
    (hok : ∀ (mask : ℕ → Bool) (kt : ℕ),
      (need (instanceSize (callSite P kt I h active mask rows ab rb sb mb bb))
        (callSite P kt I h active mask rows ab rb sb mb bb).height).Ok lim fr (d + 1))
    (hdim : d < lim.depth)
    (hTcall : (callArgs.map Expr.cost).sum + 2 + Tt k ≤ Tcall)
    (hret : ∀ (t : ℕ) (mask : ℕ → Bool) (μ : ℕ → ℤ) (r : ℤ) (μ' : ℕ → ℤ), t < N →
      Post (callSite P k I h active mask rows ab rb sb mb bb) μ μ' →
      r = bracketAccumulate (μ (x.c + t * x.n)) tests N) :
    ∀ (t : ℕ) (mask : ℕ → Bool) (l : ℕ → ℤ) (μ : ℕ → ℤ), t < N →
      (∀ k' : ℕ, k' < 9 → l k' =
        (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]).getD k' 0) →
      ThinMatrix.CallerChain.StageReads P I active mask rows ab rb mb μ →
      WirePins lim Out
        (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)])
        x N ⟨l, μ⟩ →
      Ends lim
        (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
        d (Light.Stmt.call 6 callArgs Tmp) ⟨l, μ⟩ Tcall
        (fun σ₁ => σ₁.loc Tmp = bracketAccumulate (μ (x.c + t * x.n)) tests N ∧
          σ₁.mem x.c = μ x.c ∧
          WirePins lim Out
            (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)])
            x N σ₁) := by
  intro t mask l μ htN hloc hreads hpins
  refine Ends.callLast (hslots mask k μ hreads (hflag mask) (hok mask k)) ?_ ?_ ?_ ?_
  · intro r μ' hR
    obtain ⟨cs₁, hlen, hnd, hmem, hmask, hsam, h0, hpos⟩ := id hR
    refine ⟨?_, ?_, ?_⟩
    · show Function.update l Tmp r Tmp = bracketAccumulate (μ (x.c + t * x.n)) tests N
      rw [Function.update_self]
      exact hret t mask μ r μ' htN ⟨cs₁, hlen, hnd, hmem, hmask, hsam, h0, hpos⟩
    · show μ' x.c = μ x.c
      exact hsam x.c haway
    · exact WirePins_update hOutNe
        (fun t' ht' j hj => hTtmp t' ht' j hj) hpins
  · refine ⟨fun e he => ?_, ?_⟩
    simp only [callArgs, List.mem_cons] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact absurd h (by simp)
    have hlits : callArgs.map (fun e => e.val ⟨l, μ⟩) =
        [l Candidates, l Len, l Height, l Active, l Rows, l Scores, l Remaining,
          l Base, l Free] := rfl
    rw [hlits, hloc 0 (by omega), hloc 1 (by omega), hloc 2 (by omega),
      hloc 3 (by omega), hloc 4 (by omega), hloc 5 (by omega),
      hloc 6 (by omega), hloc 7 (by omega), hloc 8 (by omega)]
    rfl
  · exact hdim
  · exact hTcall


/-! ## The wire-level assembly: the reads-threaded induction -/

/-- THE ROW-WRITE SOCKET (never claimed): the row's stores write the
round's delivered value into cell (t, 0), preserve the pinning, and
preserve the reads (the product-region cells lie outside the
reads-regions — the layout obligation; the discharge rides the
rowUpTo_writesA machinery + the index-pinning, named). -/
def RowWrites (lim : Limits) (Pgm : Light.Program) (P I : ℕ) (d Out Tmp Bw : ℕ)
    (active : ℕ → Bool) (rows : ℕ → ℕ → ℕ) (ab rb mb : ℕ)
    (vals : List ℤ) (x : MatInst) (tests : ℕ → Bool × Bool) (N : ℕ) : Prop :=
  ∀ (t : ℕ) (mask : ℕ → Bool) (ll : ℕ → ℤ) (μ : ℕ → ℤ) (r : ℤ),
    t < N →
    WirePins lim Out vals x N ⟨ll, μ⟩ →
    ThinMatrix.CallerChain.StageReads P I active mask rows ab rb mb μ →
    Ends lim Pgm d (mpBodyWritesRow Out Tmp x t) ⟨ll, μ⟩ (x.n * Bw)
      (fun σ' => σ'.mem x.c = r ∧
        WirePins lim Out vals x N σ' ∧
        ThinMatrix.CallerChain.StageReads P I active mask rows ab rb mb σ'.mem)

/-- THE ROW-KEEP SOCKET (never claimed): the row's stores keep cell
(t', 0)'s value (in particular cell (0,0)'s delivered fold), preserve
the pinning, and preserve the reads (the same layout obligation; the
discharge rides the rowUpTo_keep machinery, named). -/
def RowKeeps (lim : Limits) (Pgm : Light.Program) (P I : ℕ) (d Out Tmp Bw : ℕ)
    (active : ℕ → Bool) (rows : ℕ → ℕ → ℕ) (ab rb mb : ℕ)
    (vals : List ℤ) (x : MatInst) (tests : ℕ → Bool × Bool) (N : ℕ) : Prop :=
  ∀ (t : ℕ) (mask : ℕ → Bool) (ll : ℕ → ℤ) (μ : ℕ → ℤ) (w : ℤ),
    t < N →
    WirePins lim Out vals x N ⟨ll, μ⟩ →
    μ x.c = w →
    ThinMatrix.CallerChain.StageReads P I active mask rows ab rb mb μ →
    Ends lim Pgm d (mpBodyWritesRow Out Tmp x t) ⟨ll, μ⟩ (x.n * Bw)
      (fun σ' => σ'.mem x.c = w ∧
        WirePins lim Out vals x N σ' ∧
        ThinMatrix.CallerChain.StageReads P I active mask rows ab rb mb σ'.mem)

/-- THE WIRE FROM THE SLOTS (the auxiliary induction): the schedule's
run threads the state, the pins, and the reads (the evolved mask
existential in the post); the per-round delivery is produced from the
certified slot family outright (the socket at the carried reads), with
the delivery-content riding the named return-premise `hret` (D7's
boundary: the oracle is a premise, never claimed) and the row-slices
riding the two named row-sockets. -/
private theorem aux_wire_from_slots
    {lim : Limits} {d : ℕ} {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr : ℕ} {Bw B : ℕ}
    {Tt : ℕ → ℕ} {R : Light.Program} {x : MatInst} {Out : ℕ}
    (tests : ℕ → Bool × Bool) (W : ℕ)
    (hOutNe : Out ≠ Tmp)
    (hTtmp : ∀ t : ℕ, t < mpRounds W → ∀ j : ℕ, j < x.n → t * x.n + j ≠ Tmp)
    (haway : (x.c < sb ∨ sb + P ≤ x.c) ∧ (x.c < bb ∨ bb + I ≤ x.c) ∧
      (x.c < mb ∨ mb + P ≤ x.c))
    (hslots : ∀ (mask : ℕ → Bool) (kt : ℕ) (μ : ℕ → ℤ),
      ThinMatrix.CallerChain.StageReads P I active mask rows ab rb mb μ →
      kt ≤ (flagged P mask).card →
      (need (instanceSize (callSite P kt I h active mask rows ab rb sb mb bb))
        (callSite P kt I h active mask rows ab rb sb mb bb).height).Ok lim fr (d + 1) →
      Meets lim (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
        6 (d + 1) (argsOf (callSite P kt I h active mask rows ab rb sb mb bb) ++ [(fr : ℤ)]) μ
        (Tt kt)
        (pinnedPost (callSite P kt I h active mask rows ab rb sb mb bb) μ fr))
    (hret : ∀ (t : ℕ) (mask : ℕ → Bool) (μ : ℕ → ℤ) (r : ℤ) (μ' : ℕ → ℤ), t < mpRounds W →
      Post (callSite P k I h active mask rows ab rb sb mb bb) μ μ' →
      r = bracketAccumulate (μ (x.c + t * x.n)) tests (mpRounds W))
    (hflag : ∀ mask : ℕ → Bool, k ≤ (flagged P mask).card)
    (hok : ∀ (mask : ℕ → Bool) (kt : ℕ),
      (need (instanceSize (callSite P kt I h active mask rows ab rb sb mb bb))
        (callSite P kt I h active mask rows ab rb sb mb bb).height).Ok lim fr (d + 1))
    (hdim : d < lim.depth)
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)])
    (hround : (callArgs.map Expr.cost).sum + 2 + Tt k + x.n * Bw ≤ B)
    (h2 : 2 ≤ mpRounds W)
    (l : ℕ → ℤ) (μ₀ : ℕ → ℤ)
    (hpins₀ : WirePins lim Out
      (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)])
      x (mpRounds W) ⟨l, μ₀⟩)
    (hreads₀ : ThinMatrix.CallerChain.StageReads P I active remaining rows ab rb mb μ₀)
    (hrowwrites : RowWrites lim
      (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
      P I d Out Tmp Bw active rows ab rb mb
      (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)])
      x tests (mpRounds W))
    (hrowkeeps : RowKeeps lim
      (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
      P I d Out Tmp Bw active rows ab rb mb
      (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)])
      x tests (mpRounds W)) :
    ∀ (t : ℕ), t ≤ mpRounds W → ∀ (mask : ℕ → Bool) (T : ℕ), t * B ≤ T →
      ∀ (ll : ℕ → ℤ) (μ : ℕ → ℤ),
      WirePins lim Out
        (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)])
        x (mpRounds W) ⟨ll, μ⟩ →
      ThinMatrix.CallerChain.StageReads P I active mask rows ab rb mb μ →
      Ends lim
        (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
        d (bodyUpTo 6 Out x W t) ⟨ll, μ⟩ T
        (fun σ' => (t = 0 → σ'.mem x.c = μ x.c) ∧
          (1 ≤ t → σ'.mem x.c = bracketAccumulate (μ x.c) tests (mpRounds W)) ∧
          WirePins lim Out
            (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)])
            x (mpRounds W) σ' ∧
          ∃ mask' : ℕ → Bool,
            ThinMatrix.CallerChain.StageReads P I active mask' rows ab rb mb σ'.mem) := by
  intro t
  induction t with
  | zero =>
    intro hN mask T hT ll μ hpins hreads
    rw [bodyUpTo_zero]
    exact Ends.skip ⟨fun _ => rfl, fun h' => absurd h' (by omega), hpins, ⟨mask, hreads⟩⟩
  | succ t ih =>
    intro hN mask T hT ll μ hpins hreads
    rw [bodyUpTo_succ]
    have hmul : (t + 1) * B = t * B + B := by ring
    have hTB : t * B ≤ T - B := by omega
    have hTsplit : (T - B) + B ≤ T := by omega
    have hcallBudget : (callArgs.map Expr.cost).sum + 2 + Tt k ≤ B - x.n * Bw := by
      omega
    have hloc : ∀ k' : ℕ, k' < 9 → ll k' =
        (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]).getD k' 0 :=
      fun k' hk' => hpins.2.2.2.2 k' hk'
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0
      -- round 0: the call (witness-exposed) ;; the row-0 writes (the write-socket)
      refine Ends.seq 0 B (Ends.skip ?_) (by omega)
      simp only [roundSlice, mpBodyWritesRow_eq]
      refine Ends.seq (B - x.n * Bw) (x.n * Bw) ?_ (by omega)
      refine Ends.callLast (hslots mask k μ hreads (hflag mask) (hok mask k)) ?_ ?_ ?_ ?_
      · intro r₁ μ₁ hR
        obtain ⟨cs₁, hlen, hnd, hmem, hmask, hsam, h0', hpos⟩ := id hR
        have hreads₁ : ThinMatrix.CallerChain.StageReads P I active
            (maskCleared cs₁.toFinset mask) rows ab rb mb μ₁ :=
          ThinMatrix.CallerChain.reads_carry (h := h) hlay hreads hsam hmask
        have hdel : Function.update ll Tmp r₁ Tmp =
            bracketAccumulate (μ (x.c + 0 * x.n)) tests (mpRounds W) :=
          hret 0 mask μ r₁ μ₁ (by omega) ⟨cs₁, hlen, hnd, hmem, hmask, hsam, h0', hpos⟩
        have hpins₁ : WirePins lim Out
            (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)])
            x (mpRounds W) ⟨Function.update ll Tmp r₁, μ₁⟩ :=
          WirePins_update hOutNe (fun t' ht' j hj => hTtmp t' ht' j hj) hpins
        -- the row-0's write-socket: the delivered value into cell (0,0)
        have hrow := hrowwrites 0 (maskCleared cs₁.toFinset mask)
          (Function.update ll Tmp r₁) μ₁ r₁ (by omega) hpins₁ hreads₁
        refine hrow.mono le_rfl (fun σ' hσrow => ?_)
        -- the post: the mem = the delivered fold; the pins; the reads
        have hw : r₁ = bracketAccumulate (μ x.c) tests (mpRounds W) := by
          have h2' : Function.update ll Tmp r₁ Tmp =
              bracketAccumulate (μ (x.c + 0 * x.n)) tests (mpRounds W) := hdel
          rw [show Function.update ll Tmp r₁ Tmp = r₁ from rfl, Nat.zero_mul,
            Nat.add_zero] at h2'
          exact h2'
        exact ⟨fun h' => absurd h' (by omega), fun _ => by
          rw [hσrow.1, hw], hσrow.2.1, ⟨maskCleared cs₁.toFinset mask, hσrow.2.2⟩⟩
      · refine ⟨fun e he => ?_, ?_⟩
        simp only [callArgs, List.mem_cons] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
        · exact trivial
        · exact trivial
        · exact trivial
        · exact trivial
        · exact trivial
        · exact trivial
        · exact trivial
        · exact trivial
        · exact trivial
        · exact absurd h (by simp)
        have hlits : callArgs.map (fun e => e.val ⟨ll, μ⟩) =
            [ll Candidates, ll Len, ll Height, ll Active, ll Rows, ll Scores, ll Remaining,
              ll Base, ll Free] := rfl
        rw [hlits, hloc 0 (by omega), hloc 1 (by omega), hloc 2 (by omega),
          hloc 3 (by omega), hloc 4 (by omega), hloc 5 (by omega),
          hloc 6 (by omega), hloc 7 (by omega), hloc 8 (by omega)]
        rfl
      · exact hdim
      · exact hcallBudget
    · -- t ≥ 1: the prefix by ih (the reads through the ∃-post), then round t keeps
      have ht : 1 ≤ t := h0
      have htN : t < mpRounds W := by omega
      refine Ends.seq (T - B) B ?_ hTsplit
      refine (ih (by omega) mask (T - B) hTB ll μ hpins hreads).mono le_rfl (fun σ₁ hσ₁ => ?_)
      obtain ⟨mask₁, hreads₁⟩ := hσ₁.2.2.2
      have hloc₁ : ∀ k' : ℕ, k' < 9 → σ₁.loc k' =
        (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)]).getD k' 0 :=
        fun k' hk' => hσ₁.2.2.1.2.2.2.2 k' hk'
      have hw0 : σ₁.mem x.c = bracketAccumulate (μ x.c) tests (mpRounds W) :=
        hσ₁.2.1 ht
      simp only [roundSlice, mpBodyWritesRow_eq]
      refine Ends.seq (B - x.n * Bw) (x.n * Bw) ?_ (by omega)
      refine Ends.callLast (hslots mask₁ k σ₁.mem hreads₁ (hflag mask₁) (hok mask₁ k)) ?_ ?_ ?_ ?_
      · intro r₁ μ₂ hR
        obtain ⟨cs₁, hlen, hnd, hmem, hmask, hsam, h0', hpos⟩ := id hR
        have hreads₂ : ThinMatrix.CallerChain.StageReads P I active
            (maskCleared cs₁.toFinset mask₁) rows ab rb mb μ₂ :=
          ThinMatrix.CallerChain.reads_carry (h := h) hlay hreads₁ hsam hmask
        have hpins₁ : WirePins lim Out
            (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)])
            x (mpRounds W) ⟨Function.update σ₁.loc Tmp r₁, μ₂⟩ :=
          WirePins_congr (by rfl) (WirePins_update hOutNe
            (fun t' ht' j hj => hTtmp t' ht' j hj) hσ₁.2.2.1)
        have hkeep : μ₂ x.c = σ₁.mem x.c := hsam x.c haway
        -- the row-t's keep-socket: cell (0,0)'s fold kept; the reads preserved
        have hrow := hrowkeeps t (maskCleared cs₁.toFinset mask₁)
          (Function.update σ₁.loc Tmp r₁) μ₂ (bracketAccumulate (μ x.c) tests (mpRounds W))
          (by omega) hpins₁ (by rw [hkeep]; exact hw0) hreads₂
        refine hrow.mono le_rfl (fun σ' hσrow => ?_)
        exact ⟨fun h' => absurd h' (by omega), fun _ => hσrow.1, hσrow.2.1,
          ⟨maskCleared cs₁.toFinset mask₁, hσrow.2.2⟩⟩
      · refine ⟨fun e he => ?_, ?_⟩
        simp only [callArgs, List.mem_cons] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
        · exact trivial
        · exact trivial
        · exact trivial
        · exact trivial
        · exact trivial
        · exact trivial
        · exact trivial
        · exact trivial
        · exact trivial
        · exact absurd h (by simp)
        have hlits : callArgs.map (fun e => e.val ⟨σ₁.loc, σ₁.mem⟩) =
            [σ₁.loc Candidates, σ₁.loc Len, σ₁.loc Height, σ₁.loc Active, σ₁.loc Rows,
              σ₁.loc Scores, σ₁.loc Remaining, σ₁.loc Base, σ₁.loc Free] := rfl
        rw [hlits, hloc₁ 0 (by omega), hloc₁ 1 (by omega), hloc₁ 2 (by omega),
          hloc₁ 3 (by omega), hloc₁ 4 (by omega), hloc₁ 5 (by omega),
          hloc₁ 6 (by omega), hloc₁ 7 (by omega), hloc₁ 8 (by omega)]
        rfl
      · exact hdim
      · exact hcallBudget

/-- THE WIRE FROM THE SLOTS: the schedule's run delivers the fold into
cell (0,0), with the delivery produced from the certified slot family
outright. The delivery-content rides the named return-premise `hret`
and the row-slices ride the two named row-sockets (D7's boundary: the
oracle is a premise, never claimed). -/
theorem wire_from_slots
    {lim : Limits} {d : ℕ} {P k I h : ℕ} {active remaining : ℕ → Bool}
    {rows : ℕ → ℕ → ℕ} {ab rb sb mb bb fr : ℕ} {Bw B T : ℕ}
    {Tt : ℕ → ℕ} {R : Light.Program} {x : MatInst} {Out : ℕ}
    (tests : ℕ → Bool × Bool) (W : ℕ)
    (hOutNe : Out ≠ Tmp)
    (hTtmp : ∀ t : ℕ, t < mpRounds W → ∀ j : ℕ, j < x.n → t * x.n + j ≠ Tmp)
    (haway : (x.c < sb ∨ sb + P ≤ x.c) ∧ (x.c < bb ∨ bb + I ≤ x.c) ∧
      (x.c < mb ∨ mb + P ≤ x.c))
    (hslots : ∀ (mask : ℕ → Bool) (kt : ℕ) (μ : ℕ → ℤ),
      ThinMatrix.CallerChain.StageReads P I active mask rows ab rb mb μ →
      kt ≤ (flagged P mask).card →
      (need (instanceSize (callSite P kt I h active mask rows ab rb sb mb bb))
        (callSite P kt I h active mask rows ab rb sb mb bb).height).Ok lim fr (d + 1) →
      Meets lim (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
        6 (d + 1) (argsOf (callSite P kt I h active mask rows ab rb sb mb bb) ++ [(fr : ℤ)]) μ
        (Tt kt)
        (pinnedPost (callSite P kt I h active mask rows ab rb sb mb bb) μ fr))
    (hret : ∀ (t : ℕ) (mask : ℕ → Bool) (μ : ℕ → ℤ) (r : ℤ) (μ' : ℕ → ℤ), t < mpRounds W →
      Post (callSite P k I h active mask rows ab rb sb mb bb) μ μ' →
      r = bracketAccumulate (μ (x.c + t * x.n)) tests (mpRounds W))
    (hflag : ∀ mask : ℕ → Bool, k ≤ (flagged P mask).card)
    (hok : ∀ (mask : ℕ → Bool) (kt : ℕ),
      (need (instanceSize (callSite P kt I h active mask rows ab rb sb mb bb))
        (callSite P kt I h active mask rows ab rb sb mb bb).height).Ok lim fr (d + 1))
    (hdim : d < lim.depth)
    (hlay : InOrder fr [(ab, I), (rb, P * I), (sb, P), (bb, I), (mb, P)])
    (hround : (callArgs.map Expr.cost).sum + 2 + Tt k + x.n * Bw ≤ B)
    (hT : mpRounds W * B ≤ T)
    (l : ℕ → ℤ) (μ₀ : ℕ → ℤ)
    (hpins₀ : WirePins lim Out
      (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)])
      x (mpRounds W) ⟨l, μ₀⟩)
    (hreads₀ : ThinMatrix.CallerChain.StageReads P I active remaining rows ab rb mb μ₀)
    (hrowwrites : RowWrites lim
      (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
      P I d Out Tmp Bw active rows ab rb mb
      (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)])
      x tests (mpRounds W))
    (hrowkeeps : RowKeeps lim
      (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
      P I d Out Tmp Bw active rows ab rb mb
      (argsOf (callSite P k I h active remaining rows ab rb sb mb bb) ++ [(fr : ℤ)])
      x tests (mpRounds W)) :
    Ends lim
      (program (callSite P k I h active remaining rows ab rb sb mb bb) ++ R)
      d (mpBodyWithWrites 6 Out x W) ⟨l, μ₀⟩ T
      (fun σ' => σ'.mem (bracketCell x 0 0) =
        bracketAccumulate (μ₀ (bracketCell x 0 0)) tests (mpRounds W)) := by
  have h2 : 2 ≤ mpRounds W := by
    rw [mpRounds_eq W]
    have hpos := Nat.succ_pos (2 * W).log2
    omega
  have hwire := aux_wire_from_slots tests W hOutNe hTtmp haway hslots hret
    hflag hok hdim hlay hround h2 l μ₀ hpins₀ hreads₀ hrowwrites hrowkeeps
    (mpRounds W) (le_refl _) remaining T hT l μ₀ hpins₀ hreads₀
  refine hwire.mono le_rfl (fun σ' hσ' => ?_)
  obtain ⟨-, hmem, hpins, -⟩ := hσ'
  simp only [bracketCell, Nat.zero_mul, Nat.add_zero] at hmem ⊢
  exact hmem (by omega)

#print axioms bracketAccumulate_step#print axioms bracketAccumulate_step

#print axioms bodyUpTo_succ
#print axioms store_writes
#print axioms store_keeps
#print axioms rowUpTo_keep
#print axioms rowUpTo_writesA
#print axioms roundZero_writes
#print axioms roundKeeps
#print axioms wire_runs
#print axioms wire_compose
#print axioms bracketFinal_of_pins
#print axioms WirePins_update
#print axioms stageDelivers_of_slot
#print axioms wire_from_slots

end ThinMatrix.CallerWire
