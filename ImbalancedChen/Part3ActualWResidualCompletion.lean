import ImbalancedChen.Part3ActualWThreeCapacityRun

/-!
# Completion after the actual W first overflow

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The residual run starts with the already allocated left/right lists.  Its
prefer-left rule has no failure outcome: the right fit is proved from each
shifted original square.  At the actual three-capacity overflow the enlarged
middle list is fixed, the original unread suffix is consumed exactly once,
and both residual capacities are proved.  No no-failure, selected-support,
or final-factorization premise is introduced.
-/

namespace ImbalancedChen.Part3.ActualWResidualCompletion

noncomputable section

open scoped Classical
open ActualWThreeCapacityRun
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

def complementary {α : Type*} (w : α → ℝ) (g : Bins α) : ℝ :=
  wp w g.left * wp w g.right

def ShiftedSquares {α : Type*} (w : α → ℝ) (D P : ℝ) (xs : List α) : Prop :=
  ∀ (i : ℕ) (hi : i < xs.length),
    (P * wp w (xs.take i)) * w xs[i] ^ 2 ≤ D

theorem shifted_cons {α : Type*} (w : α → ℝ) {D P : ℝ}
    {p : α} {xs : List α} (h : ShiftedSquares w D P (p :: xs)) :
    P * w p ^ 2 ≤ D ∧ ShiftedSquares w D (P * w p) xs := by
  constructor
  · simpa [wp] using h 0 (by simp)
  · intro i hi
    have hh := h (i + 1) (by simp; omega)
    simpa [wp, mul_assoc] using hh

/-- Preserve the existing two bins; only append original unread slots. -/
def finish {α : Type*} (w : α → ℝ) (A : ℝ) : Bins α → List α → Bins α
  | g, [] => g
  | g, p :: xs =>
      if wp w g.left * w p ≤ A then finish w A (putLeft g p) xs
      else finish w A (putRight g p) xs

/-- True no-failure theorem for this particular residual program.  When
the left test fails, the original square proves the right fit. -/
theorem finish_correct {α : Type*} (w : α → ℝ) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (xs : List α) (g : Bins α)
    (hleft : wp w g.left ≤ A) (hright : wp w g.right ≤ C)
    (hs : ShiftedSquares w (A * C) (complementary w g) xs) :
    Trace g xs (finish w A g xs) ∧
      (finish w A g xs).middle = g.middle ∧
      wp w (finish w A g xs).left ≤ A ∧ wp w (finish w A g xs).right ≤ C := by
  induction xs generalizing g with
  | nil => exact ⟨Trace.nil g, rfl, hleft, hright⟩
  | cons p xs ih =>
      obtain ⟨hhead, htail⟩ := shifted_cons w hs
      have hfit := append_fits_one_box hA hC hhead
      unfold finish
      split_ifs with hl
      · have hnew : ShiftedSquares w (A * C) (complementary w (putLeft g p)) xs := by
          simpa [complementary, putLeft, wp, mul_assoc, mul_comm, mul_left_comm] using htail
        obtain ⟨ht, hm, hL, hR⟩ := ih (putLeft g p)
          (by simpa [putLeft, wp] using hl) hright hnew
        exact ⟨Trace.left g p ht, hm, hL, hR⟩
      · have hr := hfit.resolve_left hl
        have hnew : ShiftedSquares w (A * C) (complementary w (putRight g p)) xs := by
          simpa [complementary, putRight, wp, mul_assoc, mul_comm, mul_left_comm] using htail
        obtain ⟨ht, hm, hL, hR⟩ := ih (putRight g p) hleft
          (by simpa [putRight, wp] using hr) hnew
        exact ⟨Trace.right g p ht, hm, hL, hR⟩

theorem finish_exact_product {α : Type*} (w : α → ℝ) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (xs : List α) (g : Bins α)
    (hleft : wp w g.left ≤ A) (hright : wp w g.right ≤ C)
    (hs : ShiftedSquares w (A * C) (complementary w g) xs) :
    total w (finish w A g xs) = total w g * wp w xs :=
  (finish_correct w hA hC xs g hleft hright hs).1.product w

theorem trace_append {α : Type*} {g mid out : Bins α} {xs ys : List α}
    (hfirst : Trace g xs mid) (hsecond : Trace mid ys out) :
    Trace g (xs ++ ys) out := by
  induction hfirst generalizing out with
  | nil g => exact hsecond
  | left g p h ih => exact Trace.left g p (ih hsecond)
  | middle g p h ih => exact Trace.middle g p (ih hsecond)
  | right g p h ih => exact Trace.right g p (ih hsecond)

def Positive {α : Type*} (w : α → ℝ) (g : Bins α) : Prop :=
  0 < wp w g.left ∧ 0 < wp w g.middle ∧ 0 < wp w g.right

/-- Positivity at the stopping state is inherited from its actual trace. -/
theorem trace_positive {α : Type*} (w : α → ℝ) {g out : Bins α} {xs : List α}
    (h : Trace g xs out) (hg : Positive w g)
    (hslots : ∀ p ∈ xs, 0 < w p) : Positive w out := by
  revert hg hslots
  induction h with
  | nil g => intro hg _; exact hg
  | left g p h ih =>
      intro hg hslots
      apply ih
      · exact ⟨by simpa [putLeft, wp] using mul_pos hg.1 (hslots p (by simp)),
          hg.2.1, hg.2.2⟩
      · intro q hq
        exact hslots q (by simp [hq])
  | middle g p h ih =>
      intro hg hslots
      apply ih
      · exact ⟨hg.1, by simpa [putMiddle, wp] using mul_pos hg.2.1 (hslots p (by simp)),
          hg.2.2⟩
      · intro q hq
        exact hslots q (by simp [hq])
  | right g p h ih =>
      intro hg hslots
      apply ih
      · exact ⟨hg.1, hg.2.1,
          by simpa [putRight, wp] using mul_pos hg.2.2 (hslots p (by simp))⟩
      · intro q hq
        exact hslots q (by simp [hq])

/-- Finish the actual overflow branch, including its original full product.
The only square input is the original full-list support.  Every state and
the stopping slot are generated by `run`; no residual support is supplied. -/
theorem actual_overflow_completion {α : Type*} (w : α → ℝ) {A B C U D : ℝ}
    {seed input rest : List α} {p : α} {initial g : Bins α}
    (hA : 0 < A) (hinit : Bounded w A B C initial)
    (hpositive : Positive w initial)
    (hslots : ∀ q ∈ input, 0 < w q ∧ w q ≤ U)
    (hseed : total w initial = wp w seed)
    (hfull : PrefixSquareBound w D (seed ++ input))
    (hstop : run w A B C initial input = .overflow g p rest) :
    let out := finish w A (putMiddle g p) rest
    Trace initial input out ∧ total w out = wp w (seed ++ input) ∧
      B < wp w out.middle ∧ wp w out.middle ≤ B * U ∧
      wp w out.left ≤ A ∧ wp w out.right ≤ D / (A * wp w out.middle) := by
  obtain ⟨⟨prefix, heq, ht⟩, hb, hfA, hfB, hfC, hsquare⟩ :=
    run_overflow_original_square w A B C hinit hseed hfull hstop
  have hpinput : p ∈ input := by rw [heq]; simp
  obtain ⟨hp, hpU⟩ := hslots p hpinput
  have hpre : ∀ q ∈ prefix, 0 < w q := by
    intro q hq
    exact (hslots q (by rw [heq]; simp [hq])).1
  have hg := trace_positive w ht hpositive hpre
  obtain ⟨hlo, hhi, hstrict, hright⟩ :=
    overflow_arithmetic hg.2.1 hg.2.2 hp hA hfA hfB hb.2.1 hpU hsquare
  let bnew := wp w g.middle * w p
  let Cnew := D / (A * bnew)
  have hbnew : 0 < bnew := mul_pos hg.2.1 hp
  have hCnew : 0 < Cnew := hg.2.2.trans hright
  have hAC : A * Cnew = D / bnew := by
    dsimp [Cnew]
    field_simp [hA.ne', hbnew.ne']
    <;> ring
  have hres : ShiftedSquares w (A * Cnew) (complementary w (putMiddle g p)) rest := by
    rw [hAC]
    exact overflow_residual_squares w hseed hfull heq ht hg.2.1 hp
  obtain ⟨hfinish, hmiddle, hleft, hrightfinal⟩ :=
    finish_correct w hA.le hCnew.le rest (putMiddle g p) hb.1 hright.le hres
  have htrace : Trace initial input (finish w A (putMiddle g p) rest) := by
    rw [heq]
    exact trace_append ht (Trace.middle g p hfinish)
  have hmid : wp w (finish w A (putMiddle g p) rest).middle = bnew := by
    rw [hmiddle]
    simp [putMiddle, wp, bnew]
  refine ⟨htrace, ?_, ?_, ?_, hleft, ?_⟩
  · rw [htrace.product w, hseed]
    simp [wp]
  · simpa only [hmid] using hlo
  · simpa only [hmid] using hhi
  · simpa only [hmid] using hrightfinal

/-- The complete finite program: preserve a successful initial run, or
insert its first failed slot into the middle and finish the unread suffix. -/
def complete {α : Type*} (w : α → ℝ) (A B C : ℝ)
    (initial : Bins α) (input : List α) : Bins α :=
  match run w A B C initial input with
  | .done g => g
  | .overflow g p rest => finish w A (putMiddle g p) rest

/-- Complete factorization with the manuscript's two genuine cases.
The first branch uses the original three capacities; the second has an
enlarged middle product in (B,B*U] and proven residual capacity. -/
theorem complete_correct {α : Type*} (w : α → ℝ) {A B C U D : ℝ}
    {seed input : List α} {initial : Bins α}
    (hA : 0 < A) (hinit : Bounded w A B C initial)
    (hpositive : Positive w initial)
    (hslots : ∀ q ∈ input, 0 < w q ∧ w q ≤ U)
    (hseed : total w initial = wp w seed)
    (hfull : PrefixSquareBound w D (seed ++ input)) :
    let out := complete w A B C initial input
    Trace initial input out ∧ total w out = wp w (seed ++ input) ∧
      (Bounded w A B C out ∨
        (B < wp w out.middle ∧ wp w out.middle ≤ B * U ∧
          wp w out.left ≤ A ∧ wp w out.right ≤ D / (A * wp w out.middle))) := by
  unfold complete
  cases hr : run w A B C initial input with
  | done g =>
      have hs := run_spec w A B C input initial hinit
      rw [hr] at hs
      refine ⟨hs.2, ?_, Or.inl hs.1⟩
      rw [hs.2.product w, hseed]
      simp [wp]
  | overflow g p rest =>
      obtain ⟨ht, hprod, hlo, hhi, hleft, hright⟩ :=
        actual_overflow_completion w hA hinit hpositive hslots hseed hfull hr
      exact ⟨ht, hprod, Or.inr ⟨hlo, hhi, hleft, hright⟩⟩

theorem initialBins_positive (A : ℝ) (p : Fin 3 → ℕ)
    (hp : ∀ i, 0 < p i) : Positive (fun n : ℕ => (n : ℝ)) (initialBins A p) := by
  have hp0 : (0 : ℝ) < p 0 := by exact_mod_cast hp 0
  have hp1 : (0 : ℝ) < p 1 := by exact_mod_cast hp 1
  by_cases hf : (p 1 : ℝ) ≤ A
  · simp [Positive, initialBins, actualTwoCapacityGreedy, actualTwoCapacityStep,
      wp, hf, hp0, hp1]
  · simp [Positive, initialBins, actualTwoCapacityGreedy, actualTwoCapacityStep,
      wp, hf, hp0, hp1]

open ActualWGapInitialization ActualCompactAllRankSupport VariableEnvelope

/-- Complete the actual compact retained W-gap frontier.  Original support,
positivity, and the late-slot bound are all produced by the actual carrier,
its order, and the winning W geometry.  The conclusion concerns the same
rough-prime product; small attachment and endpoint freezing are separate. -/
theorem actual_frontier_W_gap_complete
    (e h : ℝ) (m N cap k : ℕ) (hk : 3 ≤ k) (w z : ℝ) (weight : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k
      (actualExtendedThirdCompactUpperPolicy e h m N) weight [] true 1
      (roughPrimeUniverse N cap w z))
    (hN : 2 ≤ N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (howned : primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 state.selectedPrefix) ∈
      actualExtendedThirdOwnedCell m j)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hwinner : actualExtendedThirdLeastWinningIndex e m j = 4)
    (hgap : e / 4 < wInner (t 0) (t 1) (t 2) - v (t 0))
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (hshape : state.selectedPrefix.reverse = p 0 :: p 1 :: p 2 :: tail)
    (hs : actualSelectedPrimeCoordinates (N : ℝ) p ∈ actualExtendedThirdPhysicalCell m j)
    (A : ℝ) (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ)) :
    let theta := actualExtendedThirdRescueParameter e m j t
    let B := (N : ℝ) ^ (2 * theta - 1)
    let C := (N : ℝ) ^ (1 - theta - e / 32) / A
    let D := (N : ℝ) ^ (theta - e / 32)
    let U := (N : ℝ) ^ (actualSelectedSubproductUpper 1 theta - (2 * theta - 1) - e / 8)
    let out := complete (fun n : ℕ => (n : ℝ)) A B C (initialBins A p) (p 2 :: tail)
    Trace (initialBins A p) (p 2 :: tail) out ∧
      total (fun n : ℕ => (n : ℝ)) out = (state.selectedPrefix.prod : ℝ) ∧
      (Bounded (fun n : ℕ => (n : ℝ)) A B C out ∨
        (B < wp (fun n : ℕ => (n : ℝ)) out.middle ∧
          wp (fun n : ℕ => (n : ℝ)) out.middle ≤ B * U ∧
          wp (fun n : ℕ => (n : ℝ)) out.left ≤ A ∧
          wp (fun n : ℕ => (n : ℝ)) out.right ≤
            D / (A * wp (fun n : ℕ => (n : ℝ)) out.middle))) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist k
    (actualExtendedThirdCompactUpperPolicy e h m N) weight
    (roughPrimeUniverse N cap w z) state hstate
  have hpos : ∀ q ∈ p 0 :: p 1 :: p 2 :: tail, 0 < q := by
    intro q hq
    rw [← hshape] at hq
    exact (mem_roughPrimeUniverse_prime (hsub.subset hq)).pos
  have hp (i : Fin 3) : 0 < p i := by
    apply hpos
    fin_cases i <;> simp
  obtain ⟨hlo, hhi, hlevel, hfirst, hlate, hrest⟩ :=
    actual_W_gap_initial_two_slots he0 he hmesh hfull ht hwinner hgap
      (N : ℝ) hNr p hp hs
  obtain ⟨hB, hC, hcaps, hprod, hleft, hright⟩ := hrest A hA hAupper
  let theta := actualExtendedThirdRescueParameter e m j t
  let B := (N : ℝ) ^ (2 * theta - 1)
  let C := (N : ℝ) ^ (1 - theta - e / 32) / A
  let D := (N : ℝ) ^ (theta - e / 32)
  let U := (N : ℝ) ^ (actualSelectedSubproductUpper 1 theta - (2 * theta - 1) - e / 8)
  have hinit : Bounded (fun n : ℕ => (n : ℝ)) A B C (initialBins A p) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [initialBins, wp, actualTwoCapacityFactors, actualNatList_cast_prod] using hleft
    · simpa [initialBins, wp] using hfirst
    · simpa [initialBins, wp, actualTwoCapacityFactors, actualNatList_cast_prod] using hright
  have hseed : total (fun n : ℕ => (n : ℝ)) (initialBins A p) =
      wp (fun n : ℕ => (n : ℝ)) [p 0, p 1] := by
    have hh := congrArg (fun n : ℕ => (n : ℝ)) hprod
    simpa [total, initialBins, wp, actualTwoCapacityFactors,
      actualNatList_cast_prod, Nat.cast_mul] using hh
  have hsort : (p 0 :: p 1 :: p 2 :: tail).Pairwise (· > ·) := by
    rw [← hshape]
    exact (roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub
  have hthird : (p 2 :: tail).Pairwise (· > ·) :=
    (List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).2
  have hslots : ∀ q ∈ p 2 :: tail, (0 : ℝ) < q ∧ (q : ℝ) ≤ U := by
    intro q hq
    refine ⟨by exact_mod_cast hpos q (by simp only [List.mem_cons] at hq ⊢; tauto), ?_⟩
    have hqle : q ≤ p 2 := by
      rcases List.mem_cons.mp hq with rfl | hqtail
      · exact le_rfl
      · exact ((List.pairwise_cons.mp hthird).1 q hqtail).le
    exact (by exact_mod_cast hqle : (q : ℝ) ≤ p 2).trans hlate
  have horiginal := actual_compact_frontier_all_rank_support e h m N cap k hk w z weight
    state hstate hj howned
  have hsupport : PrefixSquareBound (fun n : ℕ => (n : ℝ)) D
      ([p 0, p 1] ++ p 2 :: tail) := by
    rw [hshape] at horiginal
    intro i hi
    exact (horiginal i hi).trans
      (Real.rpow_le_rpow_of_exponent_le hNr.le (by dsimp [theta]; linarith))
  obtain ⟨htrace, htotal, hcases⟩ := complete_correct (fun n : ℕ => (n : ℝ))
    (U := U) (zero_lt_one.trans_le hA) hinit (initialBins_positive A p hp)
    hslots hseed hsupport
  refine ⟨htrace, ?_, hcases⟩
  calc
    _ = wp (fun n : ℕ => (n : ℝ)) ([p 0, p 1] ++ p 2 :: tail) := htotal
    _ = (state.selectedPrefix.prod : ℝ) := by
      change ((p 0 :: p 1 :: p 2 :: tail).map (fun n : ℕ => (n : ℝ))).prod = _
      rw [← hshape, actualNatList_cast_prod, List.prod_reverse]

end

end ImbalancedChen.Part3.ActualWResidualCompletion
