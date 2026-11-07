import ImbalancedChen.Part3ActualWGapInitialization

/-!
# Original-order W allocation up to its first overflow

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

This implements the manuscript section 5 instruction to insert whole slots
into three capacities until the first slot that fits none.  Ties are
resolved left, middle, right.  A successful run and a first overflow are
outputs of this recursion, never hypotheses about a desired partition.
The occurrence trace retains the original input sequence, also for
repeated labels.  The original row-4 gap initialization is an actual caller.

The generic overflow arithmetic records the strict residual-capacity
inequality and the new middle-product bounds.  Finishing the two-bin
continuation and proving the analytic monomials are separate obligations.
-/

namespace ImbalancedChen.Part3.ActualWThreeCapacityRun

noncomputable section

open scoped Classical
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation
open ActualWGapInitialization VariableEnvelope

structure Bins (α : Type*) where
  left : List α
  middle : List α
  right : List α

def wp {α : Type*} (w : α → ℝ) (xs : List α) : ℝ := (xs.map w).prod

def total {α : Type*} (w : α → ℝ) (g : Bins α) : ℝ :=
  wp w g.left * wp w g.middle * wp w g.right

def putLeft {α : Type*} (g : Bins α) (p : α) : Bins α :=
  ⟨g.left ++ [p], g.middle, g.right⟩

def putMiddle {α : Type*} (g : Bins α) (p : α) : Bins α :=
  ⟨g.left, g.middle ++ [p], g.right⟩

def putRight {α : Type*} (g : Bins α) (p : α) : Bins α :=
  ⟨g.left, g.middle, g.right ++ [p]⟩

def Bounded {α : Type*} (w : α → ℝ) (A B C : ℝ) (g : Bins α) : Prop :=
  wp w g.left ≤ A ∧ wp w g.middle ≤ B ∧ wp w g.right ≤ C

/-- Every constructor assigns exactly the next original occurrence. -/
inductive Trace {α : Type*} : Bins α → List α → Bins α → Prop
  | nil (g : Bins α) : Trace g [] g
  | left (g : Bins α) (p : α) {xs : List α} {out : Bins α} :
      Trace (putLeft g p) xs out → Trace g (p :: xs) out
  | middle (g : Bins α) (p : α) {xs : List α} {out : Bins α} :
      Trace (putMiddle g p) xs out → Trace g (p :: xs) out
  | right (g : Bins α) (p : α) {xs : List α} {out : Bins α} :
      Trace (putRight g p) xs out → Trace g (p :: xs) out

theorem Trace.product {α : Type*} {g out : Bins α} {xs : List α}
    (h : Trace g xs out) (w : α → ℝ) :
    total w out = total w g * wp w xs := by
  induction h with
  | nil g => simp [wp]
  | left g p h ih =>
      simpa [total, putLeft, wp, mul_assoc, mul_comm, mul_left_comm] using ih
  | middle g p h ih =>
      simpa [total, putMiddle, wp, mul_assoc, mul_comm, mul_left_comm] using ih
  | right g p h ih =>
      simpa [total, putRight, wp, mul_assoc, mul_comm, mul_left_comm] using ih

inductive Outcome (α : Type*) where
  | done (bins : Bins α)
  | overflow (bins : Bins α) (slot : α) (rest : List α)

/-- Stop without consuming the first overflowing slot. -/
def run {α : Type*} (w : α → ℝ) (A B C : ℝ) :
    Bins α → List α → Outcome α
  | g, [] => .done g
  | g, p :: xs =>
      if wp w g.left * w p ≤ A then run w A B C (putLeft g p) xs
      else if wp w g.middle * w p ≤ B then run w A B C (putMiddle g p) xs
      else if wp w g.right * w p ≤ C then run w A B C (putRight g p) xs
      else .overflow g p xs

def RunSpec {α : Type*} (w : α → ℝ) (A B C : ℝ)
    (initial : Bins α) (input : List α) : Outcome α → Prop
  | .done g => Bounded w A B C g ∧ Trace initial input g
  | .overflow g p rest => ∃ prefix,
      input = prefix ++ p :: rest ∧ Bounded w A B C g ∧
      Trace initial prefix g ∧
      A < wp w g.left * w p ∧ B < wp w g.middle * w p ∧
      C < wp w g.right * w p

/-- A total correctness theorem with both genuine outcomes.  In particular
it supplies the earliest overflow and preserves the exact unread suffix. -/
theorem run_spec {α : Type*} (w : α → ℝ) (A B C : ℝ)
    (input : List α) (initial : Bins α) (hinit : Bounded w A B C initial) :
    RunSpec w A B C initial input (run w A B C initial input) := by
  induction input generalizing initial with
  | nil => exact ⟨hinit, Trace.nil initial⟩
  | cons p xs ih =>
      unfold run
      split_ifs with hl hm hr
      · have hn : Bounded w A B C (putLeft initial p) := by
          exact ⟨by simpa [putLeft, wp] using hl, hinit.2.1, hinit.2.2⟩
        have hs := ih (putLeft initial p) hn
        cases hout : run w A B C (putLeft initial p) xs with
        | done g =>
            rw [hout] at hs
            exact ⟨hs.1, Trace.left initial p hs.2⟩
        | overflow g q rest =>
            rw [hout] at hs
            obtain ⟨prefix, heq, hb, ht, hf⟩ := hs
            exact ⟨p :: prefix, by simp [heq], hb, Trace.left initial p ht, hf⟩
      · have hn : Bounded w A B C (putMiddle initial p) := by
          exact ⟨hinit.1, by simpa [putMiddle, wp] using hm, hinit.2.2⟩
        have hs := ih (putMiddle initial p) hn
        cases hout : run w A B C (putMiddle initial p) xs with
        | done g =>
            rw [hout] at hs
            exact ⟨hs.1, Trace.middle initial p hs.2⟩
        | overflow g q rest =>
            rw [hout] at hs
            obtain ⟨prefix, heq, hb, ht, hf⟩ := hs
            exact ⟨p :: prefix, by simp [heq], hb, Trace.middle initial p ht, hf⟩
      · have hn : Bounded w A B C (putRight initial p) := by
          exact ⟨hinit.1, hinit.2.1, by simpa [putRight, wp] using hr⟩
        have hs := ih (putRight initial p) hn
        cases hout : run w A B C (putRight initial p) xs with
        | done g =>
            rw [hout] at hs
            exact ⟨hs.1, Trace.right initial p hs.2⟩
        | overflow g q rest =>
            rw [hout] at hs
            obtain ⟨prefix, heq, hb, ht, hf⟩ := hs
            exact ⟨p :: prefix, by simp [heq], hb, Trace.right initial p ht, hf⟩
      · exact ⟨[], rfl, hinit, Trace.nil initial,
          lt_of_not_ge hl, lt_of_not_ge hm, lt_of_not_ge hr⟩

/-- The successful output has exact product and all three capacity bounds. -/
theorem run_done_product {α : Type*} (w : α → ℝ) (A B C : ℝ)
    {input : List α} {initial out : Bins α}
    (hinit : Bounded w A B C initial)
    (hdone : run w A B C initial input = .done out) :
    Bounded w A B C out ∧ total w out = total w initial * wp w input := by
  have hs := run_spec w A B C input initial hinit
  rw [hdone] at hs
  exact ⟨hs.1, hs.2.product w⟩

/-- The original full-square at an actual stopping slot. -/
theorem stopping_square {α : Type*} (w : α → ℝ) {D : ℝ}
    {seed input prefix rest : List α} {p : α} {initial g : Bins α}
    (hseed : total w initial = wp w seed)
    (hfull : PrefixSquareBound w D (seed ++ input))
    (hinput : input = prefix ++ p :: rest) (htrace : Trace initial prefix g) :
    total w g * w p ^ 2 ≤ D := by
  have hs : PrefixSquareBound w D ((seed ++ prefix) ++ p :: rest) := by
    simpa only [hinput, List.append_assoc] using hfull
  have hh := hs (seed ++ prefix).length (by simp)
  have heq : total w g = wp w (seed ++ prefix) := by
    rw [htrace.product w, hseed]
    simp [wp]
  rw [heq]
  simpa [wp, List.getElem_append_right] using hh

/-- Read an arbitrary square after an exact original prefix. -/
theorem suffix_square {α : Type*} (w : α → ℝ) {D : ℝ}
    {prefix rest : List α} (hfull : PrefixSquareBound w D (prefix ++ rest))
    (i : ℕ) (hi : i < rest.length) :
    (wp w prefix * wp w (rest.take i)) * w rest[i] ^ 2 ≤ D := by
  have hindex : prefix.length + i < (prefix ++ rest).length := by simp; omega
  have hh := hfull (prefix.length + i) hindex
  have htake : (prefix ++ rest).take (prefix.length + i) = prefix ++ rest.take i := by
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp
  have hget : (prefix ++ rest)[prefix.length + i]'hindex = rest[i] := by
    rw [List.getElem_append_right (by omega)]
    simp
  rw [htake, hget] at hh
  simpa [wp] using hh

/-- After the failed slot enters the middle bin, every unread square is
inherited from the same original full list.  The two existing complementary
products remain explicit; there is no reordered-square assumption. -/
theorem overflow_residual_squares {α : Type*} (w : α → ℝ) {D : ℝ}
    {seed input prefix rest : List α} {p : α} {initial g : Bins α}
    (hseed : total w initial = wp w seed)
    (hfull : PrefixSquareBound w D (seed ++ input))
    (hinput : input = prefix ++ p :: rest) (htrace : Trace initial prefix g)
    (hb : 0 < wp w g.middle) (hp : 0 < w p) :
    ∀ (i : ℕ) (hi : i < rest.length),
      ((wp w g.left * wp w g.right) * wp w (rest.take i)) * w rest[i] ^ 2 ≤
        D / (wp w g.middle * w p) := by
  have hs : PrefixSquareBound w D (((seed ++ prefix) ++ [p]) ++ rest) := by
    simpa only [hinput, List.append_assoc, List.singleton_append] using hfull
  have hpre : wp w ((seed ++ prefix) ++ [p]) = total w g * w p := by
    rw [htrace.product w, hseed]
    simp [wp, mul_assoc]
  intro i hi
  have hh := suffix_square w hs i hi
  rw [hpre] at hh
  apply (le_div_iff₀ (mul_pos hb hp)).mpr
  calc
    ((wp w g.left * wp w g.right) * wp w (rest.take i)) * w rest[i] ^ 2 *
        (wp w g.middle * w p) =
        (total w g * w p * wp w (rest.take i)) * w rest[i] ^ 2 := by
          dsimp [total]
          ring
    _ ≤ D := hh

/-- The stopping square is obtained from the actual run, without a supplied
partition, selected mask, or stopping-prefix witness. -/
theorem run_overflow_original_square {α : Type*} (w : α → ℝ) (A B C : ℝ)
    {D : ℝ} {seed input rest : List α} {p : α} {initial g : Bins α}
    (hinit : Bounded w A B C initial)
    (hseed : total w initial = wp w seed)
    (hfull : PrefixSquareBound w D (seed ++ input))
    (hstop : run w A B C initial input = .overflow g p rest) :
    (∃ prefix, input = prefix ++ p :: rest ∧ Trace initial prefix g) ∧
      Bounded w A B C g ∧
      A < wp w g.left * w p ∧ B < wp w g.middle * w p ∧
      C < wp w g.right * w p ∧ total w g * w p ^ 2 ≤ D := by
  have hs := run_spec w A B C input initial hinit
  rw [hstop] at hs
  obtain ⟨prefix, heq, hb, ht, hA, hB, hC⟩ := hs
  exact ⟨⟨prefix, heq, ht⟩, hb, hA, hB, hC,
    stopping_square w hseed hfull heq ht⟩

/-- The decisive manuscript inequality is strict.  It follows from the
failure of the first capacity and the ORIGINAL square, not a residual
support premise.  The middle-bin overflow supplies its lower bound. -/
theorem overflow_arithmetic {A B U D l b c p : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hp : 0 < p)
    (hA : 0 < A) (hleft : A < l * p) (hmiddle : B < b * p)
    (hbound : b ≤ B) (hlate : p ≤ U)
    (hsquare : (l * b * c) * p ^ 2 ≤ D) :
    B < b * p ∧ b * p ≤ B * U ∧
      A * (b * p) * c < D ∧ c < D / (A * (b * p)) := by
  have hU : 0 < U := hp.trans_le hlate
  have hnew : b * p ≤ B * U :=
    mul_le_mul hbound hlate hp.le (hb.le.trans hbound)
  have hstrict : A * (b * p) * c < D := by
    calc
      A * (b * p) * c < (l * p) * (b * c * p) := by
        nlinarith [mul_lt_mul_of_pos_right hleft (mul_pos (mul_pos hb hc) hp)]
      _ = (l * b * c) * p ^ 2 := by ring
      _ ≤ D := hsquare
  refine ⟨hmiddle, hnew, hstrict, ?_⟩
  apply (lt_div_iff₀ (mul_pos hA (mul_pos hb hp))).mpr
  nlinarith [hstrict]

/-- Actual first-two-slot allocation, retaining the two allocator lists
rather than replacing them by unrelated factors or a chosen mask. -/
def initialBins (A : ℝ) (p : Fin 3 → ℕ) : Bins ℕ :=
  let ac := actualTwoCapacityGreedy (fun n : ℕ => (n : ℝ)) A [p 1]
  ⟨ac.1, [p 0], ac.2⟩

theorem initialBins_product (A : ℝ) (p : Fin 3 → ℕ)
    {C : ℝ} (hA : 1 ≤ A) (hC : 1 ≤ C)
    (hsquare : actualDwellSupport (A * C) [p 1]) :
    total (fun n : ℕ => (n : ℝ)) (initialBins A p) =
      wp (fun n : ℕ => (n : ℝ)) [p 0, p 1] := by
  have hpart := (actualTwoCapacityGreedy_correct (fun n : ℕ => (n : ℝ))
    hA hC [p 1] hsquare).1
  have heq := hpart.prod_eq (fun n : ℕ => (n : ℝ))
  simpa [total, initialBins, wp, mul_assoc, mul_comm, mul_left_comm] using
    congrArg (fun z : ℝ => (p 0 : ℝ) * z) heq

/-- The actual least-winning row-4 gap supplies the starting bounds.
For every original suffix the recursion now produces either all three
bounded factors or a first-overflow witness.  There is no no-failure or
final-factorization premise. -/
theorem actual_W_gap_run {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hwinner : actualExtendedThirdLeastWinningIndex e m j = 4)
    (hgap : e / 4 < wInner (t 0) (t 1) (t 2) - v (t 0))
    (N : ℝ) (hN : 1 < N) (p : Fin 3 → ℕ) (hp : ∀ i, 0 < p i)
    (hs : actualSelectedPrimeCoordinates N p ∈ actualExtendedThirdPhysicalCell m j)
    (A : ℝ) (hA : 1 ≤ A) (hAupper : A ≤ N ^ (1 / 3 : ℝ))
    (tail : List ℕ) :
    let theta := actualExtendedThirdRescueParameter e m j t
    let B := N ^ (2 * theta - 1)
    let C := N ^ (1 - theta - e / 32) / A
    let initial := initialBins A p
    let suffix := p 2 :: tail
    total (fun n : ℕ => (n : ℝ)) initial = (p 0 : ℝ) * p 1 ∧
      RunSpec (fun n : ℕ => (n : ℝ)) A B C initial suffix
        (run (fun n : ℕ => (n : ℝ)) A B C initial suffix) := by
  obtain ⟨hlo, hhi, hlevel, hfirst, hlate, hrest⟩ :=
    actual_W_gap_initial_two_slots he0 he hmesh hfull ht hwinner hgap N hN p hp hs
  obtain ⟨hB, hC, hcaps, hprod, hleft, hright⟩ := hrest A hA hAupper
  have hinit : Bounded (fun n : ℕ => (n : ℝ)) A
      (N ^ (2 * actualExtendedThirdRescueParameter e m j t - 1))
      (N ^ (1 - actualExtendedThirdRescueParameter e m j t - e / 32) / A)
      (initialBins A p) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [initialBins, wp, actualTwoCapacityFactors, actualNatList_cast_prod] using hleft
    · simpa [initialBins, wp] using hfirst
    · simpa [initialBins, wp, actualTwoCapacityFactors, actualNatList_cast_prod] using hright
  refine ⟨?_, run_spec _ _ _ _ _ _ hinit⟩
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) hprod
  simpa [total, initialBins, wp, actualTwoCapacityFactors,
    actualNatList_cast_prod, Nat.cast_mul] using hcast

end

end ImbalancedChen.Part3.ActualWThreeCapacityRun
