import ImbalancedChen.P1OriginalHistoricalCanonicalTrace
import ImbalancedChen.P1OriginalHistoricalRankedBeta

/-!
The original historical coefficient is grouped by its COMPLETE actual
old/fresh decision word. The rank bound fixes a finite code type before N.
These fibres retain all arithmetic policy tests; no fibre is asserted to
be a Cartesian box or an affine atom. The original beta choice and the
filter on the complete small/rough product are unchanged.
-/
namespace ImbalancedChen.P1OriginalHistoricalFiniteTraceFamily
noncomputable section
open Classical
open scoped BigOperators
open P4AUpperTaggedFirstPrefixDisagreement (decisionAt)
open P1OriginalHistoricalCoefficientDictionary
open P1OriginalHistoricalCanonicalTrace
open P1OriginalHistoricalRankedBeta
open P1Full87TrueDPolicyDelta (trueDDeltaSupport trueDDeltaRho)
open P1Full87HistoricalMiddleSmoothing (remainingModuli)

private theorem validSelection_iff_decisions {α : Type*}
    (P : Bool → List α → Bool) (pre : List α) (positive : Bool) (xs : List α) :
    FirstExitValidSelection P pre positive xs ↔
      ∀ k : ℕ, k < xs.length → decisionAt P pre positive xs k = true := by
  induction xs generalizing pre positive with
  | nil => simp [FirstExitValidSelection]
  | cons p ps ih =>
    rw [FirstExitValidSelection, ih]
    constructor
    · rintro ⟨hhead, htail⟩ k hk
      cases k with
      | zero => exact hhead
      | succ k => exact htail k (by simpa using hk)
    · intro h
      exact ⟨h 0 (by simp), fun k hk => h (k + 1) (by simpa using hk)⟩

private theorem decisionAt_padding {α : Type*} (P : Bool → List α → Bool)
    (pre : List α) (positive : Bool) (xs : List α) (k : ℕ)
    (hk : xs.length ≤ k) : decisionAt P pre positive xs k = true := by
  induction xs generalizing pre positive k with
  | nil => rfl
  | cons p ps ih =>
    cases k with
    | zero => simp at hk
    | succ k => exact ih (p :: pre) (!positive) k (by simpa using hk)

private theorem validSelection_iff_bounded_decisions {α : Type*}
    (P : Bool → List α → Bool) (pre : List α) (positive : Bool)
    (xs : List α) (R : ℕ) (hlen : xs.length ≤ R) :
    FirstExitValidSelection P pre positive xs ↔
      ∀ i : Fin R, decisionAt P pre positive xs i.val = true := by
  rw [validSelection_iff_decisions]
  constructor
  · intro h i
    by_cases hi : i.val < xs.length
    · exact h i.val hi
    · exact decisionAt_padding P pre positive xs i.val (Nat.le_of_not_gt hi)
  · intro h k hk
    exact h ⟨k, hk.trans_le hlen⟩

/-- The two complete decision words, including all proper-prefix tests.
Out-of-range positions are true by the actual decisionAt recursion. -/
abbrev TraceCode (R : ℕ) := Fin R → Bool × Bool

def canonicalCode (R : ℕ) (old fresh : List ℕ → Bool) (b : ℕ) : TraceCode R :=
  fun i =>
    (decisionAt (oddFirstExitPolicy old) [] true b.primeFactorsList.reverse i.val,
     decisionAt (oddFirstExitPolicy fresh) [] true b.primeFactorsList.reverse i.val)

def traceMask {R : ℕ} (s : TraceCode R) : ℝ :=
  (if ∀ i, (s i).2 = true then 1 else 0) -
    (if ∀ i, (s i).1 = true then 1 else 0)

theorem traceCode_card (R : ℕ) : Fintype.card (TraceCode R) = 4 ^ R := by
  simp [TraceCode]

theorem traceMask_abs_le_one {R : ℕ} (s : TraceCode R) : |traceMask s| ≤ 1 := by
  unfold traceMask
  split_ifs <;> norm_num

/-- The actual fresh-minus-old mask is determined by this fixed finite code.
No endpoint-stability or affine classification premise is introduced. -/
theorem rough_mask_eq_traceMask (R : ℕ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) {b : ℕ}
    (hb : b ∈ commonRoughSupport old fresh N cap w z) (hr : roughRank b ≤ R) :
    roughMaskDelta old fresh N cap w z b = traceMask (canonicalCode R old fresh b) := by
  have hlen : b.primeFactorsList.reverse.length ≤ R := by
    simpa only [List.length_reverse, roughRank] using hr
  rw [rough_mask_eq_canonical_trace_difference old fresh N cap w z b hb]
  have ho := validSelection_iff_bounded_decisions (oddFirstExitPolicy old)
    [] true b.primeFactorsList.reverse R hlen
  have hf := validSelection_iff_bounded_decisions (oddFirstExitPolicy fresh)
    [] true b.primeFactorsList.reverse R hlen
  simp only [traceMask, canonicalCode, ho, hf]
  rfl

/-- Only rough rows with some surviving COMPLETE small attachment are kept.
The omitted rows contribute zero for every arithmetic test. -/
def activeRough (B : ℝ) (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  (commonRoughSupport old fresh N cap w z).filter (fun b =>
    ∃ a ∈ actualSmallRosserSupport N cap w,
      a * b ∈ remainingModuli B N (trueDDeltaSupport old fresh N cap w z))

def codeFibre (B : ℝ) (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (R r : ℕ) (s : TraceCode R) : Finset ℕ :=
  (activeRough B old fresh N cap w z).filter
    (fun b => (roughRank b, canonicalCode R old fresh b) = (r, s))

theorem activeRough_rank_le {N cap : ℕ} (hN : 1 < N) (old fresh : List ℕ → Bool)
    (rho z B : ℝ) (hrho : 0 < rho) {b : ℕ}
    (hb : b ∈ activeRough B old fresh N cap ((N : ℝ) ^ rho) z) :
    roughRank b ≤ rankBound rho := by
  obtain ⟨hc, a, ha, hq⟩ := Finset.mem_filter.mp hb
  exact remaining_rough_rank_le hN old fresh rho z B hrho ha hc hq

def exterior {R : ℕ} (r : ℕ) (s : TraceCode R) : ℂ :=
  (traceMask s : ℂ) * ((-1 : ℝ) ^ r : ℂ)

theorem exterior_norm_le_one {R : ℕ} (r : ℕ) (s : TraceCode R) :
    ‖exterior r s‖ ≤ 1 := by
  simpa only [exterior, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_pow, norm_neg, norm_one, Complex.ofReal_neg, Complex.ofReal_one,
    abs_pow, abs_neg, abs_one, one_pow, mul_one] using traceMask_abs_le_one s

/-- This budget depends on the fixed code rank only, before N, policies,
the actual rough rows or arithmetic tests. It is a TRACE-fibre budget,
not a norm estimate for a later rectangular refinement. -/
theorem exterior_norm_sum_le (R : ℕ) :
    (∑ r ∈ Finset.range (R + 1), ∑ s : TraceCode R, ‖exterior r s‖) ≤
      (((R + 1) * 4 ^ R : ℕ) : ℝ) := by
  calc
    _ ≤ ∑ _r ∈ Finset.range (R + 1), ∑ _s : TraceCode R, (1 : ℝ) :=
      Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun s _ => exterior_norm_le_one r s))
    _ = _ := by simp [Nat.cast_mul]

/-- Exact original signed coefficient, indexed by a fixed finite family.
The beta sign uses the original rough rank BEFORE the retention mask.
The pan lower bound and strict .599 ceiling remain on the same a*b. -/
theorem remaining_test_eq_finite_trace_sum {N cap : ℕ} (hN : 1 < N)
    (old fresh : List ℕ → Bool) (rho z B L : ℝ) (hrho : 0 < rho) (G : ℕ → ℂ) :
    (∑ q ∈ remainingModuli B N (trueDDeltaSupport old fresh N cap ((N : ℝ) ^ rho) z),
      (trueDDeltaRho old fresh N cap ((N : ℝ) ^ rho) z L q : ℂ) * G q) =
    ∑ r ∈ Finset.range (rankBound rho + 1), ∑ s : TraceCode (rankBound rho),
      exterior r s *
        ∑ b ∈ codeFibre B old fresh N cap ((N : ℝ) ^ rho) z (rankBound rho) r s,
          ∑ a ∈ actualSmallRosserSupport N cap ((N : ℝ) ^ rho),
            (rankBeta N cap ((N : ℝ) ^ rho) L r a : ℂ) *
              (if a * b ∈ remainingModuli B N
                (trueDDeltaSupport old fresh N cap ((N : ℝ) ^ rho) z)
                then G (a * b) else 0) := by
  let F (b : ℕ) : ℂ :=
    ∑ a ∈ actualSmallRosserSupport N cap ((N : ℝ) ^ rho),
      (roughMaskDelta old fresh N cap ((N : ℝ) ^ rho) z b : ℂ) *
        (attachedMobius N cap ((N : ℝ) ^ rho) L a b : ℂ) *
          (if a * b ∈ remainingModuli B N
            (trueDDeltaSupport old fresh N cap ((N : ℝ) ^ rho) z) then G (a * b) else 0)
  rw [remaining_trueDDeltaRho_test_eq_pair_sum, Finset.sum_comm]
  change (∑ b ∈ commonRoughSupport old fresh N cap ((N : ℝ) ^ rho) z, F b) = _
  have hactive : (∑ b ∈ commonRoughSupport old fresh N cap ((N : ℝ) ^ rho) z, F b) =
      ∑ b ∈ activeRough B old fresh N cap ((N : ℝ) ^ rho) z, F b := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b hb hout
    apply Finset.sum_eq_zero
    intro a ha
    have hn : a * b ∉ remainingModuli B N
        (trueDDeltaSupport old fresh N cap ((N : ℝ) ^ rho) z) := by
      intro hq
      exact hout (Finset.mem_filter.mpr ⟨hb, a, ha, hq⟩)
    simp only [if_neg hn, mul_zero]
  rw [hactive]
  have hpartition := Finset.sum_fiberwise_of_maps_to
    (s := activeRough B old fresh N cap ((N : ℝ) ^ rho) z)
    (t := (Finset.range (rankBound rho + 1)).product
      (Finset.univ : Finset (TraceCode (rankBound rho))))
    (g := fun b => (roughRank b, canonicalCode (rankBound rho) old fresh b))
    (fun b hb => Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le
        (activeRough_rank_le (cap := cap) hN old fresh rho z B hrho hb)), Finset.mem_univ _⟩) F
  rw [← hpartition]
  calc
    _ = ∑ r ∈ Finset.range (rankBound rho + 1), ∑ s : TraceCode (rankBound rho),
        ∑ b ∈ codeFibre B old fresh N cap ((N : ℝ) ^ rho) z (rankBound rho) r s,
          F b := Finset.sum_product _ _ _
    _ = _ := ?_
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  obtain ⟨ha, heq⟩ := Finset.mem_filter.mp hb
  have hc := (Finset.mem_filter.mp ha).1
  have hr : roughRank b = r := congrArg Prod.fst heq
  have hs : canonicalCode (rankBound rho) old fresh b = s := congrArg Prod.snd heq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [attachedMobius_eq_rank_beta old fresh N cap ((N : ℝ) ^ rho) z L hc hr a,
    rough_mask_eq_traceMask (rankBound rho) old fresh N cap ((N : ℝ) ^ rho) z hc
      (activeRough_rank_le (cap := cap) hN old fresh rho z B hrho ha), hs]
  simp only [exterior, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

end
end ImbalancedChen.P1OriginalHistoricalFiniteTraceFamily
