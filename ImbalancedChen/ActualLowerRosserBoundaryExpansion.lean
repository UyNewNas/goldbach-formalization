import ImbalancedChen.ActualRosserBoundaryExpansion

/-!
# Exact boundary loss of the actual lower Rosser density

At the literal level `ceil R`, the normalized density is one minus a finite
sum of nonnegative first-boundary contributions. A tail has odd cardinality;
adjoining its distinguished least prime gives an even boundary. The physical
prime carrier still excludes every prime dividing the target. All statements
are finite identities or inequalities, with no analytic premise.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Finite telescoping of the exact one-prime lower recurrence. -/
theorem lowerRosserSetDensityRatio_eq_one_sub_sum_boundary
    (nu : ℕ → ℝ) {D : ℕ} (P : Finset ℕ) (hD : 1 < D)
    (hprime : ∀ p ∈ P, p.Prime) (hpD : ∀ p ∈ P, p < D)
    (hfactor : ∀ p ∈ P, 1 - nu p ≠ 0) :
    LinearSieve.lowerRosserSetDensitySum nu D P / ∏ p ∈ P, (1 - nu p) =
      1 - ∑ q ∈ P,
        (nu q / (1 - nu q)) *
          ((∑ s ∈ (P.filter (fun p => q < p)).powerset.filter
                (LinearSieve.LowerRosserBoundarySet D q),
              ∏ p ∈ s, nu p) /
            ∏ p ∈ P.filter (fun p => q < p), (1 - nu p)) := by
  induction P using Finset.induction_on_min with
  | empty =>
      simp [LinearSieve.lowerRosserSetDensitySum, LinearSieve.lowerRosserSetWeight,
        LinearSieve.LowerRosserAdmissibleSet, hD]
  | @insert q P hqmin ih =>
      have hq : q ∉ P := by
        intro hqP
        have := hqmin q hqP
        omega
      have htail : (insert q P).filter (fun p => q < p) = P := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hp, hlt⟩
          · omega
          · exact hp
        · intro hp
          exact ⟨Or.inr hp, hqmin p hp⟩
      have hfilter (r : ℕ) (hr : r ∈ P) :
          (insert q P).filter (fun p => r < p) = P.filter (fun p => r < p) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hp, hlt⟩
          · have := hqmin r hr
            omega
          · exact ⟨hp, hlt⟩
        · rintro ⟨hp, hlt⟩
          exact ⟨Or.inr hp, hlt⟩
      have hrec := LinearSieve.lowerRosserSetDensityRatio_insert_min nu hq
        (hprime q (Finset.mem_insert_self q P))
        (hpD q (Finset.mem_insert_self q P))
        (fun p hp => Nat.le_of_lt (hqmin p hp))
        (hfactor q (Finset.mem_insert_self q P))
        (Finset.prod_ne_zero_iff.mpr (fun p hp =>
          hfactor p (Finset.mem_insert_of_mem hp)))
      rw [hrec]
      rw [ih (fun p hp => hprime p (Finset.mem_insert_of_mem hp))
        (fun p hp => hpD p (Finset.mem_insert_of_mem hp))
        (fun p hp => hfactor p (Finset.mem_insert_of_mem hp))]
      rw [Finset.sum_insert hq, htail]
      have hsum :
          (∑ r ∈ P,
            nu r / (1 - nu r) *
              ((∑ s ∈ ((insert q P).filter (fun p => r < p)).powerset.filter
                    (LinearSieve.LowerRosserBoundarySet D r),
                  ∏ p ∈ s, nu p) /
                ∏ p ∈ (insert q P).filter (fun p => r < p), (1 - nu p))) =
          ∑ r ∈ P,
            nu r / (1 - nu r) *
              ((∑ s ∈ (P.filter (fun p => r < p)).powerset.filter
                    (LinearSieve.LowerRosserBoundarySet D r),
                  ∏ p ∈ s, nu p) /
                ∏ p ∈ P.filter (fun p => r < p), (1 - nu p)) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hfilter r hr]
      rw [hsum]
      ring

/-- Exact subset-density dictionary for the actual lower coefficient. -/
theorem actualSmallRosserMinusDensity_eq_setDensitySum
    (N cap : ℕ) (hEven : Even N) (y R : ℝ) (hcap : y ≤ (cap : ℝ)) :
    actualSmallRosserMinusDensity N cap y R =
      LinearSieve.lowerRosserSetDensitySum (fun p : ℕ => 1 / ((p : ℝ) - 1))
        (Nat.ceil R) (actualSmallPrimeFinset N cap y) := by
  rw [actualSmallRosserMinusDensity_eq_b8_mainSum_natCeil N cap hEven y R hcap,
    LinearSieve.mainSum_lowerRosserWeight_eq_setDensitySum]
  unfold LinearSieve.lowerRosserSetDensitySum
  change (∑ s ∈ (goldbachB10ProdPrimes N y).primeFactors.powerset,
    LinearSieve.lowerRosserSetWeight (Nat.ceil R) s *
      ∏ p ∈ s, (goldbachB8PlusBoundingSieve N hEven y).nu p) = _
  rw [goldbachB10ProdPrimes_primeFactors,
    ← actualSmallPrimeFinset_eq_goldbachB10SiftingPrimes N cap y hcap]
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := actualSmallPrimeFinset_prime N cap y p
    (Finset.mem_powerset.mp hs hp)
  rw [goldbachB8PlusBoundingSieve_nu_eq_inv_totient,
    Nat.totient_prime hprime, Nat.cast_sub hprime.one_le, Nat.cast_one]

/-- Odd tails above their distinguished least prime in the actual carrier. -/
def actualLowerRosserBoundarySets (N cap : ℕ) (y R : ℝ) (q : ℕ) :
    Finset (Finset ℕ) :=
  ((actualSmallPrimeFinset N cap y).filter (fun p => q < p)).powerset.filter
    (LinearSieve.LowerRosserBoundarySet (Nat.ceil R) q)

/-- The same positive Euler-ratio term, now selected by the lower boundary. -/
def actualLowerRosserBoundaryTerm (N cap : ℕ) (y : ℝ) (q : ℕ) (s : Finset ℕ) : ℝ :=
  actualUpperRosserBoundaryTerm N cap y q s

theorem actualLowerRosserBoundaryTerm_nonneg
    (N cap : ℕ) (hEven : Even N) (y : ℝ) {q : ℕ} {s : Finset ℕ}
    (hq : q ∈ actualSmallPrimeFinset N cap y)
    (hs : s ⊆ actualSmallPrimeFinset N cap y) :
    0 ≤ actualLowerRosserBoundaryTerm N cap y q s :=
  actualUpperRosserBoundaryTerm_nonneg N cap hEven y hq hs

/-- Exact finite expansion of the actual lower density as one minus its
nonnegative even-boundary loss. -/
theorem actualSmallRosserMinusDensity_ratio_eq_one_sub_boundary
    (N cap : ℕ) (hEven : Even N) (y R : ℝ)
    (hcap : y ≤ (cap : ℝ)) (hR : 1 < R)
    (hlevel : ∀ p ∈ actualSmallPrimeFinset N cap y, (p : ℝ) < R) :
    actualSmallRosserMinusDensity N cap y R / actualSmallEulerProduct N cap y =
      1 - ∑ q ∈ actualSmallPrimeFinset N cap y,
        ∑ s ∈ actualLowerRosserBoundarySets N cap y R q,
          actualLowerRosserBoundaryTerm N cap y q s := by
  rw [actualSmallRosserMinusDensity_eq_setDensitySum N cap hEven y R hcap]
  change LinearSieve.lowerRosserSetDensitySum (fun p : ℕ => 1 / ((p : ℝ) - 1))
      (Nat.ceil R) (actualSmallPrimeFinset N cap y) /
      (∏ p ∈ actualSmallPrimeFinset N cap y, (1 - 1 / ((p : ℝ) - 1))) = _
  rw [lowerRosserSetDensityRatio_eq_one_sub_sum_boundary
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) (actualSmallPrimeFinset N cap y)
    (Nat.lt_ceil.mpr (by simpa only [Nat.cast_one] using hR))
    (actualSmallPrimeFinset_prime N cap y)
    (fun p hp => Nat.lt_ceil.mpr (hlevel p hp))
    (fun p hp => ne_of_gt (actualSmallPrimeFinset_euler_factor_pos hEven hp))]
  apply congrArg (fun x : ℝ => 1 - x)
  apply Finset.sum_congr rfl
  intro q hq
  change ((1 / ((q : ℝ) - 1)) / (1 - 1 / ((q : ℝ) - 1))) *
      ((∑ s ∈ actualLowerRosserBoundarySets N cap y R q,
          ∏ p ∈ s, 1 / ((p : ℝ) - 1)) /
        (∏ p ∈ (actualSmallPrimeFinset N cap y).filter (fun p => q < p),
          (1 - 1 / ((p : ℝ) - 1)))) = _
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  exact actualSmallEulerProduct_boundary_term N cap hEven y hq
    (∏ p ∈ s, 1 / ((p : ℝ) - 1))

/-- Dropping only genuine nonnegative loss terms yields an upper bound for
the actual lower coefficient density. -/
theorem actualSmallRosserMinusDensity_ratio_le_selected_boundary
    (N cap : ℕ) (hEven : Even N) (y R : ℝ)
    (hcap : y ≤ (cap : ℝ)) (hR : 1 < R)
    (hlevel : ∀ p ∈ actualSmallPrimeFinset N cap y, (p : ℝ) < R)
    (Q : Finset ℕ) (T : ℕ → Finset (Finset ℕ))
    (hQ : Q ⊆ actualSmallPrimeFinset N cap y)
    (hT : ∀ q ∈ Q, T q ⊆ actualLowerRosserBoundarySets N cap y R q) :
    actualSmallRosserMinusDensity N cap y R / actualSmallEulerProduct N cap y ≤
      1 - ∑ q ∈ Q, ∑ s ∈ T q, actualLowerRosserBoundaryTerm N cap y q s := by
  rw [actualSmallRosserMinusDensity_ratio_eq_one_sub_boundary
    N cap hEven y R hcap hR hlevel]
  apply sub_le_sub_left
  have hterm (q : ℕ) (hq : q ∈ actualSmallPrimeFinset N cap y)
      (s : Finset ℕ) (hs : s ∈ actualLowerRosserBoundarySets N cap y R q) :
      0 ≤ actualLowerRosserBoundaryTerm N cap y q s := by
    apply actualLowerRosserBoundaryTerm_nonneg N cap hEven y hq
    exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1).trans
      (Finset.filter_subset _ _)
  calc
    (∑ q ∈ Q, ∑ s ∈ T q, actualLowerRosserBoundaryTerm N cap y q s) ≤
        ∑ q ∈ Q, ∑ s ∈ actualLowerRosserBoundarySets N cap y R q,
          actualLowerRosserBoundaryTerm N cap y q s := by
      apply Finset.sum_le_sum
      intro q hq
      exact Finset.sum_le_sum_of_subset_of_nonneg (hT q hq)
        (fun s hs _ => hterm q (hQ hq) s hs)
    _ ≤ ∑ q ∈ actualSmallPrimeFinset N cap y,
        ∑ s ∈ actualLowerRosserBoundarySets N cap y R q,
          actualLowerRosserBoundaryTerm N cap y q s :=
      Finset.sum_le_sum_of_subset_of_nonneg hQ
        (fun q hq _ => Finset.sum_nonneg (fun s hs => hterm q hq s hs))

/-- A lower estimate for a genuinely selected finite boundary loss gives
the corresponding upper estimate for the same actual lower density. -/
theorem actualSmallRosserMinusDensity_ratio_le_of_selected_boundary_loss
    (N cap : ℕ) (hEven : Even N) (y R : ℝ)
    (hcap : y ≤ (cap : ℝ)) (hR : 1 < R)
    (hlevel : ∀ p ∈ actualSmallPrimeFinset N cap y, (p : ℝ) < R)
    (Q : Finset ℕ) (T : ℕ → Finset (Finset ℕ))
    (hQ : Q ⊆ actualSmallPrimeFinset N cap y)
    (hT : ∀ q ∈ Q, T q ⊆ actualLowerRosserBoundarySets N cap y R q)
    (L : ℝ)
    (hL : L ≤ ∑ q ∈ Q, ∑ s ∈ T q, actualLowerRosserBoundaryTerm N cap y q s) :
    actualSmallRosserMinusDensity N cap y R / actualSmallEulerProduct N cap y ≤ 1 - L :=
  (actualSmallRosserMinusDensity_ratio_le_selected_boundary
    N cap hEven y R hcap hR hlevel Q T hQ hT).trans (sub_le_sub_left hL 1)

end

end ImbalancedChen
