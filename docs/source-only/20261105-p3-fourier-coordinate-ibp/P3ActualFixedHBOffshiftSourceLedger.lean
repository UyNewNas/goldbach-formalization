import ImbalancedChen.P3ActualOffshiftSignedPhysicalDivisorMean
import ImbalancedChen.P3ActualFrozenWholeBoxHBFixedFibre
import ImbalancedChen.P3ActualFrozenThreeWholeBoxHBTarget

/-!
P3.6 / manuscript 9731290e8f53cffda44129906cde6a965eaa869b
§§2–4. Full three independent fine-prime boxes with genuine fixed-product
HB words. Exact signed physical Q response on NONZERO whole-product
shifts is split into divisors and the ORIGINAL primitive mean.

The complete product=N case is killed by the actual rough-HB coefficient
BEFORE any natural-number divisors are formed. No analytic savings,
full PP compiler exhaustiveness or Fourier uniformity is assumed.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualFixedHBOffshiftSourceLedger
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualFrozenWholeBoxHBFixedFibre
open ImbalancedChen.P3ActualFrozenThreeWholeBoxHBTarget
open ImbalancedChen.P3ActualFrozenTaggedPrimeBox
open ImbalancedChen.P3ActualOffshiftSignedPhysicalDivisorMean
open ImbalancedChen.P3ActualMarkedOffShiftDivisors
open ImbalancedChen.P3HBOriginalMarkedFineTarget
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords

/-- The actual fixed-product HB positional mass is ZERO on the whole
three-box diagonal. W may depend on all ordered HB slots. -/
theorem hbPositionalMass_zero_of_actual_target
    (N m j : ℕ) (τ z y : ℝ) (u v w a b d : List ℕ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (ha : a ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) u)
    (hb : b ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) v)
    (hd : d ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) w)
    (hz : (2 : ℝ) ≤ z) (hN : Even N)
    (htarget : a.prod * b.prod * d.prod * m = N) :
    hbPositionalMass m j z y W a b d = 0 := by
  unfold hbPositionalMass
  apply Finset.sum_eq_zero
  intro h hh
  have hprod : h.prod = m :=
    (factorTuples_spec (2 * (j + 1)) m h hh).2.1
  have hmarked : a ++ b ++ d ∈
      actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
        (u ++ v ++ w) :=
    three_prime_boxes_whole_mem _ u v w a b d ha hb hd
  have hfull : (a ++ b ++ d).prod * h.prod = N := by
    simp only [List.prod_append]
    rw [hprod]
    simpa only [mul_assoc] using htarget
  have hzero : roughTupleWeight z y (roles j) h = 0 :=
    original_marked_fine_rough_occurrence_target_zero
      N m j τ z y (u ++ v ++ w) (a ++ b ++ d) h
      hz hN hmarked hh hfull
  simp [hzero]

/-- Exact signed count, ONLY at nonzero complete-product shifts.
The same integer physical rho appears in the two ledger components. -/
def fixedThreeHBOffshiftCount
    (N m j : ℕ) (τ z y : ℝ) (u v w : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ) : ℂ :=
  let B := actualPrimeFineLabelFinset N τ
  ∑ a ∈ actualPrimeSlotBox B u,
    ∑ b ∈ actualPrimeSlotBox B v,
      ∑ d ∈ actualPrimeSlotBox B w,
        if a.prod * b.prod * d.prod * m = N then 0 else
          hbPositionalMass m j z y W a b d *
            (∑ q ∈ Q.filter (fun q =>
              q ∈ (markedShiftAbs (a.prod * b.prod * d.prod) N m).divisors),
              (rho q : ℂ))

/-- Exact coprime mean; its gcd concerns the FULL product (not m). -/
def fixedThreeHBOffshiftMean
    (N m j : ℕ) (τ z y : ℝ) (u v w : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ) : ℂ :=
  let B := actualPrimeFineLabelFinset N τ
  ∑ a ∈ actualPrimeSlotBox B u,
    ∑ b ∈ actualPrimeSlotBox B v,
      ∑ d ∈ actualPrimeSlotBox B w,
        if a.prod * b.prod * d.prod * m = N then 0 else
          hbPositionalMass m j z y W a b d *
            (∑ q ∈ Q.filter (fun q =>
              Nat.Coprime (a.prod * b.prod * d.prod * m) q),
              (rho q : ℂ) * (((Nat.totient q : ℝ)⁻¹ : ℝ) : ℂ))

/-- Exact genuine physical three-box HB signed-response reduction.
The diagonal is PAID, not assumed small; divisor(0) is never formed.
This is not yet a mixed shifted-divisor moment estimate. -/
theorem fixedThreeHB_sameRho_offshift_count_sub_mean
    (N m j : ℕ) (τ z y : ℝ) (u v w : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    (∑ q ∈ Q, (rho q : ℂ) *
      threeWholeHBAtQ N m j q τ z y u v w W) =
      fixedThreeHBOffshiftCount N m j τ z y u v w Q rho W -
      fixedThreeHBOffshiftMean N m j τ z y u v w Q rho W := by
  rw [threeWholeHB_sameRho_fixed]
  unfold fixedThreeHBOffshiftCount fixedThreeHBOffshiftMean
  dsimp only
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases htarget : a.prod * b.prod * d.prod * m = N
  · have hzero := hbPositionalMass_zero_of_actual_target
      N m j τ z y u v w a b d W ha hb hd hz hN htarget
    simp [htarget, hzero]
  · rw [sameRhoFixedProductResponse_offshift_count_mean
      N (a.prod * b.prod * d.prod) m Q rho htarget]
    simp only [if_neg htarget]
    ring

/-- The genuine order-three HB signs +3,-3,+1 survive intact; this
is a fixed-three-box SOURCE statement, not all-compiler admission. -/
theorem fixedThreeHB_signed_all_occurrences_offshift
    (N m : ℕ) (τ z y : ℝ) (u v w : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (W : ℕ → List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    (∑ j ∈ Finset.range 3,
      ((((-1 : ℝ)^j * (Nat.choose 3 (j+1) : ℝ) : ℝ) : ℂ)) *
        (∑ q ∈ Q, (rho q : ℂ) *
          threeWholeHBAtQ N m j q τ z y u v w (W j))) =
    ∑ j ∈ Finset.range 3,
      ((((-1 : ℝ)^j * (Nat.choose 3 (j+1) : ℝ) : ℝ) : ℂ)) *
        (fixedThreeHBOffshiftCount N m j τ z y u v w Q rho (W j) -
          fixedThreeHBOffshiftMean N m j τ z y u v w Q rho (W j)) := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [fixedThreeHB_sameRho_offshift_count_sub_mean
    N m j τ z y u v w Q rho (W j) hz hN]

end
end ImbalancedChen.P3ActualFixedHBOffshiftSourceLedger
