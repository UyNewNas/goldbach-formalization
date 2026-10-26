import ImbalancedChen.P5OriginalOrdinaryPresievedSigma

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The genuine rough/common-beta coefficient majorizes the original quotient
receiver count. This is proved from the actual beta sandwich and rough
tree, rather than transferred from the all-prime native sigma. The final
ordinary sum uses the ONE explicitly named presievedSigma in its density,
signed prime AP error and centre correction. No analytic bound is supplied.
-/

namespace ImbalancedChen.P5Z.OriginalOrdinaryPresievedQuotientUpper

noncomputable section
open scoped BigOperators
open Classical
open U1011OriginalSixteenArithmeticProducts
open P5U1011JointOverlap
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryPresievedSigma
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

/-- The concrete common-beta majorant on the literal quotient source.
Only small-level and prime-carrier inequalities enter; no majorant target
or distribution hypothesis is assumed. -/
theorem quotient_upper (retainOdd : List ℕ→Bool) (N b cap : ℕ) (w z B : ℝ)
    (hB : 1<B) (hwB : w≤B) (hwz : w≤z) (hzcap : z≤(cap:ℝ)) :
    ((chenSiftedQuotientPrimeSource N b z).card:ℝ) ≤
      ∑r∈actualSmallRoughModuli retainOdd N cap w z,
        actualSmallRoughRho retainOdd N cap w z B r *
          (chenPrimeAPCount N N (b*r)-chenCentrePrimeAPCount N N (b*r)) := by
  have hsum := currentChen_quotient_sum_supportedDivisorSum N b
    (actualSmallRoughModuli retainOdd N cap w z) (actualSmallRoughRho retainOdd N cap w z B)
  rw [←hsum]
  calc
    ((chenSiftedQuotientPrimeSource N b z).card:ℝ) =
        ∑q∈chenQuotientPrimeSource N b,
          if Nat.Coprime q (sieveProduct N (Nat.ceil z)) then (1:ℝ) else 0 := by
      rw [←Finset.sum_filter,←chenSiftedQuotientPrimeSource_eq_coprime_filter]
      simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hq
      have h := actualSmallRoughRho_majorant retainOdd N cap w z B
        hB hwB hwz hzcap (q:ℤ)
      have hind : actualSmallRoughIndicator N z (q:ℤ)=
          if Nat.Coprime q (sieveProduct N (Nat.ceil z)) then (1:ℝ) else 0 := by
        unfold actualSmallRoughIndicator
        rw [←actualSmallPrimeProduct_coprime_natAbs_iff N cap z hzcap (q:ℤ)]
        simp only [Int.natAbs_natCast,
          currentChen_actualSmallPrimeProduct_eq_sieveProduct N cap z hzcap,Nat.coprime_comm]
      simpa only [hind,Int.natAbs_natCast,physicalDivisorSum,supportedDivisorSum,
        Finset.sum_filter] using h

/-- The actual original ordinary tuple is bounded by its genuinely
presieved row, including the true lowered cutoff and full prefix. -/
theorem original_row_upper {n N : ℕ} {eta : ℚ} {w B : ℝ} {E : ℕ×ℕ→Prop}
    (hN : 1<N) (heta : 0<eta) (hB : 1<B) (hwB : w≤B)
    {t : Four} (ht : t∈tuples n N E)
    (hw : w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) :
    U11Adaptive.weight N t≤
      ∑r∈rowSupport n N eta w t,rowCoefficient n N eta w B t r *
        (chenPrimeAPCount N N (fullPrefix t*r)-chenCentrePrimeAPCount N N (fullPrefix t*r)) := by
  have htOrd := (Finset.mem_filter.mp ht).1
  have hs := (Finset.mem_filter.mp htOrd).1
  have hleg := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta htOrd
  have h12 := (joint_carrier_order hs).2.2.2.2.1
  have hz2 : U1011OriginalSixteenJointNearCapCompiler.Z n N eta t≤(t.1.2:ℝ) :=
    hleg.2.2.1.trans (by exact_mod_cast h12.le)
  have hweight : U11Adaptive.weight N t=
      ((chenSiftedQuotientPrimeSource N (fullPrefix t) (t.1.2:ℝ)).card:ℝ) := by
    rw [fullPrefix_eq_multiplier]
    rfl
  have hcount : U11Adaptive.weight N t≤
      ((chenSiftedQuotientPrimeSource N (fullPrefix t)
        (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)).card:ℝ) := by
    rw [hweight]
    exact_mod_cast Finset.card_le_card
      (U11LoweredRosser.siftedSource_subset_lowered N _ _ _ hz2)
  exact hcount.trans (quotient_upper
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N (fullPrefix t)
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
    (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) B hB hwB hw (Nat.le_ceil _))

def density (n N : ℕ) (eta : ℚ) (w B : ℝ) (E : ℕ×ℕ→Prop) : ℝ :=
  physicalDensitySum (physicalSupport n N eta w E) (presievedSigma n N eta w B E)

def signedAP (n N : ℕ) (eta : ℚ) (w B : ℝ) (E : ℕ×ℕ→Prop) : ℝ :=
  ∑q∈physicalSupport n N eta w E,presievedSigma n N eta w B E q *
    chenQuotientPrimeAPError N (trueLogarithmicIntegral N) q

def signedCentre (n N : ℕ) (eta : ℚ) (w B : ℝ) (E : ℕ×ℕ→Prop) : ℝ :=
  ∑q∈physicalSupport n N eta w E,presievedSigma n N eta w B E q * chenCentrePrimeAPCount N N q

/-- The actual ordinary receiver count, density and both signed errors
now use the same genuine common-beta coefficient. The AP term remains an
explicit OPEN analytic obligation; it is not the old native AP term. -/
theorem original_same_presieved_sigma_upper {n N : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1<N) (heta : 0<eta) (hB : 1<B) (hwB : w≤B) (E : ℕ×ℕ→Prop)
    (hw : ∀t∈tuples n N E,w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) :
    (∑t∈tuples n N E,U11Adaptive.weight N t) ≤
      trueLogarithmicIntegral N*density n N eta w B E +
        signedAP n N eta w B E-signedCentre n N eta w B E := by
  calc
    (∑t∈tuples n N E,U11Adaptive.weight N t) ≤
        ∑t∈tuples n N E,∑r∈rowSupport n N eta w t,rowCoefficient n N eta w B t r *
          (chenPrimeAPCount N N (fullPrefix t*r)-chenCentrePrimeAPCount N N (fullPrefix t*r)) :=
      Finset.sum_le_sum (fun t ht=>original_row_upper hN heta hB hwB ht (hw t ht))
    _ = ∑q∈physicalSupport n N eta w E,presievedSigma n N eta w B E q *
          (chenPrimeAPCount N N q-chenCentrePrimeAPCount N N q) :=
      exact_pushforward n N eta w B E (fun q=>chenPrimeAPCount N N q-chenCentrePrimeAPCount N N q)
    _ = _ := by
      unfold density signedAP signedCentre physicalDensitySum
      rw [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      unfold chenQuotientPrimeAPError
      ring

end
end ImbalancedChen.P5Z.OriginalOrdinaryPresievedQuotientUpper
