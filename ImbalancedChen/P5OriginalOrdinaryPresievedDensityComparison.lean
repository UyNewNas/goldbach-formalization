import ImbalancedChen.P5OriginalOrdinaryPresievedSigma
import ImbalancedChen.P5OriginalCommonBetaVariableCutoffReserve
import ImbalancedChen.ActualFirstExitDensityProjection

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The manuscript's common-beta density comparison is an upper projection,
not a coefficientwise identification. This file proves that comparison
for every later ordinary row cutoff using one beta pair, and transports
it to the actual physical presievedSigma. Physical totients are split
only after actual original-prefix coprimality is proved. Native density
evaluation, currentK and signed AP/PP estimates remain separate.
-/

namespace ImbalancedChen.P5Z.OriginalOrdinaryPresievedDensityComparison

noncomputable section
open scoped BigOperators
open Classical
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open OriginalOrdinaryBetaRegroup OriginalOrdinaryCommonBetaModel OriginalOrdinaryPresievedSigma
open OriginalCommonBetaVariableCutoffReserve

def rowDensity (n N:ℕ) (eta:ℚ) (w B:ℝ) (t:Four) : ℝ :=
  physicalDensitySum (rowSupport n N eta w t) (rowCoefficient n N eta w B t)

theorem rowSupport_subset_full_divisors {n N r:ℕ} {eta:ℚ} {w:ℝ} {t:Four}
    (hw:w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (hr:r∈rowSupport n N eta w t) :
    r∈actualSmallRosserSupport N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
      (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) := by
  obtain ⟨⟨e,d⟩,hed,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨he,hd⟩ := Finset.mem_product.mp hed
  have hdM := fixedRoughSupport_subset_primeProduct_divisors
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
    (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) hd
  rw [nativeSupport_eq_products N _ hw]
  exact Finset.mem_image.mpr ⟨(e,d),Finset.mem_product.mpr ⟨he,hdM⟩,rfl⟩

theorem rowSupport_coprime_prefix {n N r:ℕ} {eta:ℚ} {w:ℝ} {E:ℕ×ℕ→Prop}
    (hN:1<N) (heta:0<eta) {t:Four} (ht:t∈tuples n N E)
    (hw:w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (hr:r∈rowSupport n N eta w t) : (fullPrefix t).Coprime r := by
  have htOrd := (Finset.mem_filter.mp ht).1
  have hs := (Finset.mem_filter.mp htOrd).1
  have hlegal := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta htOrd
  have hz : U1011OriginalSixteenJointNearCapCompiler.Z n N eta t≤(slots t 3:ℝ) := by
    simpa only [slots,Matrix.cons_val_three] using hlegal.2.2.1
  have hb := fullPrefix_coprime_lowered_sieve hs hz
  have hdvd := (Nat.mem_divisors.mp (rowSupport_subset_full_divisors hw hr)).1
  rw [currentChen_actualSmallPrimeProduct_eq_sieveProduct N _ _ (Nat.le_ceil _)] at hdvd
  exact chenQuotient_allowed_coprime hb hdvd

/-- Same physical density, with every full-prefix denominator retained
until the actual original prime-ceiling proof supplies coprimality. -/
theorem physical_density_eq_rows {n N:ℕ} {eta:ℚ} {w B:ℝ}
    (hN:1<N) (heta:0<eta) (E:ℕ×ℕ→Prop)
    (hw:∀t∈tuples n N E,w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) :
    physicalDensitySum (physicalSupport n N eta w E) (presievedSigma n N eta w B E) =
      ∑t∈tuples n N E,(1/(Nat.totient (fullPrefix t):ℝ))*rowDensity n N eta w B t := by
  have hpush := exact_pushforward n N eta w B E (fun q=>1/(Nat.totient q:ℝ))
  calc
    physicalDensitySum (physicalSupport n N eta w E) (presievedSigma n N eta w B E) =
        ∑t∈tuples n N E,∑r∈rowSupport n N eta w t,
          rowCoefficient n N eta w B t r/(Nat.totient (fullPrefix t*r):ℝ) := by
      simpa only [physicalDensitySum,one_div,div_eq_mul_inv] using hpush.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      unfold rowDensity physicalDensitySum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Nat.totient_mul (rowSupport_coprime_prefix hN heta ht (hw t ht) hr),Nat.cast_mul]
      ring

theorem full_ordinary_density (N cap:ℕ) (z L:ℝ) (hL:1<L) :
    reciprocalTotientDensity (fixedRoughSupport (ordinaryRetainOdd L) N cap 0 z)
      (fixedRoughCoefficient (ordinaryRetainOdd L) N cap 0 z) =
      actualSmallRosserPlusDensity N cap z L := by
  have ht := UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (ordinaryParityRosserPolicy false L) (ordinaryParityRosserPolicy_upper_even L) N cap 0 z
  have hn := firstExitRetainedPolynomial_ordinaryParityRosser_eq_actualDensity
    false N cap z L hL (by simp)
  have hn' : firstExitRetainedPolynomial (ordinaryParityRosserPolicy false L)
      (fun p:ℕ=>1/((p:ℝ)-1)) [] true 1 (roughPrimeUniverse N cap 0 z)=
      actualSmallRosserPlusDensity N cap z L := by
    simpa only [Bool.false_eq_true,if_false] using hn
  exact ht.symm.trans hn'

/-- One common beta pair is compared to every later variable ordinary
native level and cutoff by actual projection plus its absolute attachment
reserve. No equality of those two coefficient functions is asserted. -/
theorem exists_common_beta_ordinary_density_comparison (nu r reserve epsilonMax:ℝ)
    (hnu:0<nu) (hr:0<r) (hreserve:0<reserve) (hepsilonMax:0<epsilonMax) :
    ∃epsilon:ℝ,0<epsilon ∧ epsilon<1/8 ∧ epsilon<epsilonMax ∧ epsilon^2≤r ∧
      ∃N0:ℕ,2≤N0 ∧ ∀N:ℕ,N0≤N → Even N → ∀cap:ℕ,
        (N:ℝ)^(nu*epsilon^2)≤(cap:ℝ) → ∀z:ℝ,
          (N:ℝ)^(nu*epsilon^2)≤z → z≤(N:ℝ)^(nu*r) → ∀L:ℝ,1<L →
            physicalDensitySum
              (actualSmallRoughModuli (ordinaryRetainOdd L) N cap ((N:ℝ)^(nu*epsilon^2)) z)
              (actualSmallRoughRho (ordinaryRetainOdd L) N cap ((N:ℝ)^(nu*epsilon^2)) z
                ((N:ℝ)^(nu*epsilon))) ≤
              actualSmallRosserPlusDensity N cap z L + reserve*singularSeries N/Real.log (N:ℝ) := by
  obtain ⟨epsilon,he,he8,heMax,her,N0,hN0,hbound⟩ :=
    exists_variable_cutoff_target_reserve nu r reserve epsilonMax hnu hr hreserve hepsilonMax
  refine ⟨epsilon,he,he8,heMax,her,N0,hN0,?_⟩
  intro N hN hEven cap hcap z hwz hzmax L hL
  have herror := (hbound N hN hEven cap hcap z hwz hzmax (ordinaryRetainOdd L)).2
  have hprojection := fixedRoughDensity_presieveProjection (ordinaryRetainOdd L) N cap
    ((N:ℝ)^(nu*epsilon^2)) z hwz
  rw [full_ordinary_density N cap z L hL] at hprojection
  dsimp only at herror ⊢
  linarith

/-- The genuine common-beta physical coefficient has the original native
ordinary density as an upper comparison, with its explicit absolute
attachment reserve. E, all tuples, actual levels and cutoffs are later
than the ONE beta choice and threshold. -/
theorem exists_same_presieved_sigma_density_comparison (n:ℕ) (eta:ℚ) (heta:0<eta)
    (nu r reserve epsilonMax:ℝ) (hnu:0<nu) (hr:0<r)
    (hreserve:0<reserve) (hepsilonMax:0<epsilonMax) :
    ∃epsilon:ℝ,0<epsilon ∧ epsilon<1/8 ∧ epsilon<epsilonMax ∧ epsilon^2≤r ∧
      ∃N0:ℕ,2≤N0 ∧ ∀N:ℕ,N0≤N → Even N → ∀E:ℕ×ℕ→Prop,
        (∀t∈tuples n N E,(N:ℝ)^(nu*epsilon^2)≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t ∧
          U1011OriginalSixteenJointNearCapCompiler.Z n N eta t≤(N:ℝ)^(nu*r)) →
        physicalDensitySum (physicalSupport n N eta ((N:ℝ)^(nu*epsilon^2)) E)
          (presievedSigma n N eta ((N:ℝ)^(nu*epsilon^2)) ((N:ℝ)^(nu*epsilon)) E) ≤
        (∑t∈tuples n N E,(1/(Nat.totient (fullPrefix t):ℝ))*
          actualSmallRosserPlusDensity N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
            (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
            (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) +
        (reserve*singularSeries N/Real.log (N:ℝ)) *
          ∑t∈tuples n N E,1/(Nat.totient (fullPrefix t):ℝ) := by
  obtain ⟨epsilon,he,he8,heMax,her,N0,hN0,hbound⟩ :=
    exists_common_beta_ordinary_density_comparison nu r reserve epsilonMax
      hnu hr hreserve hepsilonMax
  refine ⟨epsilon,he,he8,heMax,her,N0,hN0,?_⟩
  intro N hN hEven E hwalls
  have hN1 : 1<N := by omega
  rw [physical_density_eq_rows hN1 heta E (fun t ht=>(hwalls t ht).1)]
  calc
    _ ≤ ∑t∈tuples n N E,(1/(Nat.totient (fullPrefix t):ℝ))*
        (actualSmallRosserPlusDensity N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
          (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
          (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) +
          reserve*singularSeries N/Real.log (N:ℝ)) := by
      apply Finset.sum_le_sum
      intro t ht
      apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr (Nat.cast_nonneg _))
      have hlegal := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN1 heta
        (Finset.mem_filter.mp ht).1
      exact hbound N hN hEven _ ((hwalls t ht).1.trans (Nat.le_ceil _)) _
        (hwalls t ht).1 (hwalls t ht).2 _ hlegal.2.1
    _ = _ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib,←Finset.sum_mul]
      ring

end
end ImbalancedChen.P5Z.OriginalOrdinaryPresievedDensityComparison
