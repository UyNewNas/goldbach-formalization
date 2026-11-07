import ImbalancedChen.P5OriginalJointPresievedCompiler
import ImbalancedChen.P5OriginalCommonBetaActualParameters

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

One common beta pair is genuinely chosen from the actual ALL16 selected
bank before N, E or any tuple. It supplies the complete original joint
source upper bound and the density comparison of the SAME explicitly new
jointPresievedSigma. The distinct W row is included. No equality to the
old all-prime native sigma, sharp currentK estimate or PP licence occurs.
-/

namespace ImbalancedChen.P5Z.OriginalJointCommonBetaModel

noncomputable section
open scoped BigOperators
open Classical
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenCommonSmallParameters (owner_mem_selected)
open OriginalOrdinaryPresievedSigma OriginalOrdinaryPresievedDensityComparison
open OriginalCommonBetaActualParameters OriginalJointPresievedCompiler
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

/-- The actual W branch shares the same finite common-beta budget with
the ordinary masks, while retaining its own actual cutoff and delta. -/
theorem parameters_on_joint_row {n N:ℕ} {eta:ℚ} {nu epsilon:ℝ}
    (hN:1<N) (heta:0<eta) (hnu:0<nu) (he:0<epsilon)
    (heBudget:epsilon<epsilonBudget n eta nu) {E:ℕ×ℕ→Prop} {t:Four}
    (ht:t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E) :
    (N:ℝ)^(nu*epsilon^2)≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t ∧
      U1011OriginalSixteenJointNearCapCompiler.Z n N eta t≤(N:ℝ)^(59/250:ℝ) ∧
      nu*epsilon≤(U1011OriginalSixteenNearCapBoxProfiles.delta
        (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t)
        (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) eta:ℝ)/8 := by
  have hs := (Finset.mem_filter.mp ht).1
  have htag : U1011OriginalSixteenStaticNativeCompiler.tupleTag n N t≠0 :=
    (Finset.mem_filter.mp ht).2
  have hj := owner_mem_selected htag
  have hcut : (cutoffMin n eta:ℝ)≤
      (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
        (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t)
        (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) eta:ℝ) := by
    exact_mod_cast cutoffMin_le_cell eta _ hj
  have hell : (U1011OriginalSixteenNearCapCommonSmallParameters.ellMax n eta:ℝ)≤
      (U1011OriginalSixteenNearCapBoxProfiles.delta
        (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t)
        (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) eta:ℝ)/2 := by
    exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.ellMax_le_cell eta _ hj
  have he8 : epsilon≤1/8 := heBudget.le.trans (min_le_left _ _)
  have heCut : epsilon≤(cutoffMin n eta:ℝ)/nu :=
    heBudget.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heEll : epsilon≤
      (U1011OriginalSixteenNearCapCommonSmallParameters.ellMax n eta:ℝ)/(4*nu) :=
    heBudget.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcutLinear := (le_div_iff₀ hnu).mp heCut
  have hellLinear := (le_div_iff₀ (by positivity:0<4*nu)).mp heEll
  have heSquare : epsilon^2≤epsilon := by nlinarith
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hw : (N:ℝ)^(nu*epsilon^2)≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t := by
    change (N:ℝ)^(nu*epsilon^2)≤(N:ℝ)^
      (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
        (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t)
        (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) eta:ℝ)
    apply Real.rpow_le_rpow_of_exponent_le hn.le
    exact (mul_le_mul_of_nonneg_left heSquare hnu.le).trans (by nlinarith [hcut])
  have hlegal := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht
  obtain ⟨h1,h2,h3,h4,h12,h23,h34⟩ := joint_carrier_order hs
  have hp14 : (t.1.1:ℝ)≤t.2.2 := by exact_mod_cast (h12.trans (h23.trans h34)).le
  exact ⟨hw,(hlegal.2.2.1.trans hp14).trans (joint_band_and_mask hs).2.2.1.le,
    by nlinarith [hell]⟩

theorem joint_row_coprime_prefix {n N r:ℕ} {eta:ℚ} {w:ℝ} {E:ℕ×ℕ→Prop}
    (hN:1<N) (heta:0<eta) {t:Four}
    (ht:t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hw:w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (hr:r∈rowSupport n N eta w t) : (fullPrefix t).Coprime r := by
  have hs := (Finset.mem_filter.mp ht).1
  have hlegal := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht
  have hz : U1011OriginalSixteenJointNearCapCompiler.Z n N eta t≤(slots t 3:ℝ) := by
    simpa only [slots,Matrix.cons_val_three] using hlegal.2.2.1
  have hb := fullPrefix_coprime_lowered_sieve hs hz
  have hdvd := (Nat.mem_divisors.mp (rowSupport_subset_full_divisors hw hr)).1
  rw [currentChen_actualSmallPrimeProduct_eq_sieveProduct N _ _ (Nat.le_ceil _)] at hdvd
  exact chenQuotient_allowed_coprime hb hdvd

theorem joint_density_eq_rows {n N:ℕ} {eta:ℚ} {w B:ℝ}
    (hN:1<N) (heta:0<eta) (E:ℕ×ℕ→Prop)
    (hw:∀t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) :
    jointDensity n N eta w B E =
      ∑t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
        (1/(Nat.totient (fullPrefix t):ℝ))*rowDensity n N eta w B t := by
  have hp := joint_exact_pushforward n N eta w B E (fun q=>1/(Nat.totient q:ℝ))
  calc
    jointDensity n N eta w B E =
        ∑t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
          ∑r∈rowSupport n N eta w t,
            rowCoefficient n N eta w B t r/(Nat.totient (fullPrefix t*r):ℝ) := by
      simpa only [jointDensity,physicalDensitySum,one_div,div_eq_mul_inv] using hp.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      unfold rowDensity physicalDensitySum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Nat.totient_mul (joint_row_coprime_prefix hN heta ht (hw t ht) hr),Nat.cast_mul]
      ring

/-- Complete actual common-beta modeling statement on the ORIGINAL joint
source. All positive levels, prime walls and beta factor-size budgets are
derived. Numerical density evaluation and signed high-modulus AP/PP are
the remaining visible analytic tasks for this actual constructed rho. -/
theorem exists_original_joint_common_beta_model (n:ℕ) (eta:ℚ) (heta:0<eta)
    (nu reserve:ℝ) (hnu:0<nu) (hreserve:0<reserve) :
    ∃epsilon:ℝ,0<epsilon ∧ epsilon<epsilonBudget n eta nu ∧
      ∃N0:ℕ,2≤N0 ∧ ∀N:ℕ,N0≤N → Even N → ∀E:ℕ×ℕ→Prop,
        let w:=(N:ℝ)^(nu*epsilon^2)
        let B:=(N:ℝ)^(nu*epsilon)
        (∀q:ℕ,|jointPresievedSigma n N eta w B E q|≤1) ∧
        (currentChenUpsilon10 N+currentChenUpsilon11 N E≤
          (∑t∈U1011OriginalSixteenJointNearCapCompiler.fallbackTuples n N E,U11Adaptive.weight N t)+
          trueLogarithmicIntegral N*jointDensity n N eta w B E+
            jointAP n N eta w B E-jointCentre n N eta w B E) ∧
        (jointDensity n N eta w B E≤
          (∑t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
            (1/(Nat.totient (fullPrefix t):ℝ))*
              actualSmallRosserPlusDensity N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
                (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
                (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) +
          (reserve*singularSeries N/Real.log (N:ℝ))*
            ∑t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
              1/(Nat.totient (fullPrefix t):ℝ)) ∧
        ∀t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,nu*epsilon≤
          (U1011OriginalSixteenNearCapBoxProfiles.delta
            (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t)
            (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) eta:ℝ)/8 := by
  have hr : 0<(59/250:ℝ)/nu := div_pos (by norm_num) hnu
  obtain ⟨epsilon,he,_he8,heBudget,_her,N0,hN0,hbound⟩ :=
    exists_common_beta_ordinary_density_comparison nu ((59/250:ℝ)/nu) reserve
      (epsilonBudget n eta nu) hnu hr hreserve (epsilonBudget_pos n eta heta nu hnu)
  refine ⟨epsilon,he,heBudget,N0,hN0,?_⟩
  intro N hN hEven E
  have hN1 : 1<N := by omega
  have hn : (1:ℝ)<N := by exact_mod_cast hN1
  have he8 : epsilon≤1/8 := heBudget.le.trans (min_le_left _ _)
  have heSquare : epsilon^2≤epsilon := by nlinarith
  have hB : 1<(N:ℝ)^(nu*epsilon) := Real.one_lt_rpow hn (mul_pos hnu he)
  have hwB : (N:ℝ)^(nu*epsilon^2)≤(N:ℝ)^(nu*epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hn.le (mul_le_mul_of_nonneg_left heSquare hnu.le)
  have hp (t:Four) (ht:t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E) :=
    parameters_on_joint_row hN1 heta hnu he heBudget ht
  have hscale : nu*((59/250:ℝ)/nu)=59/250 := by field_simp [hnu.ne']
  have hdensity : jointDensity n N eta ((N:ℝ)^(nu*epsilon^2)) ((N:ℝ)^(nu*epsilon)) E ≤
      (∑t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
        (1/(Nat.totient (fullPrefix t):ℝ))*
          actualSmallRosserPlusDensity N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
            (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
            (U1011OriginalSixteenJointNearCapCompiler.D n N eta t))+
      (reserve*singularSeries N/Real.log (N:ℝ))*
        ∑t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
          1/(Nat.totient (fullPrefix t):ℝ) := by
    rw [joint_density_eq_rows hN1 heta E (fun t ht=>(hp t ht).1)]
    calc
      _ ≤ ∑t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
          (1/(Nat.totient (fullPrefix t):ℝ))*
            (actualSmallRosserPlusDensity N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
              (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
              (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)+
              reserve*singularSeries N/Real.log (N:ℝ)) := by
        apply Finset.sum_le_sum
        intro t ht
        apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr (Nat.cast_nonneg _))
        have hl := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN1 heta ht
        exact hbound N hN hEven _ ((hp t ht).1.trans (Nat.le_ceil _)) _ (hp t ht).1
          (by simpa only [hscale] using (hp t ht).2.1) _ hl.2.1
      _ = _ := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib,←Finset.sum_mul]
        ring
  dsimp only
  exact ⟨jointSigma_abs_le_one hN1 heta E (fun t ht=>(hp t ht).1),
    original_joint_source_upper hN1 heta hB hwB E (fun t ht=>(hp t ht).1),
    hdensity,fun t ht=>(hp t ht).2.2⟩

end
end ImbalancedChen.P5Z.OriginalJointCommonBetaModel
