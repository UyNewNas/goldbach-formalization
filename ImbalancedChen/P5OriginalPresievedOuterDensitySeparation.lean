import ImbalancedChen.P5OriginalPresievedOuterTargetBinding

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The independent outer coefficient has an exactly separated physical mean.
The prefix primes are coprime to the ENTIRE frozen residual carrier, even
outside the original tuple source. Thus its reciprocal-totient mean is
the actual frozen common-beta density times four genuine one-prime smooth
means. This does not identify the outer coefficient with the original
source coefficient or provide an AP/PP estimate.
-/

namespace ImbalancedChen.P5Z.OriginalPresievedOuterDensitySeparation

noncomputable section
open scoped BigOperators
open Classical
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenCommonSmallParameters (selectedCells)
open OriginalOrdinaryCommonBetaModel OriginalPresievedOuterAtomSupport
open OriginalPresievedOuterAtomArithmetic OriginalPresievedOuterAtomCoefficient
open OriginalPresievedOuterTargetBinding OriginalCommonBetaActualParameters

def outerSupport (n:ℕ) (eta:ℚ) (j:Grid n) (N:ℕ) (w:ℝ) (a b:Fin 4→ℝ) : Finset ℕ :=
  (outerMarks n eta j N w a b).image outerModulus

def prefixSmoothMass (N:ℕ) (a b:Fin 4→ℝ) (inner:Bool) (delta:ℝ)
    (fine:ℕ) (cell:Grid fine) : ℝ :=
  ∑t∈actualPrimeBoxTuples N a b,
    U1011FourDimensionalSmoothBoxAtoms.boxAtom inner delta fine cell (actualPrimeTupleLog N t) /
      (Nat.totient (∏i,t i):ℝ)

def scalarSmoothMass (N:ℕ) (a b:Fin 4→ℝ) (inner:Bool) (delta:ℝ)
    (fine:ℕ) (cell:Grid fine) (i:Fin 4) : ℝ :=
  ∑p∈roughPrimeFinset N (Nat.ceil ((N:ℝ)^b i)) ((N:ℝ)^a i) ((N:ℝ)^b i),
    U1011CompactLogIntervalSmoothing.weight inner delta
      (logPrimeMeshLo (lower:ℝ) (upper:ℝ) fine cell i)
      (logPrimeMeshHi (lower:ℝ) (upper:ℝ) fine cell i)
      (Real.log (p:ℝ)/Real.log (N:ℝ)) / ((p:ℝ)-1)

private theorem frozenSupport_subset_full {n N r:ℕ} {eta:ℚ} {j:Grid n} {w:ℝ}
    (hw:w≤U1011OriginalSixteenJointNearCapCompiler.rowZ
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N)
    (hr:r∈frozenSupport n eta j N w) :
    r∈actualSmallRosserSupport N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.rowZ
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N))
      (U1011OriginalSixteenJointNearCapCompiler.rowZ
        (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N) := by
  obtain ⟨⟨e,d⟩,hed,rfl⟩:=Finset.mem_image.mp hr
  obtain ⟨he,hd⟩:=Finset.mem_product.mp hed
  have hdM:=fixedRoughSupport_subset_primeProduct_divisors
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.rowD
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N))
    N _ w _ hd
  rw [nativeSupport_eq_products N _ hw]
  exact Finset.mem_image.mpr ⟨(e,d),Finset.mem_product.mpr ⟨he,hdM⟩,rfl⟩

theorem independent_prefix_coprime_residual {n N:ℕ} {eta:ℚ} {nu epsilon:ℝ}
    (hN:1<N) (hnu:0<nu) (he:0<epsilon) (heBudget:epsilon<epsilonBudget n eta nu)
    (j:Grid n) (hj:j∈selectedCells n) (a b:Fin 4→ℝ)
    (hcut:∀i,(U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta:ℝ)≤a i)
    {t:Fin 4→ℕ} (ht:t∈actualPrimeBoxTuples N a b) {r:ℕ}
    (hr:r∈frozenSupport n eta j N ((N:ℝ)^(nu*epsilon^2))) :
    (∏i,t i).Coprime r := by
  have hw:=(common_parameters_on_selected_cell hN hnu he heBudget j hj).1
  exact (actual_box_prefix_coprime_full_carrier (cap:=Nat.ceil
    (U1011OriginalSixteenJointNearCapCompiler.rowZ
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N))
    hN j a b hcut ht).of_dvd_right
    (Nat.mem_divisors.mp (frozenSupport_subset_full hw hr)).1

theorem outer_exact_signed_test (n N:ℕ) (eta:ℚ) (j:Grid n) (w ell:ℝ)
    (a b:Fin 4→ℝ) (inner:Bool) (delta:ℝ) (fine:ℕ) (cell:Grid fine) (F:ℕ→ℝ) :
    (∑q∈outerSupport n eta j N w a b,
      outerSigma n eta j N w ell a b inner delta fine cell q*F q) =
    ∑t∈actualPrimeBoxTuples N a b,∑r∈frozenSupport n eta j N w,
      (frozenCoefficient n eta j N w ell r*
        U1011FourDimensionalSmoothBoxAtoms.boxAtom inner delta fine cell (actualPrimeTupleLog N t))*
        F ((∏i,t i)*r) := by
  have hf:=Finset.sum_fiberwise_of_maps_to (s:=outerMarks n eta j N w a b)
    (t:=outerSupport n eta j N w a b) (g:=outerModulus)
    (fun m hm=>Finset.mem_image_of_mem outerModulus hm)
    (fun m=> (frozenCoefficient n eta j N w ell m.2*
      U1011FourDimensionalSmoothBoxAtoms.boxAtom inner delta fine cell (actualPrimeTupleLog N m.1))*
      F (outerModulus m))
  calc
    _ = ∑q∈outerSupport n eta j N w a b,
        ∑m∈(outerMarks n eta j N w a b).filter (fun m=>outerModulus m=q),
          (frozenCoefficient n eta j N w ell m.2*
            U1011FourDimensionalSmoothBoxAtoms.boxAtom inner delta fine cell (actualPrimeTupleLog N m.1))*
            F (outerModulus m) := by
      apply Finset.sum_congr rfl
      intro q hq
      unfold outerSigma
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m hm
      rw [(Finset.mem_filter.mp hm).2]
    _ = _ := by
      rw [hf]
      exact Finset.sum_product _ _ _

/-- The actual residual sum is kept signed until after the physical
totient is split. The common pair stays frozen at the original target. -/
theorem outer_physical_density_separated {n N:ℕ} {eta:ℚ} {nu epsilon:ℝ}
    (hN:1<N) (hnu:0<nu) (he:0<epsilon) (heBudget:epsilon<epsilonBudget n eta nu)
    (j:Grid n) (hj:j∈selectedCells n) (a b:Fin 4→ℝ)
    (hcut:∀i,(U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta:ℝ)≤a i)
    (inner:Bool) (delta:ℝ) (fine:ℕ) (cell:Grid fine) :
    physicalDensitySum (outerSupport n eta j N ((N:ℝ)^(nu*epsilon^2)) a b)
      (outerSigma n eta j N ((N:ℝ)^(nu*epsilon^2)) (nu*epsilon) a b inner delta fine cell) =
      prefixSmoothMass N a b inner delta fine cell *
        physicalDensitySum (frozenSupport n eta j N ((N:ℝ)^(nu*epsilon^2)))
          (frozenCoefficient n eta j N ((N:ℝ)^(nu*epsilon^2)) (nu*epsilon)) := by
  rw [show physicalDensitySum (outerSupport n eta j N ((N:ℝ)^(nu*epsilon^2)) a b)
      (outerSigma n eta j N ((N:ℝ)^(nu*epsilon^2)) (nu*epsilon) a b inner delta fine cell) =
    ∑q∈outerSupport n eta j N ((N:ℝ)^(nu*epsilon^2)) a b,
      outerSigma n eta j N ((N:ℝ)^(nu*epsilon^2)) (nu*epsilon) a b inner delta fine cell q*
        (1/(Nat.totient q:ℝ)) by simp only [physicalDensitySum,div_eq_mul_one_div]]
  rw [outer_exact_signed_test]
  unfold prefixSmoothMass physicalDensitySum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Nat.totient_mul (independent_prefix_coprime_residual hN hnu he heBudget j hj a b hcut ht hr),
    Nat.cast_mul]
  ring

theorem prefixSmoothMass_eq_product {N:ℕ} (hN:1≤N) (a b:Fin 4→ℝ)
    (hsep:∀i:Fin 3,b i.succ≤a i.castSucc)
    (inner:Bool) (delta:ℝ) (fine:ℕ) (cell:Grid fine) :
    prefixSmoothMass N a b inner delta fine cell =
      ∏i,scalarSmoothMass N a b inner delta fine cell i := by
  unfold prefixSmoothMass
  calc
    _ = ∑t∈actualPrimeBoxTuples N a b,∏i:Fin 4,
        U1011CompactLogIntervalSmoothing.weight inner delta
          (logPrimeMeshLo (lower:ℝ) (upper:ℝ) fine cell i)
          (logPrimeMeshHi (lower:ℝ) (upper:ℝ) fine cell i)
          (Real.log (t i:ℝ)/Real.log (N:ℝ)) / ((t i:ℝ)-1) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [div_eq_mul_one_div,actualPrimeBoxTuple_reciprocalTotient ht
        (actualPrimeBoxTuples_injective hN hsep ht)]
      simp only [U1011FourDimensionalSmoothBoxAtoms.boxAtom,actualPrimeTupleLog,
        ←Finset.prod_mul_distrib,div_eq_mul_one_div]
    _ = _ := by
      exact (Finset.prod_univ_sum
        (fun i=>roughPrimeFinset N (Nat.ceil ((N:ℝ)^b i)) ((N:ℝ)^a i) ((N:ℝ)^b i))
        (fun i p=>U1011CompactLogIntervalSmoothing.weight inner delta
          (logPrimeMeshLo (lower:ℝ) (upper:ℝ) fine cell i)
          (logPrimeMeshHi (lower:ℝ) (upper:ℝ) fine cell i)
          (Real.log (p:ℝ)/Real.log (N:ℝ))/((p:ℝ)-1))).symm

/-- Four independently smoothed prime factors and ONE unchanged signed
common-beta residual density give the physical mean of the actual outer
coefficient, including all outside-source arithmetic tuples. -/
theorem actual_outer_mean_four_prime_factors {n N:ℕ} {eta:ℚ} {nu epsilon:ℝ}
    (hN:1<N) (hnu:0<nu) (he:0<epsilon) (heBudget:epsilon<epsilonBudget n eta nu)
    (j:Grid n) (hj:j∈selectedCells n) (a b:Fin 4→ℝ)
    (hsep:∀i:Fin 3,b i.succ≤a i.castSucc)
    (hcut:∀i,(U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta:ℝ)≤a i)
    (inner:Bool) (delta:ℝ) (fine:ℕ) (cell:Grid fine) :
    physicalDensitySum (outerSupport n eta j N ((N:ℝ)^(nu*epsilon^2)) a b)
      (outerSigma n eta j N ((N:ℝ)^(nu*epsilon^2)) (nu*epsilon) a b inner delta fine cell) =
      (∏i,scalarSmoothMass N a b inner delta fine cell i) *
        physicalDensitySum (frozenSupport n eta j N ((N:ℝ)^(nu*epsilon^2)))
          (frozenCoefficient n eta j N ((N:ℝ)^(nu*epsilon^2)) (nu*epsilon)) := by
  rw [outer_physical_density_separated hN hnu he heBudget j hj a b hcut,
    prefixSmoothMass_eq_product (by omega:1≤N) a b hsep]

end
end ImbalancedChen.P5Z.OriginalPresievedOuterDensitySeparation
