import ImbalancedChen.P5OriginalPresievedOuterAtomCoefficient
import ImbalancedChen.P5OriginalPresievedTargetTransport

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

An independent outer prefix has no original-source provenance. Its actual
prime-box endpoints nevertheless prove that marking the deletion target
by its prefix product removes no prime below the FROZEN physical cutoff.
This proves full support/function transport and identifies the marked-row
outer coefficient with the canonical-target outer coefficient. Physical
D, Z and the common beta pair are never recomputed at the marked target.
-/

namespace ImbalancedChen.P5Z.OriginalPresievedOuterTargetBinding

noncomputable section
open scoped BigOperators
open Classical
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenCommonSmallParameters (selectedCells)
open OriginalOrdinaryCommonBetaModel OriginalPresievedOuterAtomSupport
open OriginalPresievedOuterAtomArithmetic OriginalPresievedOuterAtomCoefficient
open OriginalCommonBetaActualParameters OriginalPresievedTargetTransport

theorem actual_box_prefix_coprime_full_carrier {n N cap:ℕ} {eta:ℚ} (hN:1<N)
    (j:Grid n) (a b:Fin 4→ℝ)
    (hcut:∀i,(U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta:ℝ)≤a i)
    {t:Fin 4→ℕ} (ht:t∈actualPrimeBoxTuples N a b) :
    (∏i,t i).Coprime (actualSmallPrimeProduct N cap
      (U1011OriginalSixteenJointNearCapCompiler.rowZ
        (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N)) := by
  have hn:(1:ℝ)<N:=by exact_mod_cast hN
  apply Nat.coprime_prod_left_iff.mpr
  intro i hi
  have hpi:=(mem_actualPrimeBoxTuples_iff.mp ht i).1
  apply hpi.coprime_iff_not_dvd.mpr
  intro hdvd
  have hp: t i∈(actualSmallPrimeProduct N cap
      (U1011OriginalSixteenJointNearCapCompiler.rowZ
        (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N)).primeFactors:=
    Nat.mem_primeFactors.mpr ⟨hpi,hdvd,actualSmallPrimeProduct_ne_zero _ _ _⟩
  rw [actualSmallPrimeProduct_primeFactors] at hp
  have hsmall:=(mem_actualSmallPrimeFinset.mp hp).2.2.2
  have hlarge:= (Real.rpow_le_rpow_of_exponent_le hn.le (hcut i)).trans
    (mem_actualPrimeBoxTuples_iff.mp ht i).2.2.1
  exact (not_lt_of_ge hlarge) hsmall

/-- The entire genuine presieved marked row, including zero and inactive
arguments and its displayed carrier, is the canonical row. Covering caps
may vary with the independent prefix. -/
theorem actual_outer_presieved_target_match {n N:ℕ} {eta:ℚ} {nu epsilon:ℝ}
    (hN:1<N) (hnu:0<nu) (he:0<epsilon) (heBudget:epsilon<epsilonBudget n eta nu)
    (j:Grid n) (hj:j∈selectedCells n) (a b:Fin 4→ℝ)
    (hcut:∀i,(U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta:ℝ)≤a i)
    {t:Fin 4→ℕ} (ht:t∈actualPrimeBoxTuples N a b) (rowCap:ℕ)
    (hrow:U1011OriginalSixteenJointNearCapCompiler.rowZ
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N≤(rowCap:ℝ)) :
    let z:=U1011OriginalSixteenJointNearCapCompiler.rowZ
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N
    let physicalD:=U1011OriginalSixteenJointNearCapCompiler.rowD
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N
    let w:=(N:ℝ)^(nu*epsilon^2)
    actualSmallRoughModuli (ordinaryRetainOdd physicalD) ((∏i,t i)*N) rowCap w z =
      frozenSupport n eta j N w ∧
    actualSmallRoughRho (ordinaryRetainOdd physicalD) ((∏i,t i)*N) rowCap w z
      ((N:ℝ)^(nu*epsilon)) = frozenCoefficient n eta j N w (nu*epsilon) := by
  have hw:=(common_parameters_on_selected_cell hN hnu he heBudget j hj).1
  have hB:=actual_box_prefix_coprime_full_carrier (cap:=Nat.ceil
    (U1011OriginalSixteenJointNearCapCompiler.rowZ
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N))
    hN j a b hcut ht
  exact presieved_target_mul_cover
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.rowD
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N))
    ((N:ℝ)^(nu*epsilon)) hw hB (Nat.le_ceil _) hrow

/-- The canonical carrier is justified by the preceding full carrier
identity. Each deletion target may be marked by its own actual prefix,
while the physical profile and common beta pair remain frozen at N. -/
def markedOuterSigma (n:ℕ) (eta:ℚ) (j:Grid n) (N:ℕ) (nu epsilon:ℝ) (a b:Fin 4→ℝ)
    (rowCap:(Fin 4→ℕ)→ℕ) (inner:Bool) (delta:ℝ) (fine:ℕ) (cell:Grid fine) (q:ℕ) : ℝ :=
  ∑m∈(outerMarks n eta j N ((N:ℝ)^(nu*epsilon^2)) a b).filter (fun m=>outerModulus m=q),
    actualSmallRoughRho
      (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.rowD
        (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N))
      ((∏i,m.1 i)*N) (rowCap m.1) ((N:ℝ)^(nu*epsilon^2))
      (U1011OriginalSixteenJointNearCapCompiler.rowZ
        (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N)
      ((N:ℝ)^(nu*epsilon)) m.2 *
    U1011FourDimensionalSmoothBoxAtoms.boxAtom inner delta fine cell (actualPrimeTupleLog N m.1)

/-- This is actual quotient-target binding of the independent coefficient,
not equality with the old native or source-owned physical sigma. -/
theorem markedOuterSigma_eq_canonical {n N:ℕ} {eta:ℚ} {nu epsilon:ℝ}
    (hN:1<N) (hnu:0<nu) (he:0<epsilon) (heBudget:epsilon<epsilonBudget n eta nu)
    (j:Grid n) (hj:j∈selectedCells n) (a b:Fin 4→ℝ)
    (hcut:∀i,(U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta:ℝ)≤a i)
    (rowCap:(Fin 4→ℕ)→ℕ)
    (hrow:∀t∈actualPrimeBoxTuples N a b,U1011OriginalSixteenJointNearCapCompiler.rowZ
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N≤(rowCap t:ℝ))
    (inner:Bool) (delta:ℝ) (fine:ℕ) (cell:Grid fine) :
    markedOuterSigma n eta j N nu epsilon a b rowCap inner delta fine cell =
      outerSigma n eta j N ((N:ℝ)^(nu*epsilon^2)) (nu*epsilon) a b inner delta fine cell := by
  funext q
  apply Finset.sum_congr rfl
  intro m hm
  have hmt:=(Finset.mem_product.mp (Finset.mem_filter.mp hm).1).1
  have htr:=actual_outer_presieved_target_match hN hnu he heBudget j hj a b hcut hmt
    (rowCap m.1) (hrow m.1 hmt)
  dsimp only at htr
  rw [htr.2]

end
end ImbalancedChen.P5Z.OriginalPresievedOuterTargetBinding
