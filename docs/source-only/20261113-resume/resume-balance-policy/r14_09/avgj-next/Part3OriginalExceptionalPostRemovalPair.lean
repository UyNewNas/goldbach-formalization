import ImbalancedChen.Part3OriginalExceptionalJInitialAverage
import ImbalancedChen.Part3OriginalContinuousClassRemoval
import ImbalancedChen.Part3ZExceptionalThresholdGeometry

/-! The two actual forms after coprime n-removal in Medium §7. The
published fixed-level estimate pays the marked n row. The only
spectral energies on the right are Pascadi's two printed level sums. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalExceptionalPostRemovalPair20261113
open Finset
open scoped BigOperators MatrixGroups Classical
open ActualFullCuspEigenbasis20261026b ActualCuspBasisWhittakerCoefficients20261102
open ActualContinuousPoincarePairing20261110 OriginalNativeCuspFunctionals20261102
open OriginalExceptionalJNativeCompletion20261110 OriginalExceptionalJInitialAverage20261113
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant sieveConstant_pos)
open OriginalContinuousClassRemoval20261110 (markedRow reduced)
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalTwoZFourierAssembly20261102 OriginalPrincipalTraceRow20261102r
open ActualPrincipalCuspOneRemoval20261102r
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly (dyadicScale dyadicScale_pos)
open ImbalancedChen.P3ZExceptionalThresholdGeometry (threshold)
open P3NativePeriod64SamplingSourceOnly (D4)

local instance (z : ℕ+) : NeZero z.val := ⟨z.property.ne'⟩

/-- Both endpoint-corrected pieces of one fixed physical Z chart. -/
abbrev levels (D : OriginalData) (k : BlockKey) (upper : Bool) :=
  originalLevels D k upper true ∪ originalLevels D k upper false

private theorem chart_mem (D : OriginalData) (k : BlockKey) (upper : Bool)
    (z : ↥(levels D k upper)) : z.val.val ∈ chartLevels D k upper := by
  rcases Finset.mem_union.mp z.property with h | h <;> exact (Finset.mem_filter.mp h).2

private def sourceRow (D : OriginalData) (k : BlockKey) (upper : Bool)
    (z : ↥(levels D k upper)) : Row D k :=
  ⟨z.val.val,chartLevels_subset D k upper (chart_mem D k upper z)⟩

def rowLength (k : BlockKey) : ℝ := dyadicScale k.2.1/(k.1 : ℝ)

def rowWeight (D : OriginalData) (k : BlockKey) (upper : Bool) : ℝ :=
  2 + fixedZ D upper / rowLength k

def rowMass (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (z : ℕ+) : ℝ := ∑ n ∈ nCarrier D k z.val, ‖blockBeta D r k (decode k z.val n)‖^2

def reducedN (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (upper negativeM : Bool) (ell : D4 → ℤ) (z : ↥(levels D k upper))
    (i : actualCuspBasisIndex z.val z.val.property) : ℂ :=
  reduced D r k (sourceRow D k upper z) upper negativeM ell
    (basisR z.val z.val.property i (originalFrame true))

theorem reduced_row_square (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (ell : D4 → ℤ) (z : ↥(levels D k upper)) :
    (∑ i : ↥(exceptional z.val), (rowWeight D k upper) ^ tau z.val i.val *
      ‖reducedN D r k upper negativeM ell z i.val‖^2) ≤
        4*sieveConstant*(1+rowLength k/fixedZ D upper)*rowMass D r k z.val := by
  let Z := fixedZ D upper
  let L := rowLength k
  let q := z.val
  let s := principalTraceSign D k negativeM
  let w (n : ℕ) := modulatedBeta D r k upper ell q.val n * sourceCuspPhase q.val (-(s*(n : ℤ)))
  have hz : 0 < Z := fixedZ_pos D upper
  have zq : Z ≤ (q.val : ℝ) := by
    simpa only [one_mul] using
      (le_div_iff₀ hz).mp (chartLevels_normalized D k upper (chart_mem D k upper z)).1
  obtain ⟨n₀,hn₀⟩ := levelCarrier_has_n D k (sourceRow D k upper z).property
  have nu : 0 < (k.1 : ℝ) := by
    exact_mod_cast (nCarrier_positive_coprime D k q.val hn₀).1
  have hl : 0 < L := div_pos (dyadicScale_pos _) nu
  have band (n : ℕ) (hn : n ∈ nCarrier D k q.val) : L < (n : ℝ) ∧ (n : ℝ) ≤ 2*L := by
    have ⟨lo,hi⟩ := nCarrier_dyadic D k q.val hn
    rw [Nat.cast_mul] at lo hi
    constructor
    · exact (div_lt_iff₀ nu).mpr (by simpa only [mul_comm (k.1 : ℝ) (n : ℝ)] using lo)
    · change (n : ℝ) ≤ 2*(dyadicScale k.2.1/(k.1 : ℝ))
      rw [← mul_div_assoc]
      exact (le_div_iff₀ nu).mpr (by simpa only [mul_comm (k.1 : ℝ) (n : ℝ)] using hi)
  have hX : 0 < rowWeight D k upper := by
    change 0 < 2+Z/L
    positivity
  have range : rowWeight D k upper ≤ 3 * max 1 ((q.val : ℝ)/L) := by
    change 2+Z/L ≤ _
    linarith only [div_le_div_of_nonneg_right zq hl.le,
      le_max_left (1:ℝ) ((q.val : ℝ)/L), le_max_right (1:ℝ) ((q.val : ℝ)/L)]
  have b := signed_row q true hl hX range (nCarrier D k q.val) w s
    (principalTraceSign_cases D k negativeM) band
  have mass : (∑ n ∈ nCarrier D k q.val, ‖w n‖^2) = rowMass D r k q := by
    simp only [w,norm_mul,sourceCuspPhase_norm,mul_one,norm_modulatedBeta,rowMass]
  have hm : 0 ≤ rowMass D r k q := Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have cz : (sieveConstant * (1 + max 1 (3:ℝ))) = 4*sieveConstant := by norm_num <;> ring
  rw [mass,cz] at b
  refine b.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (add_le_add_left (div_le_div_of_nonneg_left hl.le hz zq) 1) ?_) hm)
  exact mul_nonneg (by norm_num) sieveConstant_pos.le

abbrev Slots (D : OriginalData) (k : BlockKey) (upper : Bool) :=
  Σ z : ↥(levels D k upper), ↥(exceptional z.val)

/-- The positive factors are the two square roots used in level/eigenvalue
Cauchy. The native basis at q is shared by both factors. -/
def mFactor (D : OriginalData) (k : BlockKey) (upper : Bool)
    (J j : ℕ) (ell : D4 → ℤ) (a : Slots D k upper) : ℝ :=
  Real.sqrt ((threshold (((2:ℕ)^j : ℕ) : ℝ) (fixedZ D upper)) ^ tau a.1.val a.2.val) *
    ‖originalMFunctional J j ell a.1.val a.1.val.property a.2.val‖

def nFactor (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (upper negativeM : Bool) (ell : D4 → ℤ) (a : Slots D k upper) : ℝ :=
  Real.sqrt ((rowWeight D k upper) ^ tau a.1.val a.2.val) *
    ‖reducedN D r k upper negativeM ell a.1 a.2.val‖

/-- The marked post-removal product is bounded by the two classical
level energies at the same phase and the arithmetic coefficient square.
This is the weight at the full manuscript threshold. -/
theorem original_pair_to_pascadi (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ) :
    let Z := fixedZ D upper
    let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
    let W := threshold V Z
    let F := mFactor D k upper J j ell
    let G := nFactor D r k upper negativeM ell
    let energy := (∑ a : Slots D k upper, F a ^ 2) * ∑ a : Slots D k upper, G a ^ 2
    ∃ ω : ℝ, (∑ a : Slots D k upper, F a * G a)^2 ≤ energy ∧ energy ≤
      ((2+Real.log (4*V+1))^2 *
        ((pascadiJ (classicalLevels (Z/2)) W j ω + pascadiJ (classicalLevels Z) W j ω)/4)) *
      ((4*sieveConstant*(1+rowLength k/Z))*∑ z : ↥(levels D k upper), rowMass D r k z.val) := by
  classical
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
  let W := threshold V Z
  let F := mFactor D k upper J j ell
  let G := nFactor D r k upper negativeM ell
  have hW : 0 < W := ImbalancedChen.P3ZExceptionalThresholdGeometry.threshold_pos
    (show 0 < V by dsimp [V]; positivity)
  have hL : 0 ≤ rowLength k := div_nonneg (dyadicScale_pos _).le (Nat.cast_nonneg _)
  have hZ : 0 < Z := fixedZ_pos D upper
  have hY : 0 ≤ rowWeight D k upper := by
    change 0 ≤ 2+Z/rowLength k
    positivity
  have mSq : (∑ a : Slots D k upper, (F a)^2) = clippedJ (levels D k upper) W J j ell := by
    rw [Fintype.sum_sigma]
    simp only [F,mFactor,W,V,Z,mul_pow,Real.sq_sqrt (Real.rpow_nonneg hW.le _),
      clippedJ,Finset.univ_eq_attach,Finset.sum_attach]
  obtain ⟨ω,hm⟩ := original_chart_J_one_phase D k upper hW J j ell
  rw [← mSq] at hm
  have hs : (∑ a : Slots D k upper, (G a)^2) ≤
      (4*sieveConstant*(1+rowLength k/Z))*∑ z : ↥(levels D k upper), rowMass D r k z.val := by
    rw [Fintype.sum_sigma,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z _
    simpa only [G,nFactor,mul_pow,Real.sq_sqrt (Real.rpow_nonneg hY _),Z] using
      reduced_row_square D r k upper negativeM ell z
  have mnon : 0 ≤ ∑ a : Slots D k upper, (F a)^2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have nnon : 0 ≤ ∑ a : Slots D k upper, (G a)^2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  exact ⟨ω,Finset.sum_mul_sq_le_sq_mul_sq Finset.univ F G,
    mul_le_mul hm hs nnon (mnon.trans hm)⟩

end ImbalancedChen.Part3.OriginalExceptionalPostRemovalPair20261113
end
