import ImbalancedChen.P5ZU11SelectedLargestOrdinary

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Literal setup(n) policy dictionary of certify_combined_four_prefix_min.py.
Policy source IDs1,...,15 are exactly the nonempty bit masks on the four
DECREASING coordinates. Source ID16 is the distinct W branch. This is the
actual original finite bank, not a replacement constant-policy family.
Floating box scheduling, numeric gains and policy analytic licences are
not used here. Only the exact policy circuit/gates are transcribed.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenPolicyBank
noncomputable section
open Set MeasureTheory
open Classical
open U11Integral U11H248
open scoped BigOperators

abbrev Policy := Fin 16
def sourceId (p : Policy) : ℕ := p.val+1
def Selected (p : Policy) (i : Fin 4) : Prop := p.val<15 ∧ (sourceId p).testBit i.val=true
def selectedMass (p : Policy) (v : LogFour) : ℝ := ∑ i : Fin 4, if Selected p i then v i else 0

/-- Literal unselected-prefix square from e+previous, with previous
counting ONLY earlier unselected coordinates. -/
def selectedSquare (p : Policy) (j : Fin 4) (v : LogFour) : ℝ :=
  selectedMass p v + (∑ i : Fin 4, if i.val<j.val ∧ ¬Selected p i then v i else 0)+2*v j

def fullSquare (j : Fin 4) (v : LogFour) : ℝ :=
  (∑ i : Fin 4, if i.val<j.val then v i else 0)+2*v j

/-- The original W cap is 153/256-3*z/8. Its x<25/128 and
(1+x)/2 gates below must not be confused with another selected mask. -/
def cap (p : Policy) (v : LogFour) : ℝ :=
  if p.val<15 then min ((1+selectedMass p v)/2) (57/64-(3/2:ℝ)*selectedMass p v)
  else 153/256-(3/8:ℝ)*v 2

def TypedEligible (p : Policy) (v : LogFour) : Prop :=
  (1/2:ℝ)<cap p v ∧ (∀ j : Fin 4, fullSquare j v<cap p v) ∧
    (if p.val<15 then ∀ j : Fin 4, ¬Selected p j → selectedSquare p j v<cap p v
      else (1+v 0)/2<cap p v ∧ v 0<(25/128:ℝ))

def typedResidual (p : Policy) (v : LogFour) : ℝ := cap p v-U11SelectedLargest.prefixSum v

/-- Uniform exact affine ABI for the common partition. W has one branch;
its two displayed left flags agree and must not be treated as two owners. -/
def selectedLinear (p : Policy) : LogFour →L[ℝ] ℝ :=
  ∑ i : Fin 4, if Selected p i then ContinuousLinearMap.proj i else 0
def sumLinear : LogFour →L[ℝ] ℝ := ∑ i : Fin 4, ContinuousLinearMap.proj i
def fullSquareLinear (j : Fin 4) : LogFour →L[ℝ] ℝ :=
  (∑ i : Fin 4, if i.val<j.val then ContinuousLinearMap.proj i else 0)+
    (2:ℝ) • ContinuousLinearMap.proj j
def selectedSquareLinear (p : Policy) (j : Fin 4) : LogFour →L[ℝ] ℝ :=
  selectedLinear p+(∑ i : Fin 4,
    if i.val<j.val ∧ ¬Selected p i then ContinuousLinearMap.proj i else 0)+
      (2:ℝ) • ContinuousLinearMap.proj j
def capLinear (p : Policy) (left : Bool) : LogFour →L[ℝ] ℝ :=
  if p.val<15 then (if left then (1/2:ℝ) else -(3/2:ℝ)) • selectedLinear p
  else -(3/8:ℝ) • ContinuousLinearMap.proj 2
def capOffset (p : Policy) (left : Bool) : ℝ :=
  if p.val<15 then (if left then 1/2 else 57/64) else 153/256
def affineCap (p : Policy) (left : Bool) (v : LogFour) : ℝ := capLinear p left v+capOffset p left

theorem selectedLinear_apply (p : Policy) (v : LogFour) : selectedLinear p v=selectedMass p v := by
  simp only [selectedLinear,selectedMass,ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : Selected p i <;> simp [hi]

theorem sumLinear_apply (v : LogFour) : sumLinear v=U11SelectedLargest.prefixSum v := by
  simp [sumLinear,ContinuousLinearMap.sum_apply,Fin.sum_univ_succ,U11SelectedLargest.prefixSum]
  <;> ring

theorem fullSquareLinear_apply (j : Fin 4) (v : LogFour) : fullSquareLinear j v=fullSquare j v := by
  simp only [fullSquareLinear,fullSquare,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val<j.val <;> simp [hi]

theorem selectedSquareLinear_apply (p : Policy) (j : Fin 4) (v : LogFour) :
    selectedSquareLinear p j v=selectedSquare p j v := by
  simp only [selectedSquareLinear,selectedSquare,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,selectedLinear_apply]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val<j.val ∧ ¬Selected p i <;> simp [hi]

theorem cap_eq_affine_circuit (p : Policy) (v : LogFour) :
    cap p v=if p.val<15 then min (affineCap p true v) (affineCap p false v)
      else affineCap p true v := by
  by_cases hp : p.val<15
  · simp only [cap,affineCap,capLinear,capOffset,if_pos hp,if_true,Bool.false_eq_true,
      if_false,ContinuousLinearMap.smul_apply,smul_eq_mul,selectedLinear_apply]
    congr 1 <;> ring
  · simp only [cap,affineCap,capLinear,capOffset,if_neg hp,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul]
    ring

def first : Policy := ⟨0,by norm_num⟩
def wPolicy : Policy := ⟨15,by norm_num⟩

theorem selectedMass_first (v : LogFour) : selectedMass first v=v 0 := by
  norm_num [selectedMass,Selected,sourceId,first,Fin.sum_univ_succ]

theorem cap_first (v : LogFour) : cap first v=U11SelectedLargest.cap v := by
  simp [cap,first,selectedMass_first,U11SelectedLargest.cap]

theorem typedResidual_first (v : LogFour) :
    typedResidual first v=U11SelectedLargest.residual 0 v := by
  simp only [typedResidual,cap_first,U11SelectedLargest.residual]

theorem selectedSquare_first_of_unselected (j : Fin 4) (v : LogFour)
    (hj : ¬Selected first j) : selectedSquare first j v=fullSquare j v := by
  fin_cases j <;> norm_num [Selected,sourceId,first] at hj
  all_goals norm_num [selectedSquare,selectedMass,Selected,sourceId,first,
    fullSquare,Fin.sum_univ_succ] <;> ring

theorem first_fullSquares (v : LogFour) :
    (∀ j : Fin 4, fullSquare j v<cap first v) ↔
      U11SelectedLargest.fullSquares v (U11SelectedLargest.cap v) := by
  rw [cap_first]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    norm_num [fullSquare,Fin.sum_univ_succ] at h0 h1 h2 h3
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  · intro h j
    fin_cases j <;> norm_num [fullSquare,Fin.sum_univ_succ] <;>
      linarith [h.1,h.2.1,h.2.2.1,h.2.2.2]

/-- Exact mask1 correspondence with the already existing single-policy
source, including all full and selected squares, not only its cap. -/
theorem typedEligible_first_iff (v : LogFour) :
    TypedEligible first v ↔ U11SelectedLargest.eligible 0 v := by
  constructor
  · intro h
    have hf := (first_fullSquares v).1 h.2.1
    refine ⟨rfl,?_,hf,?_⟩
    · simpa only [cap_first] using h.1
    · exact hf.2
  · intro h
    have hf := (first_fullSquares v).2 h.2.2.1
    refine ⟨?_,hf,?_⟩
    · simpa only [cap_first] using h.2.1
    · change ∀ j : Fin 4, ¬Selected first j → selectedSquare first j v<cap first v
      intro j hj
      rw [selectedSquare_first_of_unselected j v hj]
      exact hf j

theorem w_policy_dictionary (v : LogFour) :
    cap wPolicy v=153/256-(3/8:ℝ)*v 2 ∧
      (TypedEligible wPolicy v ↔ (1/2:ℝ)<cap wPolicy v ∧
        (∀ j : Fin 4, fullSquare j v<cap wPolicy v) ∧
        (1+v 0)/2<cap wPolicy v ∧ v 0<(25/128:ℝ)) := by
  simp [cap,TypedEligible,wPolicy]

def bank : Finset ℕ := Finset.range 16
def eligible (j : ℕ) (v : LogFour) : Prop :=
  if hj : j<16 then TypedEligible ⟨j,hj⟩ v else False
def residual (j : ℕ) (v : LogFour) : ℝ :=
  if hj : j<16 then typedResidual ⟨j,hj⟩ v else 0

theorem bank_sourceIds : bank.image (fun j => j+1)=Finset.Icc 1 16 := by
  ext j
  simp only [bank,Finset.mem_image,Finset.mem_range,Finset.mem_Icc]
  constructor
  · rintro ⟨i,hi,rfl⟩; omega
  · rintro ⟨hlo,hhi⟩
    exact ⟨j-1,by omega,by omega⟩

theorem fullSquare_last (v : LogFour) :
    fullSquare 3 v=U11SelectedLargest.prefixSum v+v 3 := by
  simp [fullSquare,Fin.sum_univ_succ,U11SelectedLargest.prefixSum]
  <;> ring

/-- The TRUE full eligibility, for every one of the sixteen original
policies, supplies residual>w. No artificial residual>=2w is required. -/
theorem typedEligible_residual_gt_smallest (p : Policy) (v : LogFour)
    (he : TypedEligible p v) : v 3<typedResidual p v := by
  have h := he.2.1 3
  rw [fullSquare_last] at h
  dsimp only [typedResidual]
  linarith

theorem continuous_selectedMass (p : Policy) : Continuous (selectedMass p) := by
  apply continuous_finsetSum
  intro i _
  by_cases hi : Selected p i
  · simpa only [selectedMass,if_pos hi] using (continuous_apply i : Continuous (fun v : LogFour => v i))
  · simp only [if_neg hi]
    exact continuous_const

theorem continuous_selectedSquare (p : Policy) (j : Fin 4) : Continuous (selectedSquare p j) := by
  apply ((continuous_selectedMass p).add ?_).add ((continuous_apply j).const_mul 2)
  apply continuous_finsetSum
  intro i _
  by_cases hi : i.val<j.val ∧ ¬Selected p i
  · simpa only [if_pos hi] using (continuous_apply i : Continuous (fun v : LogFour => v i))
  · simp only [if_neg hi]
    exact continuous_const

theorem continuous_fullSquare (j : Fin 4) : Continuous (fullSquare j) := by
  apply Continuous.add ?_ ((continuous_apply j).const_mul 2)
  apply continuous_finsetSum
  intro i _
  by_cases hi : i.val<j.val
  · simpa only [if_pos hi] using (continuous_apply i : Continuous (fun v : LogFour => v i))
  · simp only [if_neg hi]
    exact continuous_const

theorem continuous_cap (p : Policy) : Continuous (cap p) := by
  by_cases hp : p.val<15
  · simp only [cap,if_pos hp]
    exact ((continuous_const.add (continuous_selectedMass p)).div_const 2).min
      (continuous_const.sub ((continuous_selectedMass p).const_mul (3/2:ℝ)))
  · simp only [cap,if_neg hp]
    exact continuous_const.sub ((continuous_apply 2).const_mul (3/8:ℝ))

theorem measurableSet_typedEligible (p : Policy) : MeasurableSet {v | TypedEligible p v} := by
  have hc := (continuous_cap p).measurable
  have hf : MeasurableSet {v | ∀ j : Fin 4, fullSquare j v<cap p v} := by
    exact MeasurableSet.iInter (fun j => measurableSet_lt (continuous_fullSquare j).measurable hc)
  have hextra : MeasurableSet {v | if p.val<15 then
      ∀ j : Fin 4, ¬Selected p j → selectedSquare p j v<cap p v
      else (1+v 0)/2<cap p v ∧ v 0<(25/128:ℝ)} := by
    by_cases hp : p.val<15
    · simp only [if_pos hp,setOf_forall]
      apply MeasurableSet.iInter
      intro j
      by_cases hj : Selected p j
      · simp only [hj,not_true_eq_false,false_implies,setOf_true]
        exact MeasurableSet.univ
      · simpa only [hj,not_false_eq_true,true_implies] using
          measurableSet_lt (continuous_selectedSquare p j).measurable hc
    · simp only [if_neg hp]
      have ht : Measurable (fun v : LogFour => (1+v 0)/2) := by fun_prop
      exact (measurableSet_lt ht hc).inter (measurableSet_lt (measurable_pi_apply 0) measurable_const)
  exact (measurableSet_lt measurable_const hc).inter (hf.inter hextra)

theorem measurableSet_eligible (j : ℕ) : MeasurableSet {v | eligible j v} := by
  by_cases hj : j<16
  · simpa only [eligible,dif_pos hj] using measurableSet_typedEligible ⟨j,hj⟩
  · simp only [eligible,dif_neg hj,setOf_false]
    exact MeasurableSet.empty

theorem measurable_residual (j : ℕ) : Measurable (residual j) := by
  by_cases hj : j<16
  · simp only [residual,dif_pos hj,typedResidual]
    exact ((continuous_cap ⟨j,hj⟩).sub U11SelectedLargest.continuous_prefixSum).measurable
  · simp only [residual,dif_neg hj]
    exact measurable_const

/-- Concrete sixteen-policy ordinary range on the ORIGINAL unaltered
U11 support. H248 range is proved by its existing literal array supplier. -/
theorem ordinary_actual_bounds (mask : Set (ℝ×ℝ)) (j : ℕ) (v : LogFour)
    (hv : v ∈ originalDomain mask) (he : eligible j v) :
    0≤ordinaryKernel H248 residual j v ∧ ordinaryKernel H248 residual j v≤(20000/417:ℝ) := by
  have hj : j<16 := by
    by_contra hn
    simp only [eligible,dif_neg hn] at he
  have he' : TypedEligible ⟨j,hj⟩ v := by simpa only [eligible,dif_pos hj] using he
  have hr : v 3<residual j v := by
    simpa only [residual,dif_pos hj] using typedEligible_residual_gt_smallest ⟨j,hj⟩ v he'
  have hw := (originalDomain_denominators_pos mask v hv).1
  have hp : 0<residual j v := hw.trans hr
  have ha : (417/5000:ℝ)≤v 3 := hv.1
  have hH := H248_max_two_bounds (residual j v/v 3)
  unfold ordinaryKernel
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hH.2)) hp.le
  · apply (div_le_iff₀ hp).2
    nlinarith [hH.1]

/-- The actual original sixteen-policy nonlinear minimum is integrable.
This does not infer a prime-harmonic mean by exchanging minimum and mean. -/
theorem integrableOn_actual_sixteen_policy_envelope (mask : Set (ℝ×ℝ))
    (hm : MeasurableSet mask) :
    IntegrableOn (envelope bank (guarded eligible
      (switchedKernel currentK LiLiuPrereqBuchstab.buchstab)
      (ordinaryKernel H248 residual))) (originalDomain mask) volume := by
  apply U11Canonical.integrableOn_original_canonical_envelope mask hm bank eligible currentK
    (by norm_num [currentK]) H248 residual (fun j _ => measurableSet_eligible j)
    measurable_H248 (fun j _ => measurable_residual j)
  intro j hj v hv he
  exact (ordinary_actual_bounds mask j v hv he).1

end
end ImbalancedChen.P5Z.U1011OriginalSixteenPolicyBank
