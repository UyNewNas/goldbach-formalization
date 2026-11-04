import ImbalancedChen.P3U5ProductChartDerivativeBudget

/-!
Manuscript-internal / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Bind the constructed multipliers to the SAME original groups and COMPLETE
product. One grouping assigns every slot once. The atlas uses the two
chosen original groups; the trim uses ALL groups. It never uses a residual
quotient. No HB/source admission or arithmetic estimate is inferred here.
-/
namespace ImbalancedChen.P3U5PhysicalProductChart
noncomputable section
open scoped Classical BigOperators
open P3AffineTransitionJets P3LogProductTransitionJets
open P3U5ProductChartDerivativeBudget P3U5LogChartDerivativeBudget P3U5RootAtlas
open P3U5SmoothRootPartition (smoothWeight)

private theorem exp_finsetSum {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    Real.exp (∑ i ∈ S,f i)=∏ i ∈ S,Real.exp (f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp only [Finset.sum_insert hi,Finset.prod_insert hi,Real.exp_add,ih]

def groupBase {d g : ℕ} (U : Fin d → ℝ) (group : Fin d → Fin g) (j : Fin g) : ℝ :=
  ∏ i,if group i=j then U i else 1

def groupValue {d g : ℕ} (G : Fin g → ℝ) (group : Fin d → Fin g)
    (x : Point d) (j : Fin g) : ℝ := G j*Real.exp (groupSum group x j)

def completeValue {d g : ℕ} (G : Fin g → ℝ) (group : Fin d → Fin g) (x : Point d) : ℝ :=
  ∏ j,groupValue G group x j

theorem groupBase_pos {d g : ℕ} (U : Fin d → ℝ) (hU : ∀ i,0 < U i)
    (group : Fin d → Fin g) (j : Fin g) : 0 < groupBase U group j := by
  apply Finset.prod_pos
  intro i hi
  dsimp
  split_ifs
  · exact hU i
  · norm_num

/-- The group base can be the ACTUAL product of individual lower scales.
Empty groups have value one, and no quotient/slot is dropped. -/
theorem groupValue_eq_slotProduct {d g : ℕ} (U : Fin d → ℝ)
    (group : Fin d → Fin g) (x : Point d) (j : Fin g) :
    groupValue (groupBase U group) group x j =
      ∏ i,if group i=j then U i*Real.exp (x i) else 1 := by
  unfold groupValue groupBase groupSum
  rw [exp_finsetSum,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : group i=j <;> simp [h]

theorem sum_groupSum {d g : ℕ} (group : Fin d → Fin g) (x : Point d) :
    (∑ j,groupSum group x j)=∑ i,x i := by
  simp only [groupSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem completeValue_eq_complete_scale {d g : ℕ} (G : Fin g → ℝ)
    (group : Fin d → Fin g) (x : Point d) :
    completeValue G group x=(∏ j,G j)*Real.exp (∑ i,x i) := by
  simp only [completeValue,groupValue,Finset.prod_mul_distrib]
  rw [← exp_finsetSum,sum_groupSum]

def pairSlots {d g : ℕ} (group : Fin d → Fin g) (pair : Fin 2 → Fin g) :
    Fin d → Option (Fin 2) :=
  fun i => if group i=pair 0 then some 0 else if group i=pair 1 then some 1 else none

theorem groupLog_pairSlots {d g : ℕ} (group : Fin d → Fin g) (pair : Fin 2 → Fin g)
    (hne : pair 0 ≠ pair 1) (x : Point d) (j : Fin 2) :
    groupLog (pairSlots group pair) x j=groupSum group x (pair j) := by
  simp only [groupLog,groupSum]
  apply Finset.sum_congr rfl
  intro i hi
  fin_cases j
  · by_cases h0 : group i=pair 0
    · simp [pairSlots,h0]
    · by_cases h1 : group i=pair 1 <;> simp [pairSlots,h0,h1]
  · by_cases h0 : group i=pair 0
    · have h1 : group i ≠ pair 1 := fun h => hne (h0.symm.trans h)
      simp [pairSlots,h0,h1]
    · by_cases h1 : group i=pair 1 <;> simp [pairSlots,h0,h1]

/-- The two atlas coordinates are logarithms of exactly those two full
original group values, not merely independently assigned affine offsets. -/
theorem chartPoint_eq_original_groups {d g : ℕ} (ell : ℝ) (G : Fin g → ℝ)
    (hG : ∀ j,0 < G j) (group : Fin d → Fin g) (pair : Fin 2 → Fin g)
    (hne : pair 0 ≠ pair 1) (x : Point d) :
    chartPoint ell (fun j => G (pair j)) (pairSlots group pair) x =
      fun j => Real.log (groupValue G group x (pair j))/ell := by
  funext j
  rw [chartPoint_original_group ell _ (fun j => hG (pair j)),
    groupLog_pairSlots group pair hne]
  rfl

theorem hat_eq_original_group {d g : ℕ} (G R : Fin g → ℝ)
    (hG : ∀ j,0 < G j) (hR : ∀ j,0 < R j)
    (group : Fin d → Fin g) (x : Point d) (j : Fin g) :
    logHat (Real.log (G j/R j)+groupSum group x j) =
      psi (groupValue G group x j/R j) := by
  have hy := logHat_log (Real.exp_pos (Real.log (G j/R j)+groupSum group x j))
  rw [Real.log_exp] at hy
  rw [hy,Real.exp_add,Real.exp_log (div_pos (hG j) (hR j))]
  congr 1
  dsimp [groupValue]
  ring

theorem trim_eq_complete_product {d g : ℕ} (G : Fin g → ℝ)
    (hG : ∀ j,0 < G j) (group : Fin d → Fin g) {T : ℝ} (hT : 0 < T) (x : Point d) :
    logStep (Real.log ((∏ j,G j)/T)+∑ i,x i) = eta (completeValue G group x/T) := by
  have hp : 0 < ∏ j,G j := Finset.prod_pos (fun j _ => hG j)
  rw [logStep,Real.exp_add,Real.exp_log (div_pos hp hT),completeValue_eq_complete_scale]
  congr 1
  ring

/-- Direct physical expression, independent of the formal jet expression.
For the manuscript use T=N^(1-kappa0) and R_j equal to original dyadic scales. -/
def physicalProfile {d g : ℕ} (ell : ℝ) (G R : Fin g → ℝ)
    (group : Fin d → Fin g) (pair : Fin 2 → Fin g) (T : ℝ) (m : ℕ) (l : Lane)
    (x : Point d) : ℝ :=
  (window x * smoothWeight m l (fun j => Real.log (groupValue G group x (pair j))/ell)) *
    (eta (completeValue G group x/T) * ∏ j,psi (groupValue G group x j/R j))

theorem physicalProfile_eq_productProfile {d g : ℕ} (ell : ℝ) (G R : Fin g → ℝ)
    (hG : ∀ j,0 < G j) (hR : ∀ j,0 < R j)
    (group : Fin d → Fin g) (pair : Fin 2 → Fin g) (hne : pair 0 ≠ pair 1)
    {T : ℝ} (hT : 0 < T) (m : ℕ) (l : Lane) :
    physicalProfile ell G R group pair T m l =
      productProfile ell (fun j => G (pair j)) (pairSlots group pair) group
        (fun j => Real.log (G j/R j)) (Real.log ((∏ j,G j)/T)) m l := by
  funext x
  rw [productProfile,profile,chartPoint_eq_original_groups ell G hG group pair hne,
    trim_eq_complete_product G hG group hT]
  simp_rw [hat_eq_original_group G R hG hR group x]
  rfl

theorem physicalProfile_original_chart {d g : ℕ} (ell : ℝ) (G R : Fin g → ℝ)
    (group : Fin d → Fin g) (pair : Fin 2 → Fin g) (T : ℝ) (m : ℕ) (l : Lane)
    {x : Point d} (hx : ∀ i,0 ≤ x i ∧ x i ≤ Real.log 2) :
    physicalProfile ell G R group pair T m l x =
      smoothWeight m l (fun j => Real.log (groupValue G group x (pair j))/ell) *
        (eta (completeValue G group x/T) * ∏ j,psi (groupValue G group x j/R j)) := by
  have hl : Real.log 2 ≤ (1 : ℝ) := by
    simpa using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
  rw [physicalProfile,window_eq_one (fun i => ⟨by linarith [(hx i).1],(hx i).2.trans hl⟩),one_mul]

/-- Source algebra for ANY signed arithmetic test and the SAME rho.
This is an exact equality, not a PP estimate or a causal admission theorem. -/
theorem same_rho_finite_partition {α : Type*} {d g : ℕ}
    (Q : Finset ℕ) (S : Finset α) (rho : ℕ → ℝ) (F : ℕ → α → ℝ)
    (z : α → Point d) (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (m : ℕ) :
    (∑ l : Lane,∑ q ∈ Q,rho q * ∑ t ∈ S,
      F q t*productProfile ell R slot group b trim m l (z t)) =
    ∑ q ∈ Q,rho q * ∑ t ∈ S,F q t*window (z t) *
      (logStep (trim+∑ i,z t i)*∏ j,logHat (b j+groupSum group (z t) j)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.mul_sum,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.mul_sum,productProfile_sum]
  ring

end
end ImbalancedChen.P3U5PhysicalProductChart
