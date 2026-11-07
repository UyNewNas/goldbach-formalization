import ImbalancedChen.P5ZU1011OriginalSixteenBufferedEnvelopeIntegral
import ImbalancedChen.P5ZU1011OriginalSixteenNearCapBoxProfiles
import ImbalancedChen.P5ZU1011OriginalSixteenTightGridLocalGeometry

/-!
# Actual near-cap grid data instantiate the geometric buffer contract

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The mesh M(n)=32(n+1) and eta=its rational step are fixed before every
point and N. Only the concrete WholeBoxEligibleTest-certified policies
contribute their ACTUAL near-cap tau/xiEff/rho. The finite Ico pieces are
measurable and uniquely owned; other pieces extend by zero.

The actual d841 formula gives each buffer<=12*step<=1/(n+1), uniformly.
Thus the constructed GeometricBufferData has NO buffer-geometry premise.
This is an actual-data caller, not a restatement of the generic contract.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenNearCapGridBufferData

noncomputable section

open Set MeasureTheory Filter Topology U11Integral
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenRationalGridGeometry U1011OriginalSixteenTightGridLocalGeometry
open U1011OriginalSixteenBufferedEnvelopeIntegral
open scoped BigOperators
open Classical

def meshLevel (n : ℕ) : ℕ := 32 * (n + 1)
def eta (n : ℕ) : ℚ := step (meshLevel n)
def box (n : ℕ) (j : Index (meshLevel n)) : Box := gridBox (meshLevel n) j
def Certified (n : ℕ) (p : Policy) (j : Index (meshLevel n)) : Prop := wholeBoxEligibleTest p (box n j) = true

instance (n : ℕ) (p : Policy) (j : Index (meshLevel n)) : Decidable (Certified n p j) := by
  unfold Certified
  infer_instance

theorem eta_pos (n : ℕ) : 0 < eta n := step_pos _

theorem step_buffer_rate (n : ℕ) : 12 * (step (meshLevel n) : ℝ) ≤
    U1011OriginalSixteenBufferedCandidate.bufferRate n := by
  have hQ : (12 : ℚ) * step (meshLevel n) ≤ 1 / (n + 1 : ℕ) := by
    unfold step
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity : (0 : ℚ) < (meshLevel n + 1 : ℕ))
      (by positivity : (0 : ℚ) < (n + 1 : ℕ))).2
    norm_num [meshLevel, a, b]
    push_cast
    nlinarith only [Nat.cast_nonneg n : (0 : ℚ) ≤ n]
  have hR : (12 : ℝ) * (step (meshLevel n) : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hQ
  simpa only [U1011OriginalSixteenBufferedCandidate.bufferRate, Nat.cast_add, Nat.cast_one] using hR

private def piecewiseBuffer (n : ℕ) (p : Policy)
    (f : Index (meshLevel n) → LogFour → ℝ) (v : LogFour) : ℝ :=
  ∑ j : Index (meshLevel n), if Certified n p j then (cell (meshLevel n) j).indicator (f j) v else 0

private theorem piecewise_eq_owner (n : ℕ) (p : Policy)
    (f : Index (meshLevel n) → LogFour → ℝ) {v : LogFour} (hv : v ∈ cube) :
    piecewiseBuffer n p f v =
      if Certified n p (owner (meshLevel n) v) then f (owner (meshLevel n) v) v else 0 := by
  unfold piecewiseBuffer
  rw [Finset.sum_eq_single (owner (meshLevel n) v)]
  · by_cases ht : Certified n p (owner (meshLevel n) v)
    · simp only [if_pos ht, indicator_of_mem (owner_mem _ hv)]
    · simp only [if_neg ht]
  · intro j hj hne
    have hnot : v ∉ cell (meshLevel n) j := fun h => hne (owner_unique _ hv h)
    by_cases ht : Certified n p j <;> simp only [ht, if_true, if_false, indicator_of_notMem hnot]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

private theorem piecewise_eq_zero_outside (n : ℕ) (p : Policy)
    (f : Index (meshLevel n) → LogFour → ℝ) {v : LogFour} (hv : v ∉ cube) :
    piecewiseBuffer n p f v = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have hnot : v ∉ cell (meshLevel n) j := by
    intro hcell
    apply hv
    rw [← cells_union (meshLevel n)]
    exact mem_iUnion.mpr ⟨j, hcell⟩
  by_cases ht : Certified n p j <;> simp only [ht, if_true, if_false, indicator_of_notMem hnot]

def tauData (n : ℕ) (p : Policy) : LogFour → ℝ := piecewiseBuffer n p
  (fun j => U1011OriginalSixteenNearCapBoxProfiles.tau p (box n j) (eta n))
def xiData (n : ℕ) (p : Policy) : LogFour → ℝ := piecewiseBuffer n p
  (fun j => U1011OriginalSixteenNearCapBoxProfiles.xiEff p (box n j) (eta n))
def rhoData (n : ℕ) (p : Policy) : LogFour → ℝ := piecewiseBuffer n p
  (fun j _ => (U1011OriginalSixteenNearCapBoxProfiles.rho p (box n j) (eta n) : ℝ))

private theorem measurable_piecewise (n : ℕ) (p : Policy)
    (f : Index (meshLevel n) → LogFour → ℝ) (hf : ∀ j, Measurable (f j)) :
    Measurable (piecewiseBuffer n p f) := by
  apply Finset.measurable_sum
  intro j hj
  by_cases ht : Certified n p j
  · simpa only [if_pos ht] using (hf j).indicator (cell_measurable _ j)
  · simp only [if_neg ht]
    exact measurable_const

theorem measurable_tauData (n : ℕ) (p : Policy) : Measurable (tauData n p) :=
  measurable_piecewise n p _ (fun j => U1011OriginalSixteenNearCapBoxProfiles.measurable_tau p _ _)
theorem measurable_xiData (n : ℕ) (p : Policy) : Measurable (xiData n p) :=
  measurable_piecewise n p _ (fun j => U1011OriginalSixteenNearCapBoxProfiles.measurable_xiEff p _ _)
theorem measurable_rhoData (n : ℕ) (p : Policy) : Measurable (rhoData n p) :=
  measurable_piecewise n p _ (fun _ => measurable_const)

theorem certified_owner_buffer_bounds (n : ℕ) (p : Policy) {v : LogFour}
    (hv : v ∈ cube) (ht : Certified n p (owner (meshLevel n) v)) :
    U1011OriginalSixteenNearCapBoxProfiles.tau p (box n (owner (meshLevel n) v)) (eta n) v ∈
        Icc 0 (U1011OriginalSixteenBufferedCandidate.bufferRate n) ∧
      U1011OriginalSixteenNearCapBoxProfiles.xiEff p (box n (owner (meshLevel n) v)) (eta n) v ∈
        Icc 0 (U1011OriginalSixteenBufferedCandidate.bufferRate n) ∧
      (U1011OriginalSixteenNearCapBoxProfiles.rho p (box n (owner (meshLevel n) v)) (eta n) : ℝ) ∈
        Icc 0 (U1011OriginalSixteenBufferedCandidate.bufferRate n) := by
  have hb := U1011OriginalSixteenNearCapBoxProfiles.uniform_buffer_bound_of_coordinate_side
    p (box n (owner (meshLevel n) v)) (eta n) (gridBox_valid _ _)
    (U1011OriginalSixteenRationalIntegralCertificates.grid_lo_pos _ _ 3) ht (eta_pos n)
    (step (meshLevel n) : ℝ) (by exact_mod_cast (step_pos (meshLevel n)).le)
    (owner_width (meshLevel n) v) le_rfl v (cell_subset_closedBox _ _ (owner_mem _ hv))
  have hmax := hb.2.2.2.trans (step_buffer_rate n)
  exact ⟨⟨hb.1, (le_max_left _ _).trans hmax⟩,
    ⟨hb.2.1, ((le_max_left _ _).trans (le_max_right _ _)).trans hmax⟩,
    ⟨hb.2.2.1, ((le_max_right _ _).trans (le_max_right _ _)).trans hmax⟩⟩

theorem actual_buffer_data_bounds (n : ℕ) (p : Policy) (v : LogFour) :
    tauData n p v ∈ Icc 0 (U1011OriginalSixteenBufferedCandidate.bufferRate n) ∧
      xiData n p v ∈ Icc 0 (U1011OriginalSixteenBufferedCandidate.bufferRate n) ∧
      rhoData n p v ∈ Icc 0 (U1011OriginalSixteenBufferedCandidate.bufferRate n) := by
  have hzero : (0 : ℝ) ∈ Icc 0 (U1011OriginalSixteenBufferedCandidate.bufferRate n) := by
    constructor
    · exact le_rfl
    · unfold U1011OriginalSixteenBufferedCandidate.bufferRate
      positivity
  by_cases hv : v ∈ cube
  · rw [tauData, xiData, rhoData, piecewise_eq_owner _ _ _ hv,
      piecewise_eq_owner _ _ _ hv, piecewise_eq_owner _ _ _ hv]
    by_cases ht : Certified n p (owner (meshLevel n) v)
    · simp only [if_pos ht]
      exact certified_owner_buffer_bounds n p hv ht
    · simp only [if_neg ht]
      exact ⟨hzero, hzero, hzero⟩
  · rw [tauData, xiData, rhoData, piecewise_eq_zero_outside _ _ _ hv,
      piecewise_eq_zero_outside _ _ _ hv, piecewise_eq_zero_outside _ _ _ hv]
    exact ⟨hzero, hzero, hzero⟩

/-- The caller constructs the exact generic data object from actual
near-cap parameters; no buffer-smallness premise remains. -/
def actualBufferData : GeometricBufferData where
  tau := tauData
  xi := xiData
  rho := rhoData
  measurable_tau := measurable_tauData
  measurable_xi := measurable_xiData
  measurable_rho := measurable_rhoData
  tau_mem := fun n p v => (actual_buffer_data_bounds n p v).1
  xi_mem := fun n p v => (actual_buffer_data_bounds n p v).2.1
  rho_mem := fun n p v => (actual_buffer_data_bounds n p v).2.2

theorem actual_data_on_certified_owner (n : ℕ) (p : Policy) {v : LogFour}
    (hv : v ∈ cube) (ht : Certified n p (owner (meshLevel n) v)) :
    tauData n p v = U1011OriginalSixteenNearCapBoxProfiles.tau p (box n (owner (meshLevel n) v)) (eta n) v ∧
      xiData n p v = U1011OriginalSixteenNearCapBoxProfiles.xiEff p (box n (owner (meshLevel n) v)) (eta n) v ∧
      rhoData n p v = (U1011OriginalSixteenNearCapBoxProfiles.rho p (box n (owner (meshLevel n) v)) (eta n) : ℝ) := by
  simp only [tauData, xiData, rhoData, piecewise_eq_owner _ _ _ hv, if_pos ht]

end

end ImbalancedChen.P5Z.U1011OriginalSixteenNearCapGridBufferData
