import ImbalancedChen.P5ZU1011OriginalSixteenJointNearCapCompiler
import ImbalancedChen.P5ZU1011OriginalJointHarmonic
import ImbalancedChen.P5ZU1011OriginalFifteenSeparateGridCoverage
import ImbalancedChen.P5ZU1011BufferedPrimeReserve

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual JOINT low-unmasked/high-retained native labels are attached to
their reversed prime slots, full natural totient, exact logarithms and
half-open rational owner box. The true near-cap profile is used on every
certified policy; no D10 subset D11 assertion or profile datum is supplied.
-/

namespace ImbalancedChen.P5Z.JointNearCapOwnerBinding

noncomputable section

open Set
open Classical
open scoped BigOperators
open U11Integral U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenNativeHarmonic
open U1011OriginalFifteenNativeGridCells U1011OriginalFifteenJointNativeRows
open P5U1011JointOverlap

def precision (m : ℕ) : ℚ := (upper - lower) / (m + 1 : ℚ)
def step (m : ℕ) : ℝ := logPrimeMeshStep (lower : ℝ) (upper : ℝ) m

theorem precision_pos (m : ℕ) : 0 < precision m := by
  unfold precision
  exact div_pos (by norm_num [lower, upper]) (by positivity)

theorem cast_precision (m : ℕ) : (precision m : ℝ) = step m := by
  simp [precision, step, logPrimeMeshStep]

theorem step_pos (m : ℕ) : 0 < step m := logPrimeMeshStep_pos (by norm_num [lower, upper]) m

def ownerBox (m : ℕ) (v : LogFour) : Box := gridBox m (owner m v)
def Certified (m : ℕ) (p : Policy) (v : LogFour) : Prop := wholeBoxEligibleTest p (ownerBox m v) = true

def tauMap (m : ℕ) (p : Policy) (v : LogFour) : ℝ :=
  if v ∈ cube ∧ Certified m p v then
    U1011OriginalSixteenNearCapBoxProfiles.tau p (ownerBox m v) (precision m) v else 0
def xiMap (m : ℕ) (p : Policy) (v : LogFour) : ℝ :=
  if v ∈ cube ∧ Certified m p v then
    U1011OriginalSixteenNearCapBoxProfiles.xiEff p (ownerBox m v) (precision m) v else 0
def rhoMap (m : ℕ) (p : Policy) (v : LogFour) : ℝ :=
  if v ∈ cube ∧ Certified m p v then
    (U1011OriginalSixteenNearCapBoxProfiles.rho p (ownerBox m v) (precision m) : ℝ) else 0

def nativeCost (m : ℕ) (p : Policy) (v : LogFour) : ℝ :=
  U1011OriginalSixteenNearCapBoxProfiles.nativeCost p (ownerBox m v) (precision m)

theorem owner_closed_mem (m : ℕ) {v : LogFour} (hv : v ∈ cube) : v ∈ (ownerBox m v).region :=
  cell_subset_closed_box m (owner m v) (owner_mem m hv)

theorem certified_eligible (m : ℕ) (p : Policy) {v : LogFour} (hv : v ∈ cube)
    (ht : Certified m p v) : TypedEligible p v :=
  wholeBoxEligibleTest_sound p (ownerBox m v) ht v (owner_closed_mem m hv)

theorem buffer_bounds (m : ℕ) (p : Policy) (v : LogFour) :
    0 ≤ tauMap m p v ∧ tauMap m p v ≤ 12 * step m ∧
      0 ≤ xiMap m p v ∧ xiMap m p v ≤ 12 * step m ∧
      0 ≤ rhoMap m p v ∧ rhoMap m p v ≤ 12 * step m := by
  by_cases hact : v ∈ cube ∧ Certified m p v
  · have hb := U1011OriginalSixteenNearCapBoxProfiles.uniform_buffer_bound_of_coordinate_side
      p (ownerBox m v) (precision m) (gridBox_valid m (owner m v))
      (gridBox_lower_positive m (owner m v) 3) hact.2 (precision_pos m)
      (step m) (step_pos m).le (U1011OriginalFifteenSeparateGridCoverage.grid_width m (owner m v))
      (by rw [cast_precision]) v (owner_closed_mem m hact.1)
    have ht := (le_max_left _ _).trans hb.2.2.2
    have hx := (le_max_left _ _).trans ((le_max_right _ _).trans hb.2.2.2)
    have hr := (le_max_right _ _).trans ((le_max_right _ _).trans hb.2.2.2)
    simp only [tauMap, xiMap, rhoMap, if_pos hact]
    exact ⟨hb.1, ht, hb.2.1, hx, hb.2.2.1, hr⟩
  · simp only [tauMap, xiMap, rhoMap, if_neg hact]
    have hs := (step_pos m).le
    constructor
    · exact le_rfl
    · constructor
      · positivity
      · constructor
        · exact le_rfl
        · constructor
          · positivity
          · exact ⟨le_rfl, by positivity⟩

theorem nativeCost_eq_physical (m : ℕ) (p : Policy) {v : LogFour} (hv : v ∈ cube)
    (ht : Certified m p v) :
    nativeCost m p v = BufferedOrdinaryClamp.physicalCost (typedResidual p v) (v 3)
      (tauMap m p v) (xiMap m p v) (rhoMap m p v) := by
  have hh := U1011OriginalSixteenNearCapBoxProfiles.nativeCost_eq_physicalCost p (ownerBox m v)
    (precision m) (gridBox_valid m (owner m v)) (gridBox_lower_positive m (owner m v) 3)
    ht (precision_pos m) v
  simpa only [nativeCost, tauMap, xiMap, rhoMap, if_pos (show v ∈ cube ∧ Certified m p v from ⟨hv, ht⟩)] using hh

theorem joint_slots_mem_box {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) : slots t ∈ BufferedPrimeErrorPayment.tuples N := by
  apply (mem_actualPrimeBoxTuples_log_iff hN _ _ (slots t)).mpr
  refine ⟨?_, ?_⟩
  · intro i
    have hc := (mem_chenAdditivePrimeCarrier.mp (slots_carrier ht i)).2
    exact ⟨hc.1, hc.1.coprime_iff_not_dvd.mp hc.2⟩
  · simpa only [coordinates, cube, lower, upper] using joint_coordinates_cube hN ht

/-- Exact full natural totient, not a selected-subproduct surrogate. -/
theorem joint_reciprocal_totient {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) :
    1 / (Nat.totient (fullPrefix t) : ℝ) = BufferedPrimeErrorPayment.weight (slots t) := by
  exact actualPrimeBoxTuple_reciprocalTotient (joint_slots_mem_box hN ht) (slots_strictAnti ht).injective

/-- Owner geometry and native physical profile bound on the actual joint
carrier, with its low band unmasked and its literal high E complement. -/
theorem joint_owner_profile {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (m : ℕ) (p : Policy) (hc : Certified m p (coordinates N t)) :
    coordinates N t ∈ (ownerBox m (coordinates N t)).region ∧
      TypedEligible p (coordinates N t) ∧
      nativeCost m p (coordinates N t) = BufferedOrdinaryClamp.physicalCost
        (typedResidual p (coordinates N t)) (coordinates N t 3)
        (tauMap m p (coordinates N t)) (xiMap m p (coordinates N t)) (rhoMap m p (coordinates N t)) := by
  have hv := joint_coordinates_cube hN ht
  exact ⟨owner_closed_mem m hv, certified_eligible m p hv hc, nativeCost_eq_physical m p hv hc⟩

end

end ImbalancedChen.P5Z.JointNearCapOwnerBinding
