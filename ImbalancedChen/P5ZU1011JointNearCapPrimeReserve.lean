import ImbalancedChen.P5ZU1011JointNearCapPointError

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual JOINT native near-cap prime reserve. Low-fourth labels remain
unmasked by E and high-fourth labels retain the SAME literal complement.
The actual full-prefix totient and owner-box profile are used. Mesh and
precision precede N, E and every moving keep mask. Only the SAME certified
bank minimum is compared; completeness of that bank is not invented.
-/

namespace ImbalancedChen.P5Z.JointNearCapPrimeReserve

noncomputable section

open Set Filter Topology
open Classical
open scoped BigOperators
open U11Integral U1011OriginalSixteenPolicyBank U1011OriginalSixteenArithmeticProducts
open U1011OriginalSixteenNativeHarmonic U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenKnotPayment U1011AdaptivePrimeError
open BufferedActualSixteenError BufferedPrimeErrorPayment
open JointNearCapOwnerBinding JointNearCapPointError P5U1011JointOverlap

def jointKept (N : ℕ) (E : ℕ × ℕ → Prop) (keep : Four → Prop) (q : Tuple) : Prop :=
  unslots q ∈ jointSelector N E ∧ keep (unslots q)

def jointMass (N : ℕ) (E : ℕ × ℕ → Prop) (keep : Four → Prop) (f : LogFour → ℝ) : ℝ :=
  ∑ t ∈ jointSelector N E, if keep t then f (coordinates N t) / (Nat.totient (fullPrefix t) : ℝ) else 0

/-- Exact native Nat-phi/log/slot attachment with both arbitrary moving
masks. The cube restriction comes from genuine JOINT arithmetic geometry. -/
theorem jointMass_eq_box {N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop)
    (keep : Four → Prop) (f : LogFour → ℝ) :
    jointMass N E keep f = ∑ q ∈ tuples N,
      if jointKept N E keep q then weight q * f (actualPrimeTupleLog N q) else 0 := by
  let T := (jointSelector N E).filter keep
  let Q := (tuples N).filter (jointKept N E keep)
  calc
    jointMass N E keep f = ∑ t ∈ T, f (coordinates N t) / (Nat.totient (fullPrefix t) : ℝ) := by
      simp only [jointMass, T, Finset.sum_filter]
    _ = ∑ q ∈ Q, weight q * f (actualPrimeTupleLog N q) := by
      refine Finset.sum_bij (fun t _ => slots t) ?_ ?_ ?_ ?_
      · intro t ht
        obtain ⟨ht, hk⟩ := Finset.mem_filter.mp ht
        refine Finset.mem_filter.mpr ⟨joint_slots_mem_box hN ht, ?_⟩
        simpa only [jointKept, unslots_slots] using (show t ∈ jointSelector N E ∧ keep t from ⟨ht, hk⟩)
      · intro t _ u _ heq
        exact slots_injective heq
      · intro q hq
        obtain ⟨hq, hj, hk⟩ := Finset.mem_filter.mp hq
        refine ⟨unslots q, Finset.mem_filter.mpr ⟨hj, hk⟩, slots_unslots q⟩
      · intro t ht
        have hj := (Finset.mem_filter.mp ht).1
        have hPhi := joint_reciprocal_totient hN hj
        change f (actualPrimeTupleLog N (slots t)) / (Nat.totient (fullPrefix t) : ℝ) = _
        rw [div_eq_mul_one_div, hPhi]
        ring
    _ = _ := by simp only [Q, Finset.sum_filter]

private theorem jointMass_le_payment {N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop)
    (keep : Four → Prop) (f : LogFour → ℝ) {δ e : ℝ} (he : 0 ≤ e)
    (hpaid : ∀ v ∈ cube, f v ≤ pointError δ e v) :
    jointMass N E keep f ≤ payment N (jointKept N E keep) δ e := by
  rw [jointMass_eq_box hN]
  unfold payment actualPrimeBoxMass maskedStripMass
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q hq
  have hw : 0 ≤ weight q := actualPrimeBoxWeight_nonneg hq
  have hew : 0 ≤ e * weight q := mul_nonneg he hw
  have hv : actualPrimeTupleLog N q ∈ cube := by
    simpa only [cube, lower, upper] using ((mem_actualPrimeBoxTuples_log_iff hN _ _ q).mp hq).2
  by_cases hk : jointKept N E keep q
  · have hh := mul_le_mul_of_nonneg_left (hpaid _ hv) hw
    simp only [if_pos hk]
    by_cases hb : actualPrimeTupleLog N q ∈ knotStrip δ
    · simp only [pointError, if_pos hb] at hh
      simp only [hk, hb, and_self, if_true]
      change weight q * f (actualPrimeTupleLog N q) ≤ e * weight q + badCostBound * weight q
      nlinarith only [hh, hew]
    · simp only [pointError, if_neg hb] at hh
      simp only [hb, and_false, if_false, mul_zero, add_zero]
      simpa only [weight, mul_comm] using hh
  · simp only [if_neg hk, hk, false_and, if_false, mul_zero, add_zero]
    exact hew

def jointPolicyError (N m : ℕ) (E : ℕ × ℕ → Prop) (keep : Four → Prop) (p : Policy) : ℝ :=
  jointMass N E keep (policyExcess m p)
def jointMinimumError (N m : ℕ) (E : ℕ × ℕ → Prop) (keep : Four → Prop) : ℝ :=
  jointMass N E keep (minimumExcess m)
def jointTotalError (N m : ℕ) (E : ℕ × ℕ → Prop) (keep : Four → Prop) : ℝ :=
  (∑ p : Policy, jointPolicyError N m E keep p) + jointMinimumError N m E keep

theorem jointPolicyError_le_payment {N : ℕ} (hN : 1 < N) (m : ℕ)
    (E : ℕ × ℕ → Prop) (keep : Four → Prop) {δ e : ℝ} (hd : 0 < δ) (he : 0 < e)
    (hstep : 12 * step m ≤ scale δ e) (p : Policy) :
    jointPolicyError N m E keep p ≤ payment N (jointKept N E keep) δ e :=
  jointMass_le_payment hN E keep _ he.le (fun _ hv => policyExcess_le m p hv hd he hstep)

theorem jointMinimumError_le_payment {N : ℕ} (hN : 1 < N) (m : ℕ)
    (E : ℕ × ℕ → Prop) (keep : Four → Prop) {δ e : ℝ} (hd : 0 < δ) (he : 0 < e)
    (hstep : 12 * step m ≤ scale δ e) :
    jointMinimumError N m E keep ≤ payment N (jointKept N E keep) δ e :=
  jointMass_le_payment hN E keep _ he.le (fun _ hv => minimumExcess_le m hv hd he hstep)

/-- A true actual native-profile reserve BEFORE N, E and every keep mask.
No buffer data/cost reserve/mean premise is supplied. Every physical datum
is the actual rational owner profile at eta=step, supplied by its source.
Only same-certified-bank minima appear, so no lost option is ignored. -/
theorem exists_uniform_joint_native_reserve (ε : ℝ) (he : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ m N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      ∀ (E : ℕ × ℕ → Prop) (keep : Four → Prop),
        jointTotalError N m E keep < ε ∧
          (∀ p : Policy, jointPolicyError N m E keep p < ε) ∧ jointMinimumError N m E keep < ε := by
  have hB : 0 < badCostBound := badCostBound_pos
  have hC : 0 ≤ originalCubeMassBound := by unfold originalCubeMassBound; positivity
  have hC1 : 0 < originalCubeMassBound + 1 := by linarith only [hC]
  let e : ℝ := ε / (100 * (originalCubeMassBound + 1))
  have he0 : 0 < e := by dsimp only [e]; positivity
  obtain ⟨δ, hd, Nwall, hNwall, hwall⟩ := exists_uniform_masked_strip_reserve
    (ε / (100 * badCostBound)) (by positivity)
  have hscale : 0 < scale δ e / 12 := div_pos (scale_pos hd he0) (by norm_num)
  obtain ⟨m, hm⟩ := ((tendsto_logPrimeMeshStep (lower : ℝ) (upper : ℝ)).eventually
    (gt_mem_nhds hscale)).exists
  have hstep : 12 * step m ≤ scale δ e := by
    change logPrimeMeshStep (lower : ℝ) (upper : ℝ) m < scale δ e / 12 at hm
    dsimp only [step]
    linarith only [hm]
  obtain ⟨Nmass, hNmass⟩ := eventually_atTop.mp eventually_originalCube_mass_bounded
  refine ⟨δ, hd, m, max Nwall (max Nmass 2), ?_, ?_⟩
  · exact (le_max_right Nmass 2).trans (le_max_right _ _)
  · intro N hN E keep
    have hNW : Nwall ≤ N := (le_max_left _ _).trans hN
    have hNM : Nmass ≤ N := (le_max_left Nmass 2).trans ((le_max_right _ _).trans hN)
    have hN2 : 1 < N := by have hh := (le_max_right Nmass 2).trans ((le_max_right _ _).trans hN); omega
    have hMass := hNmass N hNM
    have hStrip := hwall N hNW (jointKept N E keep) δ hd.le le_rfl
    have hGood : e * actualPrimeBoxMass N
        (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ)) ≤ ε / 100 := by
      have hh := mul_le_mul_of_nonneg_left hMass he0.le
      have hBudget : e * (originalCubeMassBound + 1) = ε / 100 := by
        dsimp only [e]
        field_simp [hC1.ne']
        <;> ring
      have hExtra : e * originalCubeMassBound ≤ e * (originalCubeMassBound + 1) := by nlinarith only [he0]
      exact hh.trans (hExtra.trans_eq hBudget)
    have hBad : badCostBound * maskedStripMass N (jointKept N E keep) δ < ε / 100 := by
      have hh := mul_lt_mul_of_pos_left hStrip hB
      have hBudget : badCostBound * (ε / (100 * badCostBound)) = ε / 100 := by
        field_simp [hB.ne']
        <;> ring
      simpa only [hBudget] using hh
    have hPay : payment N (jointKept N E keep) δ e < ε / 50 := by
      dsimp only [payment]
      linarith only [hGood, hBad]
    have hPolicy : ∀ p : Policy, jointPolicyError N m E keep p ≤ payment N (jointKept N E keep) δ e :=
      jointPolicyError_le_payment hN2 m E keep hd he0 hstep
    have hMin := jointMinimumError_le_payment hN2 m E keep hd he0 hstep
    have hSum : (∑ p : Policy, jointPolicyError N m E keep p) ≤ 16 * payment N (jointKept N E keep) δ e := by
      have hh := Finset.sum_le_sum (s := (Finset.univ : Finset Policy)) (fun p _ => hPolicy p)
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
    have hTotal : jointTotalError N m E keep < ε := by
      dsimp only [jointTotalError]
      linarith only [hSum, hMin, hPay, he]
    exact ⟨hTotal, fun p => (hPolicy p).trans_lt (hPay.trans (by linarith only [he])),
      hMin.trans_lt (hPay.trans (by linarith only [he]))⟩

end

end ImbalancedChen.P5Z.JointNearCapPrimeReserve
