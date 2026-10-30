import ImbalancedChen.P1OriginalFifthGrid400RefinedFullBoxCover
import Mathlib.Topology.Instances.Rat

/-!
The original grid400 moving-mesh quantifier order.

SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT. No selected-row or first-stop verdict
is inferred. The kernel moduli below are the per-raw-row moduli in (B13),
not an assumed integral estimate. The missing actual crossing sections and
compact-kernel modulus construction remain separate obligations.
-/
namespace ImbalancedChen.P1OriginalFifthJointMeshSchedule

noncomputable section
open Set
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover

/-- The geometric B13 envelope for one original grid400 raw row. It has
no factor counting the decoded refined owners. -/
def rowEnvelope {ι : Type*} (modulus : ι → ℝ → ℝ) (massBound : ι → ℝ)
    (i : ι) (e : ℝ) : ℝ :=
  modulus i e / (400 : ℝ)^5 + massBound i * (428 / 75 : ℝ) * e / (400 : ℝ)^4

/-- Only the fixed raw-row bank is summed. Its index set is chosen before
the positive buffer, and is independent of the moving mesh. -/
def bankEnvelope {ι : Type*} (S : Finset ι)
    (modulus : ι → ℝ → ℝ) (massBound : ι → ℝ) (e : ℝ) : ℝ :=
  ∑ i ∈ S, rowEnvelope modulus massBound i e

theorem bankEnvelope_continuousAt_zero {ι : Type*} (S : Finset ι)
    (modulus : ι → ℝ → ℝ) (massBound : ι → ℝ)
    (hmodulus : ∀ i ∈ S, ContinuousAt (modulus i) 0) :
    ContinuousAt (bankEnvelope S modulus massBound) 0 := by
  classical
  suffices h : ∀ T : Finset ι,
      (∀ i ∈ T, ContinuousAt (modulus i) 0) →
        ContinuousAt (bankEnvelope T modulus massBound) 0 from h S hmodulus
  intro T
  induction T using Finset.induction_on with
  | empty =>
      intro _
      have hEq : bankEnvelope (∅ : Finset ι) modulus massBound = (fun _ : ℝ => (0 : ℝ)) := by
        funext e
        simp only [bankEnvelope, Finset.sum_empty]
      rw [hEq]
      exact continuousAt_const
  | @insert i T hi ih =>
      intro hT
      have htail := ih (fun j hj => hT j (Finset.mem_insert_of_mem hj))
      have hhead : ContinuousAt (rowEnvelope modulus massBound i) 0 := by
        have hw : ContinuousAt (modulus i) 0 := hT i (Finset.mem_insert_self i T)
        unfold rowEnvelope
        fun_prop
      have hEq : bankEnvelope (insert i T) modulus massBound =
          (fun e => rowEnvelope modulus massBound i e + bankEnvelope T modulus massBound e) := by
        funext e
        simp only [bankEnvelope, Finset.sum_insert hi]
      rw [hEq]
      exact hhead.add htail

theorem bankEnvelope_zero {ι : Type*} (S : Finset ι)
    (modulus : ι → ℝ → ℝ) (massBound : ι → ℝ)
    (hzero : ∀ i ∈ S, modulus i 0 = 0) :
    bankEnvelope S modulus massBound 0 = 0 := by
  unfold bankEnvelope
  apply Finset.sum_eq_zero
  intro i hi
  simp only [rowEnvelope, hzero i hi, zero_div, mul_zero, add_zero]

/-- A rational buffer is chosen from the genuine finite-bank continuity
radius. It is chosen BEFORE the refinement. This is the step unavailable
if a positive mesh was fixed in advance. -/
theorem exists_rational_buffer_for_bank {ι : Type*} (S : Finset ι)
    (modulus : ι → ℝ → ℝ) (massBound : ι → ℝ)
    (hmodulus : ∀ i ∈ S, ContinuousAt (modulus i) 0)
    (hzero : ∀ i ∈ S, modulus i 0 = 0)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ e : ℚ, 0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧
      bankEnvelope S modulus massBound e < eta := by
  have hc := bankEnvelope_continuousAt_zero S modulus massBound hmodulus
  obtain ⟨delta, hdelta, hnear⟩ := Metric.continuousAt_iff.mp hc eta heta
  have hr : (0 : ℝ) < min (3 / 51200 : ℝ) delta :=
    lt_min (by norm_num) hdelta
  obtain ⟨e, he, her⟩ := exists_rat_btwn hr
  have hecap : (e : ℝ) < 3 / 51200 := her.trans_le (min_le_left _ _)
  have hedelta : (e : ℝ) < delta := her.trans_le (min_le_right _ _)
  have hd : dist (e : ℝ) 0 < delta := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos he] using hedelta
  have hbudget := hnear hd
  rw [Real.dist_eq, bankEnvelope_zero S modulus massBound hzero, sub_zero] at hbudget
  exact ⟨e, he, hecap, (abs_lt.mp hbudget).2⟩

/-- There is ONE positive rational e and ONE refinement for the entire
fixed raw-row bank. chi=e/20 meets the literal Gamma hypotheses, and the
same refinement also meets any previously chosen positive omega budget.
The actual complete grid400 Ico cover is retained for EVERY original raw
row, including all equality faces. No decoded-owner cardinality enters
the bank envelope. -/
theorem exists_joint_buffer_mesh_complete_cover {ι : Type*} (S : Finset ι)
    (modulus : ι → ℝ → ℝ) (massBound : ι → ℝ)
    (hmodulus : ∀ i ∈ S, ContinuousAt (modulus i) 0)
    (hzero : ∀ i ∈ S, modulus i 0 = 0)
    (eta omega : ℝ) (heta : 0 < eta) (homega : 0 < omega) :
    ∃ e : ℚ, ∃ q : ℕ,
      0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧ 0 < q ∧
      0 < (e : ℝ) / 20 ∧ (e : ℝ) / 20 < (e : ℝ) / 10 ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 ∧
      bankEnvelope S modulus massBound e < eta ∧
      ∀ raw : FifthWireRow, raw.grid = 400 → 0 ≤ raw.mask →
        raw.originalBox ∩
          logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) =
            ⋃ r ∈ decodeFifthRows raw (refinedMesh q),
              logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell := by
  obtain ⟨e, he, hecap, hbudget⟩ :=
    exists_rational_buffer_for_bank S modulus massBound hmodulus hzero eta heta
  have hradius : 0 < min ((e : ℝ) / 10) omega := lt_min (by positivity) homega
  obtain ⟨q, hq, hstep, hcover⟩ :=
    exists_small_step_complete_cover (min ((e : ℝ) / 10) omega) hradius
  have hstepE : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 := by
    have hmin : min ((e : ℝ) / 10) omega ≤ (e : ℝ) / 10 := min_le_left _ _
    linarith
  have hstepOmega : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 := by
    have hmin : min ((e : ℝ) / 10) omega ≤ omega := min_le_right _ _
    linarith
  exact ⟨e, q, he, hecap, hq, by positivity, by linarith,
    hstepE, hstepOmega, hbudget, hcover⟩

/-- Once actual per-row B13 bounds have been proved, their signed sum is
paid by the same scalar bank envelope. This is a finite triangle inequality,
not a source for the missing per-row analytic estimates. -/
theorem abs_sum_le_bankEnvelope {ι : Type*} (S : Finset ι)
    (modulus : ι → ℝ → ℝ) (massBound : ι → ℝ) (e : ℝ)
    (error : ι → ℝ)
    (hrow : ∀ i ∈ S, |error i| ≤ rowEnvelope modulus massBound i e) :
    |∑ i ∈ S, error i| ≤ bankEnvelope S modulus massBound e := by
  classical
  calc
    |∑ i ∈ S, error i| ≤ ∑ i ∈ S, |error i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ bankEnvelope S modulus massBound e := Finset.sum_le_sum hrow

end
end ImbalancedChen.P1OriginalFifthJointMeshSchedule
