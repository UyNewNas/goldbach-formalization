import ImbalancedChen.P1OriginalFifthAdoptedOwnerBank
import Mathlib

/-!
Finite fixed-parent bank: actual B13, uniform rational e then refinement q,
and a true omitted-parent mass payment. SOURCE_ONLY / UNCOMPILED.
The remaining geometric trim budget is a real fixed-parent remainder,
not a desired integral bound hidden in a new primitive.
-/
namespace ImbalancedChen.P1OriginalFifthUniformAdoptedBankError
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators ENNReal
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover P1OriginalCoarseFifthContinuation
open P1OriginalFifthLiteralKernelModulus P1OriginalFifthJointMeshSchedule
open P1OriginalFifthAdoptedOwnerBank

def parentBankIntegral (records : Finset FifthWireRow) : ℝ := ∑ raw ∈ records, parentIntegral raw

def baselineBankIntegral (records : Finset FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  ∑ raw ∈ records, ownerIntegral raw e q chi omega 0

def retainedBankIntegral (records : Finset FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  ∑ raw ∈ records, ownerIntegral raw e q chi omega e

def trimMassBank (records : Finset FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  ∑ raw ∈ records, omittedMass raw e q chi omega

def trimVolumeBank (records : Finset FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  ∑ raw ∈ records, omittedVolumeCost raw e q chi omega

theorem trimVolumeBank_nonneg (records : Finset FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    0 ≤ trimVolumeBank records e q chi omega :=
  Finset.sum_nonneg (fun raw _ => omittedVolumeCost_nonneg raw e q chi omega)

theorem trimMassBank_nonneg (records : Finset FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    0 ≤ trimMassBank records e q chi omega :=
  Finset.sum_nonneg (fun raw _ => omittedMass_nonneg raw e q chi omega)

theorem trimMassBank_le_volumeBank (records : Finset FifthWireRow)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (hpositive : ∀ raw ∈ records, ∀ i, 1 ≤ raw.lo i)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    trimMassBank records e q chi omega ≤ trimVolumeBank records e q chi omega :=
  Finset.sum_le_sum (fun raw hr => omittedMass_le_exact_volumeCost raw
    (hgrid raw hr) (hpositive raw hr) e q chi omega)

/-- The baseline deficiency is the actual nonnegative integral on the
fixed-parent omitted domains, with no assumption that it vanishes. -/
theorem parentBank_sub_baseline_eq_trimMass (records : Finset FifthWireRow)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (hpositive : ∀ raw ∈ records, ∀ i, 1 ≤ raw.lo i)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    parentBankIntegral records - baselineBankIntegral records e q chi omega =
      trimMassBank records e q chi omega := by
  unfold parentBankIntegral baselineBankIntegral trimMassBank
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun raw hr =>
    (omittedMass_eq_parent_sub_baseline raw (hgrid raw hr) (hpositive raw hr) e q chi omega).symm)

/-- The actual canonical finite adopted bank, with its selected/firstStop
verdicts now constructed, satisfies the old B13 envelope after summation. -/
theorem retainedBank_sub_baseline_abs_le (records : Finset FifthWireRow)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (hpositive : ∀ raw ∈ records, ∀ i, 1 ≤ raw.lo i)
    (hkey : ∀ raw ∈ records, raw.lo 0 ≤ 77)
    (q : ℕ) (hq : 0 < q) (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi ≤ (e : ℝ) / 10)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) :
    |retainedBankIntegral records e q chi omega - baselineBankIntegral records e q chi omega| ≤
      bankEnvelope records rowModulus rowMassBound e := by
  unfold retainedBankIntegral baselineBankIntegral
  rw [← Finset.sum_sub_distrib]
  exact abs_sum_le_bankEnvelope records rowModulus rowMassBound e
    (fun raw => ownerIntegral raw e q chi omega e - ownerIntegral raw e q chi omega 0)
    (fun raw hr => adopted_ownerIntegral_B13 raw q hq (hgrid raw hr) (hpositive raw hr)
      (hkey raw hr) e he hemax chi omega hchi hstep)

/-- One payment for actual moving historical walls plus one payment for
the exact fixed-parent trim. The bank is indexed by original raw rows,
never by the growing number of refined decoded children. -/
theorem retainedBank_parent_error_le (records : Finset FifthWireRow)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (hpositive : ∀ raw ∈ records, ∀ i, 1 ≤ raw.lo i)
    (hkey : ∀ raw ∈ records, raw.lo 0 ≤ 77)
    (q : ℕ) (hq : 0 < q) (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi ≤ (e : ℝ) / 10)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) :
    |retainedBankIntegral records e q chi omega - parentBankIntegral records| ≤
      bankEnvelope records rowModulus rowMassBound e + trimVolumeBank records e q chi omega := by
  have hmove := retainedBank_sub_baseline_abs_le records hgrid hpositive hkey q hq e he hemax
    chi omega hchi hstep
  have hid := parentBank_sub_baseline_eq_trimMass records hgrid hpositive e q chi omega
  have htrim : |baselineBankIntegral records e q chi omega - parentBankIntegral records| =
      trimMassBank records e q chi omega := by
    rw [abs_sub_comm, hid, abs_of_nonneg (trimMassBank_nonneg records e q chi omega)]
  calc
    |retainedBankIntegral records e q chi omega - parentBankIntegral records| ≤
        |retainedBankIntegral records e q chi omega - baselineBankIntegral records e q chi omega| +
          |baselineBankIntegral records e q chi omega - parentBankIntegral records| := abs_sub_le _ _ _
    _ ≤ bankEnvelope records rowModulus rowMassBound e + trimMassBank records e q chi omega := by
      rw [htrim]
      exact add_le_add_right hmove _
    _ ≤ bankEnvelope records rowModulus rowMassBound e + trimVolumeBank records e q chi omega :=
      add_le_add_left (trimMassBank_le_volumeBank records hgrid hpositive e q chi omega) _

/-- A prescribed half-budget fixes ONE positive rational e before ONE
actual rational refinement q. The canonical common-adopted bank is then
formed from that same e/q. Its full fixed-parent error is strictly below
half the prescribed tolerance plus its TRUE weighted trim volume.
If this remaining geometric trim fits the other half, the total error
is strictly below eta. No small-trim assertion or full archived cover is
smuggled into the buffer/mesh choice. -/
theorem exists_uniform_adopted_bank_error_parameters (records : Finset FifthWireRow)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (hpositive : ∀ raw ∈ records, ∀ i, 1 ≤ raw.lo i)
    (hkey : ∀ raw ∈ records, raw.lo 0 ≤ 77)
    (eta omega : ℝ) (heta : 0 < eta) (homega : 0 < omega) :
    ∃ e : ℚ, ∃ q : ℕ,
      0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧ 0 < q ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 ∧
      (∀ raw ∈ records, 0 ≤ raw.mask →
        fixedParent raw = ⋃ r ∈ decodeFifthRows raw (refinedMesh q),
          logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell) ∧
      |retainedBankIntegral records e q ((e : ℝ) / 20) omega - parentBankIntegral records| <
        eta / 2 + trimVolumeBank records e q ((e : ℝ) / 20) omega ∧
      (trimVolumeBank records e q ((e : ℝ) / 20) omega ≤ eta / 2 →
        |retainedBankIntegral records e q ((e : ℝ) / 20) omega - parentBankIntegral records| < eta) := by
  obtain ⟨e, q, he, hecap, hq, _hchiPos, hchi10, hstep, hstepOmega, hbudget, hcover⟩ :=
    exists_joint_buffer_mesh_complete_cover records rowModulus rowMassBound
      (fun raw _ => (rowModulus_continuous raw).continuousAt)
      (fun raw _ => rowModulus_zero raw) (eta / 2) omega (by positivity) homega
  have heQ : (0 : ℚ) ≤ e := by exact_mod_cast he.le
  have hemaxQ : e ≤ (3 / 51200 : ℚ) := by exact_mod_cast hecap.le
  have hbound := retainedBank_parent_error_le records hgrid hpositive hkey q hq e heQ hemaxQ
    ((e : ℝ) / 20) omega hchi10.le hstep
  have hstrict :
      |retainedBankIntegral records e q ((e : ℝ) / 20) omega - parentBankIntegral records| <
        eta / 2 + trimVolumeBank records e q ((e : ℝ) / 20) omega :=
    hbound.trans_lt (add_lt_add_right hbudget _)
  refine ⟨e, q, he, hecap, hq, hstep, hstepOmega, ?_, hstrict, ?_⟩
  · intro raw hr hmask
    exact hcover raw (hgrid raw hr) hmask
  · intro htrim
    linarith

end
end ImbalancedChen.P1OriginalFifthUniformAdoptedBankError
