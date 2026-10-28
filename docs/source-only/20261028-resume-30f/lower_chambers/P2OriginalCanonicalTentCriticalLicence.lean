import ImbalancedChen.P2OriginalIdealTentCanonicalScreen
import ImbalancedChen.ActualSelectedSubproductParameters

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The canonical tent source's original selected sum enters the independently
formalized critical interval, including moving residue alpha=1+3*kappa.
The same buffered cap and mask are used. This is the exact real source-form
parameter port, not a replacement for the analytic PP theorem or W licence.
-/

namespace ImbalancedChen.P2OriginalCanonicalTentCriticalLicence

noncomputable section
open scoped Classical BigOperators
open P2OriginalLowerSelectedCapConstructor (Code)
open P2OriginalLowerWholeBoxBranchSelect
open P2OriginalLowerBufferedAffineBoxes
open P2OriginalLowerAffineTieSelector
open P2OriginalPairSourceReceiver
open P2OriginalCanonicalPairTentBank

-- The complete source prefix remains elsewhere in the residual level;
-- this sum identifies only the original selected subproduct parameter.
theorem cap_plus_buffer_le_original_tent (R : PairRange) {mesh : ℕ}
    (code : Code mesh) (mask : Finset (Fin 5)) (b : SelectedBranchData)
    (hside : lowerSide R code mask = some b)
    (x : Fin 5 → ℝ) (hx : inBox (box R code) x) (buffer : ℚ) :
    (rowCap R code buffer b : ℝ) + buffer ≤ VariableEnvelope.v (∑ i ∈ mask, x i) := by
  have heval := lowerSide_eval_actual_v R code mask b hside x hx
  have hinf := wholeBoxInfimum_le_affine b.cap.constant b.cap.slope (box R code) x hx
  have heval' : affineValue b.cap.constant b.cap.slope x = b.cap.eval x := rfl
  rw [heval', heval] at hinf
  unfold rowCap
  push_cast
  linarith

theorem actual_selected_critical_interval (R : PairRange) {mesh : ℕ}
    (code : Code mesh) (mask : Finset (Fin 5)) (b : SelectedBranchData)
    (hside : lowerSide R code mask = some b)
    (x : Fin 5 → ℝ) (hx : inBox (box R code) x)
    (buffer : ℚ) (hbuffer : 0 ≤ buffer) :
    2 * (rowCap R code buffer b : ℝ) - 1 ≤ (∑ i ∈ mask, x i) ∧
      (∑ i ∈ mask, x i) ≤ actualSelectedSubproductUpper 1 (rowCap R code buffer b) := by
  have hcap := cap_plus_buffer_le_original_tent R code mask b hside x hx buffer
  have hb : (0 : ℝ) ≤ buffer := by exact_mod_cast hbuffer
  apply (actualSelectedSubproduct_critical_iff 1 (rowCap R code buffer b) _).mp
  rw [actualSelectedSubproductV_one]
  linarith

-- Whole-box endpoint slack pays the precise original moving-residue loss.
-- No auxiliary endpoint/critical interval is imposed as a new premise.
theorem actual_moving_residue_critical_interval (R : PairRange) {mesh : ℕ}
    (code : Code mesh) (mask : Finset (Fin 5)) (b : SelectedBranchData)
    (hside : lowerSide R code mask = some b)
    (x : Fin 5 → ℝ) (hx : inBox (box R code) x)
    (buffer : ℚ) (hbuffer : 0 < buffer) (kappa : ℝ) (hkappa : kappa ≤ buffer) :
    (rowCap R code buffer b : ℝ) + (buffer : ℝ) / 2 ≤
        actualSelectedSubproductV (1 + 3 * kappa) (∑ i ∈ mask, x i) ∧
      (2 * (rowCap R code buffer b : ℝ) - 1 ≤ (∑ i ∈ mask, x i) ∧
        (∑ i ∈ mask, x i) ≤ actualSelectedSubproductUpper (1 + 3 * kappa)
          (rowCap R code buffer b)) := by
  have hb : (0 : ℝ) < buffer := by exact_mod_cast hbuffer
  have hcap := cap_plus_buffer_le_original_tent R code mask b hside x hx buffer
  have hres := actualSelectedSubproductV_residue_margin
    (e := 4 * (buffer : ℝ)) (κ := kappa)
    (θ := (rowCap R code buffer b : ℝ)) (s := ∑ i ∈ mask, x i)
    (by linarith) (by linarith) (by linarith)
  have hsurplus : (rowCap R code buffer b : ℝ) + (buffer : ℝ) / 2 ≤
      actualSelectedSubproductV (1 + 3 * kappa) (∑ i ∈ mask, x i) := by
    convert hres using 1 <;> ring
  refine ⟨hsurplus, ?_⟩
  apply (actualSelectedSubproduct_critical_iff (1 + 3 * kappa)
    (rowCap R code buffer b) _).mp
  linarith

end
end ImbalancedChen.P2OriginalCanonicalTentCriticalLicence
