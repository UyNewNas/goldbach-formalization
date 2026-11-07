import ImbalancedChen.Part3OriginalS3ClosePairCount
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Pay section 4's close-pair source with Csep chosen AFTER the fixed shift
cutoff.  The 12*x*log(x)^(6*Ccut) endpoint cost is absorbed by the original
occupied-key geometry.  No divisor subpower is used on the logarithmic
main term, and no large-shift estimate is assumed.
-/
namespace ImbalancedChen.Part3.OriginalS3ClosePairPayment20261102
noncomputable section
open Classical Finset Filter
open scoped BigOperators
open OriginalS3ClosePairCount20261102
open MediumActualDiagonalDivisorPayment20261028 MediumActualRestorationPayment20261028
open MediumGlobalDyadicOwnership20261028 MediumReceiverCutoffArithmetic20261028
open MediumOriginalAllKeyRestorationPayment20261102
open OriginalSamePsiS1OwnedAtlas OriginalS1KeyMultiplicityPayment
open OriginalS1OuterCauchy20261028 OriginalS1OuterScalePayment20261028
open ActualMediumVarianceAtomBindingSourceOnly ActualOuterPrincipalScalePayment20261028
open OriginalPrincipalVarianceInOuterCauchy20261028
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding

def shiftCutoff (atom : MediumAtom) (c : ℝ) : ℝ := Real.log atom.scale ^ c
def closeWidth (atom : MediumAtom) (c A : ℝ) : ℝ :=
  atom.U / Real.log atom.scale ^ (A + 6*c)

theorem closeDeleted_log_main_and_endpoint {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hAdm : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (c A : ℝ)
    (ht : 0 < Real.log atom.scale) :
    ‖closeDeleted atom z y k (shiftCutoff atom c) (closeWidth atom c A)‖ ≤
      48 * actualVScale atom k / Real.log atom.scale ^ A +
        12 * atom.scale * Real.log atom.scale ^ (6*c) := by
  have hY := keyY_positive hAdm k
  have hU : 0 < atom.U := zero_lt_one.trans_le hAdm.1
  have hh := closeDeleted_le hAdm z y k (shiftCutoff atom c) (closeWidth atom c A)
    (by unfold shiftCutoff; positivity) (by unfold closeWidth; positivity)
  apply hh.trans_eq
  unfold shiftCutoff closeWidth actualVScale MediumAtom.scale
  rw [← Real.rpow_mul_natCast ht.le,
    show c * ((6 : ℕ) : ℝ) = 6*c by norm_num; ring,
    Real.rpow_add ht A (6*c)]
  field_simp [hY.ne', (Real.rpow_pos_of_pos ht A).ne',
    (Real.rpow_pos_of_pos ht (6*c)).ne'] <;> ring

/-- Fixed Ccut precedes requested separation and every atom/key. The
original (9) supplier removes the endpoint term at the same threshold. -/
theorem exists_closeDeleted_log_payment (σ κ c A : ℝ)
    (hσ : 0 < σ) (hσsmall : σ < 1/100) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
      ∀ (z : ℝ) (k : Key), 0 ≤ z →
        k ∈ keyBank atom (strictReceiverCutoff z) (roughY atom.scale) →
        ‖closeDeleted atom (strictReceiverCutoff z) (roughY atom.scale) k
          (shiftCutoff atom c) (closeWidth atom c A)‖ ≤
          60 * actualVScale atom k / Real.log atom.scale ^ A := by
  obtain ⟨xg, hxg, hgeom⟩ := exists_original_occupied_key_geometry σ hσ hσsmall
  obtain ⟨xp, hpay⟩ := eventually_atTop.mp
    (TransposedPrimitiveUPayment.eventually_const_log_rpow_le_rpow 1 (A+6*c)
      (by norm_num) (show 0 < σ/2 by positivity))
  refine ⟨max xg (max xp (Real.exp 1)), hxg.trans_le (le_max_left _ _), ?_⟩
  intro B c0 atom hAdm hc0 hx z k hz hk
  have hxg' := (le_max_left xg (max xp (Real.exp 1))).trans hx
  have hxp' := (le_max_left xp (Real.exp 1)).trans ((le_max_right xg _).trans hx)
  have he := (le_max_right xp (Real.exp 1)).trans ((le_max_right xg _).trans hx)
  have hlog1 : 1 ≤ Real.log atom.scale := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  have ht : 0 < Real.log atom.scale := zero_lt_one.trans_le hlog1
  have hscale : 0 < atom.scale := by unfold MediumAtom.scale; nlinarith [hAdm.1, hAdm.2.1]
  have hpow : Real.log atom.scale ^ (A+6*c) ≤ atom.scale ^ (σ/2) := by
    simpa only [one_mul] using hpay _ hxp'
  have hV : atom.scale ^ (1+σ/2) ≤ actualVScale atom k :=
    diagonal_scale_ge_power hAdm (σ/2) k (hgeom B κ c0 atom hAdm hc0 hxg' _ k hk).1
  have hend : atom.scale * Real.log atom.scale ^ (6*c) ≤
      actualVScale atom k / Real.log atom.scale ^ A := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos ht A)).mpr
    calc
      _ = atom.scale * Real.log atom.scale ^ (A+6*c) := by
        rw [Real.rpow_add ht A (6*c)]; ring
      _ ≤ atom.scale * atom.scale ^ (σ/2) := mul_le_mul_of_nonneg_left hpow hscale.le
      _ = atom.scale ^ (1+σ/2) := by
        rw [show 1+σ/2 = σ/2+1 by ring, Real.rpow_add_one hscale.ne']; ring
      _ ≤ _ := hV
  have hlocal := closeDeleted_log_main_and_endpoint hAdm (strictReceiverCutoff z)
    (roughY atom.scale) k c A ht
  have h12 := mul_le_mul_of_nonneg_left hend (show (0:ℝ) ≤ 12 by norm_num)
  calc
    _ ≤ 48 * actualVScale atom k / Real.log atom.scale ^ A +
        12 * atom.scale * Real.log atom.scale ^ (6*c) := hlocal
    _ ≤ 60 * actualVScale atom k / Real.log atom.scale ^ A := by linarith

/-- Precision after the original beta-square mean and both owner-bank
multiplicities. It is fixed before any atom is selected. -/
def outerPrecision (B : ℕ) (A : ℝ) : ℝ := A + ((betaMomentOrder B + 12 : ℕ) : ℝ)

def actualOuterCloseBudget (B : ℕ) (atom : MediumAtom) (z c A : ℝ) : ℝ :=
  ((originalNumericKeys atom z).card : ℝ) *
    ∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
      ‖closeDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
        (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A))‖

/-- The actual original outside weights are paid; local precision pays
the true beta moment and the log^12 square of the occupied key bank. -/
theorem exists_actualOuterCloseBudget_payment (B : ℕ) (σ κ c A : ℝ)
    (hσ : 0 < σ) (hσsmall : σ < 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (c0 : ℝ) (atom : MediumAtom),
        MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
        ∀ z : ℝ, 0 ≤ z →
          actualOuterCloseBudget B atom z c A ≤ C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  let p : ℕ := betaMomentOrder B
  let D : ℝ := outerPrecision B A
  obtain ⟨x1, hx1, hclose⟩ := exists_closeDeleted_log_payment σ κ c D hσ hσsmall
  let Cout : ℝ := 720 * betaLogConstant ^ p * (2 * keyLogConstant) ^ 12
  have hCout : 0 < Cout := by
    have := betaLogConstant_pos
    have := keyLogConstant_pos
    dsimp only [Cout]; positivity
  refine ⟨Cout, hCout, max x1 (Real.exp 1), hx1.trans_le (le_max_left _ _), ?_⟩
  intro c0 atom hAdm hc0 hx z hz
  have hx1' : x1 ≤ atom.scale := (le_max_left _ _).trans hx
  have hlog : 1 ≤ Real.log atom.scale := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      ((le_max_right _ _).trans hx)
  let t := Real.log atom.scale
  let K := originalNumericKeys atom z
  have ht : 0 < t := by dsimp only [t]; linarith
  have hV : 0 ≤ atom.V := zero_le_one.trans hAdm.2.1
  have hQ : 0 < atom.Q1 := zero_lt_one.trans_le hAdm.2.2.1
  have hbeta0 := betaL2_nonneg atom
  have hbeta := actual_betaL2_le_scale_log atom hAdm hlog
  have hcard := originalNumericKeys_card_sq_le_scale_log hAdm hσ.le z hlog
  have hkeyC := keyLogConstant_pos
  have hbetaC := betaLogConstant_pos
  let E : ℝ := 360 * betaL2 atom * atom.V * atom.U ^ 2 / t ^ D
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hterm : ∀ k ∈ K, outerL2 atom k *
      ‖closeDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
        (shiftCutoff atom c) (closeWidth atom c D)‖ ≤ E := by
    intro k hk
    have hY := keyY_positive hAdm k
    have hk' : k ∈ keyBank atom (strictReceiverCutoff z) (roughY atom.scale) := by
      simpa only [K, originalNumericKeys, originalSmoothTrim, roughY] using hk
    have hr := hclose B c0 atom hAdm hc0 hx1' z k hz hk'
    have hr' : ‖closeDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
        (shiftCutoff atom c) (closeWidth atom c D)‖ ≤
        60 * atom.V * atom.U ^ 2 / (keyY atom k * t ^ D) := by
      convert hr using 1 <;>
        simp only [originalSmoothTrim, roughY, actualVScale, t, div_eq_mul_inv, mul_inv_rev] <;> ring
    calc
      _ ≤ (6 * keyY atom k * betaL2 atom) *
          (60 * atom.V * atom.U ^ 2 / (keyY atom k * t ^ D)) :=
        mul_le_mul (outerL2_le_actual_Y_betaL2 atom k hAdm) hr' (norm_nonneg _) (by positivity)
      _ = E := by
        dsimp only [E]
        field_simp [hY.ne', (Real.rpow_pos_of_pos ht D).ne'] <;> ring
  calc
    actualOuterCloseBudget B atom z c A ≤ (K.card : ℝ) ^ 2 * E := by
      unfold actualOuterCloseBudget
      change (K.card : ℝ) * (∑ k ∈ K, _) ≤ _
      calc
        _ ≤ (K.card : ℝ) * (∑ _k ∈ K, E) :=
          mul_le_mul_of_nonneg_left (sum_le_sum hterm) (Nat.cast_nonneg _)
        _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ ((2 * keyLogConstant) ^ 12 * t ^ 12) *
        (360 * (2 * atom.V * betaLogConstant ^ p * t ^ p) * atom.V * atom.U ^ 2 / t ^ D) := by
      have hEupper : E ≤
          360 * (2 * atom.V * betaLogConstant ^ p * t ^ p) * atom.V * atom.U ^ 2 / t ^ D := by
        dsimp only [E]
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg ht.le D)
        have hh := mul_le_mul_of_nonneg_left hbeta
          (show 0 ≤ 360 * atom.V * atom.U ^ 2 by positivity)
        convert hh using 1 <;> ring
      exact mul_le_mul hcard hEupper hE (by positivity)
    _ = Cout * atom.scale ^ 2 / t ^ A := by
      dsimp only [Cout, D, outerPrecision]
      change _ = 720 * betaLogConstant ^ p * (2 * keyLogConstant)^12 * atom.scale^2 / t^A
      rw [Real.rpow_add ht A ((p+12 : ℕ) : ℝ), Real.rpow_natCast, pow_add]
      unfold MediumAtom.scale
      field_simp [ht.ne', (Real.rpow_pos_of_pos ht A).ne', pow_ne_zero p ht.ne'] <;> ring

end
end ImbalancedChen.Part3.OriginalS3ClosePairPayment20261102
