import ImbalancedChen.Part3OriginalS2SingleZeroPayment
import ImbalancedChen.Part3MediumOriginalAllKeyRestorationPayment
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Pay the genuine mean-weighted S2 singleZeroCorrection after the actual
outerL2 and BOTH originalNumericKeys multiplicities. This is a different
source from the two off-diagonal S3 single zeros. No residual estimate,
free-key geometry or replacement principal model is assumed.
-/

namespace ImbalancedChen.Part3.OriginalAllKeyS2SingleZeroPayment20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalSamePsiS1OwnedAtlas OriginalS1KeyMultiplicityPayment
open OriginalS1OuterCauchy20261028 OriginalS1OuterScalePayment20261028
open ActualMediumVarianceAtomBindingSourceOnly ActualOuterPrincipalScalePayment20261028
open MediumGlobalDyadicOwnership20261028 MediumReceiverCutoffArithmetic20261028
open MediumActualDiagonalDivisorPayment20261028
open ImbalancedChen.Part3OriginalS2SingleZeroPayment
open ImbalancedChen.Part3OriginalS2FixedDMixedTail
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary

/-- Only the actual outside norm budget is named; the original residual
functional and its signed summands are not redefined. -/
def actualOuterS2SingleZeroBudget (atom : MediumAtom) (z : ℝ) : ℝ :=
  ((originalNumericKeys atom z).card : ℝ) *
    ∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
      ‖singleZeroCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖

/-- Request D=A+betaMomentOrder(B)+12 once from the independently
counted H S2 source. The Y denominator cancels against the real outer
energy; the ordinary beta mean and both key multiplicities are paid.
The threshold precedes c0, atom, receiver and every occupied key. -/
theorem original_all_key_S2_singleZero_log_payment
    (B : ℕ) (κ A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (σ c0 : ℝ) (atom : MediumAtom),
        MediumAdmissible B σ κ c0 atom → 0 ≤ σ → 0 < c0 → x0 ≤ atom.scale →
        ∀ z : ℝ, 0 ≤ z →
          actualOuterS2SingleZeroBudget atom z ≤
            C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  let p : ℕ := betaMomentOrder B
  let D : ℝ := A + ((p + 12 : ℕ) : ℝ)
  obtain ⟨Cz, Xz, hCz, hXz, hsingle⟩ :=
    exists_actual_S2_singleZero_arbitrary_log κ D
  let Cout : ℝ := 12 * Cz * betaLogConstant ^ p * (2 * keyLogConstant) ^ 12
  have hCout : 0 < Cout := by
    have := betaLogConstant_pos
    have := keyLogConstant_pos
    dsimp only [Cout]
    positivity
  refine ⟨Cout, hCout, max Xz (Real.exp 1 + 1), ?_, ?_⟩
  · have hpos := Real.exp_pos 1
    exact (by linarith : 1 < Real.exp 1 + 1).trans_le (le_max_right _ _)
  intro σ c0 atom hAdm hσ hc0 hx z hz
  have hxz : Xz ≤ atom.scale := (le_max_left _ _).trans hx
  have hexp : Real.exp 1 ≤ atom.scale := by
    have h := (le_max_right _ _).trans hx
    linarith
  have hlog : 1 ≤ Real.log atom.scale := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
  let t := Real.log atom.scale
  let K := originalNumericKeys atom z
  have ht : 0 < t := by dsimp only [t]; linarith
  have hV : 0 ≤ atom.V := zero_le_one.trans hAdm.2.1
  have hbeta0 := betaL2_nonneg atom
  have hbeta := actual_betaL2_le_scale_log atom hAdm hlog
  have hcard := originalNumericKeys_card_sq_le_scale_log hAdm hσ z hlog
  have hkeyC := keyLogConstant_pos
  have hbetaC := betaLogConstant_pos
  let E : ℝ := 6 * Cz * betaL2 atom * atom.V * atom.U ^ 2 / t ^ D
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hterm : ∀ k ∈ K,
      outerL2 atom k *
        ‖singleZeroCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ ≤ E := by
    intro k hk
    have hY := keyY_positive hAdm k
    have hk' : k ∈ keyBank atom (strictReceiverCutoff z) (roughY atom.scale) := by
      simpa only [K, originalNumericKeys, originalSmoothTrim, roughY] using hk
    have hs := hsingle B σ c0 atom k z hAdm hσ hc0 hz hk' hxz
    have hs' : ‖singleZeroCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ ≤
        Cz * atom.V * atom.U ^ 2 / (keyY atom k * t ^ D) := by
      convert hs using 1 <;>
        simp only [originalSmoothTrim, roughY, fixedDScale, keyY, keyD, t,
          Nat.cast_pow, Nat.cast_ofNat, Real.rpow_neg ht.le, div_eq_mul_inv,
          mul_inv_rev] <;> ring
    calc
      _ ≤ (6 * keyY atom k * betaL2 atom) *
          (Cz * atom.V * atom.U ^ 2 / (keyY atom k * t ^ D)) :=
        mul_le_mul (outerL2_le_actual_Y_betaL2 atom k hAdm) hs'
          (norm_nonneg _) (by positivity)
      _ = E := by
        dsimp only [E]
        field_simp [hY.ne', (Real.rpow_pos_of_pos ht D).ne'] <;> ring
  calc
    actualOuterS2SingleZeroBudget atom z ≤ (K.card : ℝ) ^ 2 * E := by
      unfold actualOuterS2SingleZeroBudget
      change (K.card : ℝ) * (∑ k ∈ K, _) ≤ _
      calc
        _ ≤ (K.card : ℝ) * (∑ _k ∈ K, E) :=
          mul_le_mul_of_nonneg_left (sum_le_sum hterm) (Nat.cast_nonneg _)
        _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ ((2 * keyLogConstant) ^ 12 * t ^ 12) *
        (6 * Cz * (2 * atom.V * betaLogConstant ^ p * t ^ p) *
          atom.V * atom.U ^ 2 / t ^ D) := by
      have hEupper : E ≤
          6 * Cz * (2 * atom.V * betaLogConstant ^ p * t ^ p) *
            atom.V * atom.U ^ 2 / t ^ D := by
        dsimp only [E]
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg ht.le D)
        have hh := mul_le_mul_of_nonneg_left hbeta
          (show 0 ≤ 6 * Cz * atom.V * atom.U ^ 2 by positivity)
        convert hh using 1 <;> ring
      exact mul_le_mul hcard hEupper hE (by positivity)
    _ = Cout * atom.scale ^ 2 / t ^ A := by
      dsimp only [Cout, D]
      rw [Real.rpow_add ht A ((p + 12 : ℕ) : ℝ), Real.rpow_natCast, pow_add]
      unfold MediumAtom.scale
      field_simp [ht.ne', (Real.rpow_pos_of_pos ht A).ne', pow_ne_zero p ht.ne'] <;> ring

end
end ImbalancedChen.Part3.OriginalAllKeyS2SingleZeroPayment20261102
