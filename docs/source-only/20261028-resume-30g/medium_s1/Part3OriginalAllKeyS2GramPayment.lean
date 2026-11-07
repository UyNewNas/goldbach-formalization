import ImbalancedChen.Part3OriginalCompleteS123Ledger
import ImbalancedChen.Part3ActualOuterPrincipalScalePayment
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Consume the independent F actual S2 zero/Gram mismatch bound at its
true V(D)=M*N^2/(Q1*D), then insert the original outside L2 and TWO
actual key cardinalities. This pays the real factor 2 in S1-2S2+S3.
No general residual, spectral or bare-medium conclusion is a premise.
-/

namespace ImbalancedChen.Part3.OriginalAllKeyS2GramPayment20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open ActualRoughContourParameters20261026b ActualMediumVarianceAtomBindingSourceOnly
open MediumReceiverCutoffArithmetic20261028 MediumGlobalDyadicOwnership20261028
open OriginalS1OuterCauchy20261028 OriginalS1OuterScalePayment20261028
open OriginalS1KeyMultiplicityPayment OriginalSamePsiS1OwnedAtlas
open ActualOuterPrincipalScalePayment20261028
open ImbalancedChen.Part3OriginalS2SameSourcePrincipal
open ImbalancedChen.Part3OriginalS2NativeZeroGramBudget
open ImbalancedChen.Part3OriginalS2FixedDMixedTail
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding

def actualOuterZeroGramBudget (atom : MediumAtom) : ℝ :=
  2 * ((originalNumericKeys atom (roughZ atom.scale)).card : ℝ) *
    ∑ k ∈ originalNumericKeys atom (roughZ atom.scale), outerL2 atom k *
      ‖actualZeroGramError atom (strictReceiverCutoff (roughZ atom.scale))
        (originalSmoothTrim atom) k‖

/-- The count estimate is called once at a precision fixed before all
keys. There is no summation of d separate arbitrary-log errors, and the
physical factor Y cancels only against the original MY outer multiplier. -/
theorem original_all_key_S2_Gram_log_payment (B : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (σ κ c0 : ℝ) (atom : MediumAtom),
        MediumAdmissible B σ κ c0 atom → 0 ≤ σ → 0 < c0 → x0 ≤ atom.scale →
          actualOuterZeroGramBudget atom ≤ C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  let p : ℕ := betaMomentOrder B
  let e : ℕ := p + 12
  let D : ℝ := A + (e : ℝ)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  obtain ⟨C, X, hC, hX, hGram⟩ := exists_actualZeroGramError_arbitrary_log D hD
  let Cout := 24 * C * betaLogConstant ^ p * (2 * keyLogConstant) ^ 12
  have hCout : 0 < Cout := by
    have := betaLogConstant_pos
    have := keyLogConstant_pos
    dsimp only [Cout]
    positivity
  have hXone : 1 < X := by
    have he1 : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    have he2 : Real.exp 1 < Real.exp (Real.exp 1) := Real.exp_lt_exp.mpr he1
    linarith
  refine ⟨Cout, hCout, max X (Real.exp 1), hXone.trans_le (le_max_left _ _), ?_⟩
  intro σ κ c0 atom hAdm hσ hc0 hx
  have hX' : X ≤ atom.scale := (le_max_left _ _).trans hx
  have hlog : 1 ≤ Real.log atom.scale := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      ((le_max_right _ _).trans hx)
  let t := Real.log atom.scale
  let K := originalNumericKeys atom (roughZ atom.scale)
  have ht : 0 < t := by dsimp only [t]; linarith
  have hV : 0 ≤ atom.V := zero_le_one.trans hAdm.2.1
  have hQ : 0 < atom.Q1 := lt_of_lt_of_le zero_lt_one hAdm.2.2.1
  have hbeta0 := betaL2_nonneg atom
  have hbeta := actual_betaL2_le_scale_log atom hAdm hlog
  have hcard := originalNumericKeys_card_sq_le_scale_log hAdm hσ (roughZ atom.scale) hlog
  have hkeyC := keyLogConstant_pos
  have hbetaC := betaLogConstant_pos
  let E := 6 * C * betaL2 atom * atom.V * atom.U ^ 2 / t ^ D
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hterm : ∀ k ∈ K,
      outerL2 atom k * ‖actualZeroGramError atom (strictReceiverCutoff (roughZ atom.scale))
        (originalSmoothTrim atom) k‖ ≤ E := by
    intro k hk
    have hY : 0 < keyY atom k := by dsimp only [keyY, keyD]; positivity
    have hg := hGram B σ κ c0 atom k hAdm hσ hc0 hX'
    have hscale : fixedDScale atom ((2 : ℝ) ^ k.d) = atom.V * atom.U ^ 2 / keyY atom k := by
      simp only [fixedDScale, keyY, keyD, Nat.cast_pow, Nat.cast_ofNat]
    rw [hscale, Real.rpow_neg ht.le] at hg
    have hg' : ‖actualZeroGramError atom (strictReceiverCutoff (roughZ atom.scale))
        (originalSmoothTrim atom) k‖ ≤ C * atom.V * atom.U ^ 2 / (keyY atom k * t ^ D) := by
      convert hg using 1 <;>
        simp only [originalSmoothTrim, roughY, t, div_eq_mul_inv, mul_inv_rev] <;> ring
    calc
      _ ≤ (6 * keyY atom k * betaL2 atom) *
          (C * atom.V * atom.U ^ 2 / (keyY atom k * t ^ D)) :=
        mul_le_mul (outerL2_le_actual_Y_betaL2 atom k hAdm) hg' (norm_nonneg _) (by positivity)
      _ = E := by
        dsimp only [E]
        field_simp [hY.ne', (Real.rpow_pos_of_pos ht D).ne'] <;> ring
  calc
    actualOuterZeroGramBudget atom ≤ 2 * (K.card : ℝ) ^ 2 * E := by
      unfold actualOuterZeroGramBudget
      change 2 * (K.card : ℝ) * (∑ k ∈ K, _) ≤ _
      calc
        _ ≤ 2 * (K.card : ℝ) * (∑ _k ∈ K, E) :=
          mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by positivity)
        _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ 2 * ((2 * keyLogConstant) ^ 12 * t ^ 12) *
        (6 * C * (2 * atom.V * betaLogConstant ^ p * t ^ p) * atom.V * atom.U ^ 2 / t ^ D) := by
      have hEupper : E ≤
          6 * C * (2 * atom.V * betaLogConstant ^ p * t ^ p) * atom.V * atom.U ^ 2 / t ^ D := by
        dsimp only [E]
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg ht.le D)
        have h := mul_le_mul_of_nonneg_left hbeta
          (show 0 ≤ 6 * C * atom.V * atom.U ^ 2 by positivity)
        convert h using 1 <;> ring
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcard (by norm_num)) hEupper hE (by positivity)
    _ = Cout * atom.scale ^ 2 / t ^ A := by
      dsimp only [Cout, D, e]
      rw [Real.rpow_add ht A ((p + 12 : ℕ) : ℝ), Real.rpow_natCast, pow_add]
      unfold MediumAtom.scale
      field_simp [ht.ne', (Real.rpow_pos_of_pos ht A).ne', pow_ne_zero p ht.ne'] <;> ring

end
end ImbalancedChen.Part3.OriginalAllKeyS2GramPayment20261028
