import ImbalancedChen.Part3OriginalCompleteS123Ledger
import ImbalancedChen.Part3SignedDivisorDeletion
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Pay the actual preliminary linear exactProductCorrection, not a restored
post-square diagonal. At nm=a the beta index divides the moving residue.
The existing original divisorBeta mass and U*physical-cap power margin
therefore pay this entrance term. No divisor bound at zero is used.
-/

namespace ImbalancedChen.Part3.OriginalEntranceExactProductPayment20261028
noncomputable section
open Classical Finset Filter Topology
open scoped BigOperators
open MediumActualPreliminaryCauchy20261028 MediumActualPostSquareDeletion20261028
open OriginalS1OuterCauchy20261028

theorem exactProductCorrection_eq_original_divisorBeta (atom : MediumAtom) :
    exactProductCorrection atom = ∑ l ∈ atom.complexRowLabels, ∑ n ∈ atom.alphaCarrier,
      atom.alpha n * atom.complexFactorGamma l.1 * atom.divisorBeta l.2 *
        exactCongruence atom n l := by
  unfold exactProductCorrection
  apply sum_congr rfl
  intro l hl
  apply sum_congr rfl
  intro n hn
  by_cases he : ((n * l.2 : ℕ) : ℤ) = atom.residue
  · have hd : (l.2 : ℤ) ∣ atom.residue := by
      refine ⟨n, ?_⟩
      rw [← he]
      push_cast
      ring
    simp only [MediumAtom.divisorBeta, if_pos hd]
  · simp only [exactCongruence, if_neg he, mul_zero]

private theorem original_gamma_norm_le_one {b : ℕ} {σ κ c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible b σ κ c0 atom)
    {l : ℕ × ℕ × ℕ} (hl : l ∈ atom.complexFactorLabels) :
    ‖atom.complexFactorGamma l‖ ≤ 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3⟩ := hA
  obtain ⟨hq, h23⟩ := mem_product.mp hl
  obtain ⟨h2q, h3q⟩ := mem_product.mp h23
  rw [MediumAtom.complexFactorGamma, norm_mul, norm_mul]
  calc
    _ ≤ 1 * 1 * 1 := mul_le_mul
      (mul_le_mul (h1 _ hq).1 (h2 _ h2q).1 (norm_nonneg _) zero_le_one)
      (h3 _ h3q).1 (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

theorem exactProductCorrection_le_actual_finite_mass
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom)
    (hA : MediumAdmissible b σ κ c0 atom) :
    ‖exactProductCorrection atom‖ ≤
      81 * (atom.U * atom.Q1 * atom.Q2 * atom.Q3) *
        ∑ m ∈ atom.betaCarrier, ‖atom.divisorBeta m‖ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ := hA
  have hαsub : atom.alphaCarrier ⊆ factorCarrier atom.U := by
    unfold MediumAtom.alphaCarrier factorCarrier
    exact filter_subset _ _
  have hαcard : (atom.alphaCarrier.card : ℝ) ≤ 3 * atom.U :=
    (by exact_mod_cast card_le_card hαsub).trans (factorCarrier_card_le_three hA.1)
  have hlabels : (atom.complexFactorLabels.card : ℝ) ≤
      (3 * atom.Q1) * ((3 * atom.Q2) * (3 * atom.Q3)) := by
    simp only [MediumAtom.complexFactorLabels, card_product, Nat.cast_mul]
    exact mul_le_mul (factorCarrier_card_le_three hA.2.2.1)
      (mul_le_mul (factorCarrier_card_le_three hA.2.2.2.1)
        (factorCarrier_card_le_three hA.2.2.2.2.1) (Nat.cast_nonneg _)
        (by have := hA.2.2.2.1; positivity)) (by positivity)
      (by have := hA.2.2.1; positivity)
  rw [exactProductCorrection_eq_original_divisorBeta]
  calc
    _ ≤ ∑ l ∈ atom.complexRowLabels, ∑ n ∈ atom.alphaCarrier,
        ‖atom.alpha n * atom.complexFactorGamma l.1 * atom.divisorBeta l.2 *
          exactCongruence atom n l‖ := by
      apply (norm_sum_le _ _).trans
      exact sum_le_sum (fun l hl => norm_sum_le _ _)
    _ ≤ ∑ l ∈ atom.complexRowLabels, ∑ _n ∈ atom.alphaCarrier, ‖atom.divisorBeta l.2‖ := by
      apply sum_le_sum
      intro l hl
      apply sum_le_sum
      intro n hn
      have hg := original_gamma_norm_le_one hA (mem_product.mp hl).1
      have hi : ‖exactCongruence atom n l‖ ≤ 1 := by
        unfold exactCongruence
        split_ifs <;> norm_num
      simp only [norm_mul]
      have hag : ‖atom.alpha n‖ * ‖atom.complexFactorGamma l.1‖ ≤ 1 := by
        simpa only [one_mul] using mul_le_mul (hAlpha n hn) hg (norm_nonneg _) zero_le_one
      calc
        _ ≤ (1 * ‖atom.divisorBeta l.2‖) * 1 := mul_le_mul
          (mul_le_mul_of_nonneg_right hag (norm_nonneg _)) hi (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = (atom.alphaCarrier.card : ℝ) * (atom.complexFactorLabels.card : ℝ) *
        ∑ m ∈ atom.betaCarrier, ‖atom.divisorBeta m‖ := by
      simp only [MediumAtom.complexRowLabels, sum_product, sum_const, nsmul_eq_mul,
        ← mul_sum, ← sum_mul]
      ring
    _ ≤ (3 * atom.U) * ((3 * atom.Q1) * ((3 * atom.Q2) * (3 * atom.Q3))) *
        ∑ m ∈ atom.betaCarrier, ‖atom.divisorBeta m‖ := by
      apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => norm_nonneg _)
      exact mul_le_mul hαcard hlabels (Nat.cast_nonneg _) (by have := hA.1; positivity)
    _ = _ := by ring

theorem original_exactProductCorrection_power_payment (b : ℕ) (σ κ c0 : ℝ)
    (hσ : 0 < σ) (hc0 : 0 < c0) :
    ∃ C : ℝ, 0 < C ∧ ∀ atom : MediumAtom,
      MediumAdmissible b σ κ c0 atom →
        ‖exactProductCorrection atom‖ ≤ C * atom.scale ^ (1 - 8 * σ) := by
  obtain ⟨C, hC, hmass⟩ := divisorBetaMass_subpower b κ hσ
  refine ⟨81 * C, by positivity, ?_⟩
  intro atom hA
  have hx : 0 < atom.scale := zero_lt_one.trans_le (TransposedPrimitiveUPayment.one_le_scale hA)
  have hg : atom.U * atom.Q1 * atom.Q2 * atom.Q3 ≤ atom.scale ^ (1 - 9 * σ) := by
    have h := atom.U_mul_physicalFactorCap_le hA
    unfold MediumAtom.physicalFactorCap at h
    nlinarith
  calc
    _ ≤ 81 * (atom.U * atom.Q1 * atom.Q2 * atom.Q3) *
        ∑ m ∈ atom.betaCarrier, ‖atom.divisorBeta m‖ :=
      exactProductCorrection_le_actual_finite_mass atom hA
    _ ≤ 81 * atom.scale ^ (1 - 9 * σ) * (C * atom.scale ^ σ) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hg (by norm_num))
        (hmass σ c0 atom hc0 hA) (by positivity) (by positivity)
    _ = _ := by
      rw [show 81 * atom.scale ^ (1 - 9 * σ) * (C * atom.scale ^ σ) =
        (81 * C) * (atom.scale ^ (1 - 9 * σ) * atom.scale ^ σ) by ring,
        ← Real.rpow_add hx, show 1 - 9 * σ + σ = 1 - 8 * σ by ring]

/-- One uniform threshold pays the original entrance correction for
all moving residues and atoms. This is a linear bound, before Cauchy. -/
theorem original_exactProductCorrection_log_payment (b : ℕ) (σ κ c0 A : ℝ)
    (hσ : 0 < σ) (hc0 : 0 < c0) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ atom : MediumAtom,
      MediumAdmissible b σ κ c0 atom → x0 ≤ atom.scale →
        ‖exactProductCorrection atom‖ ≤ atom.scale / Real.log atom.scale ^ A := by
  obtain ⟨C, hC, hbound⟩ := original_exactProductCorrection_power_payment b σ κ c0 hσ hc0
  obtain ⟨x1, hx1⟩ := eventually_atTop.mp
    (TransposedPrimitiveUPayment.eventually_const_log_rpow_le_rpow C A hC.le
      (by linarith : 0 < 8 * σ))
  obtain ⟨x2, hx2⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ))
  refine ⟨max 2 (max x1 x2), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro atom hA hx
  have hxpos : 0 < atom.scale := zero_lt_one.trans_le (TransposedPrimitiveUPayment.one_le_scale hA)
  have hlog : 1 ≤ Real.log atom.scale := hx2 atom.scale
    ((le_max_right x1 x2).trans ((le_max_right 2 (max x1 x2)).trans hx))
  have hpay := hx1 atom.scale ((le_max_left x1 x2).trans ((le_max_right 2 (max x1 x2)).trans hx))
  apply (hbound atom hA).trans
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (by linarith) A)).mpr
  calc
    _ = (C * Real.log atom.scale ^ A) * atom.scale ^ (1 - 8 * σ) := by ring
    _ ≤ atom.scale ^ (8 * σ) * atom.scale ^ (1 - 8 * σ) :=
      mul_le_mul_of_nonneg_right hpay (Real.rpow_nonneg hxpos.le _)
    _ = atom.scale := by
      rw [← Real.rpow_add hxpos, show 8 * σ + (1 - 8 * σ) = 1 by ring, Real.rpow_one]

end
end ImbalancedChen.Part3.OriginalEntranceExactProductPayment20261028
