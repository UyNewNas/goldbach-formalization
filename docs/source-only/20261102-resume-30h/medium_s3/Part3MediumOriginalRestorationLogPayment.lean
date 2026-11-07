import ImbalancedChen.Part3MediumActualRestorationPayment
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Complete the missing analytic payment after the G physical divisor counts.
The actual deleted diagonal and BOTH actual S3 single zeros are paid at
V(D)=M*N^2/Y, with one threshold preceding every atom, receiver and key.
The single-zero count is consumed from its independent S2-lane producer;
it is not reproved or assumed as a final logarithmic estimate here.
-/

namespace ImbalancedChen.Part3.MediumOriginalRestorationLogPayment20261102
noncomputable section
open Classical Finset Filter
open scoped BigOperators
open MediumActualDiagonalDivisorPayment20261028
open MediumActualRestorationPayment20261028
open MediumLiteralS3Stages20261028 MediumGlobalDyadicOwnership20261028
open MediumReceiverCutoffArithmetic20261028 OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3OriginalActualSingleZeroSource
open ImbalancedChen.Part3OriginalActualSingleZeroCounting
open ImbalancedChen.Part3OriginalActualSingleZeroPayment
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding

/-- Power-to-log absorption at the genuine source, BEFORE the occupied
key geometry is discharged. The factor 2 is the original N+Y cost.
No count/diagonal/log-saving conclusion occurs among the hypotheses. -/
theorem exists_actual_S3_singleZeros_log_from_geometry
    (κ δ A : ℝ) (hδ : 0 < δ) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (σ c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B σ κ c0 atom → 0 ≤ σ → 0 < c0 → x0 ≤ atom.scale →
      ∀ (z : ℝ) (k : Key), 0 ≤ z →
      keyY atom k ≤ atom.U * atom.scale ^ (-δ) →
      keyY atom k * keyR k ≤ atom.scale ^ (1 - δ) →
      ‖actualFirstZero atom (strictReceiverCutoff z) (roughY atom.scale) k‖ +
        ‖actualSecondZero atom (strictReceiverCutoff z) (roughY atom.scale) k‖ ≤
        2 * actualVScale atom k / Real.log atom.scale ^ A := by
  obtain ⟨C, hC, hsingle⟩ :=
    exists_actual_singleZeros_subpower_budget κ (δ / 2) (by positivity)
  obtain ⟨x1, hx1⟩ := eventually_atTop.mp
    (TransposedPrimitiveUPayment.eventually_const_log_rpow_le_rpow C A hC.le
      (show 0 < δ / 2 by positivity))
  obtain ⟨x2, hx2⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ))
  refine ⟨max 2 (max x1 x2), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro B σ c0 atom hAdm hσ hc0 hx z k hz hY hYR
  have hx1' : x1 ≤ atom.scale :=
    (le_max_left x1 x2).trans ((le_max_right 2 (max x1 x2)).trans hx)
  have hx2' : x2 ≤ atom.scale :=
    (le_max_right x1 x2).trans ((le_max_right 2 (max x1 x2)).trans hx)
  have hlog : 0 < Real.log atom.scale := lt_of_lt_of_le zero_lt_one (hx2 _ hx2')
  have hxpos : 0 < atom.scale := by
    unfold MediumAtom.scale
    nlinarith [hAdm.1, hAdm.2.1]
  have hK : 0 ≤ singleZeroR k * (atom.U + singleZeroY atom k) := by
    have hQ : 0 < atom.Q1 := zero_lt_one.trans_le hAdm.2.2.1
    have hU : 0 < atom.U := zero_lt_one.trans_le hAdm.1
    unfold singleZeroR singleZeroY
    positivity
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hlog A)).mpr
  calc
    _ ≤ (C * (singleZeroR k * (atom.U + singleZeroY atom k) *
        atom.scale ^ (δ / 2))) * Real.log atom.scale ^ A :=
      mul_le_mul_of_nonneg_right (hsingle B σ c0 atom k z hAdm hσ hc0 hz)
        (Real.rpow_nonneg hlog.le A)
    _ = (singleZeroR k * (atom.U + singleZeroY atom k)) *
        atom.scale ^ (δ / 2) * (C * Real.log atom.scale ^ A) := by ring
    _ ≤ (singleZeroR k * (atom.U + singleZeroY atom k)) *
        atom.scale ^ (δ / 2) * atom.scale ^ (δ / 2) :=
      mul_le_mul_of_nonneg_left (hx1 _ hx1')
        (mul_nonneg hK (Real.rpow_nonneg hxpos.le _))
    _ = atom.scale ^ δ * (singleZeroR k * (atom.U + singleZeroY atom k)) := by
      rw [mul_assoc, ← Real.rpow_add hxpos,
        show δ / 2 + δ / 2 = δ by ring, mul_comm]
    _ ≤ _ := singleZeros_scale_geometry hAdm hδ k hY hYR

/-- The two components are paid at ONE common threshold, using only
the original occupied keyBank, original trim and original admissibility.
The stronger intermediate exponent sigma/2 is proved in G from (1),(7);
the manuscript's sigma/3 is not added as a new hypothesis. -/
theorem exists_original_S3_restoration_component_payments
    (σ κ A : ℝ) (hσ : 0 < σ) (hσsmall : σ < 1 / 100) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
      ∀ (z : ℝ) (k : Key), 0 ≤ z →
      k ∈ keyBank atom (strictReceiverCutoff z) (roughY atom.scale) →
      ‖actualDiagonal atom (strictReceiverCutoff z) (roughY atom.scale) k‖ ≤
          actualVScale atom k / Real.log atom.scale ^ A ∧
      ‖actualFirstZero atom (strictReceiverCutoff z) (roughY atom.scale) k‖ +
        ‖actualSecondZero atom (strictReceiverCutoff z) (roughY atom.scale) k‖ ≤
          2 * actualVScale atom k / Real.log atom.scale ^ A := by
  obtain ⟨xg, hxg, hgeom⟩ := exists_original_occupied_key_geometry σ hσ hσsmall
  obtain ⟨xd, hxd, hdiag⟩ :=
    exists_actual_deleted_diagonal_log_payment κ (σ / 2) A (by positivity)
  obtain ⟨xs, hxs, hsingle⟩ :=
    exists_actual_S3_singleZeros_log_from_geometry κ (σ / 2) A (by positivity)
  refine ⟨max xg (max xd xs), hxg.trans_le (le_max_left _ _), ?_⟩
  intro B c0 atom hAdm hc0 hx z k hz hk
  have hxg' : xg ≤ atom.scale := (le_max_left _ _).trans hx
  have hxd' : xd ≤ atom.scale :=
    (le_max_left xd xs).trans ((le_max_right xg (max xd xs)).trans hx)
  have hxs' : xs ≤ atom.scale :=
    (le_max_right xd xs).trans ((le_max_right xg (max xd xs)).trans hx)
  obtain ⟨hY, hYR⟩ := hgeom B κ c0 atom hAdm hc0 hxg' (strictReceiverCutoff z) k hk
  exact ⟨hdiag B σ c0 atom hAdm hxd' (strictReceiverCutoff z) (roughY atom.scale) k hY,
    hsingle B σ c0 atom hAdm hσ.le hc0 hxs' z k hz hY hYR⟩

/-- The genuine deleted/full-off-diagonal correction is now arbitrary-
logarithmically small. The norm retains its three actual signed sources. -/
theorem exists_original_S3_restoration_log_payment
    (σ κ A : ℝ) (hσ : 0 < σ) (hσsmall : σ < 1 / 100) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
      ∀ (z : ℝ) (k : Key), 0 ≤ z →
      k ∈ keyBank atom (strictReceiverCutoff z) (roughY atom.scale) →
      ‖restorationCorrection atom (strictReceiverCutoff z) (roughY atom.scale) k‖ ≤
        3 * actualVScale atom k / Real.log atom.scale ^ A := by
  obtain ⟨x0, hx0, hpay⟩ := exists_original_S3_restoration_component_payments σ κ A hσ hσsmall
  refine ⟨x0, hx0, ?_⟩
  intro B c0 atom hAdm hc0 hx z k hz hk
  obtain ⟨hd, hs⟩ := hpay B c0 atom hAdm hc0 hx z k hz hk
  unfold restorationCorrection
  have hn := (norm_sub_le
      (actualDiagonal atom (strictReceiverCutoff z) (roughY atom.scale) k -
        actualFirstZero atom (strictReceiverCutoff z) (roughY atom.scale) k)
      (actualSecondZero atom (strictReceiverCutoff z) (roughY atom.scale) k)).trans
    (add_le_add_right (norm_sub_le _ _) _)
  calc
    _ ≤ _ := hn
    _ ≤ actualVScale atom k / Real.log atom.scale ^ A +
        2 * actualVScale atom k / Real.log atom.scale ^ A := by linarith
    _ = _ := by ring

end
end ImbalancedChen.Part3.MediumOriginalRestorationLogPayment20261102
