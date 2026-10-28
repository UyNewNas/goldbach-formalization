import ImbalancedChen.Part3OriginalPrimitiveS1Atlas
import ImbalancedChen.Part3TransposedPrimitiveUPayment
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Pay the genuine original keyBank multiplicity, then the actual M length.
The weighted sum retains each original Y_k=Q*D_k. No list of hypothetical
blocks or multiplicity premise replaces the actual finite image bank.
-/

namespace ImbalancedChen.Part3.OriginalS1KeyMultiplicityPayment
noncomputable section
open Classical Finset Filter Topology
open scoped BigOperators
open MediumGlobalDyadicOwnership20261028 OriginalSamePsiS1OwnedAtlas
open OriginalOwnedS1PolynomialCaps OriginalPrimitiveS1Atlas
open OriginalOwnedS1BlockBudget

def keyLogConstant : ℝ := 4 + 2 / Real.log 2

theorem keyLogConstant_pos : 0 < keyLogConstant := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  dsimp [keyLogConstant]
  positivity

theorem actual_keyBank_card_le_log {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom)
    (hσ : 0 ≤ σ) :
    ((keyBank atom z y).card : ℝ) ≤
      keyLogConstant ^ 6 * (1 + Real.log atom.scale) ^ 6 := by
  let N := MediumGlobalDyadicOwnership20261028.physicalCap atom
  obtain ⟨hx, _, _, _, _⟩ :=
    ActualFixedFeatureCountGeometrySourceOnly.actual_admissible_geometry hA hσ
  have hQ2 : 1 ≤ atom.Q2 := hA.2.2.2.1
  have hQ3 : 1 ≤ atom.Q3 := hA.2.2.2.2.1
  have hn2 : 1 ≤ Nat.floor (2 * atom.Q2) := Nat.le_floor (by linarith)
  have hn3 : 1 ≤ Nat.floor (2 * atom.Q3) := Nat.le_floor (by linarith)
  have hNpos : 0 < N := by
    dsimp [N, MediumGlobalDyadicOwnership20261028.physicalCap]
    exact mul_pos (by omega) (by omega)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNcap : (N : ℝ) ≤ 4 * atom.scale ^ 2 := physical_cap_le_four_scale_sq hA hσ
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpow : (2 : ℝ) ^ Nat.log2 N ≤ (N : ℝ) := by
    exact_mod_cast Nat.log2_self_le hNpos.ne'
  have hlogpow := Real.log_le_log (pow_pos (by norm_num) (Nat.log2 N)) hpow
  rw [Real.log_pow] at hlogpow
  have hlogN := Real.log_le_log hNR hNcap
  have hxpos : 0 < atom.scale := lt_of_lt_of_le zero_lt_one hx
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (pow_ne_zero _ hxpos.ne'),
    Real.log_pow] at hlogN
  have hfour : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    ring
  rw [hfour] at hlogN
  have hlogx : 0 ≤ Real.log atom.scale := Real.log_nonneg hx
  have hlogindex : (Nat.log2 N : ℝ) + 1 ≤
      keyLogConstant * (1 + Real.log atom.scale) := by
    have hdiv : (Nat.log2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 :=
      (le_div_iff₀ hlog2).mpr (by nlinarith [hlogpow])
    have hupper : Real.log (N : ℝ) / Real.log 2 ≤
        2 + (2 / Real.log 2) * Real.log atom.scale := by
      apply (div_le_iff₀ hlog2).mpr
      have heq : (2 + (2 / Real.log 2) * Real.log atom.scale) * Real.log 2 =
          2 * Real.log 2 + 2 * Real.log atom.scale := by
        field_simp [hlog2.ne'] <;> ring
      rw [heq]
      exact hlogN
    have hfrac : 0 ≤ 2 / Real.log (2 : ℝ) := by positivity
    dsimp [keyLogConstant]
    nlinarith [mul_nonneg hfrac hlogx]
  calc
    _ ≤ (((Nat.log2 N + 1 : ℕ) : ℝ)) ^ 6 := by
      exact_mod_cast keyBank_card_le atom z y
    _ ≤ (keyLogConstant * (1 + Real.log atom.scale)) ^ 6 := by
      push_cast
      exact pow_le_pow_left₀ (by positivity) hlogindex 6
    _ = _ := mul_pow _ _ _

def weightedS1Error {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom) : ℝ :=
  ∑ k ∈ keyBank atom z y, keyY atom k *
    ‖(MediumLiteralS3Stages20261028.primitiveS1 atom z y k : ℂ) -
      primitiveAtlasMain atom z y k hA‖

/-- Every actual key is counted, with its genuine Y_k left in the sum. -/
theorem actual_weighted_S1Error_le_log44 :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℕ) (σ κ c0 : ℝ)
      (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom),
      0 ≤ σ → weightedS1Error atom z y hA ≤
        C * atom.U ^ 2 * (1 + Real.log atom.scale) ^ 44 := by
  obtain ⟨C, hC, hbound⟩ := original_primitiveS1_sub_main_le_log_over_Y
  have hK : 0 < keyLogConstant ^ 6 := pow_pos keyLogConstant_pos _
  refine ⟨C * keyLogConstant ^ 6, by positivity, ?_⟩
  intro b σ κ c0 atom z y hA hσ
  obtain ⟨hx, _, _, _, _⟩ :=
    ActualFixedFeatureCountGeometrySourceOnly.actual_admissible_geometry hA hσ
  have hlogx : 0 ≤ 1 + Real.log atom.scale := by linarith [Real.log_nonneg hx]
  have hterm (k : Key) (hk : k ∈ keyBank atom z y) :
      keyY atom k *
        ‖(MediumLiteralS3Stages20261028.primitiveS1 atom z y k : ℂ) -
          primitiveAtlasMain atom z y k hA‖ ≤
      C * atom.U ^ 2 * (1 + Real.log atom.scale) ^ 38 := by
    have hY : 0 < keyY atom k := by
      dsimp [keyY, keyD]
      exact mul_pos (lt_of_lt_of_le zero_lt_one hA.2.2.1) (by positivity)
    have h := mul_le_mul_of_nonneg_left
      (hbound b σ κ c0 atom z y k hA hσ hk) hY.le
    have hcancel : keyY atom k *
        (C * atom.U ^ 2 * (1 + Real.log atom.scale) ^ 38 / keyY atom k) =
          C * atom.U ^ 2 * (1 + Real.log atom.scale) ^ 38 := by
      field_simp [hY.ne'] <;> ring
    simpa only [hcancel] using h
  unfold weightedS1Error
  calc
    _ ≤ ∑ _k ∈ keyBank atom z y, C * atom.U ^ 2 * (1 + Real.log atom.scale) ^ 38 :=
      sum_le_sum hterm
    _ = ((keyBank atom z y).card : ℝ) *
        (C * atom.U ^ 2 * (1 + Real.log atom.scale) ^ 38) := by simp
    _ ≤ (keyLogConstant ^ 6 * (1 + Real.log atom.scale) ^ 6) *
        (C * atom.U ^ 2 * (1 + Real.log atom.scale) ^ 38) :=
      mul_le_mul_of_nonneg_right (actual_keyBank_card_le_log atom z y hA hσ) (by positivity)
    _ = _ := by ring

/-- The original restricted-medium monomial supplies the actual M
power margin. This is derived from the existing U<=x^(1/2) theorem. -/
theorem actual_M_lower_half {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (hσ : 0 < σ) :
    atom.scale ^ (1 / 2 : ℝ) ≤ atom.V := by
  have hx : 0 ≤ atom.scale := zero_le_one.trans (TransposedPrimitiveUPayment.one_le_scale hA)
  have hxpos : 0 < atom.scale := lt_of_lt_of_le zero_lt_one
    (TransposedPrimitiveUPayment.one_le_scale hA)
  have hroot : 0 < atom.scale ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hxpos _
  have hsq : (atom.scale ^ (1 / 2 : ℝ)) ^ 2 = atom.scale := by
    simpa using Real.rpow_inv_natCast_pow (n := 2) hx (by norm_num : (2 : ℕ) ≠ 0)
  apply (mul_le_mul_left hroot).mp
  calc
    _ = atom.scale := by rw [← pow_two, hsq]
    _ = atom.U * atom.V := rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (TransposedPrimitiveUPayment.U_le_scale_half hσ hA) (zero_le_one.trans hA.2.1)

/-- One threshold precedes every atom, original z/y and actual key.
The genuine key multiplicity is included before the M power margin is
spent, giving the original arbitrary-logarithmic S1 counting payment. -/
theorem actual_weighted_S1Error_log_payment (A : ℝ) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (b : ℕ) (σ κ c0 : ℝ)
      (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom),
      0 < σ → x0 ≤ atom.scale →
      weightedS1Error atom z y hA ≤
        atom.V * atom.U ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨C, hC, hbound⟩ := actual_weighted_S1Error_le_log44
  let E : ℝ := C * (2 : ℝ) ^ 44
  have hE : 0 ≤ E := by dsimp [E]; positivity
  obtain ⟨x1, hx1⟩ := eventually_atTop.mp
    (TransposedPrimitiveUPayment.eventually_const_log_rpow_le_rpow E (A + 44) hE
      (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨x2, hx2⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ))
  refine ⟨max 2 (max x1 x2), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro b σ κ c0 atom z y hA hσ hx
  have hlog : 1 ≤ Real.log atom.scale := hx2 atom.scale
    ((le_max_right x1 x2).trans ((le_max_right 2 (max x1 x2)).trans hx))
  have hlog0 : 0 < Real.log atom.scale := by linarith
  have hpoly : E * Real.log atom.scale ^ (A + 44) ≤ atom.V :=
    (hx1 atom.scale ((le_max_left x1 x2).trans
      ((le_max_right 2 (max x1 x2)).trans hx))).trans (actual_M_lower_half hA hσ)
  have hpay : E * (Real.log atom.scale) ^ (44 : ℕ) ≤
      atom.V / Real.log atom.scale ^ A := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hlog0 A)).mpr
    calc
      _ = E * Real.log atom.scale ^ (A + 44) := by
        rw [Real.rpow_add hlog0, Real.rpow_natCast]
        ring
      _ ≤ _ := hpoly
  calc
    _ ≤ C * atom.U ^ 2 * (1 + Real.log atom.scale) ^ 44 :=
      hbound b σ κ c0 atom z y hA hσ.le
    _ ≤ C * atom.U ^ 2 * (2 * Real.log atom.scale) ^ 44 := by
      gcongr
      linarith
    _ = atom.U ^ 2 * (E * Real.log atom.scale ^ (44 : ℕ)) := by dsimp [E]; ring
    _ ≤ atom.U ^ 2 * (atom.V / Real.log atom.scale ^ A) :=
      mul_le_mul_of_nonneg_left hpay (sq_nonneg _)
    _ = _ := by ring

/-- Include the additional actual key-cardinality factor from outer
finite Cauchy before comparing the retained source with its block sum. -/
def outerKeyS1Error {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom) : ℝ :=
  ((keyBank atom z y).card : ℝ) * weightedS1Error atom z y hA

theorem actual_outerKeyS1Error_le_log50 :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℕ) (σ κ c0 : ℝ)
      (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom),
      0 ≤ σ → outerKeyS1Error atom z y hA ≤
        C * atom.U ^ 2 * (1 + Real.log atom.scale) ^ 50 := by
  obtain ⟨C, hC, hbound⟩ := actual_weighted_S1Error_le_log44
  have hK : 0 < keyLogConstant ^ 6 := pow_pos keyLogConstant_pos _
  refine ⟨C * keyLogConstant ^ 6, by positivity, ?_⟩
  intro b σ κ c0 atom z y hA hσ
  obtain ⟨hx, _, _, _, _⟩ :=
    ActualFixedFeatureCountGeometrySourceOnly.actual_admissible_geometry hA hσ
  have hlog : 0 ≤ 1 + Real.log atom.scale := by linarith [Real.log_nonneg hx]
  have hcount : 0 ≤ ((keyBank atom z y).card : ℝ) := Nat.cast_nonneg _
  unfold outerKeyS1Error
  calc
    _ ≤ ((keyBank atom z y).card : ℝ) *
        (C * atom.U ^ 2 * (1 + Real.log atom.scale) ^ 44) :=
      mul_le_mul_of_nonneg_left (hbound b σ κ c0 atom z y hA hσ) hcount
    _ ≤ (keyLogConstant ^ 6 * (1 + Real.log atom.scale) ^ 6) *
        (C * atom.U ^ 2 * (1 + Real.log atom.scale) ^ 44) :=
      mul_le_mul_of_nonneg_right (actual_keyBank_card_le_log atom z y hA hσ) (by positivity)
    _ = _ := by ring

theorem actual_outerKeyS1Error_log_payment (A : ℝ) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (b : ℕ) (σ κ c0 : ℝ)
      (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom),
      0 < σ → x0 ≤ atom.scale →
      outerKeyS1Error atom z y hA ≤
        atom.V * atom.U ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨C, hC, hbound⟩ := actual_outerKeyS1Error_le_log50
  let E : ℝ := C * (2 : ℝ) ^ 50
  have hE : 0 ≤ E := by dsimp [E]; positivity
  obtain ⟨x1, hx1⟩ := eventually_atTop.mp
    (TransposedPrimitiveUPayment.eventually_const_log_rpow_le_rpow E (A + 50) hE
      (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨x2, hx2⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ))
  refine ⟨max 2 (max x1 x2), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro b σ κ c0 atom z y hA hσ hx
  have hlog : 1 ≤ Real.log atom.scale := hx2 atom.scale
    ((le_max_right x1 x2).trans ((le_max_right 2 (max x1 x2)).trans hx))
  have hlog0 : 0 < Real.log atom.scale := by linarith
  have hpoly : E * Real.log atom.scale ^ (A + 50) ≤ atom.V :=
    (hx1 atom.scale ((le_max_left x1 x2).trans
      ((le_max_right 2 (max x1 x2)).trans hx))).trans (actual_M_lower_half hA hσ)
  have hpay : E * (Real.log atom.scale) ^ (50 : ℕ) ≤
      atom.V / Real.log atom.scale ^ A := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hlog0 A)).mpr
    calc
      _ = E * Real.log atom.scale ^ (A + 50) := by
        rw [Real.rpow_add hlog0, Real.rpow_natCast]
        ring
      _ ≤ _ := hpoly
  calc
    _ ≤ C * atom.U ^ 2 * (1 + Real.log atom.scale) ^ 50 :=
      hbound b σ κ c0 atom z y hA hσ.le
    _ ≤ C * atom.U ^ 2 * (2 * Real.log atom.scale) ^ 50 := by gcongr; linarith
    _ = atom.U ^ 2 * (E * Real.log atom.scale ^ (50 : ℕ)) := by dsimp [E]; ring
    _ ≤ atom.U ^ 2 * (atom.V / Real.log atom.scale ^ A) :=
      mul_le_mul_of_nonneg_left hpay (sq_nonneg _)
    _ = _ := by ring

/-- For the original numeric z, use the proved discrete receiver map;
the analytic z in the manuscript is not replaced in any estimate. -/
def originalNumericWeightedS1Error {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom) : ℝ :=
  weightedS1Error atom (MediumReceiverCutoffArithmetic20261028.strictReceiverCutoff z) y hA

theorem original_numeric_weighted_S1Error_log_payment (A : ℝ) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (b : ℕ) (σ κ c0 : ℝ)
      (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom),
      0 < σ → x0 ≤ atom.scale →
      originalNumericWeightedS1Error atom z y hA ≤
        atom.V * atom.U ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨x0, hx0, hbound⟩ := actual_weighted_S1Error_log_payment A
  exact ⟨x0, hx0, fun b σ κ c0 atom z y hA hσ hx =>
    hbound b σ κ c0 atom _ y hA hσ hx⟩

end
end ImbalancedChen.Part3.OriginalS1KeyMultiplicityPayment
