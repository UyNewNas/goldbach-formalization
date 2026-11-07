import ImbalancedChen.Part3OriginalOwnedS1PolynomialCaps
import ImbalancedChen.Part3MediumReceiverCutoffArithmetic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual finite atlas S1 remainder is paid with one common-m constant,
then one entire d mean per q piece. The original scale is Y=Q1*2^k.d.
The resulting power 38 is fixed, independent of requested log precision.
-/

namespace ImbalancedChen.Part3.OriginalOwnedS1BlockBudget
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalSamePsiS1OwnedAtlas OriginalOwnedS1PolynomialCaps
open OriginalSamePsiS1Remainder OriginalPaperPsiCoprimeCount
open OriginalMediumS1SeparatedDivisorMean OriginalMediumS1WeightedRemainder
open OriginalMediumPhysicalE3Block MediumGlobalDyadicOwnership20261028
open OriginalGevreyPoissonPacket20261028

theorem sourceLog_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ sourceLog x := by
  have hxlog := Real.log_nonneg hx
  have hc := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 256)
  dsimp [sourceLog]
  positivity

private theorem inverse_qScale_le {Q : ℝ} (hQ : 1 ≤ Q) (j : Fin 3) :
    1 / qScale Q j ≤ 2 / Q := by
  have hg := qPiece_geometry hQ j
  calc
    _ ≤ 1 / (Q / 2) := one_div_le_one_div_of_le (by linarith) hg.2.1
    _ = _ := by ring

theorem atlas_kernel_point_le_log_factor {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom)
    (hσ : 0 ≤ σ) (hk : k ∈ keyBank atom z y)
    (j : Fin 3) (d : ℕ) (hd : d ∈ activeD atom k) :
    S1DivisorKernel (atlasBlock atom z y k hA j d hd) ≤
      (32 * atom.U ^ 2 * sourceLog atom.scale ^ 22 / atom.Q1) *
        (tauR d ^ 3 / (d : ℝ) ^ 2) := by
  let B := atlasBlock atom z y k hA j d hd
  obtain ⟨hx, _, _, _, _⟩ :=
    ActualFixedFeatureCountGeometrySourceOnly.actual_admissible_geometry hA hσ
  have hL := sourceLog_nonneg hx
  obtain ⟨hP, hQ, hR, _⟩ := atlas_log_caps atom z y k hA hσ hk j d hd
  have hq0 := (qPiece_geometry hA.2.2.1 j).1
  have hlogQ : 0 ≤ 1 + Real.log (OriginalMediumS1ActualCoefficientBinding.qCap B : ℝ) := by
    have hcap : (1 : ℝ) ≤ OriginalMediumS1ActualCoefficientBinding.qCap B := by
      exact_mod_cast le_max_left 1 B.qHi
    linarith [Real.log_nonneg hcap]
  have hQfactor :
      (1 + Real.log (OriginalMediumS1ActualCoefficientBinding.qCap B : ℝ)) ^ 4 /
        qScale atom.Q1 j ≤ sourceLog atom.scale ^ 4 * (2 / atom.Q1) := by
    calc
      _ ≤ sourceLog atom.scale ^ 4 / qScale atom.Q1 j :=
        div_le_div_of_nonneg_right
          (pow_le_pow_left₀ hlogQ hQ 4) hq0.le
      _ ≤ _ := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left (inverse_qScale_le hA.2.2.1 j) (by positivity)
  have hτ : 0 ≤ tauR d := by dsimp [tauR]; positivity
  have hlogP : 0 ≤ P5Z.RoughSquareWeightedBudget.logBudget
      (OriginalMediumS1ActualCoefficientBinding.physicalCap B) :=
    P5Z.RoughSquareWeightedBudget.logBudget_nonneg _
  have hlogR : 0 ≤ 1 + Real.log (OriginalMediumS1ActualCoefficientBinding.roughCap B : ℝ) := by
    have hcap : (1 : ℝ) ≤ OriginalMediumS1ActualCoefficientBinding.roughCap B := by
      exact_mod_cast le_max_left 1 (Nat.floor (2 * B.roughLength))
    linarith [Real.log_nonneg hcap]
  calc
    _ ≤ 4 * (2 * atom.U) ^ 2 *
        P5Z.RoughSquareWeightedBudget.logBudget
          (OriginalMediumS1ActualCoefficientBinding.physicalCap B) ^ 2 *
        (tauR d ^ 3 / (d : ℝ) ^ 2) *
        ((1 + Real.log (OriginalMediumS1ActualCoefficientBinding.qCap B : ℝ)) ^ 4 /
          qScale atom.Q1 j) *
        (1 + Real.log (OriginalMediumS1ActualCoefficientBinding.roughCap B : ℝ)) ^ 16 :=
      atlasBlock_samePsi_kernel_bound atom z y k hA j d hd
    _ ≤ 4 * (2 * atom.U) ^ 2 * sourceLog atom.scale ^ 2 *
        (tauR d ^ 3 / (d : ℝ) ^ 2) *
        (sourceLog atom.scale ^ 4 * (2 / atom.Q1)) * sourceLog atom.scale ^ 16 := by
      gcongr
    _ = _ := by ring

theorem actual_d_divisor_mean_le_sourceLog {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom)
    (hσ : 0 ≤ σ) (hk : k ∈ keyBank atom z y) :
    (∑ d ∈ activeD atom k, tauR d ^ 3 / (d : ℝ) ^ 2) ≤
      sourceLog atom.scale ^ 16 / keyD k := by
  obtain ⟨hx, _, _, _, _⟩ :=
    ActualFixedFeatureCountGeometrySourceOnly.actual_admissible_geometry hA hσ
  have hL := sourceLog_nonneg hx
  have hDpos : 0 < keyD k := by dsimp [keyD]; positivity
  have hD1 : 1 ≤ keyD k := by
    exact_mod_cast (show 1 ≤ (2 : ℕ) ^ k.d from one_le_pow₀ (by norm_num))
  have hsub : activeD atom k ⊆ Ioc 0 (Nat.floor (2 * keyD k)) := by
    intro d hd
    obtain ⟨hdlo, hdhi⟩ := mem_Ico.mp (mem_filter.mp hd).1
    have hdpos : 0 < d := lt_of_lt_of_le (pow_pos (by norm_num) _) hdlo
    apply mem_Ioc.mpr
    refine ⟨hdpos, Nat.le_floor ?_⟩
    have hdc : (d : ℝ) < ((2 : ℕ) ^ (k.d + 1) : ℕ) := by exact_mod_cast hdhi
    simpa only [keyD, pow_succ, Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hdc.le
  have hlo : ∀ d ∈ activeD atom k, keyD k ≤ (d : ℝ) := by
    intro d hd
    exact_mod_cast (mem_Ico.mp (mem_filter.mp hd).1).1
  have hdmean := sum_tauR_cube_div_square_le_log (activeD atom k)
    (keyD k) (2 * keyD k) hDpos (by linarith) hsub hlo
  by_cases hne : (activeD atom k).Nonempty
  · obtain ⟨d, hd⟩ := hne
    have hlogD := (atlas_log_caps atom z y k hA hσ hk 0 d hd).2.2.2
    have hlogD0 : 0 ≤ 1 + Real.log (2 * keyD k) := by
      linarith [Real.log_nonneg (show 1 ≤ 2 * keyD k by linarith)]
    calc
      _ ≤ (1 / keyD k) * (1 + Real.log (2 * keyD k)) ^ 16 := hdmean
      _ ≤ (1 / keyD k) * sourceLog atom.scale ^ 16 := by
        gcongr
      _ = _ := by ring
  · have hempty : activeD atom k = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp only [hempty, sum_empty]
    positivity

def atlasKernelSum {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom) : ℝ :=
  ∑ j : Fin 3, ∑ d ∈ (activeD atom k).attach,
    S1DivisorKernel (atlasBlock atom z y k hA j d.val d.property)

theorem atlasKernelSum_le_Y {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom)
    (hσ : 0 ≤ σ) (hk : k ∈ keyBank atom z y) :
    atlasKernelSum atom z y k hA ≤
      96 * atom.U ^ 2 * sourceLog atom.scale ^ 38 / keyY atom k := by
  obtain ⟨hx, _, _, _, _⟩ :=
    ActualFixedFeatureCountGeometrySourceOnly.actual_admissible_geometry hA hσ
  have hL := sourceLog_nonneg hx
  have hQ : 0 < atom.Q1 := lt_of_lt_of_le zero_lt_one hA.2.2.1
  let C : ℝ := 32 * atom.U ^ 2 * sourceLog atom.scale ^ 22 / atom.Q1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hj (j : Fin 3) :
      (∑ d ∈ (activeD atom k).attach,
        S1DivisorKernel (atlasBlock atom z y k hA j d.val d.property)) ≤
      C * sourceLog atom.scale ^ 16 / keyD k := by
    calc
      _ ≤ ∑ d ∈ (activeD atom k).attach, C * (tauR d.val ^ 3 / (d.val : ℝ) ^ 2) :=
        sum_le_sum (fun d _ => atlas_kernel_point_le_log_factor atom z y k hA hσ hk j d.val d.property)
      _ = C * ∑ d ∈ activeD atom k, tauR d ^ 3 / (d : ℝ) ^ 2 := by
        rw [← mul_sum]
        simp only [sum_attach]
      _ ≤ C * (sourceLog atom.scale ^ 16 / keyD k) :=
        mul_le_mul_of_nonneg_left (actual_d_divisor_mean_le_sourceLog atom z y k hA hσ hk) hC
      _ = _ := by ring
  calc
    _ ≤ ∑ _j : Fin 3, C * sourceLog atom.scale ^ 16 / keyD k := sum_le_sum (fun j _ => hj j)
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin, Nat.cast_ofNat]
      dsimp [C, keyY]
      ring

def atlasRemainder {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom) : ℂ :=
  ∑ j : Fin 3, ∑ d ∈ (activeD atom k).attach,
    paperS1ActualRemainder (atlasBlock atom z y k hA j d.val d.property)
      (paperPsiNaturalCarrier atom.V) atom.V

def atlasPureS1 {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom) : ℂ :=
  ∑ j : Fin 3, ∑ d ∈ (activeD atom k).attach,
    let B := atlasBlock atom z y k hA j d.val d.property
    ∑ q ∈ B.qCarrier, ∑ r ∈ B.wCarrier, ∑ s ∈ B.wCarrier,
      actualQWeight B q * paperS1PurePair B (paperPsiNaturalCarrier atom.V) atom.V q r s

def atlasMainS1 {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom) : ℂ :=
  ∑ j : Fin 3, ∑ d ∈ (activeD atom k).attach,
    let B := atlasBlock atom z y k hA j d.val d.property
    ∑ q ∈ B.qCarrier, ∑ r ∈ B.wCarrier, ∑ s ∈ B.wCarrier,
      actualQWeight B q * paperS1PrincipalPair B atom.V q r s

theorem atlasPureS1_eq_main_add_remainder {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom) :
    atlasPureS1 atom z y k hA = atlasMainS1 atom z y k hA + atlasRemainder atom z y k hA := by
  unfold atlasPureS1 atlasMainS1 atlasRemainder
  simp_rw [paperS1PurePair_eq_principal_add_remainder, mul_add, sum_add_distrib]
  rfl

/-- An actual coefficient/support instance of the manuscript's S1
ordinary-count remainder, with fixed exponent and exact Y=Q*D. -/
theorem actual_atlas_S1_remainder_le_log_over_Y :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℕ) (σ κ c0 : ℝ)
      (atom : MediumAtom) (z y : ℝ) (k : Key)
      (hA : MediumAdmissible b σ κ c0 atom),
      0 ≤ σ → k ∈ keyBank atom z y →
      ‖atlasRemainder atom z y k hA‖ ≤
        C * atom.U ^ 2 * (1 + Real.log atom.scale) ^ 38 / keyY atom k := by
  obtain ⟨C, hC, hbound⟩ := paperS1ActualRemainder_le_uniform_divisor_kernel
  have hc : 0 < (6 + Real.log (256 : ℝ)) ^ 38 := by
    have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 256)
    positivity
  refine ⟨96 * C * (6 + Real.log (256 : ℝ)) ^ 38, by positivity, ?_⟩
  intro b σ κ c0 atom z y k hA hσ hk
  have hV : 0 < atom.V := lt_of_lt_of_le zero_lt_one hA.2.1
  have hpoint (j : Fin 3) (d : {d // d ∈ activeD atom k}) :
      ‖paperS1ActualRemainder (atlasBlock atom z y k hA j d.val d.property)
        (paperPsiNaturalCarrier atom.V) atom.V‖ ≤
      C * S1DivisorKernel (atlasBlock atom z y k hA j d.val d.property) :=
    hbound _ _ hV _ (fun m hm => paperWeight_support hV hm)
  have hsum : ‖atlasRemainder atom z y k hA‖ ≤ C * atlasKernelSum atom z y k hA := by
    unfold atlasRemainder atlasKernelSum
    calc
      _ ≤ ∑ j : Fin 3, ∑ d ∈ (activeD atom k).attach,
          ‖paperS1ActualRemainder (atlasBlock atom z y k hA j d.val d.property)
            (paperPsiNaturalCarrier atom.V) atom.V‖ := by
        apply (norm_sum_le _ _).trans
        exact sum_le_sum (fun j _ => norm_sum_le _ _)
      _ ≤ C * ∑ j : Fin 3, ∑ d ∈ (activeD atom k).attach,
          S1DivisorKernel (atlasBlock atom z y k hA j d.val d.property) := by
        simp only [mul_sum]
        exact sum_le_sum (fun j _ => sum_le_sum (fun d _ => hpoint j d))
  calc
    _ ≤ C * atlasKernelSum atom z y k hA := hsum
    _ ≤ C * (96 * atom.U ^ 2 * sourceLog atom.scale ^ 38 / keyY atom k) :=
      mul_le_mul_of_nonneg_left (atlasKernelSum_le_Y atom z y k hA hσ hk) hC.le
    _ = _ := by unfold sourceLog; rw [mul_pow]; ring

/-- The original numeric z is unchanged in estimates. Only the discrete
receiver is translated so that original p>z equals receiver p>=cutoff. -/
def originalNumericAtlasRemainder {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom) : ℂ :=
  atlasRemainder atom
    (MediumReceiverCutoffArithmetic20261028.strictReceiverCutoff z) y k hA

theorem original_numeric_atlas_S1_remainder_le_log_over_Y :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℕ) (σ κ c0 : ℝ)
      (atom : MediumAtom) (z y : ℝ) (k : Key)
      (hA : MediumAdmissible b σ κ c0 atom),
      0 ≤ σ →
      k ∈ keyBank atom (MediumReceiverCutoffArithmetic20261028.strictReceiverCutoff z) y →
      ‖originalNumericAtlasRemainder atom z y k hA‖ ≤
        C * atom.U ^ 2 * (1 + Real.log atom.scale) ^ 38 / keyY atom k := by
  obtain ⟨C, hC, hbound⟩ := actual_atlas_S1_remainder_le_log_over_Y
  exact ⟨C, hC, fun b σ κ c0 atom z y k hA hσ hk =>
    hbound b σ κ c0 atom _ y k hA hσ hk⟩

theorem actual_atlas_pureS1_sub_main_le_log_over_Y :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℕ) (σ κ c0 : ℝ)
      (atom : MediumAtom) (z y : ℝ) (k : Key)
      (hA : MediumAdmissible b σ κ c0 atom),
      0 ≤ σ → k ∈ keyBank atom z y →
      ‖atlasPureS1 atom z y k hA - atlasMainS1 atom z y k hA‖ ≤
        C * atom.U ^ 2 * (1 + Real.log atom.scale) ^ 38 / keyY atom k := by
  obtain ⟨C, hC, hbound⟩ := actual_atlas_S1_remainder_le_log_over_Y
  refine ⟨C, hC, ?_⟩
  intro b σ κ c0 atom z y k hA hσ hk
  rw [atlasPureS1_eq_main_add_remainder, add_sub_cancel_left]
  exact hbound b σ κ c0 atom z y k hA hσ hk

end
end ImbalancedChen.Part3.OriginalOwnedS1BlockBudget
