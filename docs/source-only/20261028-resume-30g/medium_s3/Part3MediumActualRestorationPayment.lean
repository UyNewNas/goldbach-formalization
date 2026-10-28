import ImbalancedChen.Part3MediumActualDiagonalDivisorPayment
import ImbalancedChen.Part3OriginalActualSingleZeroPayment
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Single-zero estimates are consumed ONE WAY from the independent G S2
producer. This file does not repeat its counting proof. The actual
occupied keyBank and original smooth trim supply the preliminary (9)
geometry. The resulting payment concerns the true deleted diagonal and
the two single zeros in E's literal S3 restoration identity. Rough-gcd,
coefficient cutoffs, close pairs and genuine Fourier diagonal corrections
are separate obligations, not hidden in this correction's definition.
-/
namespace ImbalancedChen.Part3.MediumActualRestorationPayment20261028
noncomputable section
open Classical Finset Filter
open scoped BigOperators
open MediumActualDiagonalDivisorPayment20261028
open MediumLiteralS3Stages20261028 MediumLiteralS3Deleted20261028
open MediumActualPreliminaryCauchy20261028 MediumPrimitivePsiSource20261028
open MediumGlobalDyadicOwnership20261028 MediumCanonicalFixedBlock20261028
open MediumReceiverCutoffArithmetic20261028 OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3OriginalActualSingleZeroSource
open ImbalancedChen.Part3OriginalActualSingleZeroCounting
open ImbalancedChen.Part3OriginalActualSingleZeroPayment
open ImbalancedChen.Part3OriginalS2NativePhysicalRange
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding

theorem occupied_keyD_le_trim_sq {atom : MediumAtom} {z y : ℝ} {k : Key}
    (hy : 0 ≤ y) (hk : k ∈ keyBank atom z y) : keyD k ≤ y ^ 2 := by
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hk
  obtain ⟨_, hret⟩ := mem_filter.mp hq
  have hwin := ((owner_eq_iff_windows z q (owner z q)).mp rfl).2.2.2.2.1
  have hlow : ((2 : ℕ) ^ (owner z q).d : ℝ) ≤ (actualD z q : ℝ) := by
    exact_mod_cast (mem_Ico.mp hwin).1
  have hprod : (actualD z q : ℝ) ≤ y * y := by
    change ((smoothPart z q.1 * smoothPart z q.2 : ℕ) : ℝ) ≤ y * y
    rw [Nat.cast_mul]
    exact mul_le_mul hret.2.2.1 hret.2.2.2 (Nat.cast_nonneg _) hy
  exact hlow.trans (by simpa only [pow_two] using hprod)

/-- Ownership controls D*R by the original Q2,Q3 physical product,
including every prime-power multiplicity and every half-open boundary. -/
theorem occupied_keyDR_le_physical {atom : MediumAtom} {z y : ℝ} {k : Key}
    (hQ2 : 0 ≤ atom.Q2) (hQ3 : 0 ≤ atom.Q3)
    (hk : k ∈ keyBank atom z y) : keyD k * keyR k ≤ 4 * atom.Q2 * atom.Q3 := by
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hk
  obtain ⟨hphysical, hret⟩ := mem_filter.mp hq
  have hwin := (owner_eq_iff_windows z q (owner z q)).mp rfl
  have hD : keyD (owner z q) ≤ (actualD z q : ℝ) := by
    exact_mod_cast (mem_Ico.mp hwin.2.2.2.2.1).1
  have hR : keyR (owner z q) ≤ (actualW z q : ℝ) := by
    exact_mod_cast (mem_Ico.mp hwin.2.2.2.2.2).1
  have hsplit : actualD z q * actualW z q = q.1 * q.2 := by
    unfold actualD actualW canonicalFactor
    change (smoothPart z q.1 * smoothPart z q.2) *
      (roughPart z q.1 * roughPart z q.2) = q.1 * q.2
    calc
      _ = (smoothPart z q.1 * roughPart z q.1) *
          (smoothPart z q.2 * roughPart z q.2) := by ring
      _ = _ := by rw [smooth_mul_rough z hret.1, smooth_mul_rough z hret.2.1]
  have hq2 : (q.1 : ℝ) ≤ 2 * atom.Q2 :=
    (show (q.1 : ℝ) ≤ (Nat.floor (2 * atom.Q2) : ℝ) by
      exact_mod_cast (mem_Icc.mp (mem_product.mp hphysical).1).2).trans
        (Nat.floor_le (by linarith))
  have hq3 : (q.2 : ℝ) ≤ 2 * atom.Q3 :=
    (show (q.2 : ℝ) ≤ (Nat.floor (2 * atom.Q3) : ℝ) by
      exact_mod_cast (mem_Icc.mp (mem_product.mp hphysical).2).2).trans
        (Nat.floor_le (by linarith))
  calc
    _ ≤ (actualD z q : ℝ) * (actualW z q : ℝ) :=
      mul_le_mul hD hR (by unfold keyR; positivity) (Nat.cast_nonneg _)
    _ = (q.1 : ℝ) * q.2 := by exact_mod_cast hsplit
    _ ≤ (2 * atom.Q2) * (2 * atom.Q3) :=
      mul_le_mul hq2 hq3 (Nat.cast_nonneg _) (by linarith [hq2, Nat.cast_nonneg q.1])
    _ = _ := by ring

/-- The (9) geometry is instantiated on actual occupied keys, rather
than retained as a free hypothesis of the final original-source caller. -/
theorem exists_original_occupied_key_geometry (σ : ℝ) (hσ : 0 < σ)
    (hσsmall : σ < 1 / 100) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (κ c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
      ∀ (receiver : ℝ) (k : Key), k ∈ keyBank atom receiver (roughY atom.scale) →
      keyY atom k ≤ atom.U * atom.scale ^ (-(σ / 2)) ∧
      keyY atom k * keyR k ≤ atom.scale ^ (1 - σ / 2) := by
  obtain ⟨x1, hx1⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (4 / σ))
  obtain ⟨x2, hx2⟩ := eventually_atTop.mp
    (TransposedPrimitiveUPayment.eventually_const_log_rpow_le_rpow 4 0 (by norm_num)
      (show 0 < (1 : ℝ) / 10 by norm_num))
  refine ⟨max 2 (max x1 x2), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro B κ c0 atom hA hc0 hx receiver k hk
  have hxpos : 0 < atom.scale := by unfold MediumAtom.scale; nlinarith [hA.1, hA.2.1]
  have hxone : 1 ≤ atom.scale := by linarith [(le_max_left 2 (max x1 x2)).trans hx]
  have hll : 4 / σ ≤ Real.log (Real.log atom.scale) := hx1 _
    ((le_max_left x1 x2).trans ((le_max_right 2 (max x1 x2)).trans hx))
  have hllpos : 0 < Real.log (Real.log atom.scale) := (div_pos (by norm_num) hσ).trans_le hll
  have htwolog : 2 / Real.log (Real.log atom.scale) ≤ σ / 2 := by
    apply (div_le_iff₀ hllpos).mpr
    have hh := mul_le_mul_of_nonneg_left hll (show 0 ≤ σ / 2 by positivity)
    have heq : (σ / 2) * (4 / σ) = (2 : ℝ) := by field_simp [hσ.ne']; ring
    rw [heq] at hh
    exact hh
  have hy : 0 < roughY atom.scale := Real.rpow_pos_of_pos hxpos _
  have hy2 : roughY atom.scale ^ 2 ≤ atom.scale ^ (σ / 2) := by
    unfold roughY
    rw [← Real.rpow_mul_natCast hxpos.le]
    apply Real.rpow_le_rpow_of_exponent_le hxone
    norm_num
    convert htwolog using 1 <;> ring
  constructor
  · calc
      keyY atom k ≤ atom.Q1 * roughY atom.scale ^ 2 :=
        mul_le_mul_of_nonneg_left (occupied_keyD_le_trim_sq hy.le hk) (by linarith [hA.2.2.1])
      _ ≤ atom.Q1 * atom.scale ^ (σ / 2) :=
        mul_le_mul_of_nonneg_left hy2 (by linarith [hA.2.2.1])
      _ ≤ (atom.U * atom.scale ^ (-σ)) * atom.scale ^ (σ / 2) :=
        mul_le_mul_of_nonneg_right hA.2.2.2.2.2.2.2.2.1.le (Real.rpow_nonneg hxpos.le _)
      _ = atom.U * atom.scale ^ (-(σ / 2)) := by
        rw [mul_assoc, ← Real.rpow_add hxpos]
        congr 1
        ring
  · have hprod := Q1Q2Q3_lt_scale_seven_tenths hA hσ.le (residue_ne_zero_of_original_c0 hA hc0)
    have hfour : (4 : ℝ) ≤ atom.scale ^ ((1 : ℝ) / 10) := by
      simpa only [Real.rpow_zero, mul_one] using hx2 atom.scale
        ((le_max_right x1 x2).trans ((le_max_right 2 (max x1 x2)).trans hx))
    calc
      keyY atom k * keyR k = atom.Q1 * (keyD k * keyR k) := by unfold keyY; ring
      _ ≤ atom.Q1 * (4 * atom.Q2 * atom.Q3) :=
        mul_le_mul_of_nonneg_left (occupied_keyDR_le_physical
          (by linarith [hA.2.2.2.1]) (by linarith [hA.2.2.2.2.1]) hk)
          (by linarith [hA.2.2.1])
      _ ≤ 4 * atom.scale ^ ((7 : ℝ) / 10) := by nlinarith
      _ ≤ atom.scale ^ ((1 : ℝ) / 10) * atom.scale ^ ((7 : ℝ) / 10) :=
        mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg hxpos.le _)
      _ = atom.scale ^ ((4 : ℝ) / 5) := by rw [← Real.rpow_add hxpos]; norm_num
      _ ≤ atom.scale ^ (1 - σ / 2) :=
        Real.rpow_le_rpow_of_exponent_le hxone (by linarith)

def restoredOffDiagonal (atom : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ t ∈ offDiagonalCarrier atom k, S3FullTerm atom z y k t

def restorationCorrection (atom : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  actualDiagonal atom z y k - actualFirstZero atom z y k - actualSecondZero atom z y k

theorem actual_S3_restoration_identity (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hM : 0 < atom.V) :
    (primitiveS3 atom z y k : ℂ) =
      restoredOffDiagonal atom z y k + restorationCorrection atom z y k := by
  have hD := S3_exact_diagonal_offDiagonal atom z y k
  have hR := offDiagonal_restore_identity atom z y k hM
  unfold restoredOffDiagonal restorationCorrection actualDiagonal actualFirstZero actualSecondZero
  linear_combination hD - hR

theorem actual_S123_restoration_identity (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hM : 0 < atom.V) :
    primitiveQuadratic atom z y k = primitiveS1 atom z y k - 2 * primitiveS2 atom z y k +
      (restoredOffDiagonal atom z y k).re + (restorationCorrection atom z y k).re := by
  have h := congrArg Complex.re (actual_S3_restoration_identity atom z y k hM)
  simp only [Complex.ofReal_re, Complex.add_re] at h
  rw [primitive_dispersion_identity, h]
  ring

theorem singleZeros_scale_geometry {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) {δ : ℝ} (hδ : 0 < δ) (k : Key)
    (hY : keyY atom k ≤ atom.U * atom.scale ^ (-δ))
    (hYR : keyY atom k * keyR k ≤ atom.scale ^ (1 - δ)) :
    atom.scale ^ δ * (singleZeroR k * (atom.U + singleZeroY atom k)) ≤
      2 * actualVScale atom k := by
  have hxone : 1 ≤ atom.scale := by unfold MediumAtom.scale; nlinarith [hA.1, hA.2.1]
  have hxpos : 0 < atom.scale := lt_of_lt_of_le zero_lt_one hxone
  have hYeq : singleZeroY atom k = keyY atom k := by simp [singleZeroY, keyY, keyD]
  have hReq : singleZeroR k = keyR k := by simp [singleZeroR, keyR]
  have hsmall : atom.scale ^ (-δ) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hxone (show -δ ≤ (0 : ℝ) by linarith)
  have hYU : keyY atom k ≤ atom.U := hY.trans (by nlinarith [hA.1])
  have hRU : atom.scale ^ δ * (keyR k * atom.U) ≤ actualVScale atom k := by
    apply (le_div_iff₀ (keyY_positive hA k)).mpr
    calc
      _ = atom.U * (atom.scale ^ δ * (keyY atom k * keyR k)) := by ring
      _ ≤ atom.U * (atom.scale ^ δ * atom.scale ^ (1 - δ)) := by
        gcongr
      _ = atom.V * atom.U ^ 2 := by
        rw [← Real.rpow_add hxpos, show δ + (1 - δ) = (1 : ℝ) by ring, Real.rpow_one]
        unfold MediumAtom.scale
        ring
  rw [hYeq, hReq]
  calc
    _ ≤ atom.scale ^ δ * (keyR k * (atom.U + atom.U)) := by
      gcongr
    _ = 2 * (atom.scale ^ δ * (keyR k * atom.U)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hRU (by norm_num)

end
end ImbalancedChen.Part3.MediumActualRestorationPayment20261028
