import ImbalancedChen.Part3OriginalS1KeyMultiplicityPayment
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Insert the already identified ORIGINAL primitive S1 into the preliminary
Cauchy on the retained linear source. All original gamma1/beta L2 weights,
all d in a key, and the second actual key cardinality are retained.
No S2/S3 zero-mode or Gram variance estimate is a premise.
-/

namespace ImbalancedChen.Part3.OriginalS1OuterCauchy20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open MediumActualPreliminaryCauchy20261028 MediumGlobalDyadicOwnership20261028
open MediumPrimitivePsiSource20261028 MediumLiteralS3Stages20261028
open OriginalPrimitiveS1Atlas OriginalS1KeyMultiplicityPayment
open OriginalSamePsiS1OwnedAtlas

def gammaL2 (atom : MediumAtom) : ℝ :=
  ∑ q ∈ factorCarrier atom.Q1, ‖atom.gamma1 q‖ ^ 2

def betaL2 (atom : MediumAtom) : ℝ :=
  ∑ m ∈ atom.betaCarrier, ‖atom.beta m‖ ^ 2

def outerL2 (atom : MediumAtom) (k : Key) : ℝ :=
  ∑ t ∈ outerCarrier atom k, ‖outerCoefficient atom t‖ ^ 2

theorem betaL2_nonneg (atom : MediumAtom) : 0 ≤ betaL2 atom :=
  sum_nonneg (fun _ _ => sq_nonneg _)

theorem outerL2_nonneg (atom : MediumAtom) (k : Key) : 0 ≤ outerL2 atom k :=
  sum_nonneg (fun _ _ => sq_nonneg _)

/-- This is an identity of the actual outer weights, before any length
bound or one-bounded-beta normalization. -/
theorem outerL2_eq_original_factors (atom : MediumAtom) (k : Key) :
    outerL2 atom k = ((dyadicWindow k.d).card : ℝ) * gammaL2 atom * betaL2 atom := by
  unfold outerL2 outerCarrier outerCoefficient
  simp only [sum_product, norm_mul, mul_pow, ← mul_sum, sum_const,
    nsmul_eq_mul, ← sum_mul]
  unfold gammaL2 betaL2
  ring

theorem factorCarrier_card_le_three {Q : ℝ} (hQ : 1 ≤ Q) :
    ((factorCarrier Q).card : ℝ) ≤ 3 * Q := by
  have hsub : factorCarrier Q ⊆ range (Nat.floor (2 * Q) + 1) := by
    intro q hq
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hq).2)
  have hc : ((factorCarrier Q).card : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) + 1 := by
    exact_mod_cast (show (factorCarrier Q).card ≤ Nat.floor (2 * Q) + 1 from
      by simpa only [card_range] using card_le_card hsub)
  have hf : (Nat.floor (2 * Q) : ℝ) ≤ 2 * Q := Nat.floor_le (by linarith)
  linarith

theorem dyadicWindow_card_le_twice (k : Key) :
    ((dyadicWindow k.d).card : ℝ) ≤ 2 * keyD k := by
  have hsub : dyadicWindow k.d ⊆ range (2 ^ (k.d + 1)) := by
    intro d hd
    exact mem_range.mpr (mem_Ico.mp hd).2
  have h := card_le_card hsub
  rw [card_range] at h
  have hcast : ((dyadicWindow k.d).card : ℝ) ≤ ((2 ^ (k.d + 1) : ℕ) : ℝ) :=
    by exact_mod_cast h
  simpa [keyD, pow_succ, Nat.cast_mul, mul_comm] using hcast

theorem outerL2_le_actual_Y_betaL2 {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (k : Key) (hA : MediumAdmissible b σ κ c0 atom) :
    outerL2 atom k ≤ 6 * keyY atom k * betaL2 atom := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hG1, _, _⟩ := hA
  have hg : gammaL2 atom ≤ ((factorCarrier atom.Q1).card : ℝ) := by
    calc
      _ ≤ ∑ _q ∈ factorCarrier atom.Q1, (1 : ℝ) := by
        apply sum_le_sum
        intro q hq
        exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr (hG1 q hq).1
      _ = _ := by simp
  have hd0 : 0 ≤ ((dyadicWindow k.d).card : ℝ) := Nat.cast_nonneg _
  have hq0 : 0 ≤ ((factorCarrier atom.Q1).card : ℝ) := Nat.cast_nonneg _
  rw [outerL2_eq_original_factors]
  calc
    _ ≤ ((dyadicWindow k.d).card : ℝ) * ((factorCarrier atom.Q1).card : ℝ) * betaL2 atom :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hd0) (betaL2_nonneg atom)
    _ ≤ (2 * keyD k) * (3 * atom.Q1) * betaL2 atom :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (dyadicWindow_card_le_twice k)
          (factorCarrier_card_le_three hA.2.2.1) hq0 (by dsimp [keyD]; positivity))
        (betaL2_nonneg atom)
    _ = _ := by unfold keyY; ring

/-- The manuscript's M*Y multiplier, with the fixed original beta
divisor-moment cost, follows from the actual coefficient energy. -/
theorem outerL2_le_original_MY_moment {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (k : Key) (hA : MediumAdmissible b σ κ c0 atom) :
    outerL2 atom k ≤ 12 * atom.V * keyY atom k *
      (1 + Real.log (2 * atom.V)) ^ ((2 ^ b) ^ 2 - 1) := by
  have hY : 0 ≤ keyY atom k := by
    dsimp [keyY, keyD]
    have := hA.2.2.1
    positivity
  calc
    _ ≤ 6 * keyY atom k * betaL2 atom := outerL2_le_actual_Y_betaL2 atom k hA
    _ ≤ 6 * keyY atom k *
        (2 * atom.V * (1 + Real.log (2 * atom.V)) ^ ((2 ^ b) ^ 2 - 1)) :=
      mul_le_mul_of_nonneg_left (mediumAdmissible_beta_norm_sq_sum_le hA) (by positivity)
    _ = _ := by ring

/-- The complete finite outer Cauchy. The key bank is the independent
actual owner image, not a supplied list of hypothetical blocks. -/
theorem retainedSource_norm_sq_le_actual_outer_dispersion
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z y : ℝ)
    (hA : MediumAdmissible b σ κ c0 atom) :
    ‖retainedSource atom z y‖ ^ 2 ≤ ((keyBank atom z y).card : ℝ) *
      ∑ k ∈ keyBank atom z y, outerL2 atom k *
        (primitiveS3 atom z y k - 2 * primitiveS2 atom z y k + primitiveS1 atom z y k) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hG1, _, _⟩ := hA
  rw [retainedSource_eq_sum_blockSource]
  have hc := complex_finset_cauchy_norm_sq (keyBank atom z y)
    (fun _ => (1 : ℂ)) (fun k => blockSource atom z y k)
  have hc' : ‖∑ k ∈ keyBank atom z y, blockSource atom z y k‖ ^ 2 ≤
      ((keyBank atom z y).card : ℝ) * ∑ k ∈ keyBank atom z y,
        ‖blockSource atom z y k‖ ^ 2 := by simpa using hc
  refine hc'.trans (mul_le_mul_of_nonneg_left (sum_le_sum ?_) (Nat.cast_nonneg _))
  intro k hk
  have h := blockSource_norm_sq_le_primitivePsi atom z y k
    (lt_of_lt_of_le zero_lt_one hA.2.2.1) (lt_of_lt_of_le zero_lt_one hA.2.1)
    (fun q hq => (hG1 q hq).2)
  simpa only [outerL2, primitive_dispersion_identity] using h

def atlasPrincipalFunctional {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom) : ℝ :=
  ((keyBank atom z y).card : ℝ) * ∑ k ∈ keyBank atom z y, outerL2 atom k *
    (primitiveS3 atom z y k - 2 * primitiveS2 atom z y k +
      (primitiveAtlasMain atom z y k hA).re)

def actualOuterS1Error {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom) : ℝ :=
  ((keyBank atom z y).card : ℝ) * ∑ k ∈ keyBank atom z y, outerL2 atom k *
    ‖(primitiveS1 atom z y k : ℂ) - primitiveAtlasMain atom z y k hA‖

/-- Insert the original S1, with its already proved same-profile main
term, inside the complete source Cauchy. S2 and S3 are untouched. -/
theorem retainedSource_norm_sq_le_main_add_actual_S1Error
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z y : ℝ)
    (hA : MediumAdmissible b σ κ c0 atom) :
    ‖retainedSource atom z y‖ ^ 2 ≤
      atlasPrincipalFunctional atom z y hA + actualOuterS1Error atom z y hA := by
  apply (retainedSource_norm_sq_le_actual_outer_dispersion atom z y hA).trans
  unfold atlasPrincipalFunctional actualOuterS1Error
  rw [← mul_add, ← sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro k hk
  have hre : primitiveS1 atom z y k - (primitiveAtlasMain atom z y k hA).re ≤
      ‖(primitiveS1 atom z y k : ℂ) - primitiveAtlasMain atom z y k hA‖ := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using Complex.re_le_norm
      ((primitiveS1 atom z y k : ℂ) - primitiveAtlasMain atom z y k hA)
  have hs1 : primitiveS1 atom z y k ≤ (primitiveAtlasMain atom z y k hA).re +
      ‖(primitiveS1 atom z y k : ℂ) - primitiveAtlasMain atom z y k hA‖ := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hs1 (outerL2_nonneg atom k)
  nlinarith

/-- The very same all-key counting remainder of E is now multiplied by
the actual outside beta L2; no beta one-bound is added. -/
theorem actualOuterS1Error_le_betaL2_outerKeyError
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z y : ℝ)
    (hA : MediumAdmissible b σ κ c0 atom) :
    actualOuterS1Error atom z y hA ≤ 6 * betaL2 atom * outerKeyS1Error atom z y hA := by
  unfold actualOuterS1Error outerKeyS1Error weightedS1Error
  calc
    _ ≤ ((keyBank atom z y).card : ℝ) * ∑ k ∈ keyBank atom z y,
        (6 * keyY atom k * betaL2 atom) *
          ‖(primitiveS1 atom z y k : ℂ) - primitiveAtlasMain atom z y k hA‖ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact sum_le_sum (fun k hk => mul_le_mul_of_nonneg_right
        (outerL2_le_actual_Y_betaL2 atom k hA) (norm_nonneg _))
    _ = _ := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro k hk
      ring

end
end ImbalancedChen.Part3.OriginalS1OuterCauchy20261028
