import ImbalancedChen.Part3OriginalExceptionalPostRemovalPair
import ImbalancedChen.Part3OriginalNativeJInitialRegion

/-!
SOURCE ONLY / UNCOMPILED. On one actual chart, if its level scale is
bounded by a fixed multiple of the common m length, apply the initial
mean to each of the two endpoint-corrected level intervals. The same
phase supplied by the original post-removal pair is used in both.
This does not perform oldform removal or prove the full physical estimate.
-/

noncomputable section
namespace ImbalancedChen.Part3.OriginalBoundedChartPair20261119
open Finset
open scoped BigOperators MatrixGroups Classical
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalTwoZFourierAssembly20261102
open OriginalExceptionalJNativeCompletion20261110 (pascadiJ classicalLevels)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open OriginalNativeJInitialRegion20261113 (initial_region)
open OriginalExceptionalPostRemovalPair20261113
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant sieveConstant_pos)
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly (dyadicScale dyadicScale_pos)
open ImbalancedChen.P3ZExceptionalThresholdGeometry (threshold threshold_pos)
open P3NativePeriod64SamplingSourceOnly (D4)

/-- The physical threshold is in the initial range at both actual level
scales. The constant depends only on the fixed ratio bound B. -/
theorem threshold_initial_range (B Z : ℝ) (hb : 0 ≤ B) (hz : 0 < Z)
    (j : ℕ) (hZ : Z ≤ B * classicalMScale j) :
    let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
    let M := classicalMScale j
    threshold V Z ≤ (2+2*B)*(Z/2+M) ∧
      threshold V Z ≤ (2+2*B)*(Z+M) := by
  let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
  let M := classicalMScale j
  have hm : 0 < M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have hMV : M ≤ V := (classicalMScale_bounds j).2.2
  have hVM : V ≤ 2*M := by
    have h := (classicalMScale_bounds j).2.1
    linarith
  have hv : 0 < V := hm.trans_le hMV
  have hZV : Z ≤ B*V := hZ.trans (mul_le_mul_of_nonneg_left hMV hb)
  have hrat : Z^2/V ≤ B*Z := (div_le_iff₀ hv).mpr (by
    have h := mul_le_mul_of_nonneg_left hZV hz.le
    nlinarith only [h])
  have hfirst : threshold V Z ≤ (2+2*B)*(Z/2+M) := by
    unfold threshold
    apply max_le
    · nlinarith only [hVM, mul_nonneg hb hm.le, mul_nonneg hb hz.le, hz.le]
    · nlinarith only [hrat, mul_nonneg hb hm.le, hm.le, hz.le]
  have ha : 0 ≤ 2+2*B := by nlinarith only [hb]
  have hsecond : (2+2*B)*(Z/2+M) ≤ (2+2*B)*(Z+M) :=
    mul_le_mul_of_nonneg_left (by linarith only [hz]) ha
  exact ⟨hfirst, hfirst.trans hsecond⟩

/-- The real physical slots and weights are unchanged; only the two
full J energies on the right of original_pair_to_pascadi are paid.
No J bound is asserted outside the fixed B chart family. -/
theorem bounded_chart_pair {ε : ℝ} (ep : 0 < ε) (B : ℝ) (hb : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
      (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ),
    let Z := fixedZ D upper
    let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
    let M := classicalMScale j
    let F := mFactor D k upper J j ell
    let G := nFactor D r k upper negativeM ell
    Z ≤ B*M →
    (∑ a : Slots D k upper, F a * G a)^2 ≤
      ((2+Real.log (4*V+1))^2 *
        ((C*((1+Z/2)*(1+M))^ε*(Z/2+M)*M +
          C*((1+Z)*(1+M))^ε*(Z+M)*M)/4)) *
      ((4*sieveConstant*(1+rowLength k/Z))*
        ∑ z : ↥(levels D k upper), rowMass D r k z.val) := by
  have ha : 0 ≤ 2+2*B := by nlinarith only [hb]
  obtain ⟨C, cp, hJ⟩ := initial_region ep (2+2*B) ha
  refine ⟨C, cp, ?_⟩
  intro D r k upper negativeM J j ell
  dsimp only
  intro hZ
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
  let M := classicalMScale j
  let W := threshold V Z
  have hz : 0 < Z := fixedZ_pos D upper
  have hm : 0 < M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have hv : 0 < V := hm.trans_le (classicalMScale_bounds j).2.2
  have hw : 0 < W := threshold_pos hv
  have ranges := threshold_initial_range B Z hb hz j hZ
  obtain ⟨ω, hp, hpair⟩ := original_pair_to_pascadi D r k upper negativeM J j ell
  have h1 := hJ (classicalLevels (Z/2)) j (Z/2) W ω (by linarith only [hz])
    hw (fun _ h => h) ranges.1
  have h2 := hJ (classicalLevels Z) j Z W ω hz hw (fun _ h => h) ranges.2
  have hmass : 0 ≤ ∑ z : ↥(levels D k upper), rowMass D r k z.val := by
    apply Finset.sum_nonneg
    intro z _
    unfold rowMass
    exact Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hL : 0 ≤ rowLength k := div_nonneg (dyadicScale_pos _).le (Nat.cast_nonneg _)
  have hcost : 0 ≤ (4*sieveConstant*(1+rowLength k/Z))*
      ∑ z : ↥(levels D k upper), rowMass D r k z.val := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) sieveConstant_pos.le)
      (by positivity)) hmass
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (add_le_add h1 h2) (by norm_num : (0:ℝ) ≤ 4))
      (sq_nonneg (2+Real.log (4*V+1)))) hcost
  exact hp.trans (hpair.trans hbound)

end ImbalancedChen.Part3.OriginalBoundedChartPair20261119
end
