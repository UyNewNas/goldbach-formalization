import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiContinuousLowerFactorSecondInterval
import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965Section13HatSource
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition118SourceIntegralDDE
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option Elab.async false

/-!
# Quadratic tail decay of the actual continuous sieve gap

The gap is the difference of the same canonical continuous factors that occur
in the actual Rosser density limits.  The concrete JR source contract supplies
the source equation and nonnegativity.  Monotonicity of the genuine source
layers gives monotonicity of the gap on `[2,infinity)`.  The weighted source
DDE then makes `s^2 * gap s` antitone on `[3,infinity)`, including its closed
left endpoint by continuity.  No DDE, sign, or decay premise is imposed on
the caller.  These statements do not assert a bound for an entire T3 integral.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- The actual canonical continuous upper-minus-lower factor. -/
def actualSieveGap (s : ℝ) : ℝ :=
  suzukiContinuousUpperFactor s - suzukiContinuousLowerFactor s

/-- The canonical gap equals the genuine Suzuki source on its series domain. -/
theorem actualSieveGap_eq_source {s : ℝ} (hs : 2 ≤ s) :
    actualSieveGap s = suzukiProposition118SourceQ s := by
  simp only [actualSieveGap, suzukiContinuousUpperFactor, suzukiContinuousLowerFactor,
    suzukiContinuousLowerTail, suzukiProposition118SourceQ, if_neg (not_lt.mpr hs)]
  ring

theorem actualSieveGap_nonneg {s : ℝ} (hs : 2 ≤ s) :
    0 ≤ actualSieveGap s := by
  rw [actualSieveGap_eq_source hs]
  obtain ⟨C, hC, hsource⟩ :=
    suzukiProposition118SourceQ_nonneg_and_le_hat jr1965Section13HatSourceContract
  exact (hsource s hs).1

/-- Source-layer monotonicity is retained by both convergent parity sums. -/
theorem antitoneOn_actualSieveGap : AntitoneOn actualSieveGap (Set.Ici 2) := by
  intro x hx y hy hxy
  have hx1 : 1 < x := by change 2 ≤ x at hx; linarith
  have hy1 : 1 < y := hx1.trans_le hxy
  have hodd : suzukiProposition118SourceTPlus y ≤
      suzukiProposition118SourceTPlus x := by
    apply Summable.tsum_le_tsum _
      (summable_suzukiProposition118SourceTPlus_of_sourceContract
        jr1965Section13HatSourceContract hy1)
      (summable_suzukiProposition118SourceTPlus_of_sourceContract
        jr1965Section13HatSourceContract hx1)
    intro k
    exact suzukiLayer_one_antitoneOn_parityDomain (by norm_num) (2 * k + 1)
      (by simp [suzukiParityDomainOne, KappaOneModel.parityDomain]; linarith)
      (by simp [suzukiParityDomainOne, KappaOneModel.parityDomain]; linarith) hxy
  have heven : suzukiProposition118SourceTMinus y ≤
      suzukiProposition118SourceTMinus x := by
    apply Summable.tsum_le_tsum _
      (summable_suzukiProposition118SourceTMinus_of_sourceContract
        jr1965Section13HatSourceContract hy)
      (summable_suzukiProposition118SourceTMinus_of_sourceContract
        jr1965Section13HatSourceContract hx)
    intro k
    exact suzukiLayer_one_antitoneOn_parityDomain (by norm_num) (2 * (k + 1))
      (by simpa [suzukiParityDomainOne, KappaOneModel.parityDomain] using hx)
      (by simpa [suzukiParityDomainOne, KappaOneModel.parityDomain] using hy) hxy
  change (1 + suzukiProposition118SourceTPlus y) -
      (1 - suzukiProposition118SourceTMinus y) ≤
    (1 + suzukiProposition118SourceTPlus x) -
      (1 - suzukiProposition118SourceTMinus x)
  linarith only [hodd, heven]

private theorem hasDerivAt_square_source {s : ℝ} (hs : 3 < s) :
    HasDerivAt (fun t => t ^ 2 * suzukiProposition118SourceQ t)
      (s * (suzukiProposition118SourceQ s - suzukiProposition118SourceQ (s - 1))) s := by
  have hw := hasDerivAt_weighted_suzukiProposition118SourceQ
    jr1965Section13HatSourceContract (by linarith : 2 < s) (by linarith : s ≠ 3)
  have hprod : HasDerivAt (fun t : ℝ => t * (t * suzukiProposition118SourceQ t))
      (s * suzukiProposition118SourceQ s + s * (-suzukiProposition118SourceQ (s - 1)))
      s := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id s).fun_mul hw
  have hfun : (fun t : ℝ => t ^ 2 * suzukiProposition118SourceQ t) =
      (fun t : ℝ => t * (t * suzukiProposition118SourceQ t)) := by
    funext t
    rw [pow_two, mul_assoc]
  have hvalue : s * (suzukiProposition118SourceQ s -
      suzukiProposition118SourceQ (s - 1)) =
      s * suzukiProposition118SourceQ s + s * (-suzukiProposition118SourceQ (s - 1)) := by
    rw [mul_sub, mul_neg, sub_eq_add_neg]
  rw [hfun, hvalue]
  exact hprod

/-- The closed endpoint three is included through genuine source continuity. -/
theorem antitoneOn_square_mul_actualSieveGap :
    AntitoneOn (fun s => s ^ 2 * actualSieveGap s) (Set.Ici 3) := by
  have hcont : ContinuousOn (fun s => s ^ 2 * suzukiProposition118SourceQ s)
      (Set.Ici 3) := by
    intro s hs
    exact ((continuousAt_id.pow 2).mul
      (continuousAt_suzukiProposition118SourceQ_of_two_lt
        jr1965Section13HatSourceContract (by change 3 ≤ s at hs; linarith))).continuousWithinAt
  have hanti : AntitoneOn (fun s => s ^ 2 * suzukiProposition118SourceQ s)
      (Set.Ici 3) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 3) hcont
      (f' := fun s => s *
        (suzukiProposition118SourceQ s - suzukiProposition118SourceQ (s - 1)))
    · intro s hs
      have hs3 : 3 < s := by simpa only [interior_Ici, Set.mem_Ioi] using hs
      exact (hasDerivAt_square_source hs3).hasDerivWithinAt
    · intro s hs
      have hs3 : 3 < s := by simpa only [interior_Ici, Set.mem_Ioi] using hs
      have hle := antitoneOn_actualSieveGap
        (show s - 1 ∈ Set.Ici 2 by simp only [Set.mem_Ici]; linarith)
        (show s ∈ Set.Ici 2 by simp only [Set.mem_Ici]; linarith)
        (by linarith : s - 1 ≤ s)
      rw [actualSieveGap_eq_source (by linarith : 2 ≤ s),
        actualSieveGap_eq_source (by linarith : 2 ≤ s - 1)] at hle
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (sub_nonpos.mpr hle)
  intro x hx y hy hxy
  change y ^ 2 * actualSieveGap y ≤ x ^ 2 * actualSieveGap x
  have hx2 : 2 ≤ x := (by norm_num : (2 : ℝ) ≤ 3).trans hx
  have hy2 : 2 ≤ y := (by norm_num : (2 : ℝ) ≤ 3).trans hy
  rw [actualSieveGap_eq_source (s := y) hy2, actualSieveGap_eq_source (s := x) hx2]
  exact hanti hx hy hxy

/-- Quantitative actual gap decay; the reference point may equal three. -/
theorem actualSieveGap_le_quadratic_tail {s0 s : ℝ}
    (hs0 : 3 ≤ s0) (hs : s0 ≤ s) :
    actualSieveGap s ≤ actualSieveGap s0 * (s0 / s) ^ 2 := by
  have hbound := antitoneOn_square_mul_actualSieveGap hs0 (hs0.trans hs) hs
  have hspos : 0 < s := by linarith
  rw [div_pow, ← mul_div_assoc]
  apply (le_div_iff₀ (sq_pos_of_pos hspos)).2
  calc
    actualSieveGap s * s ^ 2 = s ^ 2 * actualSieveGap s := mul_comm _ _
    _ ≤ s0 ^ 2 * actualSieveGap s0 := hbound
    _ = actualSieveGap s0 * s0 ^ 2 := mul_comm _ _

/-- The same decay after the usual positive amplitude normalization. -/
theorem actualSieveGap_normalized_le_quadratic_tail {s0 s : ℝ}
    (hs0 : 3 ≤ s0) (hs : s0 ≤ s) :
    actualSieveGap s / (2 * Real.exp Real.eulerMascheroniConstant) ≤
      (actualSieveGap s0 / (2 * Real.exp Real.eulerMascheroniConstant)) *
        (s0 / s) ^ 2 := by
  have h := div_le_div_of_nonneg_right (actualSieveGap_le_quadratic_tail hs0 hs)
    (show 0 ≤ 2 * Real.exp Real.eulerMascheroniConstant by positivity)
  calc
    actualSieveGap s / (2 * Real.exp Real.eulerMascheroniConstant) ≤
        (actualSieveGap s0 * (s0 / s) ^ 2) /
          (2 * Real.exp Real.eulerMascheroniConstant) := h
    _ = (actualSieveGap s0 / (2 * Real.exp Real.eulerMascheroniConstant)) *
        (s0 / s) ^ 2 := (div_mul_eq_mul_div _ _ _).symm

end

end ImbalancedChen
