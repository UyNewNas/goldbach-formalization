import ImbalancedChen.Part3ActualMacdonaldPrintedSliceTopology
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Actual inherited-sheet DLMF 10.32.18 on the full printed argument domain
in the SMALL ORDER STRIP |Re(nu)|<1/2. Its endpoint L1, actual parameter
derivatives, and star-connected slice topology have all been supplied.
The supplied genuine quarter-sector E18 is reused, not reproved. A first
identity theorem fixes a positive real second argument. A second uses
an actual positive-real tail accumulating inside the general printed
slice. The product K determination is literally log(z)+log(w)-log(2t)
in the half-log cover, including crossing a negative product cut. Order
zero is the independently constructed derivative model throughout.

This includes every purely imaginary order. Arbitrary complex order
extension and the unrestricted-order printed E18 remain OPEN.
-/

namespace ImbalancedChen.Part3.ActualMacdonaldPrintedSmallOrder20261026b

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ActualKUnequalPositiveShear20261026b (positiveMeasure)
open ActualComplexArgumentKLaplace20261026b
open ActualCutPlaneKOrderZeroRemovable20261026b ActualLogCoverKModel20261026b
open ActualComplexMacdonaldQuarterL120261026b ActualComplexMacdonaldQuarterHolomorphic20261026b
open ActualComplexMacdonaldQuarterIdentity20261026b
open ActualMacdonaldProductDetermination20261026b ActualMacdonaldPositiveProductSheet20261026b
open ActualMacdonaldPrintedCompactL120261026b ActualMacdonaldPrintedHolomorphic20261026b
open ActualMacdonaldPrintedSliceTopology20261026b

theorem cutPlaneKWithZero_eq_actual_small {nu q : ℂ}
    (hL : -(1 / 2 : ℝ) < nu.re) (hU : nu.re < 1 / 2) (hq : 0 < q.re) :
    cutPlaneKWithZero nu q = complexArgumentK nu q := by
  have hqn : q ≠ 0 := by
    intro hq0
    simpa only [hq0, Complex.zero_re, lt_self_iff_false] using hq
  calc
    _ = logCoverK nu (Complex.log (q / 2)) := (logCoverK_principal_half_log nu hqn).symm
    _ = _ := logCoverK_eq_actual_rightHalfPlane_small hL hU hq

/-- Binding the NEW inherited integral to the existing quarter supplier
uses the proved positive-product sheet at every positive t. -/
theorem inheritedMacdonaldValue_eq_quarter_value {nu z w : ℂ}
    (hL : -(1 / 2 : ℝ) < nu.re) (hU : nu.re < 1 / 2)
    (hz : z ∈ strictQuarterSector) (hw : w ∈ strictQuarterSector) :
    inheritedMacdonaldValue nu z w = complexMacdonaldValue nu z w := by
  have hzr := strictQuarterSector_re_pos hz
  have hwr := strictQuarterSector_re_pos hw
  have hzs : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hzr)
  have hws : w ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hwr)
  have hs : 0 < (z + w).re := by simpa only [Complex.add_re] using add_pos hzr hwr
  calc
    _ = (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ), complexMacdonaldKernel nu z w t := by
      unfold inheritedMacdonaldValue
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact inheritedMacdonaldKernel_eq_laplace hL hU hzs hws hs
        (strictQuarterSector_mul_re_pos hz hw) ht
    _ = _ := (complexMacdonaldValue_eq_single nu hz hw).symm

theorem inheritedMacdonaldValue_eq_cut_product_quarter {nu z w : ℂ}
    (hL : -(1 / 2 : ℝ) < nu.re) (hU : nu.re < 1 / 2)
    (hz : z ∈ strictQuarterSector) (hw : w ∈ strictQuarterSector) :
    inheritedMacdonaldValue nu z w = cutPlaneKWithZero nu z * cutPlaneKWithZero nu w := by
  rw [inheritedMacdonaldValue_eq_quarter_value hL hU hz hw,
    complexMacdonaldValue_eq_product nu hz hw,
    cutPlaneKWithZero_eq_actual_small hL hU (strictQuarterSector_re_pos hz),
    cutPlaneKWithZero_eq_actual_small hL hU (strictQuarterSector_re_pos hw)]

theorem cutPlaneKWithZero_analyticOnNhd_printedSlice {nu : ℂ}
    (hL : -1 < nu.re) (hU : nu.re < 1) (w : ℂ) :
    AnalyticOnNhd ℂ (cutPlaneKWithZero nu) (printedMacdonaldSlice w) :=
  (cutPlaneKWithZero_analyticOnNhd hL hU).mono (fun _ hz => hz.1)

/-- First actual continuation step: positive real second argument,
connected printed slice, and proved neighborhood equality in Q. -/
theorem inheritedMacdonaldValue_eq_cut_product_real_right {nu : ℂ} {r : ℝ}
    (horder : |nu.re| < r) (hr : 0 < r) (hrhalf : r < 1 / 2)
    {y : ℝ} (hy : 0 < y) {z : ℂ} (hz : z ∈ printedMacdonaldSlice (y : ℂ)) :
    inheritedMacdonaldValue nu z (y : ℂ) =
      cutPlaneKWithZero nu z * cutPlaneKWithZero nu (y : ℂ) := by
  have hL : -(1 / 2 : ℝ) < nu.re := by have h := (abs_lt.mp horder).1; linarith
  have hU : nu.re < 1 / 2 := by have h := (abs_lt.mp horder).2; linarith
  have hL' : -1 < nu.re := by linarith
  have hU' : nu.re < 1 := by linarith
  have hF := inheritedMacdonaldValue_analyticOnNhd_left horder hr hrhalf (y : ℂ)
  have hG : AnalyticOnNhd ℂ
      (fun x => cutPlaneKWithZero nu x * cutPlaneKWithZero nu (y : ℂ))
      (printedMacdonaldSlice (y : ℂ)) :=
    (cutPlaneKWithZero_analyticOnNhd_printedSlice hL' hU' _).mul analyticOnNhd_const
  have hOne : (1 : ℂ) ∈ strictQuarterSector := positive_real_mem_sector (by norm_num : (0 : ℝ) < 1)
  have hOneSlice : (1 : ℂ) ∈ printedMacdonaldSlice (y : ℂ) :=
    quarter_subset_printed_positive_slice hy hOne
  have hnear : (fun x => inheritedMacdonaldValue nu x (y : ℂ)) =ᶠ[𝓝 (1 : ℂ)]
      (fun x => cutPlaneKWithZero nu x * cutPlaneKWithZero nu (y : ℂ)) := by
    filter_upwards [strictQuarterSector_isOpen.mem_nhds hOne] with x hx
    exact inheritedMacdonaldValue_eq_cut_product_quarter hL hU hx (positive_real_mem_sector hy)
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG
    (printedMacdonaldSlice_isPreconnected (Complex.mem_slitPlane_iff.mpr (Or.inl hy)))
    hOneSlice hnear hz

/-- Second actual identity theorem. The accumulating real points all
belong to the printed slice, even for a fixed left-half-plane argument. -/
theorem inheritedMacdonaldValue_eq_cut_product {nu : ℂ} {r : ℝ}
    (horder : |nu.re| < r) (hr : 0 < r) (hrhalf : r < 1 / 2)
    {z w : ℂ} (h : (z, w) ∈ printedMacdonaldDomain) :
    inheritedMacdonaldValue nu z w = cutPlaneKWithZero nu z * cutPlaneKWithZero nu w := by
  have hL : -1 < nu.re := by have hh := (abs_lt.mp horder).1; linarith
  have hU : nu.re < 1 := by have hh := (abs_lt.mp horder).2; linarith
  have hF := inheritedMacdonaldValue_analyticOnNhd_right horder hr hrhalf z
  have hG : AnalyticOnNhd ℂ (fun x => cutPlaneKWithZero nu z * cutPlaneKWithZero nu x)
      (printedMacdonaldSlice z) :=
    analyticOnNhd_const.mul (cutPlaneKWithZero_analyticOnNhd_printedSlice hL hU z)
  let R : ℝ := printedSliceBase z
  have hRpos : 0 < R := printedSliceBase_pos z
  have hRmem : (R : ℂ) ∈ printedMacdonaldSlice z := printedSliceBase_mem h.1
  let sequence : ℕ → ℂ := fun n => ((R + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_natCast_atTop_atTop.add_const 1).const_div_atTop 1
  have hrealLim : Tendsto (fun n : ℕ => R + 1 / ((n : ℝ) + 1)) atTop (𝓝 R) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => R) atTop (𝓝 R)).add hinv
  have hlim : Tendsto sequence atTop (𝓝 (R : ℂ)) := by
    simpa only [sequence, Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hrealLim
  have hpunctured : Tendsto sequence atTop (𝓝[≠] (R : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hlim, Eventually.of_forall fun n => ?_⟩
    change sequence n ≠ (R : ℂ)
    intro heq
    have hh : R + 1 / ((n : ℝ) + 1) = R :=
      Complex.ofReal_injective (by simpa only [sequence] using heq)
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hseqEq : ∃ᶠ n : ℕ in atTop,
      inheritedMacdonaldValue nu z (sequence n) =
        cutPlaneKWithZero nu z * cutPlaneKWithZero nu (sequence n) := by
    apply Filter.Eventually.frequently
    apply Eventually.of_forall
    intro n
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have htail : |z.im| + |z.re| < R + 1 / ((n : ℝ) + 1) := by
      dsimp [R, printedSliceBase]
      linarith
    have hy : 0 < R + 1 / ((n : ℝ) + 1) := add_pos hRpos hp
    have hslice := positive_real_tail_mem_printedSlice h.1 htail
    exact inheritedMacdonaldValue_eq_cut_product_real_right horder hr hrhalf hy
      (printedMacdonaldDomain_swap hslice)
  exact hF.eqOn_of_preconnected_of_frequently_eq hG (printedMacdonaldSlice_isPreconnected h.1)
    hRmem (hpunctured.frequently hseqEq) (printedMacdonaldDomain_swap h)

/-- Independently proved absolute convergence of the displayed original
t density with its inherited half-log determination, including order zero. -/
theorem actual_K_macdonald_printed_small_integrable {nu z w : ℂ}
    (horder : |nu.re| < 1 / 2) (hz : z ∈ Complex.slitPlane) (hw : w ∈ Complex.slitPlane)
    (hs : |(z + w).im| < (z + w).re) :
    IntegrableOn (fun t =>
      Complex.exp (-(t : ℂ) / 2 - (z ^ 2 + w ^ 2) / (2 * (t : ℂ))) *
        logCoverK nu (Complex.log z + Complex.log w - (Real.log (2 * t) : ℂ)) / (t : ℂ)) (Ioi 0) := by
  obtain ⟨r, hnr, hrhalf⟩ := exists_between horder
  have hr : 0 < r := (abs_nonneg nu.re).trans_lt hnr
  simpa only [determinedProductK, productHalfLog] using
    inherited_macdonald_display_integrable hnr hr hrhalf (show (z, w) ∈ printedMacdonaldDomain from ⟨hz, hw, hs⟩)

/-- Genuine printed-argument-domain E18 for |Re(nu)|<1/2. The product
argument is on its inherited logarithmic sheet, not silently principalized.
The arbitrary-order extension is explicitly not a conclusion. -/
theorem actual_K_macdonald_printed_small {nu z w : ℂ}
    (horder : |nu.re| < 1 / 2) (hz : z ∈ Complex.slitPlane) (hw : w ∈ Complex.slitPlane)
    (hs : |(z + w).im| < (z + w).re) :
    cutPlaneKWithZero nu z * cutPlaneKWithZero nu w =
      (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ),
        Complex.exp (-(t : ℂ) / 2 - (z ^ 2 + w ^ 2) / (2 * (t : ℂ))) *
          logCoverK nu (Complex.log z + Complex.log w - (Real.log (2 * t) : ℂ)) / (t : ℂ) := by
  obtain ⟨r, hnr, hrhalf⟩ := exists_between horder
  have hr : 0 < r := (abs_nonneg nu.re).trans_lt hnr
  have h : (z, w) ∈ printedMacdonaldDomain := ⟨hz, hw, hs⟩
  rw [← inheritedMacdonaldValue_eq_cut_product hnr hr hrhalf h, inheritedMacdonaldValue]
  simp_rw [inheritedMacdonaldKernel_eq_display, determinedProductK, productHalfLog]

end
end ImbalancedChen.Part3.ActualMacdonaldPrintedSmallOrder20261026b
