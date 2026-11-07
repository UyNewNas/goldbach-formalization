import ImbalancedChen.Part3ActualComplexMacdonaldCombinedHolomorphic
import ImbalancedChen.Part3ActualComplexMacdonaldQuarterIdentity
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Actual Macdonald E18 and absolute convergence on the broader domain
Re(z)>0, Re(w)>0, Re(z*w)>0, |Im(z+w)|<Re(z+w).
Its one-variable slices are proved convex intersections of half-planes.
The first identity theorem extends the already supplied quarter-sector
identity with a positive real second argument. For fixed general z, a
genuine positive-real sequence in the second slice accumulates at an
interior positive real point, giving the second identity theorem.
The actual jointly L1 integral is then bound by Fubini to the literal
single K(z*w/t) kernel. No continuation identity is assumed, and no
claim is made for the printed sector allowing left-half-plane arguments.
-/

namespace ImbalancedChen.Part3.ActualComplexMacdonaldCombinedIdentity20261026b

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
open ActualKUnequalPositiveShear20261026b (positiveMeasure)
open ActualComplexArgumentKLaplace20261026b ActualComplexArgumentKHolomorphic20261026b
open ActualComplexMacdonaldQuarterL120261026b
open ActualComplexMacdonaldQuarterHolomorphic20261026b
open ActualComplexMacdonaldQuarterIdentity20261026b
open ActualComplexMacdonaldCombinedL120261026b
open ActualComplexMacdonaldCombinedHolomorphic20261026b

theorem combinedMacdonaldDomain_of_quarter {z w : ℂ}
    (hz : z ∈ strictQuarterSector) (hw : w ∈ strictQuarterSector) :
    (z, w) ∈ combinedMacdonaldDomain := by
  refine ⟨strictQuarterSector_re_pos hz, strictQuarterSector_re_pos hw,
    strictQuarterSector_mul_re_pos hz hw, ?_⟩
  change |(z + w).im| < (z + w).re
  simpa only [Complex.add_im, Complex.add_re] using
    (abs_add z.im w.im).trans_lt (add_lt_add hz hw)

/-- All varying-argument restrictions are real-linear strict half-plane
inequalities after the other argument is fixed. This proves connectedness
of the actual domain used by the identity theorem. -/
theorem combinedMacdonaldSlice_convex (w : ℂ) : Convex ℝ (combinedMacdonaldSlice w) := by
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
  have hcombine : ∀ x y : ℝ, 0 < x → 0 < y → 0 < a * x + b * y := by
    intro x y hx hy
    rcases eq_or_lt_of_le ha with (rfl | hap)
    · have hb1 : b = 1 := by linarith
      simpa only [zero_mul, zero_add, hb1, one_mul] using hy
    · have hp := mul_pos hap hx
      have hn := mul_nonneg hb hy.le
      linarith
  refine ⟨?_, hz₁.2.1, ?_, ?_⟩
  · change 0 < (a • z₁ + b • z₂).re
    simpa only [Complex.add_re, Complex.smul_re] using hcombine _ _ hz₁.1 hz₂.1
  · have he : ((a • z₁ + b • z₂) * w).re =
        a * (z₁ * w).re + b * (z₂ * w).re := by
      simp only [Complex.mul_re, Complex.add_re, Complex.add_im,
        Complex.smul_re, Complex.smul_im]
      ring
    change 0 < ((a • z₁ + b • z₂) * w).re
    rw [he]
    exact hcombine _ _ hz₁.2.2.1 hz₂.2.2.1
  · have hw : a • w + b • w = w := by rw [← add_smul, hab, one_smul]
    have he : (a • z₁ + b • z₂) + w = a • (z₁ + w) + b • (z₂ + w) := by
      rw [smul_add, smul_add]
      calc
        _ = (a • z₁ + b • z₂) + (a • w + b • w) := by rw [hw]
        _ = _ := by abel
    change (a • z₁ + b • z₂) + w ∈ strictQuarterSector
    rw [he]
    exact strictQuarterSector_convex hz₁.2.2.2 hz₂.2.2.2 ha hb hab

theorem quarter_subset_combined_real_slice {y : ℝ} (hy : 0 < y) :
    strictQuarterSector ⊆ combinedMacdonaldSlice (y : ℂ) :=
  fun _ hz => combinedMacdonaldDomain_of_quarter hz (positive_real_mem_sector hy)

/-- A genuine first identity-theorem application on the entire combined
slice. Its neighborhood equality is supplied by the proved quarter
identity, and its connected domain is proved above. -/
theorem complexMacdonaldValue_eq_product_real_right_combined (nu : ℂ) {y : ℝ}
    (hy : 0 < y) {z : ℂ} (hz : z ∈ combinedMacdonaldSlice (y : ℂ)) :
    complexMacdonaldValue nu z (y : ℂ) =
      complexArgumentK nu z * complexArgumentK nu (y : ℂ) := by
  have hF := complexMacdonaldValue_analyticOnNhd_left_combined nu (y : ℂ)
  have hK : AnalyticOnNhd ℂ (complexArgumentK nu) (combinedMacdonaldSlice (y : ℂ)) :=
    (complexArgumentK_analyticOnNhd nu).mono (combinedMacdonaldSlice_subset_rightHalfPlane _)
  have hG : AnalyticOnNhd ℂ (fun x => complexArgumentK nu x * complexArgumentK nu (y : ℂ))
      (combinedMacdonaldSlice (y : ℂ)) := hK.mul analyticOnNhd_const
  have hOneQuarter : (1 : ℂ) ∈ strictQuarterSector :=
    positive_real_mem_sector (by norm_num : (0 : ℝ) < 1)
  have hOneSlice : (1 : ℂ) ∈ combinedMacdonaldSlice (y : ℂ) :=
    quarter_subset_combined_real_slice hy hOneQuarter
  have hnear : (fun x => complexMacdonaldValue nu x (y : ℂ)) =ᶠ[𝓝 (1 : ℂ)]
      (fun x => complexArgumentK nu x * complexArgumentK nu (y : ℂ)) := by
    filter_upwards [strictQuarterSector_isOpen.mem_nhds hOneQuarter] with x hx
    exact complexMacdonaldValue_eq_product nu hx (positive_real_mem_sector hy)
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG
    (combinedMacdonaldSlice_convex _).isPreconnected hOneSlice hnear hz

/-- Every right-half-plane fixed argument admits a full positive-real
tail in its combined slice. This is proved from the sum and product
inequalities, rather than assumed as a continuation path. -/
theorem positive_tail_mem_combined_slice {z : ℂ} (hz : 0 < z.re) {y : ℝ}
    (hy : |z.im| < y) : (y : ℂ) ∈ combinedMacdonaldSlice z := by
  have hy0 : 0 < y := (abs_nonneg z.im).trans_lt hy
  refine ⟨hy0, hz, ?_, ?_⟩
  · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      using mul_pos hy0 hz
  · change |((y : ℂ) + z).im| < ((y : ℂ) + z).re
    simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.add_re, Complex.ofReal_re]
    linarith

/-- The second identity theorem uses positive real arguments accumulating
at R=|Im(z)|+1, which is an actual interior point of the combined slice.
No claim that every positive real lies in that slice is needed. -/
theorem complexMacdonaldValue_eq_product_combined (nu : ℂ) {z w : ℂ}
    (h : (z, w) ∈ combinedMacdonaldDomain) :
    complexMacdonaldValue nu z w = complexArgumentK nu z * complexArgumentK nu w := by
  have hF := complexMacdonaldValue_analyticOnNhd_right_combined nu z
  have hK : AnalyticOnNhd ℂ (complexArgumentK nu) (combinedMacdonaldSlice z) :=
    (complexArgumentK_analyticOnNhd nu).mono (combinedMacdonaldSlice_subset_rightHalfPlane z)
  have hG : AnalyticOnNhd ℂ (fun x => complexArgumentK nu z * complexArgumentK nu x)
      (combinedMacdonaldSlice z) := analyticOnNhd_const.mul hK
  let R : ℝ := |z.im| + 1
  have hR : |z.im| < R := by dsimp [R]; linarith
  have hRmem : (R : ℂ) ∈ combinedMacdonaldSlice z := positive_tail_mem_combined_slice h.1 hR
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
    have hr : R + 1 / ((n : ℝ) + 1) = R :=
      Complex.ofReal_injective (by simpa only [sequence] using heq)
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hseqEq : ∃ᶠ n : ℕ in atTop,
      complexMacdonaldValue nu z (sequence n) =
        complexArgumentK nu z * complexArgumentK nu (sequence n) := by
    apply Filter.Eventually.frequently
    apply Eventually.of_forall
    intro n
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hlarge : |z.im| < R + 1 / ((n : ℝ) + 1) := by linarith
    have hy : 0 < R + 1 / ((n : ℝ) + 1) := (abs_nonneg z.im).trans_lt hlarge
    have hslice := positive_tail_mem_combined_slice h.1 hlarge
    exact complexMacdonaldValue_eq_product_real_right_combined nu hy
      (combinedMacdonaldDomain_swap hslice)
  exact hF.eqOn_of_preconnected_of_frequently_eq hG
    (combinedMacdonaldSlice_convex z).isPreconnected hRmem
    (hpunctured.frequently hseqEq) (combinedMacdonaldDomain_swap h)

theorem complexMacdonaldKernel_integrable_combined (nu : ℂ) {z w : ℂ}
    (h : (z, w) ∈ combinedMacdonaldDomain) :
    Integrable (complexMacdonaldKernel nu z w) positiveMeasure := by
  have hL1 := (complexMacdonaldJoint_integrable_combined nu h).integral_prod_right
  apply hL1.congr
  exact Eventually.of_forall fun t => complexMacdonaldJoint_integral_v nu z w t

theorem complexMacdonaldValue_eq_single_combined (nu : ℂ) {z w : ℂ}
    (h : (z, w) ∈ combinedMacdonaldDomain) :
    complexMacdonaldValue nu z w =
      (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ), complexMacdonaldKernel nu z w t := by
  unfold complexMacdonaldValue
  congr 1
  rw [integral_prod_symm _ (complexMacdonaldJoint_integrable_combined nu h)]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => complexMacdonaldJoint_integral_v nu z w t

/-- Actual absolute convergence on the combined-damping domain. The
K argument is itself in the right half-plane for every positive t,
as separately proved in combined_product_argument_re_pos. -/
theorem actual_K_macdonald_combined_integrable (nu : ℂ) {z w : ℂ}
    (hz : 0 < z.re) (hw : 0 < w.re) (hp : 0 < (z * w).re)
    (hs : |(z + w).im| < (z + w).re) :
    IntegrableOn (fun t =>
      Complex.exp (-(t : ℂ) / 2 - (z ^ 2 + w ^ 2) / (2 * (t : ℂ))) *
        complexArgumentK nu (z * w / (t : ℂ)) / (t : ℂ)) (Ioi 0) := by
  apply (complexMacdonaldKernel_integrable_combined nu ⟨hz, hw, hp, hs⟩).congr
  exact Eventually.of_forall (complexMacdonaldKernel_eq_display nu z w)

/-- Genuine E18 on a strictly broader right-half-plane pair domain than
the independent quarter-sectors. The printed left-half-plane cases are
still OPEN, and no individual square positivity occurs in the inputs. -/
theorem actual_K_macdonald_combined (nu : ℂ) {z w : ℂ}
    (hz : 0 < z.re) (hw : 0 < w.re) (hp : 0 < (z * w).re)
    (hs : |(z + w).im| < (z + w).re) :
    complexArgumentK nu z * complexArgumentK nu w =
      (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ),
        Complex.exp (-(t : ℂ) / 2 - (z ^ 2 + w ^ 2) / (2 * (t : ℂ))) *
          complexArgumentK nu (z * w / (t : ℂ)) / (t : ℂ) := by
  have h : (z, w) ∈ combinedMacdonaldDomain := ⟨hz, hw, hp, hs⟩
  rw [← complexMacdonaldValue_eq_product_combined nu h,
    complexMacdonaldValue_eq_single_combined nu h]
  simp_rw [complexMacdonaldKernel_eq_display]

end
end ImbalancedChen.Part3.ActualComplexMacdonaldCombinedIdentity20261026b
