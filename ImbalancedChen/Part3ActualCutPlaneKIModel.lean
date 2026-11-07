import ImbalancedChen.Part3ActualComplexArgumentISlit
import ImbalancedChen.Part3ActualComplexMacdonaldQuarterIdentity
import ImbalancedChen.Part3ActualComplexKIConnection
import ImbalancedChen.Part3ActualImaginaryKIConnection
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

A branch-compatible principal-slit K model from the actual I-minus-I
connection. The actual I core supplies slit holomorphy. Agreement with
the actual right-half-plane Laplace K is proved by the analytic identity
theorem from the supplied positive-real K/I identity. The positive order
strip 0<Re(nu)<1 and the nonzero imaginary-order line are bound separately
using their exact actual suppliers. No continuation equality is assumed.

The algebraic expression is named Nonintegral: order zero has no model
binding here, and no zero-order conclusion is inferred from division by
sin(pi*nu). Extension outside the supplied order ranges and the full
large-sector Macdonald identity remain OPEN.
-/

namespace ImbalancedChen.Part3.ActualCutPlaneKIModel20261026b

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ComplexOrderKBridgeSourceOnly GeneralComplexISeriesSourceOnly
open ActualComplexArgumentISlit20261026b
open ActualComplexArgumentKLaplace20261026b ActualComplexArgumentKHolomorphic20261026b
open ActualComplexMacdonaldQuarterL120261026b ActualComplexMacdonaldQuarterIdentity20261026b

/-- The principal-slit K expression at nonintegral orders. Its binding
theorems below specify the exact orders supplied by the actual K/I chain. -/
def cutPlaneKNonintegral (nu z : ℂ) : ℂ :=
  (Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu)) *
    (complexArgumentI (-nu) z - complexArgumentI nu z)

theorem cutPlaneKNonintegral_analyticOnNhd {nu : ℂ}
    (hL : -1 < nu.re) (hU : nu.re < 1) :
    AnalyticOnNhd ℂ (cutPlaneKNonintegral nu) Complex.slitPlane := by
  have hminus : -1 < (-nu).re := by rw [Complex.neg_re]; linarith
  exact analyticOnNhd_const.mul
    ((complexArgumentI_analyticOnNhd hminus).sub (complexArgumentI_analyticOnNhd hL))

theorem rightHalfPlane_subset_slit : rightHalfPlane ⊆ Complex.slitPlane := by
  intro z hz
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl hz

theorem rightHalfPlane_convex : Convex ℝ rightHalfPlane :=
  convex_halfSpace_gt (.mk Complex.add_re Complex.smul_re) 0

/-- The nonzero connection denominator in the open positive order strip
follows from the actual Gamma reflection identity and Gamma nonvanishing. -/
theorem sin_pi_order_ne_zero_of_positive_strip {nu : ℂ}
    (hL : 0 < nu.re) (hU : nu.re < 1) :
    Complex.sin ((Real.pi : ℂ) * nu) ≠ 0 := by
  have hg : Complex.Gamma nu * Complex.Gamma (1 - nu) ≠ 0 :=
    mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hL)
      (Complex.Gamma_ne_zero_of_re_pos (by simpa using sub_pos.mpr hU))
  have he := Complex.Gamma_mul_Gamma_one_sub nu
  intro hs
  rw [hs, div_zero] at he
  exact hg he

theorem cutPlaneKNonintegral_real (nu : ℂ) (q : ℝ) :
    cutPlaneKNonintegral nu (q : ℂ) =
      (Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu)) *
        (generalI (-nu) q - generalI nu q) := by
  unfold cutPlaneKNonintegral
  rw [complexArgumentI_real, complexArgumentI_real]

theorem cutPlaneKNonintegral_real_positive_strip {nu : ℂ}
    (hL : 0 < nu.re) (hU : nu.re < 1) {q : ℝ} (hq : 0 < q) :
    cutPlaneKNonintegral nu (q : ℂ) = complexOrderK nu q := by
  rw [cutPlaneKNonintegral_real]
  exact (ActualComplexKIConnection.complexOrderK_eq_generalI_sub hL hU hq).symm

theorem cutPlaneKNonintegral_real_imaginary {nu : ℂ}
    (hre : nu.re = 0) (him : nu.im ≠ 0) {q : ℝ} (hq : 0 < q) :
    cutPlaneKNonintegral nu (q : ℂ) = complexOrderK nu q := by
  rw [cutPlaneKNonintegral_real]
  exact (ActualImaginaryKIConnectionSourceOnly.complexOrderK_eq_generalI_sub_of_re_zero hre him hq).symm

/-- Transfer from actual positive-real data to the complete right
half-plane. The real identity is a primitive supplied by the actual K/I
chain; holomorphy and the continuation conclusion are proved here. -/
private theorem cutPlaneKNonintegral_eq_right_of_real {nu : ℂ}
    (hL : -1 < nu.re) (hU : nu.re < 1)
    (hreal : ∀ q : ℝ, 0 < q → cutPlaneKNonintegral nu (q : ℂ) = complexOrderK nu q) :
    EqOn (cutPlaneKNonintegral nu) (complexArgumentK nu) rightHalfPlane := by
  have hcut : AnalyticOnNhd ℂ (cutPlaneKNonintegral nu) rightHalfPlane :=
    (cutPlaneKNonintegral_analyticOnNhd hL hU).mono rightHalfPlane_subset_slit
  have hactual := complexArgumentK_analyticOnNhd nu
  have hquarter : EqOn (cutPlaneKNonintegral nu) (complexArgumentK nu) strictQuarterSector := by
    apply eqOn_sector_of_positive_real
      (hcut.mono (fun _ hz => strictQuarterSector_re_pos hz))
      (hactual.mono (fun _ hz => strictQuarterSector_re_pos hz))
    intro q hq
    rw [complexArgumentK_real]
    exact hreal q hq
  have hnear : cutPlaneKNonintegral nu =ᶠ[𝓝 (1 : ℂ)] complexArgumentK nu := by
    filter_upwards [strictQuarterSector_isOpen.mem_nhds
      (positive_real_mem_sector (by norm_num : (0 : ℝ) < 1))] with z hz
    exact hquarter hz
  exact hcut.eqOn_of_preconnected_of_eventuallyEq hactual rightHalfPlane_convex.isPreconnected
    (by change 0 < (1 : ℂ).re; norm_num) hnear

/-- Actual agreement on the entire right half-plane for the genuine
open-strip K/I supplier. No analytic continuation hypothesis is an input. -/
theorem cutPlaneKNonintegral_eq_actual_positive_strip {nu : ℂ}
    (hL : 0 < nu.re) (hU : nu.re < 1) {z : ℂ} (hz : 0 < z.re) :
    cutPlaneKNonintegral nu z = complexArgumentK nu z := by
  apply cutPlaneKNonintegral_eq_right_of_real (by linarith : -1 < nu.re) hU
    (fun q hq => cutPlaneKNonintegral_real_positive_strip hL hU hq)
  exact hz

/-- The separately supplied nonzero imaginary-order boundary identity
also yields the actual principal-slit model throughout Re(z)>0. -/
theorem cutPlaneKNonintegral_eq_actual_imaginary {nu : ℂ}
    (hre : nu.re = 0) (him : nu.im ≠ 0) {z : ℂ} (hz : 0 < z.re) :
    cutPlaneKNonintegral nu z = complexArgumentK nu z := by
  apply cutPlaneKNonintegral_eq_right_of_real (by rw [hre]; norm_num) (by rw [hre]; norm_num)
    (fun q hq => cutPlaneKNonintegral_real_imaginary hre him hq)
  exact hz

/-- Nonzero imaginary orders have a genuine nonzero sine denominator. -/
theorem sin_pi_order_ne_zero_of_imaginary {nu : ℂ} (him : nu.im ≠ 0) :
    Complex.sin ((Real.pi : ℂ) * nu) ≠ 0 :=
  ActualImaginaryKIConnectionSourceOnly.sin_pi_mul_ne_zero_of_im_ne_zero him

end
end ImbalancedChen.Part3.ActualCutPlaneKIModel20261026b
