import ImbalancedChen.Part3ActualComplexKIConnection
import ImbalancedChen.Part3GeneralIOrderHolomorphy
import ImbalancedChen.Part3ComplexOrderKHolomorphic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
The actual positive-strip K/I connection extends continuously to every
nonzero imaginary order. This consumes the proved connection theorem;
there is no connection, continuity, or asymptotic supplier hypothesis.
The final dictionary uses exactly the literal `imaginaryOrderK t q` integral.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

noncomputable section
open scoped Topology
open Filter Set

namespace ImbalancedChen.Part3.ActualImaginaryKIConnectionSourceOnly

open GeneralComplexISeriesSourceOnly GeneralIOrderHolomorphySourceOnly
open ComplexOrderKBridgeSourceOnly ComplexOrderKHolomorphicSourceOnly
open ImaginaryOrderKBesselSourceOnly

theorem sin_pi_mul_ne_zero_of_im_ne_zero {nu : ℂ} (hnu : nu.im ≠ 0) :
    Complex.sin ((Real.pi : ℂ) * nu) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have him : Real.pi * nu.im = 0 := by
    simpa using congrArg Complex.im hk
  exact (mul_ne_zero Real.pi_ne_zero hnu) him

theorem tendsto_positive_real_translate (nu : ℂ) :
    Tendsto (fun eps : ℝ => (eps : ℂ) + nu) (𝓝[>] 0) (𝓝 nu) := by
  have hc : Continuous (fun eps : ℝ => (eps : ℂ) + nu) := by fun_prop
  have ht : Tendsto (fun eps : ℝ => (eps : ℂ) + nu) (𝓝 0) (𝓝 nu) := by
    simpa using hc.tendsto 0
  exact ht.mono_left nhdsWithin_le_nhds

/-- Boundary continuation along the explicit path epsilon+nu, epsilon>0.
Only the actual established positive-strip theorem is used. -/
theorem complexOrderK_eq_generalI_sub_of_re_zero {nu : ℂ}
    (hre : nu.re = 0) (him : nu.im ≠ 0) {q : ℝ} (hq : 0 < q) :
    complexOrderK nu q =
      (Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu)) *
        (generalI (-nu) q - generalI nu q) := by
  have hsin := sin_pi_mul_ne_zero_of_im_ne_zero him
  have hk : ContinuousAt (fun z : ℂ => complexOrderK z q) nu :=
    (complexOrderK_hasDerivAt nu q hq (by rw [hre]; norm_num)).continuousAt
  have hi : ContinuousAt (fun z : ℂ => generalI z q) nu :=
    (analyticAt_generalI_order nu (by rw [hre]; norm_num) hq).continuousAt
  have himinus : ContinuousAt (fun z : ℂ => generalI (-z) q) nu :=
    (analyticAt_generalI_order (-nu)
      (by simp only [Complex.neg_re, hre]; norm_num) hq).continuousAt.comp
        continuousAt_id.neg
  have hs : ContinuousAt
      (fun z : ℂ => (2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z)) nu := by fun_prop
  have hr : ContinuousAt (fun z : ℂ =>
      (Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * z)) *
        (generalI (-z) q - generalI z q)) nu :=
    (continuousAt_const.div hs (mul_ne_zero (by norm_num) hsin)).mul (himinus.sub hi)
  have hpath := tendsto_positive_real_translate nu
  have heq : (fun eps : ℝ => complexOrderK ((eps : ℂ) + nu) q) =ᶠ[𝓝[>] 0]
      (fun eps : ℝ => (Real.pi : ℂ) /
        (2 * Complex.sin ((Real.pi : ℂ) * ((eps : ℂ) + nu))) *
          (generalI (-((eps : ℂ) + nu)) q - generalI ((eps : ℂ) + nu) q)) := by
    have hlt : ∀ᶠ eps : ℝ in 𝓝[>] 0, eps < 1 :=
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hlt] with eps heps heps1
    apply ActualComplexKIConnection.complexOrderK_eq_generalI_sub
    · simpa only [Complex.add_re, Complex.ofReal_re, hre, add_zero] using heps
    · simpa only [Complex.add_re, Complex.ofReal_re, hre, add_zero] using heps1
    · exact hq
  exact tendsto_nhds_unique (hk.tendsto.comp hpath)
    ((hr.tendsto.comp hpath).congr' heq.symm)

/-- Genuine K_(i*tau) / I_(±i*tau) connection, for every nonzero real tau. -/
theorem complexOrderK_imaginary_eq_generalI_sub (tau : ℝ) (htau : tau ≠ 0)
    {q : ℝ} (hq : 0 < q) :
    complexOrderK ((tau : ℂ) * Complex.I) q =
      (Real.pi : ℂ) /
        (2 * Complex.sin ((Real.pi : ℂ) * ((tau : ℂ) * Complex.I))) *
          (generalI (-((tau : ℂ) * Complex.I)) q -
            generalI ((tau : ℂ) * Complex.I) q) := by
  apply complexOrderK_eq_generalI_sub_of_re_zero
  · simp
  · simpa using htau
  · exact hq

/-- The literal cosine-Laplace integral in the original K branch, with
its exact order `2*i*t`, equals the actual I-series combination. -/
theorem imaginaryOrderK_eq_generalI_sub (t : ℝ) (ht : t ≠ 0)
    {q : ℝ} (hq : 0 < q) :
    (imaginaryOrderK t q : ℂ) =
      (Real.pi : ℂ) /
        (2 * Complex.sin ((Real.pi : ℂ) * (((2 * t : ℝ) : ℂ) * Complex.I))) *
          (generalI (-(((2 * t : ℝ) : ℂ) * Complex.I)) q -
            generalI (((2 * t : ℝ) : ℂ) * Complex.I) q) := by
  rw [← complexOrderK_imaginary]
  exact complexOrderK_imaginary_eq_generalI_sub (2 * t)
    (mul_ne_zero (by norm_num) ht) hq

/-- Hyperbolic phase normalization of the same literal kernel. -/
theorem imaginaryOrderK_eq_generalI_sub_sinh (t : ℝ) (ht : t ≠ 0)
    {q : ℝ} (hq : 0 < q) :
    (imaginaryOrderK t q : ℂ) =
      (Real.pi : ℂ) / (2 * (Real.sinh (2 * Real.pi * t) : ℂ) * Complex.I) *
        (generalI (-(((2 * t : ℝ) : ℂ) * Complex.I)) q -
          generalI (((2 * t : ℝ) : ℂ) * Complex.I) q) := by
  rw [imaginaryOrderK_eq_generalI_sub t ht hq]
  have hphase : (Real.pi : ℂ) * (((2 * t : ℝ) : ℂ) * Complex.I) =
      ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hphase, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  ring

end ImbalancedChen.Part3.ActualImaginaryKIConnectionSourceOnly
