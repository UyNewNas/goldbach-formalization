import ImbalancedChen.Part3ActualLiteralPacketIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
SOURCEONLY, 2026-10-24. UNCOMPILED; no acceptance credit.
Actual new atom: the imaginary-order K Bessel integral, its absolute
integrability and joint continuity in real order parameter and positive
argument, and a concrete continuous K_{2it}(q)/q kernel with exact physical
support agreement. No continuity/integrability/spectral estimate is a premise.

Mathematical normalization: NIST DLMF 10.32.9,
https://dlmf.nist.gov/10.32.E9 , specialized to nu=2it, q>0.
We DEFINE this integral realization. No equality to an unrelated preexisting
Bessel implementation or to the FULL Kuznetsov kernel is claimed. The
Kuznetsov normalization, cusp Fourier coefficients, spectral measure, J
branch, exceptional branch and weighted estimates remain to be constructed.
The exponential majorant is solely an analytic well-definedness tool;
it is NOT the desired 7/32 spectral gain.
-/

namespace ImbalancedChen.Part3.ImaginaryOrderKBesselSourceOnly
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open P3ActualLiteralPacketIntegralSourceOnly
open P3Period64NativeReconstructionSourceOnly
  (spectralTest spectralMode)
open P3NativePeriod64SamplingSourceOnly (D4)

def kIntegrand (t q u : ℝ) : ℝ :=
  Real.exp (-q * Real.cosh u) * Real.cos (2*t*u)

/-- The integral realization of K_{2it}(q), used only for q>0. -/
def imaginaryOrderK (t q : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), kIntegrand t q u

lemma half_le_cosh (u : ℝ) : u/2 ≤ Real.cosh u := by
  rw [Real.cosh_eq]
  have h := Real.add_one_le_exp u
  have hp := Real.exp_pos (-u)
  linarith

/-- One majorant is valid for ALL real t and ALL q>=a>0. -/
lemma kIntegrand_norm_le {a q : ℝ} (ha : 0<a) (hq : a≤q)
    (t u : ℝ) :
    ‖kIntegrand t q u‖ ≤ Real.exp (-(a/2)*u) := by
  have h1 : a * Real.cosh u ≤ q * Real.cosh u :=
    mul_le_mul_of_nonneg_right hq (Real.cosh_pos u).le
  have h2 : a * (u/2) ≤ a * Real.cosh u :=
    mul_le_mul_of_nonneg_left (half_le_cosh u) ha.le
  calc
    ‖kIntegrand t q u‖ =
        Real.exp (-q * Real.cosh u) * |Real.cos (2*t*u)| := by
      simp only [kIntegrand, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-q * Real.cosh u) * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
    _ ≤ Real.exp (-(a/2)*u) := by
      rw [mul_one]
      apply Real.exp_le_exp.mpr
      nlinarith

lemma exponential_majorant_integrable {a : ℝ} (ha : 0<a) :
    IntegrableOn (fun u : ℝ => Real.exp (-(a/2)*u)) (Ioi 0) := by
  exact integrableOn_exp_mul_Ioi (by linarith : -(a/2)<0) 0

theorem kIntegrand_integrable (t : ℝ) {q : ℝ} (hq : 0<q) :
    IntegrableOn (kIntegrand t q) (Ioi 0) := by
  have hc : Continuous (kIntegrand t q) := by
    unfold kIntegrand
    fun_prop
  exact (exponential_majorant_integrable hq).mono'
    hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => kIntegrand_norm_le hq le_rfl t u))

/-- In particular t=0 is included without division by t. Joint continuity
is established on a complete half-line by dominated convergence. -/
theorem imaginaryOrderK_joint_continuous (a : ℝ) (ha : 0<a) :
    Continuous (fun p : ℝ × Ici a => imaginaryOrderK p.1 (p.2 : ℝ)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  change Tendsto
    (fun r : ℝ × Ici a => ∫ u in Ioi (0 : ℝ), kIntegrand r.1 (r.2 : ℝ) u)
    (𝓝 p) (𝓝 (∫ u in Ioi (0 : ℝ), kIntegrand p.1 (p.2 : ℝ) u))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => Real.exp (-(a/2)*u))
  · apply Filter.Eventually.of_forall
    intro r
    have hc : Continuous (fun u : ℝ => kIntegrand r.1 (r.2 : ℝ) u) := by
      unfold kIntegrand
      fun_prop
    exact hc.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun r =>
      Filter.Eventually.of_forall (fun u => kIntegrand_norm_le ha r.2.property r.1 u))
  · exact exponential_majorant_integrable ha
  · apply Filter.Eventually.of_forall
    intro u
    have hc : Continuous (fun r : ℝ × Ici a => kIntegrand r.1 (r.2 : ℝ) u) := by
      unfold kIntegrand
      fun_prop
    exact hc.continuousAt

theorem imaginaryOrderK_neg (t q : ℝ) :
    imaginaryOrderK (-t) q = imaginaryOrderK t q := by
  unfold imaginaryOrderK
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  unfold kIntegrand
  have he : 2*(-t)*u = -(2*t*u) := by ring
  rw [he, Real.cos_neg]

/-- The 1/q belongs to the Bessel transform's dq/q, and is retained. -/
def halfLineKKernel (a : ℝ) (ha : 0<a) (t : ℝ) : C(Ici a, ℂ) where
  toFun q := (imaginaryOrderK t (q : ℝ) : ℂ) / ((q : ℝ) : ℂ)
  continuous_toFun := by
    have hpair : Continuous (fun q : Ici a => (t,q)) := by fun_prop
    have hK : Continuous (fun q : Ici a => (imaginaryOrderK t (q : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((imaginaryOrderK_joint_continuous a ha).comp hpair)
    have hq : Continuous (fun q : Ici a => ((q : ℝ) : ℂ)) := by fun_prop
    exact hK.div hq (fun q => Complex.ofReal_ne_zero.mpr
      (lt_of_lt_of_le ha q.property).ne')

def extendedKKernel (a : ℝ) (ha : 0<a) (t : ℝ) : C(ℝ, ℂ) :=
  extendKernelFromHalfLine a (halfLineKKernel a ha t)

theorem extendedKKernel_eq (a : ℝ) (ha : 0<a) (t q : ℝ) (hq : a≤q) :
    extendedKKernel a ha t q = (imaginaryOrderK t q : ℂ)/(q : ℂ) := by
  exact extendKernelFromHalfLine_eq a (halfLineKKernel a ha t) q hq

/-- An actual packet's full physical region lies above this extension cutoff. -/
theorem extendedKKernel_eq_on_physical_region {ι : Type*} (P : PacketData ι)
    (t q : ℝ) (hq : q ∈ P.region) :
    extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) t q =
      (imaginaryOrderK t q : ℂ)/(q : ℂ) := by
  apply extendedKKernel_eq
  change P.Y0/16 ≤ q ∧ q ≤ 16*P.Y0 at hq
  linarith [P.Y0_pos]

/-- Outside the physical region the actual spectral test vanishes. Thus
the extended kernel gives the exact test-weighted K transform everywhere,
including q<=0, without asserting continuity of K/q at zero. -/
theorem spectralTest_mul_extendedKKernel {ι : Type*} (P : PacketData ι)
    (k : D4 → ℤ) (t q : ℝ) :
    spectralTest k P.Y0 q *
        extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) t q =
      spectralTest k P.Y0 q * ((imaginaryOrderK t q : ℂ)/(q : ℂ)) := by
  by_cases hq : q ∈ P.region
  · rw [extendedKKernel_eq_on_physical_region P t q hq]
  · simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hq,
      Complex.ofReal_zero, zero_mul]

theorem integrable_spectralTest_mul_extendedKKernel {ι : Type*} (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    Integrable (fun q : ℝ => spectralTest k P.Y0 q *
      extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) t q) := by
  have hc : Continuous (fun q : ℝ => spectralTest k P.Y0 q *
      extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) t q) :=
    (P3Period64NativeReconstructionSourceOnly.spectralTest_contDiff k P.Y0).continuous.mul
      (extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) t).continuous
  apply hc.integrable_of_hasCompactSupport
  apply (isCompact_Icc : IsCompact P.region).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_Icc : IsClosed P.region)
  intro q hq
  by_contra hn
  apply hq
  simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hn,
    Complex.ofReal_zero, zero_mul]

theorem integral_spectralTest_mul_extendedKKernel {ι : Type*} (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    (∫ q : ℝ, spectralTest k P.Y0 q *
        extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) t q) =
      ∫ q : ℝ, spectralTest k P.Y0 q * ((imaginaryOrderK t q : ℂ)/(q : ℂ)) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (spectralTest_mul_extendedKKernel P k t)

theorem integrable_spectralTest_mul_K {ι : Type*} (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    Integrable (fun q : ℝ =>
      spectralTest k P.Y0 q * ((imaginaryOrderK t q : ℂ)/(q : ℂ))) := by
  have he : (fun q : ℝ => spectralTest k P.Y0 q *
      extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) t q) =
      (fun q : ℝ => spectralTest k P.Y0 q *
        ((imaginaryOrderK t q : ℂ)/(q : ℂ))) :=
    funext (spectralTest_mul_extendedKKernel P k t)
  rw [← he]
  exact integrable_spectralTest_mul_extendedKKernel P k t

end
end ImbalancedChen.Part3.ImaginaryOrderKBesselSourceOnly
