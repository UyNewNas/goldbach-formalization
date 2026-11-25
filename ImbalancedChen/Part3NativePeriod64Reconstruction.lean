import ImbalancedChen.Part3ActualNormalizedSmoothF
import ImbalancedChen.Part3CompactCoordinateFourier
import ImbalancedChen.Part3NativePeriod64Sampling
import ImbalancedChen.Part3ActualSampledFourierLattice
import ImbalancedChen.Part3CommonSmoothCutoff
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.CompactOpen
import Mathlib.Tactic

/-
ACTUAL INTAKE -- 2026-10-23, prepared for ROOT's single compilation queue.
Frozen source: .lake/proof-continuation/drafts/20261023-P3-four-coordinate-period64-native-reconstruction-SOURCEONLY.lean.txt
Source SHA256: 6e4a32cc2301ad0657f1ce48dd576238e3710e340664bd21c939d86144e98e16
Only the import/provenance preamble and UTF-8 BOM handling change.
Mathematical bodies, namespaces, quantifiers and existing scope ends are retained.
Global noncomputable sections are valid Lean syntax and their matching ends are preserved.
Historical SOURCEONLY comments below describe provenance; this intake is UNCOMPILED / NOT OWNED.
-/

/-
SOURCE ONLY -- 2026-10-23. No Lean/lake/compiler/typechecker/CI was run.
Author: /root/p3_common_interval_phase_separation_sol_max_oct22.

This continues the already delivered source-only declarations:
 (1) compact-coordinate-IBP-and-coefficient-continuity-SOURCEONLY.lean.txt;
 (2) native-torus-period64-actual-Fourier-sampling-SOURCEONLY.lean.txt;
 (3) actual-FT-sampled-weighted-lattice-SOURCEONLY.lean.txt, SHA256
     778555adf6025b8d8fc1293fa216b270f6cf4a85dcd958f6f8734dbc9fbe075f;
 (4) source-reviews/drafts/
     20261023-P3-actual-normalizedF-smooth-compact-astra-V2-SOURCEONLY.lean.txt,
     SHA256 fc9e3c7266c0291b02c8b385bb0bb4a5c9ac8e97c8cc7a6e5d086ba327fb520a.
Use the actualF V2, which explicitly closes its noncomputable section.

ASSEMBLY HYGIENE: these are source-only declarations, not imaginary project
imports. For a future single review bundle, collect Mathlib/project imports at
the top, place all namespace bodies inside ONE noncomputable section, and close
that section at the end. Earlier drafts (1)--(3) contain a noncomputable-section
header without an extra final anonymous end; extracting their namespace bodies
under the one shared section avoids that mechanical scope issue. The present
continuation explicitly closes both its namespace and its outer section.
This is not a standalone checked module, and no compilation is claimed.

CLOSED NEW ANALYTIC STEP:
 actual f continuous + actual coordinate support inside(-32,32)^4
 -> FOUR coordinate compact continuous lifts, with endpoint matches already
    proved by liftCoord64
 -> a continuous native torus function whose value is EXACTLY period64 f.
No full-torus continuity conclusion is a hypothesis.
 actual compact C^(4L) + proved actual native coefficient summability
 -> native inverse -> exact pointwise reconstruction at physical x/64.
 actual normalizedF + a fixed actual smooth chi satisfying chi*F=F
 -> exact all-spectral-height HasSum with unchanged native Fin4->Int indices.
The common m mode has only I,V,k,m as arguments; betaMode has only beta,k,U,Z,y,z.

Primary fixed-mathlib sources additionally inspected, pin
 e4c91783ca8e6a7c693ae624ade32fd22d4e43c1:
 Topology/CompactOpen.lean, blob72358cfcca49fb9e41916f095309bc5f605d24ba:
  ContinuousMap.curry430--435, uncurry458--467.
 Analysis/Normed/Lp/PiLp.lean, blob6961e020117a12f4c823a0cd1d6ebe77931ccacc:
  continuous_toLp545--546.
 Topology/Instances/AddCircle/Defs.lean,
  blob961fd112f6bbe156fc2043e6a327b949c9b18536:
  liftIoc324--325 and liftIoc_continuous835--838.
 Analysis/Fourier/AddCircleMulti.lean,
  blob08ab569e1977c455fdde0a67df2131ea1fc864c5:
  mFourier49--51; native pointwise inverse329--332.
 Algebra/BigOperators/Fin.lean, blob8fcbbfdf1a86b0e895348e5c082db08191d495df:
  prod_univ_four124--126.
 Analysis/Calculus/BumpFunction/Basic.lean,
  blobc295ab7993c2b94fc9de8b3d6b79d7be7f4440a7:
  ContDiffBump70--74; one_of_mem_closedBall137--140;
  tsupport_eq157--158; contDiff203--204.
 Analysis/SpecialFunctions/ExpDeriv.lean,
  blob65e0c15f2921a9dfd6bea14c06d2b46699dccc2a:
  Complex.contDiff_exp114--115; ContDiff.cexp187--188.
 Topology/Algebra/InfiniteSum/Basic.lean:
  generated HasSum.congr_fun80--81.
 Topology/Algebra/InfiniteSum/Ring.lean:
  HasSum.mul_left39--40.

No derivative-mass uniform-rho estimate is used to reconstruct F.
That separate quantitative supplier is needed only for the x^epsilon budget.
-/


noncomputable section

open Set MeasureTheory
open scoped BigOperators FourierTransform ContDiff

namespace P3Period64NativeReconstructionSourceOnly

open P3NativePeriod64SamplingSourceOnly
  (D4 E4 T4 inside64 rep period64 sampleFreq liftCoord64)
open P3ActualSampledLatticeSourceOnly (coeff)
open ImbalancedChen.Part3.ActualNormalizedSmoothF
  (normalizedF normalizedF_contDiff normalizedF_hasCompactSupport
   normalizedF_support_inside64 support_subset_fixedBox boxLo boxHi)

abbrev A := UnitAddCircle

def rep1 (z : A) : ℝ := ((AddCircle.equivIoc (1 : ℝ) (-1/2 : ℝ)) z).1

def point4 (t v w z : ℝ) : E4 := WithLp.toLp 2 ![t,v,w,z]

lemma liftCoord64_rep {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y]
    (G : C(ℝ × Y, ℂ))
    (hs : ∀ t y, t ∉ Ioo (-32 : ℝ) 32 → G (t,y) = 0)
    (z : A) (y : Y) :
    liftCoord64 G hs z y = G ((64 : ℝ)*rep1 z,y) := by
  rfl

lemma coordinate_zero (f : E4 → ℂ) (hb : Function.support f ⊆ inside64)
    (i : D4) (x : E4) (hx : x i ∉ Ioo (-32 : ℝ) 32) : f x = 0 := by
  by_contra hn
  exact hx ((hb hn) i)

/- Separate the bundled lift into one opaque theorem on ORDINARY functions.
Later stages carry only the displayed function, never nested ContinuousMap
values whose continuity fields contain all preceding constructions. -/
private theorem continuous_rep_substitution
    {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y]
    (G : ℝ × Y → ℂ) (hG : Continuous G)
    (hs : ∀ t y, t ∉ Ioo (-32 : ℝ) 32 → G (t,y) = 0) :
    Continuous (fun p : A × Y => G ((64 : ℝ)*rep1 p.1,p.2)) := by
  let Gc : C(ℝ × Y, ℂ) := ⟨G,hG⟩
  have hsC : ∀ t y, t ∉ Ioo (-32 : ℝ) 32 → Gc (t,y) = 0 := hs
  have hc := P3NativePeriod64SamplingSourceOnly.continuous_liftCoord64_uncurry Gc hsC
  simpa only [liftCoord64_rep, Gc, ContinuousMap.coe_mk] using hc

private theorem continuous_real_point4 (f : E4 → ℂ) (hf : Continuous f) :
    Continuous (fun p : ℝ × (ℝ × (ℝ × ℝ)) =>
      f (point4 p.1 p.2.1 p.2.2.1 p.2.2.2)) := by
  apply hf.comp
  apply (PiLp.continuous_toLp 2 (fun _ : D4 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> fun_prop

private theorem continuous_one_rep (f : E4 → ℂ) (hf : Continuous f)
    (hb : Function.support f ⊆ inside64) :
    Continuous (fun p : A × (ℝ × (ℝ × ℝ)) =>
      f (point4 ((64 : ℝ)*rep1 p.1) p.2.1 p.2.2.1 p.2.2.2)) := by
  refine continuous_rep_substitution
    (fun p : ℝ × (ℝ × (ℝ × ℝ)) => f (point4 p.1 p.2.1 p.2.2.1 p.2.2.2))
    (continuous_real_point4 f hf) ?_
  intro t y ht
  exact coordinate_zero f hb 0 (point4 t y.1 y.2.1 y.2.2) ht

private theorem continuous_two_rep (f : E4 → ℂ) (hf : Continuous f)
    (hb : Function.support f ⊆ inside64) :
    Continuous (fun p : A × (A × (ℝ × ℝ)) =>
      f (point4 ((64 : ℝ)*rep1 p.2.1) ((64 : ℝ)*rep1 p.1) p.2.2.1 p.2.2.2)) := by
  refine continuous_rep_substitution
    (fun p : ℝ × (A × (ℝ × ℝ)) =>
      f (point4 ((64 : ℝ)*rep1 p.2.1) p.1 p.2.2.1 p.2.2.2)) ?_ ?_
  · exact (continuous_one_rep f hf hb).comp
      (show Continuous (fun p : ℝ × (A × (ℝ × ℝ)) =>
        (p.2.1,(p.1,p.2.2))) by fun_prop)
  · intro v y hv
    exact coordinate_zero f hb 1 (point4 ((64 : ℝ)*rep1 y.1) v y.2.1 y.2.2) hv

private theorem continuous_three_rep (f : E4 → ℂ) (hf : Continuous f)
    (hb : Function.support f ⊆ inside64) :
    Continuous (fun p : A × (A × (A × ℝ)) =>
      f (point4 ((64 : ℝ)*rep1 p.2.2.1) ((64 : ℝ)*rep1 p.2.1)
        ((64 : ℝ)*rep1 p.1) p.2.2.2)) := by
  refine continuous_rep_substitution
    (fun p : ℝ × (A × (A × ℝ)) =>
      f (point4 ((64 : ℝ)*rep1 p.2.2.1) ((64 : ℝ)*rep1 p.2.1) p.1 p.2.2.2)) ?_ ?_
  · exact (continuous_two_rep f hf hb).comp
      (show Continuous (fun p : ℝ × (A × (A × ℝ)) =>
        (p.2.1,(p.2.2.1,(p.1,p.2.2.2)))) by fun_prop)
  · intro w y hw
    exact coordinate_zero f hb 2
      (point4 ((64 : ℝ)*rep1 y.2.1) ((64 : ℝ)*rep1 y.1) w y.2.2) hw

private theorem continuous_four_rep (f : E4 → ℂ) (hf : Continuous f)
    (hb : Function.support f ⊆ inside64) :
    Continuous (fun p : A × (A × (A × A)) =>
      f (point4 ((64 : ℝ)*rep1 p.2.2.2) ((64 : ℝ)*rep1 p.2.2.1)
        ((64 : ℝ)*rep1 p.2.1) ((64 : ℝ)*rep1 p.1))) := by
  refine continuous_rep_substitution
    (fun p : ℝ × (A × (A × A)) =>
      f (point4 ((64 : ℝ)*rep1 p.2.2.2) ((64 : ℝ)*rep1 p.2.2.1)
        ((64 : ℝ)*rep1 p.2.1) p.1)) ?_ ?_
  · exact (continuous_three_rep f hf hb).comp
      (show Continuous (fun p : ℝ × (A × (A × A)) =>
        (p.2.1,(p.2.2.1,(p.2.2.2,p.1)))) by fun_prop)
  · intro z y hz
    exact coordinate_zero f hb 3
      (point4 ((64 : ℝ)*rep1 y.2.2) ((64 : ℝ)*rep1 y.2.1)
        ((64 : ℝ)*rep1 y.1) z) hz

/- The theorem type, period64 definition, support condition and heartbeat
limit are unchanged. Only ordinary functions occur in this final comparison. -/
set_option maxHeartbeats 800000 in
theorem continuous_period64 (f : E4 → ℂ) (hf : Continuous f)
    (hb : Function.support f ⊆ inside64) : Continuous (period64 f) := by
  have hC := (continuous_four_rep f hf hb).comp
    (show Continuous (fun z : T4 => (z 3,(z 2,(z 1,z 0)))) by fun_prop)
  have hEq : (fun z : T4 => f (point4 ((64 : ℝ)*rep1 (z 0))
      ((64 : ℝ)*rep1 (z 1)) ((64 : ℝ)*rep1 (z 2)) ((64 : ℝ)*rep1 (z 3)))) =
      period64 f := by
    funext z
    change f (point4 ((64 : ℝ)*rep1 (z 0)) ((64 : ℝ)*rep1 (z 1))
      ((64 : ℝ)*rep1 (z 2)) ((64 : ℝ)*rep1 (z 3))) =
      f ((64 : ℝ) • WithLp.toLp 2 (rep z))
    apply congrArg f
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  exact hEq ▸ hC

def period64C (f : E4 → ℂ) (hf : Continuous f)
    (hb : Function.support f ⊆ inside64) : C(T4, ℂ) :=
  ⟨period64 f, continuous_period64 f hf hb⟩

@[simp] lemma period64C_apply (f : E4 → ℂ) (hf : Continuous f)
    (hb : Function.support f ⊆ inside64) (z : T4) :
    period64C f hf hb z = period64 f z := rfl

/- Summability is the genuine output of the previous sampled-lattice proof.
   Full-torus continuity is the genuine output of the construction above. -/
theorem compact_native_hasSum (f : E4 → ℂ) (J0 : ℕ)
    (hf : ContDiff ℝ (4*(J0+3)) f) (hc : HasCompactSupport f)
    (hb : Function.support f ⊆ inside64) (z : T4) :
    HasSum (fun k : D4 → ℤ => coeff f k * UnitAddTorus.mFourier k z) (period64 f z) := by
  have hs : Summable (UnitAddTorus.mFourierCoeff (period64C f hf.continuous hb)) := by
    exact P3ActualSampledLatticeSourceOnly.native_coeff_summable f J0 hf hc hb
  simpa only [smul_eq_mul, period64C, coeff, ContinuousMap.coe_mk] using
    UnitAddTorus.hasSum_mFourier_series_apply_of_summable
      (f := period64C f hf.continuous hb) hs z

def e (s : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))

lemma e_add (s t : ℝ) : e (s+t) = e s * e t := by
  dsimp [e]
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]

lemma e_eq_fourier (s : ℝ) : e s = fourier 1 (s : A) := by
  rw [fourier_coe_apply]
  norm_num [e]

lemma norm_e (s : ℝ) : ‖e s‖ = 1 := by
  rw [e_eq_fourier]
  exact Circle.norm_coe _

lemma fourier_scaled_eq_e (n : ℤ) (x : ℝ) :
    fourier n ((x/64 : ℝ) : A) = e ((n : ℝ)/64*x) := by
  simp only [fourier_coe_apply, Complex.ofReal_one, div_one]
  dsimp [e]
  push_cast
  congr 1
  ring

def phase4 (k : D4 → ℤ) (x : E4) : ℂ :=
  e ((k 0 : ℝ)/64*x 0) *
    (e ((k 1 : ℝ)/64*x 1) *
      (e ((k 2 : ℝ)/64*x 2) * e ((k 3 : ℝ)/64*x 3)))

lemma native_monomial_scaled (k : D4 → ℤ) (x : E4) :
    UnitAddTorus.mFourier k (fun i => ((x i/64 : ℝ) : A)) = phase4 k x := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_four,
    fourier_scaled_eq_e, phase4]
  ring

/- Exact physical reconstruction on the period cell, with the native
   Fin4->Int index and positive exponential signs preserved coordinatewise. -/
theorem compact_pointwise_hasSum (f : E4 → ℂ) (J0 : ℕ)
    (hf : ContDiff ℝ (4*(J0+3)) f) (hc : HasCompactSupport f)
    (hb : Function.support f ⊆ inside64) (x : E4) (hx : x ∈ inside64) :
    HasSum (fun k : D4 → ℤ => coeff f k * phase4 k x) (f x) := by
  have h := compact_native_hasSum f J0 hf hc hb (fun i => ((x i/64 : ℝ) : A))
  rw [P3NativePeriod64SamplingSourceOnly.period64_eval_inside f x hx] at h
  simpa only [native_monomial_scaled] using h

def actualCoeff (rho sigma : ℝ) (k : D4 → ℤ) : ℂ :=
  coeff (normalizedF rho sigma) k

theorem actualCoeff_eq_fourier_sample (rho sigma : ℝ) (k : D4 → ℤ) :
    actualCoeff rho sigma k =
      ((64 : ℝ)^4)⁻¹ • 𝓕 (normalizedF rho sigma) (sampleFreq k) := by
  rw [actualCoeff, coeff]
  exact P3NativePeriod64SamplingSourceOnly.native_period64_fourier_sample
    (normalizedF rho sigma) (normalizedF_support_inside64 rho sigma) k

theorem actual_pointwise_hasSum (rho sigma : ℝ) (J0 : ℕ)
    (x : E4) (hx : x ∈ inside64) :
    HasSum (fun k : D4 → ℤ => actualCoeff rho sigma k * phase4 k x)
      (normalizedF rho sigma x) := by
  exact compact_pointwise_hasSum (normalizedF rho sigma) J0
    ((normalizedF_contDiff rho sigma).of_le (WithTop.coe_le_coe.mpr le_top))
    (normalizedF_hasCompactSupport rho sigma)
    (normalizedF_support_inside64 rho sigma) x hx

theorem actual_pointwise_sampled_hasSum (rho sigma : ℝ) (J0 : ℕ)
    (x : E4) (hx : x ∈ inside64) :
    HasSum (fun k : D4 → ℤ =>
      (((64 : ℝ)^4)⁻¹ • 𝓕 (normalizedF rho sigma) (sampleFreq k)) * phase4 k x)
      (normalizedF rho sigma x) := by
  apply (actual_pointwise_hasSum rho sigma J0 x hx).congr_fun
  intro k
  rw [actualCoeff_eq_fourier_sample]

/- A FIXED ACTUAL smooth spectral cutoff. The original route calls for a
   smooth compact spectral test. An uncut periodic exponential would not
   reconstruct physical F outside the period cell. The following chi is
   1 on[1/8,8] and has support strictly inside(1/16,16). -/
def chiBump : ContDiffBump (65/16 : ℝ) where
  rIn := 63/16
  rOut := 127/32
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def chi (t : ℝ) : ℝ := chiBump t

lemma chi_contDiff : ContDiff ℝ ∞ chi := chiBump.contDiff

lemma chi_eq_one {t : ℝ} (ht : t ∈ Icc (1/8 : ℝ) 8) : chi t = 1 := by
  apply chiBump.one_of_mem_closedBall
  change |t - 65/16| ≤ 63/16
  rw [abs_le]
  constructor <;> linarith [ht.1,ht.2]

lemma chi_tsupport_subset : tsupport chi ⊆ Ioo (1/16 : ℝ) 16 := by
  change tsupport (chiBump : ℝ → ℝ) ⊆ _
  rw [chiBump.tsupport_eq]
  intro t ht
  change |t - 65/16| ≤ 127/32 at ht
  obtain ⟨hl,hu⟩ := abs_le.mp ht
  constructor <;> linarith

lemma chi_zero_of_notMem {t : ℝ} (ht : t ∉ Ioo (-32 : ℝ) 32) : chi t = 0 := by
  by_contra hn
  have hs := chi_tsupport_subset (subset_closure hn)
  exact ht ⟨by linarith [hs.1],by linarith [hs.2]⟩

lemma actual_t_bounds {rho sigma : ℝ} {x : E4} (hx : normalizedF rho sigma x ≠ 0) :
    x 0 ∈ Icc (1/8 : ℝ) 8 := by
  have hb := support_subset_fixedBox rho sigma hx
  have h0 : x 0 ∈ Icc (Real.sqrt 10/25) (5*Real.sqrt 2) := by
    simpa only [boxLo, boxHi, if_true] using hb 0
  have hlo : (25/8 : ℝ) ≤ Real.sqrt 10 := by
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 25/8) (Real.sqrt_nonneg _)).1
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
    norm_num
  have hhi : Real.sqrt 2 ≤ (3/2 : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 3/2)).1
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  constructor <;> nlinarith [h0.1,h0.2]

lemma chi_mul_actual (rho sigma : ℝ) (x : E4) :
    (chi (x 0) : ℂ) * normalizedF rho sigma x = normalizedF rho sigma x := by
  by_cases hx : normalizedF rho sigma x = 0
  · simp only [hx, mul_zero]
  · rw [chi_eq_one (actual_t_bounds hx), Complex.ofReal_one, one_mul]

def spectralMode (k : D4 → ℤ) (t : ℝ) : ℂ :=
  (chi t : ℂ) * e ((k 0 : ℝ)/64*t)

def spectralTest (k : D4 → ℤ) (Y0 q : ℝ) : ℂ := spectralMode k (q/Y0)

lemma spectralMode_contDiff (k : D4 → ℤ) : ContDiff ℝ ∞ (spectralMode k) := by
  apply ContDiff.mul
  · exact Complex.ofRealCLM.contDiff.comp chi_contDiff
  · dsimp [e]
    have hr : ContDiff ℝ ∞ (fun t : ℝ => (k 0 : ℝ) / 64 * t) :=
      contDiff_const.mul contDiff_id
    exact ((contDiff_const : ContDiff ℝ ∞
      (fun _ : ℝ => (2 * Real.pi * Complex.I : ℂ))).mul
        (Complex.ofRealCLM.contDiff.comp hr)).cexp

lemma spectralTest_contDiff (k : D4 → ℤ) (Y0 : ℝ) :
    ContDiff ℝ ∞ (spectralTest k Y0) := by
  exact (spectralMode_contDiff k).comp (contDiff_id.div_const Y0)

lemma spectralMode_support_subset (k : D4 → ℤ) :
    Function.support (spectralMode k) ⊆ Ioo (1/16 : ℝ) 16 := by
  intro t ht
  have hc : chi t ≠ 0 := by
    intro hn
    exact ht (by simp only [spectralMode, hn, Complex.ofReal_zero, zero_mul])
  exact chi_tsupport_subset (subset_closure hc)

/- GLOBAL in the spectral coordinate t. The other three normalized physical
   coordinates may be anywhere inside their period cell; the intended
   common dyadic ranges(1,2] are therefore included. -/
theorem actual_global_separation_hasSum (rho sigma : ℝ) (J0 : ℕ)
    (t v w z : ℝ)
    (hv : v ∈ Ioo (-32 : ℝ) 32)
    (hw : w ∈ Ioo (-32 : ℝ) 32)
    (hz : z ∈ Ioo (-32 : ℝ) 32) :
    HasSum (fun k : D4 → ℤ => actualCoeff rho sigma k *
      spectralMode k t * e ((k 1 : ℝ)/64*v) *
        e ((k 2 : ℝ)/64*w + (k 3 : ℝ)/64*z))
      (normalizedF rho sigma (point4 t v w z)) := by
  by_cases hchi : chi t = 0
  · have hfzero : normalizedF rho sigma (point4 t v w z) = 0 := by
      have hh := chi_mul_actual rho sigma (point4 t v w z)
      change (chi t : ℂ) * normalizedF rho sigma (point4 t v w z) =
        normalizedF rho sigma (point4 t v w z) at hh
      rw [hchi] at hh
      simpa only [Complex.ofReal_zero, zero_mul] using hh.symm
    simp [spectralMode, hchi, hfzero]
  · have ht : t ∈ Ioo (-32 : ℝ) 32 := by
      by_contra hn
      exact hchi (chi_zero_of_notMem hn)
    have hx : point4 t v w z ∈ inside64 := by
      intro i
      fin_cases i
      · exact ht
      · exact hv
      · exact hw
      · exact hz
    have h := actual_pointwise_hasSum rho sigma J0 (point4 t v w z) hx
    have hm := HasSum.mul_left (chi t : ℂ) h
    have hid : (chi t : ℂ) * normalizedF rho sigma (point4 t v w z) =
        normalizedF rho sigma (point4 t v w z) :=
      chi_mul_actual rho sigma (point4 t v w z)
    rw [hid] at hm
    apply hm.congr_fun
    intro k
    change actualCoeff rho sigma k *
        ((chi t : ℂ)*e ((k 0 : ℝ)/64*t)) *
        e ((k 1 : ℝ)/64*v) *
        e ((k 2 : ℝ)/64*w + (k 3 : ℝ)/64*z) =
      (chi t : ℂ) * (actualCoeff rho sigma k *
        (e ((k 0 : ℝ)/64*t) *
          (e ((k 1 : ℝ)/64*v) *
            (e ((k 2 : ℝ)/64*w) * e ((k 3 : ℝ)/64*z)))))
    rw [e_add]
    ring

/- EXACT COMMON INTERVAL / PHASE INTERFACE:
   commonMMode has no y,z,level or height argument.
   betaMode has no m or spectral-height argument.
   rho,sigma are frozen block parameters of actualCoeff. -/
def commonMMode (I : Set ℤ) (V : ℝ) (k : D4 → ℤ) (m : ℤ) : ℂ := by
  classical
  exact I.indicator (fun p : ℤ => e ((k 1 : ℝ)/64*((p : ℝ)/V))) m

def betaMode (beta : ℤ → ℤ → ℂ) (k : D4 → ℤ) (U Z : ℝ) (y z : ℤ) : ℂ :=
  beta y z * e ((k 2 : ℝ)/64*((y : ℝ)/U) + (k 3 : ℝ)/64*((z : ℝ)/Z))

lemma norm_betaMode (beta : ℤ → ℤ → ℂ) (k : D4 → ℤ) (U Z : ℝ) (y z : ℤ) :
    ‖betaMode beta k U Z y z‖ = ‖beta y z‖ := by
  simp only [betaMode, norm_mul, norm_e, mul_one]

lemma betaMode_finset_l2 (beta : ℤ → ℤ → ℂ) (k : D4 → ℤ) (U Z : ℝ)
    (S : Finset (ℤ × ℤ)) :
    (∑ p ∈ S, ‖betaMode beta k U Z p.1 p.2‖^2) =
      ∑ p ∈ S, ‖beta p.1 p.2‖^2 := by
  apply Finset.sum_congr rfl
  intro p _hp
  rw [norm_betaMode]

/- Pointwise common-packet separation. I can be the PREVIOUSLY chosen common
   I_V; no level-dependent interval is introduced by Fourier reconstruction.
   y,z,m remain integer arithmetic indices throughout. -/
theorem actual_common_packet_hasSum
    (rho sigma : ℝ) (J0 : ℕ) (I : Set ℤ) (beta : ℤ → ℤ → ℂ)
    (V U Z t : ℝ) (m y z : ℤ)
    (hmV : (m : ℝ)/V ∈ Ioo (-32 : ℝ) 32)
    (hyU : (y : ℝ)/U ∈ Ioo (-32 : ℝ) 32)
    (hzZ : (z : ℝ)/Z ∈ Ioo (-32 : ℝ) 32) :
    HasSum (fun k : D4 → ℤ => actualCoeff rho sigma k *
      spectralMode k t * commonMMode I V k m * betaMode beta k U Z y z)
      (I.indicator (fun p : ℤ => beta y z *
        normalizedF rho sigma (point4 t ((p : ℝ)/V) ((y : ℝ)/U) ((z : ℝ)/Z))) m) := by
  classical
  by_cases hm : m ∈ I
  · simp only [commonMMode, Set.indicator_of_mem hm]
    have h := actual_global_separation_hasSum rho sigma J0 t
      ((m : ℝ)/V) ((y : ℝ)/U) ((z : ℝ)/Z) hmV hyU hzZ
    apply (HasSum.mul_left (beta y z) h).congr_fun
    intro k
    dsimp [betaMode]
    ring
  · simp only [commonMMode, Set.indicator_of_notMem hm, mul_zero, zero_mul]
    exact hasSum_zero

lemma negative_original_m_phase (k : D4 → ℤ) (m : ℤ) (V : ℝ) :
    e ((k 1 : ℝ)/64*((-m : ℤ) : ℝ)/V) =
      e ((-(k 1 : ℝ)/64)*((m : ℝ)/V)) := by
  congr 1
  push_cast
  ring

end P3Period64NativeReconstructionSourceOnly

end

/-
STATUS / NON-CIRCULARITY / COST

* Four-coordinate torus continuity is proved from actual support geometry.
  The final map's temporary coordinate order is(zeta,w,v,t); the equality
  hEq explicitly returns it to the NATIVE order(t,v,w,zeta). No relabeling of
  the native frequency k : Fin4->Int occurs anywhere in the inverse.

* The exact coefficient remains
    actualCoeff(rho,sigma,k)=64^-4 * Fourier(actualF)(k/64).
  Fourier reconstruction is first proved on the fundamental cell, then
  actual chi*F=F supplies the all-t identity. chi is a real fixed smooth
  bump, and spectralMode(k,t)=chi(t)e(k0*t/64).

* The common m coefficient is exactly
    1_I(m)e((k1/64)*m/V),
  independent of level z and spectral height. The modulated beta is exactly
    beta(y,z)e((k2/64)*y/U+(k3/64)*z/Z),
  independent of future m and spectral height. Its pointwise norms, and
  hence every finite divisor-fibre L2 sum, are unchanged. For a negative
  original Fourier block, substituting p=-m gives theta=-k1/64, still common.

* The scalar test at actual height q is spectralTest(k,Y0,q)
    =chi(q/Y0)e(k0*q/(64*Y0)).
  Its derivatives through J0 have the previously accounted
  C_(chi,J0)(1+|k0|)^J0 cost. The weighted coefficient sum was proved in the
  previous lattice draft using r=4L, L=J0+3. Therefore reconstruction adds
  no new rho/x loss: the derivative-mass supplier alone is needed to turn
  that actual sum into O(x^(4L eta)), or O(x^(8L eta)) after squaring.
  No uniform-rho bound was assumed in any exact-reconstruction theorem here.
  The original 5*kappa phase fee is not paid a second time.

* This is an uncompiled source-only by-proof candidate, dependent on the
  listed source-only namespace declarations. It is not a typechecked Lean
  theorem and is not an end-to-end P3 spectral-input supplier. No error in
  the original smooth-Poisson mathematics is diagnosed here.
-/

