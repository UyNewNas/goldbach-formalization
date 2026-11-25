/-
SOURCE ONLY -- 2026-10-23. No Lean/lake/compiler/typechecker/CI was run.
Author: /root/p3_common_interval_phase_separation_sol_max_oct22.

ONE MAIN STEP: actual native 4D Fourier coefficient normalization.
This file defines a real period64 function ON UnitAddTorus(Fin4) from
canonical representatives. It proves, with full uncompiled `by` bodies,
  UnitAddTorus.mFourierCoeff (period64 f) k
    = ((64:Real)^4)^(-1) smul (Fourier f)(sampleFreq k),
  sampleFreq k=toLp2(fun i => (k_i:Real)/64),
for an ACTUAL function f:EuclideanSpace Real(Fin4)->Complex whose support
lies in the interior of the period64 box. No coefficient equality or
lattice-decay theorem is a premise. The Fourier transform is mathlib's
actual `Real.fourier_eq'` integral, not an invented spectral coefficient.

The coefficient equality does not require continuity of the torus
function. That continuity is a separate necessary input for the native
inverse. A genuine compact single-coordinate continuous lift is also
implemented below, using the proved liftIoc_continuous API. Four-coordinate
assembly and weighted lattice summability are not claimed complete here.

Fixed mathlib pin e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
Primary API read at this pin:
 AddCircleMulti.lean, blob08ab569e1977c455fdde0a67df2131ea1fc864c5:
   mFourier49--51, mFourierCoeff_eq_integral251--255,
   native pointwise inverse329--332.
 Topology/Instances/AddCircle/Defs.lean,
   blob961fd112f6bbe156fc2043e6a327b949c9b18536:
   equivIoc_coe_eq332--334, liftIoc_coe_apply376--378,
   liftIoc_continuous835--838, coe_zsmul205--206, coe_period224--225.
 Haar/InnerProductSpace.lean, blobec56bf802a75333ff66105c940eed9bf271fb6e1:
   EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp124--130.
 Haar/NormedSpace.lean, blobd50348a103a29f7340c390e50696ddefaaef9dd3:
   Measure.integral_comp_smul92--110.
 FourierTransform.lean, blob0c2af6da809eafe154d557010c742de2946e2173:
   Real.fourier_eq'438--440.
 Bochner/Set.lean, blob338ff3f267c912291cbf581e3cd3f2de78982a82:
   setIntegral_eq_integral_of_forall_compl_eq_zero489--491.
 Bochner/Basic.lean, blob5aab70490dd61ebcfaf9c50ef26dcb612c25091b:
   MeasurePreserving.integral_comp'1082--1084.
 PiL2.lean, bloba938a909f274d3e80ab0fdb44aa490022fd40d2d:
   PiLp.inner_apply103--105.
 PiLp.lean, blob6961e020117a12f4c823a0cd1d6ebe77931ccacc:
   smul_apply124--125; toLp_apply139.

PoissonSummation.lean was checked first: its proved Fourier coefficient
of a translated-periodization theorem52--100 is ONE-DIMENSIONAL. It is
not a ready-made 4D normalization theorem. The native mFourierCoeff box
integral plus the Haar-scaling API closes the actual 4D step directly,
without creating an arbitrary masked DFT or a new analytic assumption.
-/

import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.CompactOpen
import Mathlib.Tactic

noncomputable section

open Set MeasureTheory
open scoped BigOperators FourierTransform RealInnerProductSpace

namespace P3NativePeriod64SamplingSourceOnly

abbrev D4 := Fin 4
abbrev R4 := D4 → ℝ
abbrev E4 := EuclideanSpace ℝ D4
abbrev T4 := UnitAddTorus D4

def unitBox : Set R4 :=
  {x | ∀ i, x i ∈ Ioc (-1/2 : ℝ) ((-1/2 : ℝ)+1)}

def inside64 : Set E4 := {y | ∀ i, y i ∈ Ioo (-32 : ℝ) 32}

def rep (z : T4) : R4 :=
  fun i => ((AddCircle.equivIoc (1 : ℝ) (-1/2 : ℝ)) (z i)).1

def period64 (f : E4 → ℂ) (z : T4) : ℂ := f ((64 : ℝ) • WithLp.toLp 2 (rep z))

def sampleFreq (k : D4 → ℤ) : E4 := WithLp.toLp 2 (fun i => (k i : ℝ)/64)

def ftKernel (f : E4 → ℂ) (k : D4 → ℤ) (y : E4) : ℂ :=
  Complex.exp (((-2*Real.pi*⟪y, sampleFreq k⟫ : ℝ) : ℂ)*Complex.I) * f y

lemma measurableSet_unitBox : MeasurableSet unitBox := by
  exact MeasurableSet.univ_pi' (fun _i : D4 => measurableSet_Ioc)

lemma rep_coe (x : R4) (hx : x ∈ unitBox) :
    rep (fun i => (x i : UnitAddCircle)) = x := by
  funext i
  exact congrArg Subtype.val
    (AddCircle.equivIoc_coe_eq (p := (1 : ℝ)) (a := (-1/2 : ℝ)) (hx i))

lemma period64_coe (f : E4 → ℂ) (x : R4) (hx : x ∈ unitBox) :
    period64 f (fun i => (x i : UnitAddCircle)) = f ((64 : ℝ) • WithLp.toLp 2 x) := by
  rw [period64, rep_coe x hx]

lemma period64_eval_inside (f : E4 → ℂ) (y : E4) (hy : y ∈ inside64) :
    period64 f (fun i => ((y i / 64 : ℝ) : UnitAddCircle)) = f y := by
  let x : R4 := fun i => y i / 64
  have hx : x ∈ unitBox := by
    intro i
    change (y i / 64 : ℝ) ∈ Ioc (-1/2 : ℝ) ((-1/2 : ℝ)+1)
    constructor <;> nlinarith [(hy i).1, (hy i).2]
  have hscale : (64 : ℝ) • WithLp.toLp 2 x = y := by
    apply PiLp.ext
    intro i
    simp only [PiLp.smul_apply, smul_eq_mul, x]
    ring
  change period64 f (fun i => (x i : UnitAddCircle)) = f y
  rw [period64_coe f x hx, hscale]

lemma unit_int_cast_eq_zero (n : ℤ) : ((n : ℝ) : UnitAddCircle) = 0 := by
  have h := AddCircle.coe_zsmul (p := (1 : ℝ)) (n := n) (x := (1 : ℝ))
  simpa only [zsmul_eq_mul, mul_one, AddCircle.coe_period, smul_zero] using h

/- A function on the native torus is really periodic when pulled back;
   this is proved for the actual period64 definition, with no periodicity
   premise on f. Translating physical coordinates by64 corresponds to
   translating normalized real coordinates by an integer. -/
lemma period64_pullback_int (f : E4 → ℂ) (x : R4) (n : D4 → ℤ) :
    period64 f (fun i => ((x i + (n i : ℝ) : ℝ) : UnitAddCircle)) =
      period64 f (fun i => (x i : UnitAddCircle)) := by
  apply congrArg (period64 f)
  funext i
  rw [AddCircle.coe_add, unit_int_cast_eq_zero, add_zero]

lemma scaled_inner_sample (x : R4) (k : D4 → ℤ) :
    ⟪(64 : ℝ) • WithLp.toLp 2 x, sampleFreq k⟫ = ∑ i, (k i : ℝ)*x i := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [sampleFreq, PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul,
    Real.inner_apply]
  ring

lemma native_character_scaled (x : R4) (k : D4 → ℤ) :
    UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) =
      Complex.exp (((-2*Real.pi*
        ⟪(64 : ℝ) • WithLp.toLp 2 x, sampleFreq k⟫ : ℝ) : ℂ)*Complex.I) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply,
    fourier_coe_apply]
  rw [← Complex.exp_sum, scaled_inner_sample]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

lemma native_integrand_scaled (f : E4 → ℂ) (x : R4) (k : D4 → ℤ) :
    UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) *
      f ((64 : ℝ) • WithLp.toLp 2 x) = ftKernel f k ((64 : ℝ) • WithLp.toLp 2 x) := by
  rw [native_character_scaled]
  rfl

/- This is a support argument about the actual f, not an assumption
   that the completed integrand already vanishes outside a chosen box. -/
lemma scaled_zero_off_unitBox (f : E4 → ℂ)
    (hs : Function.support f ⊆ inside64) (x : R4) (hx : x ∉ unitBox) :
    f ((64 : ℝ) • WithLp.toLp 2 x) = 0 := by
  by_contra hn
  apply hx
  intro i
  have hi := (hs hn) i
  simp only [PiLp.smul_apply, smul_eq_mul] at hi
  constructor <;> nlinarith [hi.1, hi.2]

lemma kernel_zero_off_unitBox (f : E4 → ℂ)
    (hs : Function.support f ⊆ inside64) (k : D4 → ℤ)
    (x : R4) (hx : x ∉ unitBox) :
    ftKernel f k ((64 : ℝ) • WithLp.toLp 2 x) = 0 := by
  rw [ftKernel, scaled_zero_off_unitBox f hs x hx, mul_zero]

lemma native_coeff_eq_unitBox_integral (f : E4 → ℂ) (k : D4 → ℤ) :
    UnitAddTorus.mFourierCoeff (period64 f) k =
      ∫ x : R4 in unitBox,
        UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) *
          f ((64 : ℝ) • WithLp.toLp 2 x) := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral (period64 f) k (fun _ : D4 => (-1/2 : ℝ))]
  apply setIntegral_congr_fun measurableSet_unitBox
  intro x hx
  change UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) *
      period64 f (fun i => (x i : UnitAddCircle)) =
    UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) *
      f ((64 : ℝ) • WithLp.toLp 2 x)
  rw [period64_coe f x hx]

lemma integral_ftKernel_eq_fourier (f : E4 → ℂ) (k : D4 → ℤ) :
    (∫ y : E4, ftKernel f k y) = 𝓕 f (sampleFreq k) := by
  rw [Real.fourier_eq']
  rfl

/- Both conversion maps below are existing MEASURE-PRESERVING maps.
   Hence there is no hidden dimension-dependent normalization beyond64^-4. -/
lemma scaled_kernel_integral (f : E4 → ℂ) (k : D4 → ℤ) :
    (∫ x : R4, ftKernel f k ((64 : ℝ) • WithLp.toLp 2 x)) =
      ((64 : ℝ)^4)⁻¹ • 𝓕 f (sampleFreq k) := by
  have hLp :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp D4).symm.integral_comp'
      (fun y : E4 => ftKernel f k ((64 : ℝ) • y))
  calc
    (∫ x : R4, ftKernel f k ((64 : ℝ) • WithLp.toLp 2 x)) =
        ∫ y : E4, ftKernel f k ((64 : ℝ) • y) := by
      simpa only [MeasurableEquiv.symm_symm, MeasurableEquiv.coe_toLp] using hLp
    _ = ((64 : ℝ)^4)⁻¹ • ∫ y : E4, ftKernel f k y := by
      have hs := Measure.integral_comp_smul (volume : Measure E4) (ftKernel f k) (64 : ℝ)
      norm_num [finrank_euclideanSpace] at hs ⊢
      exact hs
    _ = ((64 : ℝ)^4)⁻¹ • 𝓕 f (sampleFreq k) := by
      rw [integral_ftKernel_eq_fourier]

/- MAIN ACTUAL COEFFICIENT NORMALIZATION. f is the real Euclidean-space
   function; actual mathlib Fourier transform appears on the right.
   Coefficient normalization and lattice decay are NOT premises. -/
theorem native_period64_fourier_sample
    (f : E4 → ℂ) (hs : Function.support f ⊆ inside64) (k : D4 → ℤ) :
    UnitAddTorus.mFourierCoeff (period64 f) k =
      ((64 : ℝ)^4)⁻¹ • 𝓕 f (sampleFreq k) := by
  calc
    UnitAddTorus.mFourierCoeff (period64 f) k =
        ∫ x : R4 in unitBox,
          UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) *
            f ((64 : ℝ) • WithLp.toLp 2 x) := native_coeff_eq_unitBox_integral f k
    _ = ∫ x : R4 in unitBox, ftKernel f k ((64 : ℝ) • WithLp.toLp 2 x) := by
      apply setIntegral_congr_fun measurableSet_unitBox
      intro x _hx
      exact native_integrand_scaled f x k
    _ = ∫ x : R4, ftKernel f k ((64 : ℝ) • WithLp.toLp 2 x) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => kernel_zero_off_unitBox f hs k x hx)
    _ = ((64 : ℝ)^4)⁻¹ • 𝓕 f (sampleFreq k) := scaled_kernel_integral f k

/- A genuine compact-coordinate CONTINUOUS periodization primitive.
   Its input is an actual jointly continuous G and actual coordinate
   support; endpoint matching and continuity of the lift are proved.
   Y can be a product of remaining real coordinates and already-lifted
   circle coordinates; local compactness permits uncurrying afterwards. -/
section ContinuousCoordinate

variable {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y]

def liftCoord64 (G : C(ℝ × Y, ℂ))
    (hs : ∀ t y, t ∉ Ioo (-32 : ℝ) 32 → G (t,y) = 0) :
    C(UnitAddCircle, C(Y, ℂ)) := by
  let H : C(ℝ, C(Y, ℂ)) := G.curry.comp
    ⟨fun t : ℝ => (64 : ℝ)*t, by fun_prop⟩
  refine ⟨AddCircle.liftIoc (1 : ℝ) (-1/2 : ℝ) H, ?_⟩
  apply AddCircle.liftIoc_continuous
  · ext y
    change G ((64 : ℝ)*(-1/2), y) = G ((64 : ℝ)*((-1/2)+1), y)
    norm_num
    rw [hs (-32) y (by simp), hs 32 y (by simp)]
  · exact H.continuous.continuousOn

omit [LocallyCompactSpace Y] in
lemma liftCoord64_coe [LocallyCompactSpace Y] (G : C(ℝ × Y, ℂ))
    (hs : ∀ t y, t ∉ Ioo (-32 : ℝ) 32 → G (t,y) = 0)
    (x : ℝ) (hx : x ∈ Ioc (-1/2 : ℝ) ((-1/2 : ℝ)+1)) (y : Y) :
    liftCoord64 G hs (x : UnitAddCircle) y = G ((64 : ℝ)*x,y) := by
  change AddCircle.liftIoc (1 : ℝ) (-1/2 : ℝ)
    (G.curry.comp ⟨fun t : ℝ => (64 : ℝ)*t, by fun_prop⟩)
      (x : UnitAddCircle) y = G ((64 : ℝ)*x,y)
  rw [AddCircle.liftIoc_coe_apply hx]
  rfl

lemma continuous_liftCoord64_uncurry (G : C(ℝ × Y, ℂ))
    (hs : ∀ t y, t ∉ Ioo (-32 : ℝ) 32 → G (t,y) = 0) :
    Continuous (fun p : UnitAddCircle × Y => liftCoord64 G hs p.1 p.2) := by
  exact (liftCoord64 G hs).uncurry.continuous

end ContinuousCoordinate

end P3NativePeriod64SamplingSourceOnly

/-
STATUS AND EXACT NEXT BOUNDARY

The theorem native_period64_fourier_sample closes the actual coefficient
sample normalization as mathematics-in-Lean-source, with no unknown
coefficient equality, no Fourier-tail estimate, and no spectral input.
The support condition is directly geometric; the actual normalized F
from the original route has its support in the fixed positive box well
inside(-32,32)^4. The Euclidean toLp conversion preserves volume exactly.

The native inverse needs a bundled continuous period64 f and summable
native coefficients. This file does NOT assume those outputs and wrap
the inverse as if that closed the problem. It implements the continuous
one-coordinate lifting step, but does NOT yet write the complete four-
coordinate permutation/assembly proof identifying that bundle with the
canonical period64 above. It also does NOT assert unknown lattice decay.

The preceding compact-coordinate draft already gives the real multi-
dimensional derivative-integral Fourier bound at r=4L, using a proved
fixed native theorem. After the coefficient equality proved HERE, the
remaining quantitative specialization is to bound the actual derivative
integrals by the fixed support volume times the actual C^(4L) seminorm,
then sum the resulting sampled decay on Z^4 with the |kt|^J0 weight.
This is a definite lattice comparison / summability proof still to write,
not a new assumption one may insert into a claimed closed supplier.

The actual normalized F zero-extension smoothness and finite derivative
bound also remain to be written in Lean. Its variable substitution has
already removed a exactly; none of these normalizations introduces a.
The 4L eta unsquared and8L eta squared budget remains unchanged, and the
previous 5kappa phase payment is not repeated. Fourier modes still have
common m interval I_V, phase e((km/64)p/V), and beta^k(y,z) independent
of p or spectral height. Only this new TXT was written. STOP.
-/

end
