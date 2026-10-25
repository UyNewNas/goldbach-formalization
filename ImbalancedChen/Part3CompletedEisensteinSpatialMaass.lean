import ImbalancedChen.Part3CompletedEisensteinCentralHeight
import ImbalancedChen.Part3CompletedEisensteinMeromorphic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-25. UNCOMPILED; NOT ROOT ACCEPTED.

The actual completed continued Fourier expression is C2 in the two real
spatial variables, and its literal negative hyperbolic Laplacian is
s(1-s) times the expression for s!=0,1. The theorem includes s=1/2.
At that parameter the actual dslope analytic-limit value, proved in the
preceding module, supplies the sqrt(y) log(y) correction.

The nonconstant kernel has already been differentiated under its infinite
sum using actual qMoment bounds and a genuine Frechet C2 proof. Here the
constant term is differentiated and the two proved eigenrelations are added.
No hC2, hODE, summed eigenrelation, or target spectral supplier is an input.
-/

namespace ImbalancedChen.Part3.CompletedEisensteinSpatialMaass

noncomputable section

open Set Filter Topology
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.ContinuedFourierMomentSeriesCalculus
open ImbalancedChen.Part3.ContinuedFourierNonconstantMaass
open ImbalancedChen.Part3.ContinuedFourierSpatialContDiffTwo
open ImbalancedChen.Part3.CompletedEisensteinCentralHeight

def heightFirst (p : ℂ) (y : ℝ) : ℂ := p * (y : ℂ) ^ (p - 1)
def heightSecond (p : ℂ) (y : ℝ) : ℂ := p * (p - 1) * (y : ℂ) ^ (p - 2)

theorem heightPower_hasDerivAt (p : ℂ) (hp : p ≠ 0) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ p) (heightFirst p y) y :=
  hasDerivAt_ofReal_cpow_const hy.ne' hp

theorem heightFirst_hasDerivAt (p : ℂ) (hp : p ≠ 1) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (heightFirst p) (heightSecond p y) y := by
  have h := (hasDerivAt_ofReal_cpow_const hy.ne' (sub_ne_zero.mpr hp)).const_mul p
  have he : p - 1 - 1 = p - 2 := by ring
  convert h using 1 <;> simp [heightFirst, heightSecond, he] <;> ring

theorem heightSecond_euler (p : ℂ) {y : ℝ} (hy : 0 < y) :
    -(y : ℂ) ^ 2 * heightSecond p y = p * (1 - p) * (y : ℂ) ^ p := by
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  unfold heightSecond
  rw [Complex.cpow_sub p 2 hyC, Complex.cpow_two]
  field_simp [hyC] <;> ring

/-- Smoothness of actual height powers on the positive chart, including
zero exponent, via their literal exp(log(y)*p) representation. -/
theorem heightPower_contDiffOn_two (p : ℂ) :
    ContDiffOn ℝ 2 (fun z : ℝ × ℝ => (z.2 : ℂ) ^ p) upperChart := by
  have hlogR : ContDiffOn ℝ 2 (fun z : ℝ × ℝ => Real.log z.2) upperChart :=
    contDiffOn_snd.log (fun z hz => ne_of_gt hz)
  have hlog : ContDiffOn ℝ 2 (fun z : ℝ × ℝ => (Real.log z.2 : ℂ)) upperChart :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hlogR
  apply (hlog.mul_const p).cexp.congr
  intro z hz
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)),
    ← Complex.ofReal_log (le_of_lt hz)]

def noncentralFirst (s : ℂ) (y : ℝ) : ℂ :=
  completedRiemannZeta (2 * s) * heightFirst s y +
    completedRiemannZeta (2 * s - 1) * heightFirst (1 - s) y

def noncentralSecond (s : ℂ) (y : ℝ) : ℂ :=
  completedRiemannZeta (2 * s) * heightSecond s y +
    completedRiemannZeta (2 * s - 1) * heightSecond (1 - s) y

def completedFirst (s : ℂ) (y : ℝ) : ℂ :=
  if s = 1 / 2 then centralFirst y else noncentralFirst s y

def completedSecond (s : ℂ) (y : ℝ) : ℂ :=
  if s = 1 / 2 then centralSecond y else noncentralSecond s y

theorem completedConstant_noncentral_hasDerivAt
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hshalf : s ≠ 1 / 2)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => completedConstant t s) (noncentralFirst s y) y := by
  have hq0 : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have heq : (fun t : ℝ => completedConstant t s) =
      (fun t => completedRiemannZeta (2 * s) * (t : ℂ) ^ s +
        completedRiemannZeta (2 * s - 1) * (t : ℂ) ^ (1 - s)) :=
    funext fun t => completedConstant_eq_raw t s hshalf
  rw [heq]
  exact ((heightPower_hasDerivAt s hs0 hy).const_mul (completedRiemannZeta (2 * s))).add
    ((heightPower_hasDerivAt (1 - s) hq0 hy).const_mul (completedRiemannZeta (2 * s - 1)))

theorem noncentralFirst_hasDerivAt
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (noncentralFirst s) (noncentralSecond s y) y := by
  have hq1 : 1 - s ≠ 1 := by
    intro h
    apply hs0
    linear_combination -h
  exact ((heightFirst_hasDerivAt s hs1 hy).const_mul (completedRiemannZeta (2 * s))).add
    ((heightFirst_hasDerivAt (1 - s) hq1 hy).const_mul (completedRiemannZeta (2 * s - 1)))

theorem completedConstant_hasDerivAt (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => completedConstant t s) (completedFirst s y) y := by
  by_cases hh : s = 1 / 2
  · subst s
    simpa only [completedFirst, if_true] using completedConstant_half_hasDerivAt hy
  · simpa only [completedFirst, if_neg hh] using
      completedConstant_noncentral_hasDerivAt s hs0 hs1 hh hy

theorem completedFirst_hasDerivAt (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (completedFirst s) (completedSecond s y) y := by
  by_cases hh : s = 1 / 2
  · subst s
    simpa only [completedFirst, completedSecond, if_true] using centralFirst_hasDerivAt hy
  · simpa only [completedFirst, completedSecond, if_neg hh] using
      noncentralFirst_hasDerivAt s hs0 hs1 hy

theorem completedConstant_second_y (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) :
    deriv (deriv (fun t : ℝ => completedConstant t s)) y = completedSecond s y := by
  have hevent : (fun t : ℝ => deriv (fun r : ℝ => completedConstant r s) t)
      =ᶠ[𝓝 y] completedFirst s := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (completedConstant_hasDerivAt s hs0 hs1 ht).deriv
  exact ((completedFirst_hasDerivAt s hs0 hs1 hy).congr_of_eventuallyEq hevent).deriv

/-- Both the raw noncentral powers and the actual central derivative value
have the same spatial Euler eigenvalue. -/
theorem completedConstant_euler (s : ℂ) {y : ℝ} (hy : 0 < y) :
    -(y : ℂ) ^ 2 * completedSecond s y = s * (1 - s) * completedConstant y s := by
  by_cases hh : s = 1 / 2
  · subst s
    have hc := centralHeight_euler hy
    rw [completedSecond, if_true, completedConstant_half y hy]
    convert hc using 1 <;> norm_num
  · rw [completedSecond, if_neg hh, completedConstant_eq_raw y s hh]
    unfold noncentralSecond
    have hp := heightSecond_euler s hy
    have hq := heightSecond_euler (1 - s) hy
    linear_combination completedRiemannZeta (2 * s) * hp +
      completedRiemannZeta (2 * s - 1) * hq

/-- True two-variable C2 of the completed constant, with its central
analytic-limit value retained. -/
theorem completedConstant_contDiffOn_two (s : ℂ) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => completedConstant p.2 s) upperChart := by
  by_cases hh : s = 1 / 2
  · subst s
    apply centralHeight_contDiffOn_two.congr
    intro p hp
    exact completedConstant_half p.2 hp
  · apply (((heightPower_contDiffOn_two s).const_mul (completedRiemannZeta (2 * s))).add
      ((heightPower_contDiffOn_two (1 - s)).const_mul (completedRiemannZeta (2 * s - 1)))).congr
    intro p hp
    exact completedConstant_eq_raw p.2 s hh

/-- Genuine C2 of the actual full completed continued Fourier expression. -/
theorem completedEisensteinFourier_contDiffOn_two (s : ℂ) :
    ContDiffOn ℝ 2
      (fun p : ℝ × ℝ => completedEisensteinFourier s p.2 p.1) upperChart := by
  simpa only [completedEisensteinFourier, weightedKernel] using
    (completedConstant_contDiffOn_two s).add (weightedKernel_contDiffOn_two s)

def completedFourierY (s : ℂ) (y x : ℝ) : ℂ :=
  completedFirst s y + weightedKernelY s y x

theorem completedFourier_hasDerivAt_y (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => completedEisensteinFourier s t x) (completedFourierY s y x) y :=
  (completedConstant_hasDerivAt s hs0 hs1 hy).add (weightedKernel_hasDerivAt_y s y x hy)

theorem completedFourier_second_x (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    deriv (deriv (fun t : ℝ => completedEisensteinFourier s y t)) x = weightedKernelXX s y x := by
  have hfirst : deriv (fun t : ℝ => completedEisensteinFourier s y t) =
      deriv (fun t : ℝ => weightedKernel s y t) := by
    funext t
    have hk := weightedKernel_hasDerivAt_x s y t hy
    exact (hk.const_add (completedConstant y s)).deriv.trans hk.deriv.symm
  rw [hfirst]
  exact weightedKernel_second_x s y x hy

theorem completedFourier_second_y (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (y x : ℝ) (hy : 0 < y) :
    deriv (deriv (fun t : ℝ => completedEisensteinFourier s t x)) y =
      completedSecond s y + weightedKernelYY s y x := by
  have hevent : (fun t : ℝ => deriv (fun r : ℝ => completedEisensteinFourier s r x) t)
      =ᶠ[𝓝 y] (fun t => completedFourierY s t x) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (completedFourier_hasDerivAt_y s hs0 hs1 t x ht).deriv
  have h := (completedFirst_hasDerivAt s hs0 hs1 hy).add
    (weightedKernelY_hasDerivAt_y s y x hy)
  exact (h.congr_of_eventuallyEq hevent).deriv

/-- The actual completed continued Fourier expression is a genuine Maass
eigenfunction off its two physical parameter poles, INCLUDING s=1/2. -/
theorem completedEisensteinFourier_maass_eigen
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (y x : ℝ) (hy : 0 < y) :
    maassLaplacian (fun p : ℝ × ℝ => completedEisensteinFourier s p.2 p.1) x y =
      s * (1 - s) * completedEisensteinFourier s y x := by
  change -(y : ℂ) ^ 2 *
    (deriv (deriv (fun t : ℝ => completedEisensteinFourier s y t)) x +
      deriv (deriv (fun t : ℝ => completedEisensteinFourier s t x)) y) = _
  rw [completedFourier_second_x s y x hy, completedFourier_second_y s hs0 hs1 y x hy]
  have hc := completedConstant_euler s hy
  have hk := weightedKernel_maass_eigen s y x hy
  change -(y : ℂ) ^ 2 *
    (deriv (deriv (fun t : ℝ => weightedKernel s y t)) x +
      deriv (deriv (fun t : ℝ => weightedKernel s t x)) y) = _ at hk
  rw [weightedKernel_second_x s y x hy, weightedKernel_second_y s y x hy] at hk
  change -(y : ℂ) ^ 2 * (weightedKernelXX s y x +
    (completedSecond s y + weightedKernelYY s y x)) =
      s * (1 - s) * (completedConstant y s + weightedKernel s y x)
  linear_combination hc + hk

/-- Caller on the actual upper half plane, retaining its positive imaginary part. -/
theorem completedEisensteinFourier_maass_eigen_upperHalfPlane
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (z : UpperHalfPlane) :
    maassLaplacian (fun p : ℝ × ℝ => completedEisensteinFourier s p.2 p.1) z.re z.im =
      s * (1 - s) * completedEisensteinFourier s z.im z.re :=
  completedEisensteinFourier_maass_eigen s hs0 hs1 z.im z.re z.im_pos

end

end ImbalancedChen.Part3.CompletedEisensteinSpatialMaass
