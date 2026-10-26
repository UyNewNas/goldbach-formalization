import ImbalancedChen.Part3ActualMaassFourierODE
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.
Native calculus takes the actual Fourier coefficient equation to the
modified-Bessel equation. The transform is h(q)=(q/a)^(-1/2)c(q/a),
so c(y)=sqrt(y)h(a*y). No Bessel equation or solution representation
of the transformed coefficient is assumed. Order may be complex.
-/

namespace ImbalancedChen.Part3.ActualFourierBesselConjugation20261026a
noncomputable section
open Set Filter
open scoped Topology
open ActualMaassFourierODE20261026a

def heightPower (p y : ℝ) : ℂ := (y ^ p : ℝ)
def normalizedHeight (c : ℝ → ℂ) (y : ℝ) : ℂ := heightPower (-1/2) y * c y
def normalizedFirst (c : ℝ → ℂ) (y : ℝ) : ℂ :=
  (-1/2 : ℂ) * heightPower (-3/2) y * c y + heightPower (-1/2) y * deriv c y
def normalizedSecond (c : ℝ → ℂ) (y : ℝ) : ℂ :=
  (3/4 : ℂ) * heightPower (-5/2) y * c y - heightPower (-3/2) y * deriv c y +
    heightPower (-1/2) y * deriv (deriv c) y

theorem heightPower_hasDerivAt (p : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (heightPower p) ((p : ℂ) * heightPower (p-1) y) y := by
  simpa only [heightPower, Complex.ofReal_mul] using
    (Real.hasDerivAt_rpow_const (x := y) (p := p) (Or.inl hy.ne')).ofReal_comp

theorem native_first {c : ℝ → ℂ} (hc : ContDiffOn ℝ 2 c (Ioi (0 : ℝ)))
    {y : ℝ} (hy : 0 < y) : HasDerivAt c (deriv c y) y :=
  ((hc.differentiableOn (by norm_num) y hy).differentiableAt (isOpen_Ioi.mem_nhds hy)).hasDerivAt

theorem native_second {c : ℝ → ℂ} (hc : ContDiffOn ℝ 2 c (Ioi (0 : ℝ)))
    {y : ℝ} (hy : 0 < y) : HasDerivAt (deriv c) (deriv (deriv c) y) y := by
  have hd : ContDiffOn ℝ 1 (deriv c) (Ioi (0 : ℝ)) :=
    hc.deriv_of_isOpen isOpen_Ioi (by norm_num)
  exact ((hd.differentiableOn (by norm_num) y hy).differentiableAt (isOpen_Ioi.mem_nhds hy)).hasDerivAt

theorem normalizedHeight_hasDerivAt {c : ℝ → ℂ} (hc : ContDiffOn ℝ 2 c (Ioi (0 : ℝ)))
    {y : ℝ} (hy : 0 < y) : HasDerivAt (normalizedHeight c) (normalizedFirst c y) y := by
  convert (heightPower_hasDerivAt (-1/2) hy).mul (native_first hc hy) using 1 <;>
    dsimp [normalizedHeight, normalizedFirst] <;> norm_num <;> ring

theorem normalizedFirst_hasDerivAt {c : ℝ → ℂ} (hc : ContDiffOn ℝ 2 c (Ioi (0 : ℝ)))
    {y : ℝ} (hy : 0 < y) : HasDerivAt (normalizedFirst c) (normalizedSecond c y) y := by
  have hA : HasDerivAt (fun t => (-1/2 : ℂ) * heightPower (-3/2) t)
      ((3/4 : ℂ) * heightPower (-5/2) y) y := by
    convert (heightPower_hasDerivAt (-3/2) hy).const_mul (-1/2 : ℂ) using 1 <;> norm_num <;> ring
  have hB : HasDerivAt (heightPower (-1/2)) ((-1/2 : ℂ) * heightPower (-3/2) y) y := by
    convert heightPower_hasDerivAt (-1/2) hy using 1 <;> norm_num
  convert (hA.mul (native_first hc hy)).add (hB.mul (native_second hc hy)) using 1 <;>
    dsimp [normalizedFirst, normalizedSecond] <;> ring

theorem normalizedHeight_native_second {c : ℝ → ℂ}
    (hc : ContDiffOn ℝ 2 c (Ioi (0 : ℝ))) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv (normalizedHeight c)) (normalizedSecond c y) y := by
  have heq : deriv (normalizedHeight c) =ᶠ[𝓝 y] normalizedFirst c := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
    exact (normalizedHeight_hasDerivAt hc ht).deriv
  exact (normalizedFirst_hasDerivAt hc hy).congr_of_eventuallyEq heq

theorem heightPower_shift_one {y : ℝ} (hy : 0 < y) :
    (y : ℂ) * heightPower (-3/2) y = heightPower (-1/2) y := by
  have hr : y * y ^ (-3/2 : ℝ) = y ^ (-1/2 : ℝ) := by
    rw [← Real.rpow_one y, ← Real.rpow_add hy]
    norm_num
  dsimp [heightPower]
  exact_mod_cast hr

theorem heightPower_shift_two {y : ℝ} (hy : 0 < y) :
    (y : ℂ)^2 * heightPower (-5/2) y = heightPower (-1/2) y := by
  have hr : y^2 * y ^ (-5/2 : ℝ) = y ^ (-1/2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hy]
    norm_num
  dsimp [heightPower]
  exact_mod_cast hr

/-- True square-root conjugation of the differential operator. -/
theorem normalizedHeight_bessel_equation {c : ℝ → ℂ}
    (hc : ContDiffOn ℝ 2 c (Ioi (0 : ℝ))) (a : ℝ) (nu : ℂ)
    {y : ℝ} (hy : 0 < y)
    (hODE : -(y : ℂ)^2 * (deriv (deriv c) y - (a : ℂ)^2*c y) =
      (1/4 - nu^2)*c y) :
    (y : ℂ)^2 * deriv (deriv (normalizedHeight c)) y +
      (y : ℂ)*deriv (normalizedHeight c) y -
      (((a : ℂ)*(y : ℂ))^2+nu^2)*normalizedHeight c y = 0 := by
  rw [(normalizedHeight_native_second hc hy).deriv, (normalizedHeight_hasDerivAt hc hy).deriv]
  dsimp [normalizedHeight, normalizedFirst, normalizedSecond]
  linear_combination -heightPower (-1/2) y * hODE +
    (3/4 : ℂ)*c y * heightPower_shift_two hy -
    ((y : ℂ)*deriv c y+(1/2 : ℂ)*c y) * heightPower_shift_one hy

def besselTransform (c : ℝ → ℂ) (a q : ℝ) : ℂ := normalizedHeight c (q/a)

theorem besselTransform_hasDerivAt {c : ℝ → ℂ}
    (hc : ContDiffOn ℝ 2 c (Ioi (0 : ℝ))) {a q : ℝ} (ha : 0 < a) (hq : 0 < q) :
    HasDerivAt (besselTransform c a) ((a : ℂ)⁻¹ * deriv (normalizedHeight c) (q/a)) q := by
  have hq' : 0 < q/a := div_pos hq ha
  have hg := normalizedHeight_hasDerivAt hc hq'
  rw [← hg.deriv] at hg
  convert hg.comp q ((hasDerivAt_id q).div_const a) using 1 <;>
    simp [besselTransform, Function.comp_def, Complex.real_smul, div_eq_mul_inv, mul_comm]

theorem besselTransform_native_second {c : ℝ → ℂ}
    (hc : ContDiffOn ℝ 2 c (Ioi (0 : ℝ))) {a q : ℝ} (ha : 0 < a) (hq : 0 < q) :
    HasDerivAt (deriv (besselTransform c a))
      ((a : ℂ)⁻¹^2 * deriv (deriv (normalizedHeight c)) (q/a)) q := by
  have hg := normalizedHeight_native_second hc (div_pos hq ha)
  rw [← hg.deriv] at hg
  have hd : HasDerivAt (fun t => (a : ℂ)⁻¹ * deriv (normalizedHeight c) (t/a))
      ((a : ℂ)⁻¹^2 * deriv (deriv (normalizedHeight c)) (q/a)) q := by
    convert (hg.comp q ((hasDerivAt_id q).div_const a)).const_mul (a : ℂ)⁻¹ using 1 <;>
      simp [Function.comp_def, Complex.real_smul, div_eq_mul_inv] <;> ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hq] with t ht
  exact (besselTransform_hasDerivAt hc ha ht).deriv

theorem besselTransform_equation {c : ℝ → ℂ}
    (hc : ContDiffOn ℝ 2 c (Ioi (0 : ℝ))) {a : ℝ} (ha : 0 < a) (nu : ℂ)
    (hODE : ∀ y : ℝ, 0 < y → -(y : ℂ)^2 * (deriv (deriv c) y - (a : ℂ)^2*c y) =
      (1/4 - nu^2)*c y) {q : ℝ} (hq : 0 < q) :
    (q : ℂ)^2 * deriv (deriv (besselTransform c a)) q +
      (q : ℂ)*deriv (besselTransform c a) q -
      ((q : ℂ)^2+nu^2)*besselTransform c a q = 0 := by
  have h := normalizedHeight_bessel_equation hc a nu (div_pos hq ha) (hODE _ (div_pos hq ha))
  rw [(besselTransform_native_second hc ha hq).deriv, (besselTransform_hasDerivAt hc ha hq).deriv]
  convert h using 1 <;>
    simp only [besselTransform, Complex.ofReal_div] <;>
    field_simp [Complex.ofReal_ne_zero.mpr ha.ne'] <;> ring

/-- Exact inverse identity, including the real positive square root. -/
theorem coefficient_recovery (c : ℝ → ℂ) {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    c y = (Real.sqrt y : ℂ) * besselTransform c a (a*y) := by
  have hp : (Real.sqrt y : ℂ) * heightPower (-1/2) y = 1 := by
    have hr : Real.sqrt y * y ^ (-1/2 : ℝ) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hy]
      norm_num
    dsimp [heightPower]
    exact_mod_cast hr
  rw [besselTransform, mul_div_cancel_left₀ _ ha.ne', normalizedHeight, ← mul_assoc, hp, one_mul]

def modeFrequency (n : ℤ) : ℝ := 2*Real.pi*|(n : ℝ)|
theorem modeFrequency_pos {n : ℤ} (hn : n ≠ 0) : 0 < modeFrequency n := by
  have hr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (abs_pos.mpr hr)

def actualBesselMode (u : ℝ × ℝ → ℂ) (n : ℤ) : ℝ → ℂ :=
  besselTransform (coefficient u n) (modeFrequency n)

/-- The actual Maass function supplies every native Bessel jet.
This is the primitive consumed by genuine I/K classification. -/
theorem actual_fourier_bessel_jet {u : ℝ × ℝ → ℂ}
    (hu : ContDiffOn ℝ 2 u upperDomain)
    (hp : ∀ x y : ℝ, 0 < y → u (x+1,y)=u(x,y)) (nu : ℂ)
    (hPDE : ∀ p ∈ upperDomain,
      -(p.2 : ℂ)^2*(partialX (partialX u) p+partialY (partialY u) p)=(1/4-nu^2)*u p)
    {n : ℤ} (hn : n ≠ 0) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (actualBesselMode u n) (deriv (actualBesselMode u n) q) q ∧
    HasDerivAt (deriv (actualBesselMode u n)) (deriv (deriv (actualBesselMode u n)) q) q ∧
    (q : ℂ)^2*deriv (deriv (actualBesselMode u n)) q+(q : ℂ)*deriv (actualBesselMode u n) q-
      ((q : ℂ)^2+nu^2)*actualBesselMode u n q=0 := by
  have hc := coefficient_contDiffOn_two hu n
  have ha := modeFrequency_pos hn
  have h1 := besselTransform_hasDerivAt hc ha hq
  have h2 := besselTransform_native_second hc ha hq
  refine ⟨?_, ?_, ?_⟩
  · change HasDerivAt (besselTransform (coefficient u n) (modeFrequency n))
      (deriv (besselTransform (coefficient u n) (modeFrequency n)) q) q
    rw [h1.deriv]
    exact h1
  · change HasDerivAt (deriv (besselTransform (coefficient u n) (modeFrequency n)))
      (deriv (deriv (besselTransform (coefficient u n) (modeFrequency n))) q) q
    rw [h2.deriv]
    exact h2
  ·
    apply besselTransform_equation hc ha nu
    · intro y hy
      have h := actual_coefficient_maass_ode hu hp (1/4-nu^2) hPDE n hy
      have hs : ((modeFrequency n : ℝ) : ℂ)^2 = ((2*Real.pi*(n : ℝ) : ℝ) : ℂ)^2 := by
        have hr : (modeFrequency n)^2 = (2*Real.pi*(n : ℝ))^2 := by
          simp only [modeFrequency, mul_pow, sq_abs]
        exact_mod_cast hr
      rw [hs]
      exact h
    · exact hq

end
end ImbalancedChen.Part3.ActualFourierBesselConjugation20261026a
