import ImbalancedChen.Part3CuspLocalFourierCalculus
import ImbalancedChen.Part3ActualFourierBesselConjugation

/-!
# Genuine cusp-local square-root and frequency conjugation

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

All coefficient regularity is required only on y>Y, Y>=0. Native
square-root product rules and actual frequency scaling derive Bessel
jets only on q>aY. The actual periodic cusp-local Maass PDE supplies
these jets for every signed nonzero n with a=2*pi*|n|. There is no
continuation through the omitted lower cusp boundary. The n=0 physical
ODE is supplied by the preceding all-integer local calculus module.
-/

namespace ImbalancedChen.Part3.CuspLocalFourierBesselJets20261026b

noncomputable section
open Set Filter
open scoped Topology
open ActualMaassFourierODE20261026a ActualFourierBesselConjugation20261026a
open CuspLocalFourierCalculus20261026b

private theorem native_first_local {Y : ℝ} {c : ℝ → ℂ}
    (hc : ContDiffOn ℝ 2 c (Ioi Y)) {y : ℝ} (hy : Y<y) :
    HasDerivAt c (deriv c y) y :=
  ((hc.differentiableOn (by norm_num) y hy).differentiableAt (isOpen_Ioi.mem_nhds hy)).hasDerivAt

private theorem native_second_local {Y : ℝ} {c : ℝ → ℂ}
    (hc : ContDiffOn ℝ 2 c (Ioi Y)) {y : ℝ} (hy : Y<y) :
    HasDerivAt (deriv c) (deriv (deriv c) y) y := by
  have hd : ContDiffOn ℝ 1 (deriv c) (Ioi Y) := hc.deriv_of_isOpen isOpen_Ioi (by norm_num)
  exact ((hd.differentiableOn (by norm_num) y hy).differentiableAt (isOpen_Ioi.mem_nhds hy)).hasDerivAt

private theorem normalizedHeight_first_local {Y : ℝ} {c : ℝ → ℂ}
    (hc : ContDiffOn ℝ 2 c (Ioi Y)) (hY : 0≤Y) {y : ℝ} (hy : Y<y) :
    HasDerivAt (normalizedHeight c) (normalizedFirst c y) y := by
  have hy0 := hY.trans_lt hy
  convert (heightPower_hasDerivAt (-1/2) hy0).mul (native_first_local hc hy) using 1 <;>
    dsimp [normalizedHeight,normalizedFirst] <;> norm_num <;> ring

private theorem normalizedFirst_first_local {Y : ℝ} {c : ℝ → ℂ}
    (hc : ContDiffOn ℝ 2 c (Ioi Y)) (hY : 0≤Y) {y : ℝ} (hy : Y<y) :
    HasDerivAt (normalizedFirst c) (normalizedSecond c y) y := by
  have hy0 := hY.trans_lt hy
  have hA : HasDerivAt (fun t => (-1/2 : ℂ)*heightPower (-3/2) t)
      ((3/4 : ℂ)*heightPower (-5/2) y) y := by
    convert (heightPower_hasDerivAt (-3/2) hy0).const_mul (-1/2 : ℂ) using 1 <;> norm_num <;> ring
  have hB : HasDerivAt (heightPower (-1/2)) ((-1/2 : ℂ)*heightPower (-3/2) y) y := by
    convert heightPower_hasDerivAt (-1/2) hy0 using 1 <;> norm_num
  convert (hA.mul (native_first_local hc hy)).add (hB.mul (native_second_local hc hy)) using 1 <;>
    dsimp [normalizedFirst,normalizedSecond] <;> ring

private theorem normalizedHeight_second_local {Y : ℝ} {c : ℝ → ℂ}
    (hc : ContDiffOn ℝ 2 c (Ioi Y)) (hY : 0≤Y) {y : ℝ} (hy : Y<y) :
    HasDerivAt (deriv (normalizedHeight c)) (normalizedSecond c y) y := by
  have heq : deriv (normalizedHeight c)=ᶠ[𝓝 y] normalizedFirst c := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
    exact (normalizedHeight_first_local hc hY ht).deriv
  exact (normalizedFirst_first_local hc hY hy).congr_of_eventuallyEq heq

private theorem normalizedHeight_equation_local {Y : ℝ} {c : ℝ → ℂ}
    (hc : ContDiffOn ℝ 2 c (Ioi Y)) (hY : 0≤Y) (a : ℝ) (nu : ℂ)
    {y : ℝ} (hy : Y<y)
    (hODE : -(y : ℂ)^2*(deriv (deriv c) y-(a : ℂ)^2*c y)=(1/4-nu^2)*c y) :
    (y : ℂ)^2*deriv (deriv (normalizedHeight c)) y+
      (y : ℂ)*deriv (normalizedHeight c) y-
      (((a : ℂ)*(y : ℂ))^2+nu^2)*normalizedHeight c y=0 := by
  rw [(normalizedHeight_second_local hc hY hy).deriv,(normalizedHeight_first_local hc hY hy).deriv]
  dsimp [normalizedHeight,normalizedFirst,normalizedSecond]
  linear_combination -heightPower (-1/2) y*hODE+
    (3/4 : ℂ)*c y*heightPower_shift_two (hY.trans_lt hy)-
    ((y : ℂ)*deriv c y+(1/2 : ℂ)*c y)*heightPower_shift_one (hY.trans_lt hy)

theorem besselTransform_first_local {Y : ℝ} {c : ℝ → ℂ}
    (hc : ContDiffOn ℝ 2 c (Ioi Y)) (hY : 0≤Y) {a q : ℝ}
    (ha : 0<a) (hq : a*Y<q) :
    HasDerivAt (besselTransform c a) ((a : ℂ)⁻¹*deriv (normalizedHeight c) (q/a)) q := by
  have hqy : Y<q/a := (lt_div_iff₀ ha).mpr (by simpa only [mul_comm] using hq)
  have hg := normalizedHeight_first_local hc hY hqy
  rw [← hg.deriv] at hg
  convert hg.comp q ((hasDerivAt_id q).div_const a) using 1 <;>
    simp [besselTransform,Function.comp_def,Complex.real_smul,div_eq_mul_inv,mul_comm]

theorem besselTransform_second_local {Y : ℝ} {c : ℝ → ℂ}
    (hc : ContDiffOn ℝ 2 c (Ioi Y)) (hY : 0≤Y) {a q : ℝ}
    (ha : 0<a) (hq : a*Y<q) :
    HasDerivAt (deriv (besselTransform c a))
      ((a : ℂ)⁻¹^2*deriv (deriv (normalizedHeight c)) (q/a)) q := by
  have hqy : Y<q/a := (lt_div_iff₀ ha).mpr (by simpa only [mul_comm] using hq)
  have hg := normalizedHeight_second_local hc hY hqy
  rw [← hg.deriv] at hg
  have hd : HasDerivAt (fun t => (a : ℂ)⁻¹*deriv (normalizedHeight c) (t/a))
      ((a : ℂ)⁻¹^2*deriv (deriv (normalizedHeight c)) (q/a)) q := by
    convert (hg.comp q ((hasDerivAt_id q).div_const a)).const_mul (a : ℂ)⁻¹ using 1 <;>
      simp [Function.comp_def,Complex.real_smul,div_eq_mul_inv] <;> ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hq] with t ht
  exact (besselTransform_first_local hc hY ha ht).deriv

private theorem besselTransform_equation_local {Y : ℝ} {c : ℝ → ℂ}
    (hc : ContDiffOn ℝ 2 c (Ioi Y)) (hY : 0≤Y) {a : ℝ} (ha : 0<a) (nu : ℂ)
    (hODE : ∀ y : ℝ, Y<y → -(y : ℂ)^2*(deriv (deriv c) y-(a : ℂ)^2*c y)=
      (1/4-nu^2)*c y) {q : ℝ} (hq : a*Y<q) :
    (q : ℂ)^2*deriv (deriv (besselTransform c a)) q+
      (q : ℂ)*deriv (besselTransform c a) q-
      ((q : ℂ)^2+nu^2)*besselTransform c a q=0 := by
  have hqy : Y<q/a := (lt_div_iff₀ ha).mpr (by simpa only [mul_comm] using hq)
  have h := normalizedHeight_equation_local hc hY a nu hqy (hODE _ hqy)
  rw [(besselTransform_second_local hc hY ha hq).deriv,(besselTransform_first_local hc hY ha hq).deriv]
  convert h using 1 <;>
    simp only [besselTransform,Complex.ofReal_div] <;>
    field_simp [Complex.ofReal_ne_zero.mpr ha.ne'] <;> ring

/-- Every genuine cusp-local periodic C2 Maass function supplies native
Bessel jets only on the correct scaled open tail q>(2*pi*|n|)Y. -/
theorem actual_fourier_bessel_jet_local {Y : ℝ} {u : ℝ × ℝ → ℂ}
    (hY : 0≤Y) (hu : ContDiffOn ℝ 2 u (cuspDomain Y))
    (hp : ∀ x y : ℝ, Y<y → u (x+1,y)=u(x,y)) (nu : ℂ)
    (hPDE : ∀ p ∈ cuspDomain Y,
      -(p.2 : ℂ)^2*(partialX (partialX u) p+partialY (partialY u) p)=(1/4-nu^2)*u p)
    {n : ℤ} (hn : n≠0) {q : ℝ} (hq : modeFrequency n*Y<q) :
    HasDerivAt (actualBesselMode u n) (deriv (actualBesselMode u n) q) q ∧
      HasDerivAt (deriv (actualBesselMode u n)) (deriv (deriv (actualBesselMode u n)) q) q ∧
      (q : ℂ)^2*deriv (deriv (actualBesselMode u n)) q+
        (q : ℂ)*deriv (actualBesselMode u n) q-
        ((q : ℂ)^2+nu^2)*actualBesselMode u n q=0 := by
  have hc := coefficient_contDiffOn_two_local hu n
  have ha := modeFrequency_pos hn
  have h1 := besselTransform_first_local hc hY ha hq
  have h2 := besselTransform_second_local hc hY ha hq
  refine ⟨h1.differentiableAt.hasDerivAt,h2.differentiableAt.hasDerivAt,?_⟩
  apply besselTransform_equation_local hc hY ha nu
  · intro y hy
    have h := actual_coefficient_maass_ode_local hu hp (1/4-nu^2) hPDE n hy
    have hs : (modeFrequency n : ℂ)^2=((2*Real.pi*(n : ℝ) : ℝ) : ℂ)^2 := by
      have hr : (modeFrequency n)^2=(2*Real.pi*(n : ℝ))^2 := by
        simp only [modeFrequency,mul_pow,sq_abs]
      exact_mod_cast hr
    rw [hs]
    exact h
  · exact hq

end
end ImbalancedChen.Part3.CuspLocalFourierBesselJets20261026b
