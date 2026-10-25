import ImbalancedChen.Part3RealEisensteinSeedConvergence
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
# Complex parameter analyticity of the actual primitive Eisenstein sum

SOURCE ONLY / UNCOMPILED / ZERO PROOF CREDIT (2026-10-25).

At fixed z in the actual upper half plane the positive base is
Im(z)/|c*z+d|^2. The complex-s summand is its literal exponential
exp(s*log(base)). Its norm is the previously proved real seed at Re(s).
A logarithmic factor is absorbed between two neighboring real exponents,
so the derivative series has a proved summable uniform majorant on every
bounded real-part slab strictly inside Re(s)>1.

This proves an actual first complex derivative of the primitive sum by
local uniform convergence of the derivative series, and holomorphy on
Re(s)>1. No spatial C2 chain, assumed uniform bound, analytic continuation,
Fourier expansion, functional equation, or spectral input is used.
-/

namespace ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic

noncomputable section

open Complex UpperHalfPlane EisensteinSeries Set Metric Topology
open scoped UpperHalfPlane
open ImbalancedChen.Part3.RealEisensteinSeedConvergence

abbrev PrimitivePair := EisensteinSeries.gammaSet 1 1 0

/-- The actual positive imaginary-part quotient for one primitive pair. -/
def positiveBase (z : ℍ) (v : PrimitivePair) : ℝ :=
  z.im / ‖(v.1 0 : ℂ) * (z : ℂ) + (v.1 1 : ℂ)‖ ^ 2

private theorem primitive_real_pair_nonzero (v : PrimitivePair) :
    (fun i : Fin 2 => (v.1 i : ℝ)) ≠ 0 := by
  intro h
  have h0r : (v.1 0 : ℝ) = 0 := congrFun h 0
  have h1r : (v.1 1 : ℝ) = 0 := congrFun h 1
  have h0 : v.1 0 = 0 := by exact_mod_cast h0r
  have h1 : v.1 1 = 0 := by exact_mod_cast h1r
  have hg : (v.1 0).gcd (v.1 1) = 1 := v.2.2
  simp [h0, h1] at hg

theorem positiveBase_pos (z : ℍ) (v : PrimitivePair) : 0 < positiveBase z v := by
  have hlin : (v.1 0 : ℂ) * (z : ℂ) + (v.1 1 : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_intCast] using
      UpperHalfPlane.linear_ne_zero z (primitive_real_pair_nonzero v)
  exact div_pos z.im_pos (sq_pos_of_pos (norm_pos_iff.mpr hlin))

/-- Exact bridge to the existing actual real seed, not a majorant-only
surrogate. -/
theorem positiveBase_rpow_eq_seed (t : ℝ) (z : ℍ) (v : PrimitivePair) :
    positiveBase z v ^ t = seed t z v.1 := by
  unfold positiveBase
  rw [Real.div_rpow z.im_pos.le (sq_nonneg _) t]
  have hpow : (‖(v.1 0 : ℂ) * (z : ℂ) + (v.1 1 : ℂ)‖ ^ 2) ^ t =
      ‖(v.1 0 : ℂ) * (z : ℂ) + (v.1 1 : ℂ)‖ ^ (2 * t) := by
    simpa only [Real.rpow_natCast] using
      (Real.rpow_mul (norm_nonneg ((v.1 0 : ℂ) * (z : ℂ) + (v.1 1 : ℂ))) 2 t).symm
  rw [hpow]
  exact (seed_eq_quotient t z v.1).symm

/-- The actual complex parameter seed. -/
def complexSeed (z : ℍ) (v : PrimitivePair) (s : ℂ) : ℂ :=
  Complex.exp (s * (Real.log (positiveBase z v) : ℂ))

def complexSeedDerivative (z : ℍ) (v : PrimitivePair) (s : ℂ) : ℂ :=
  (Real.log (positiveBase z v) : ℂ) * complexSeed z v s

theorem norm_complexSeed (z : ℍ) (v : PrimitivePair) (s : ℂ) :
    ‖complexSeed z v s‖ = positiveBase z v ^ s.re := by
  rw [complexSeed, Complex.norm_exp, Real.rpow_def_of_pos (positiveBase_pos z v)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  congr 1
  ring

theorem complexSeed_ofReal (z : ℍ) (v : PrimitivePair) (t : ℝ) :
    complexSeed z v (t : ℂ) = (seed t z v.1 : ℂ) := by
  rw [← positiveBase_rpow_eq_seed t z v, Real.rpow_def_of_pos (positiveBase_pos z v)]
  simp only [complexSeed, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  congr 2
  ring

theorem complexSeed_hasDerivAt (z : ℍ) (v : PrimitivePair) (s : ℂ) :
    HasDerivAt (complexSeed z v) (complexSeedDerivative z v s) s := by
  have h := (Complex.hasDerivAt_exp (s * (Real.log (positiveBase z v) : ℂ))).comp s
    ((hasDerivAt_id s).mul_const (Real.log (positiveBase z v) : ℂ))
  convert h using 1 <;> simp [complexSeed, complexSeedDerivative, mul_comm]

/-- A logarithmic derivative costs only a small neighboring real exponent.
Both q<=1 and q>=1 are covered, so no false global base<=1 claim is needed. -/
theorem abs_log_mul_rpow_le_neighbors
    {q epsilon a b t : ℝ} (hq : 0 < q) (hepsilon : 0 < epsilon)
    (hat : a ≤ t) (htb : t ≤ b) :
    |Real.log q| * q ^ t ≤ (q ^ (a - epsilon) + q ^ (b + epsilon)) / epsilon := by
  by_cases hq1 : q ≤ 1
  · have hlog : |Real.log q| * q ^ epsilon ≤ 1 / epsilon := by
      simpa only [abs_mul, abs_of_nonneg (Real.rpow_nonneg hq.le epsilon)] using
        (Real.abs_log_mul_self_rpow_lt q epsilon hq hq1 hepsilon).le
    have hpow : q ^ (t - epsilon) ≤ q ^ (a - epsilon) :=
      Real.rpow_le_rpow_of_exponent_ge hq hq1 (sub_le_sub_right hat epsilon)
    have hfactor : q ^ epsilon * q ^ (t - epsilon) = q ^ t := by
      rw [← Real.rpow_add hq]
      congr 1
      ring
    calc
      _ = (|Real.log q| * q ^ epsilon) * q ^ (t - epsilon) := by
        rw [mul_assoc, hfactor]
      _ ≤ (1 / epsilon) * q ^ (a - epsilon) :=
        mul_le_mul hlog hpow (Real.rpow_nonneg hq.le _)
          (div_nonneg zero_le_one hepsilon.le)
      _ = q ^ (a - epsilon) / epsilon := by ring
      _ ≤ (q ^ (a - epsilon) + q ^ (b + epsilon)) / epsilon :=
        div_le_div_of_nonneg_right
          (le_add_of_nonneg_right (Real.rpow_nonneg hq.le _)) hepsilon.le
  · have hqge : 1 ≤ q := (lt_of_not_ge hq1).le
    have hlog : |Real.log q| ≤ q ^ epsilon / epsilon := by
      rw [abs_of_nonneg (Real.log_nonneg hqge)]
      exact Real.log_le_rpow_div hq.le hepsilon
    calc
      _ ≤ (q ^ epsilon / epsilon) * q ^ t :=
        mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hq.le _)
      _ = q ^ (t + epsilon) / epsilon := by rw [Real.rpow_add hq]; ring
      _ ≤ q ^ (b + epsilon) / epsilon :=
        div_le_div_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hqge (add_le_add_right htb epsilon)) hepsilon.le
      _ ≤ (q ^ (a - epsilon) + q ^ (b + epsilon)) / epsilon :=
        div_le_div_of_nonneg_right
          (le_add_of_nonneg_left (Real.rpow_nonneg hq.le _)) hepsilon.le

/-- Absolute convergence of the actual complex seed at every Re(s)>1. -/
theorem complexSeed_summable (z : ℍ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun v : PrimitivePair => complexSeed z v s) := by
  apply Summable.of_norm_bounded (primitiveSeed_summable s.re hs z)
  intro v
  exact ((norm_complexSeed z v s).trans (positiveBase_rpow_eq_seed s.re z v)).le

/-- The actual complex seed has a two-endpoint majorant on each bounded
real-part slab, with no restriction that its positive base be below one. -/
theorem norm_complexSeed_le_endpoint_seeds
    (z : ℍ) (v : PrimitivePair) (a b : ℝ) (s : ℂ)
    (ha : a ≤ s.re) (hb : s.re ≤ b) :
    ‖complexSeed z v s‖ ≤ seed a z v.1 + seed b z v.1 := by
  rw [norm_complexSeed, ← positiveBase_rpow_eq_seed a z v, ← positiveBase_rpow_eq_seed b z v]
  by_cases hq : positiveBase z v ≤ 1
  · exact (Real.rpow_le_rpow_of_exponent_ge (positiveBase_pos z v) hq ha).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (positiveBase_pos z v).le _))
  · exact (Real.rpow_le_rpow_of_exponent_le (lt_of_not_ge hq).le hb).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg (positiveBase_pos z v).le _))

/-- Actual local uniform seed convergence in the complex parameter,
proved directly from the two convergent neighboring real seed families. -/
theorem complexSeed_tendstoUniformlyOn
    (z : ℍ) (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    TendstoUniformlyOn
      (fun F : Finset PrimitivePair => fun s : ℂ => ∑ v ∈ F, complexSeed z v s)
      (fun s : ℂ => ∑' v : PrimitivePair, complexSeed z v s) Filter.atTop
      {s : ℂ | a ≤ s.re ∧ s.re ≤ b} := by
  apply tendstoUniformlyOn_tsum
    ((primitiveSeed_summable a ha z).add (primitiveSeed_summable b hb z))
  intro v s hs
  exact norm_complexSeed_le_endpoint_seeds z v a b s hs.1 hs.2
/-- A fully supplied uniform derivative majorant on a bounded real-part
slab. The two real exponents remain in their actual convergence range. -/
theorem complexSeedDerivative_norm_le
    (z : ℍ) (a b epsilon : ℝ) (hepsilon : 0 < epsilon)
    (v : PrimitivePair) (s : ℂ) (ha : a ≤ s.re) (hb : s.re ≤ b) :
    ‖complexSeedDerivative z v s‖ ≤
      (seed (a - epsilon) z v.1 + seed (b + epsilon) z v.1) / epsilon := by
  calc
    _ = |Real.log (positiveBase z v)| * positiveBase z v ^ s.re := by
      simp only [complexSeedDerivative, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        norm_complexSeed]
    _ ≤ ((positiveBase z v) ^ (a - epsilon) + (positiveBase z v) ^ (b + epsilon)) / epsilon :=
      abs_log_mul_rpow_le_neighbors (positiveBase_pos z v) hepsilon ha hb
    _ = _ := by rw [positiveBase_rpow_eq_seed, positiveBase_rpow_eq_seed]

theorem derivativeMajorant_summable
    (z : ℍ) (a b epsilon : ℝ) (ha : 1 < a - epsilon) (hb : 1 < b + epsilon) :
    Summable (fun v : PrimitivePair =>
      (seed (a - epsilon) z v.1 + seed (b + epsilon) z v.1) / epsilon) :=
  ((primitiveSeed_summable (a - epsilon) ha z).add
    (primitiveSeed_summable (b + epsilon) hb z)).div_const epsilon

/-- Absolute convergence of the actual first parameter-derivative series
at every s in the initial half plane. -/
theorem complexSeedDerivative_summable (z : ℍ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun v : PrimitivePair => complexSeedDerivative z v s) := by
  let epsilon : ℝ := (s.re - 1) / 2
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; linarith
  have ha : 1 < s.re - epsilon := by dsimp [epsilon]; linarith
  have hb : 1 < s.re + epsilon := by dsimp [epsilon]; linarith
  apply Summable.of_norm_bounded (derivativeMajorant_summable z s.re s.re epsilon ha hb)
  intro v
  exact complexSeedDerivative_norm_le z s.re s.re epsilon hepsilon v s le_rfl le_rfl

/-- Genuine uniform convergence of the parameter-derivative series on
bounded real-part slabs inside the region of absolute convergence. -/
theorem complexSeedDerivative_tendstoUniformlyOn
    (z : ℍ) (a b epsilon : ℝ) (hepsilon : 0 < epsilon)
    (ha : 1 < a - epsilon) (hb : 1 < b + epsilon) :
    TendstoUniformlyOn
      (fun F : Finset PrimitivePair => fun s : ℂ => ∑ v ∈ F, complexSeedDerivative z v s)
      (fun s : ℂ => ∑' v : PrimitivePair, complexSeedDerivative z v s) Filter.atTop
      {s : ℂ | a ≤ s.re ∧ s.re ≤ b} := by
  apply tendstoUniformlyOn_tsum (derivativeMajorant_summable z a b epsilon ha hb)
  intro v s hs
  exact complexSeedDerivative_norm_le z a b epsilon hepsilon v s hs.1 hs.2

/-- The actual unnormalized primitive sum has its first complex derivative
at every s in Re(s)>1. A small complex ball supplies the proved uniform
summable derivative bound required for interchange. -/
theorem primitive_tsum_hasDerivAt_parameter
    (z : ℍ) (s : ℂ) (hs : 1 < s.re) :
    HasDerivAt (fun w : ℂ => ∑' v : PrimitivePair, complexSeed z v w)
      (∑' v : PrimitivePair, complexSeedDerivative z v s) s := by
  let r : ℝ := (s.re - 1) / 4
  let a : ℝ := s.re - r
  let b : ℝ := s.re + r
  have hr : 0 < r := by dsimp [r]; linarith
  have ha : 1 < a - r := by dsimp [a, r]; linarith
  have hb : 1 < b + r := by dsimp [b, r]; linarith
  let u : PrimitivePair → ℝ := fun v =>
    (seed (a - r) z v.1 + seed (b + r) z v.1) / r
  have hu : Summable u := derivativeMajorant_summable z a b r ha hb
  have hsball : s ∈ ball s r := mem_ball_self hr
  refine hasDerivAt_tsum_of_isPreconnected (u := u) (t := ball s r)
    hu isOpen_ball (convex_ball s r).isPreconnected
    (fun v w _hw => complexSeed_hasDerivAt z v w) ?_
    hsball (complexSeed_summable z s hs) hsball
  intro v w hw
  have hnorm : ‖w - s‖ < r := by simpa only [mem_ball, dist_eq_norm] using hw
  have hre0 : |w.re - s.re| ≤ ‖w - s‖ := by
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w - s)
  have hre : |w.re - s.re| ≤ r := hre0.trans hnorm.le
  obtain ⟨hl, hu⟩ := abs_le.mp hre
  exact complexSeedDerivative_norm_le z a b r hr v w
    (by dsimp [a]; linarith) (by dsimp [b]; linarith)

/-- The actual primitive complex Eisenstein series with classical 1/2
normalization for the two oriented representatives of each primitive pair. -/
def primitiveComplexEisenstein (s : ℂ) (z : ℍ) : ℂ :=
  (1 / 2 : ℂ) * ∑' v : PrimitivePair, complexSeed z v s

theorem primitiveComplexEisenstein_hasDerivAt
    (z : ℍ) (s : ℂ) (hs : 1 < s.re) :
    HasDerivAt (fun w : ℂ => primitiveComplexEisenstein w z)
      ((1 / 2 : ℂ) * ∑' v : PrimitivePair, complexSeedDerivative z v s) s :=
  (primitive_tsum_hasDerivAt_parameter z s hs).const_mul (1 / 2 : ℂ)

theorem primitiveComplexEisenstein_differentiableOn (z : ℍ) :
    DifferentiableOn ℂ (fun s => primitiveComplexEisenstein s z) {s : ℂ | 1 < s.re} := by
  intro s hs
  exact (primitiveComplexEisenstein_hasDerivAt z s hs).differentiableAt.differentiableWithinAt

/-- Holomorphy in the complex parameter on its actual initial half plane.
This states no continuation beyond Re(s)>1. -/
theorem primitiveComplexEisenstein_analyticOnNhd (z : ℍ) :
    AnalyticOnNhd ℂ (fun s => primitiveComplexEisenstein s z) {s : ℂ | 1 < s.re} :=
  (primitiveComplexEisenstein_differentiableOn z).analyticOnNhd
    (isOpen_Ioi.preimage Complex.continuous_re)

end

end ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic