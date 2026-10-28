import Mathlib
import ImbalancedChen.Part3PrimeMellinProfileVariation
import ImbalancedChen.Part3TwoLongFixedMRectangularCore
import ImbalancedChen.P5ActualHBDyadicProductWindow

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The manuscript's two-long profiles have support [1/2,5/2], not [1,2].
The latter interval is the rectangle on which the cutoff is ONE. A smooth
cutoff supported in [1,2] cannot equal one at both rectangle endpoints.
This module constructs the correct literal Mellin modes rather than
assuming an arbitrary separable Mode. It proves a fixed quadratic N2
frequency payment and an exact same-mean rectangular core.

The all-rank Family-to-Fourier inversion binding and the fixed-m P1/P2
primitive are not conclusions of this module.
-/

namespace ImbalancedChen.Part3.TwoLongLiteralMellinModes

noncomputable section
open Classical Set Filter MeasureTheory
open scoped BigOperators Topology
open ImbalancedChen.Part3.TwoLongFixedMRectangularCore
open ImbalancedChen.Part3.PrimeMellinProfileVariation20261026b

/-- A fixed smooth cutoff with room on BOTH sides of the dyadic interval. -/
def dyadicBump : ContDiffBump (3 / 2 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def cutoff (x : ℝ) : ℝ := dyadicBump x

theorem cutoff_smooth : ContDiff ℝ ∞ cutoff := dyadicBump.contDiff

theorem cutoff_nonneg (x : ℝ) : 0 ≤ cutoff x := dyadicBump.nonneg

theorem cutoff_le_one (x : ℝ) : cutoff x ≤ 1 := dyadicBump.le_one

theorem cutoff_one {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) : cutoff x = 1 := by
  apply dyadicBump.one_of_mem_closedBall
  change dist x (3 / 2 : ℝ) ≤ 1 / 2
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [hx.1, hx.2]

theorem cutoff_support : Function.support cutoff ⊆ Icc (1 / 2 : ℝ) (5 / 2) := by
  intro x hx
  have hball : x ∈ Metric.ball (3 / 2 : ℝ) 1 := by
    change x ∈ Function.support dyadicBump at hx
    rw [dyadicBump.support_eq] at hx
    exact hx
  have ha : |x - 3 / 2| < (1 : ℝ) := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hball
  have h := abs_lt.mp ha
  constructor <;> linarith [h.1, h.2]

theorem cutoff_compact : HasCompactSupport cutoff := dyadicBump.hasCompactSupport

/-- No additional analytic bump assumption: the q-independent mode uses
this actual fixed cutoff and the manuscript's literal logarithmic phase. -/
def twist (t x : ℝ) : ℂ := (cutoff x : ℂ) * phase t x

theorem twist_norm (t x : ℝ) : ‖twist t x‖ = cutoff x := by
  rw [twist, norm_mul, phase_norm, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg x)]

theorem twist_support (t : ℝ) :
    Function.support (twist t) ⊆ Icc (1 / 2 : ℝ) (5 / 2) := by
  intro x hx
  apply cutoff_support
  intro hc
  exact hx (by simp [twist, hc])

theorem twist_compact (t : ℝ) : HasCompactSupport (twist t) := by
  change IsCompact (closure (Function.support (twist t)))
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal (twist_support t) isClosed_Icc)

/-- The singularity of log at zero is outside the cutoff support. Its
absence is proved locally, not bypassed by differentiating through zero. -/
theorem twist_smooth (t : ℝ) : ContDiff ℝ ∞ (twist t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have heq : twist t =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℂ)) := by
      filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)] with y hy
      have hc : cutoff y = 0 := by
        by_contra hn
        have hs := cutoff_support hn
        linarith [hs.1]
      simp [twist, hc]
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℂ)) 0).
      congr_of_eventuallyEq heq
  · have hl : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.mpr hx
    have hc : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hl
    have hp := (hc.const_mul (Complex.I * (t : ℂ))).cexp
    exact (Complex.ofRealCLM.contDiff.comp cutoff_smooth).contDiffAt.mul hp

theorem twist_on_dyadic (t : ℝ) {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    twist t x = phase t x := by simp [twist, cutoff_one hx]

/-- First and second derivatives of the FIXED bump, independent of t,q,U,V. -/
def bumpD1 : ℝ → ℝ := deriv cutoff
def bumpD2 : ℝ → ℝ := deriv (deriv cutoff)

theorem bumpD1_smooth : ContDiff ℝ ∞ bumpD1 :=
  (contDiff_infty_iff_deriv.mp cutoff_smooth).2

theorem bumpD2_smooth : ContDiff ℝ ∞ bumpD2 :=
  (contDiff_infty_iff_deriv.mp bumpD1_smooth).2

theorem bumpD1_compact : HasCompactSupport bumpD1 := cutoff_compact.deriv

theorem bumpD2_compact : HasCompactSupport bumpD2 := bumpD1_compact.deriv

def firstJet (t x : ℝ) : ℂ :=
  ((bumpD1 x : ℂ) + (cutoff x : ℂ) * (Complex.I * (t : ℂ)) / (x : ℂ)) *
    phase t x

theorem twist_hasDerivAt (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (twist t) (firstJet t x) x := by
  have hd := cutoff_smooth.differentiable (by norm_num)
  convert ((hd x).hasDerivAt.ofReal_comp).mul (phase_hasDerivAt t hx) using 1 <;>
    simp only [twist, firstJet, bumpD1] <;> ring

/-- The literal second derivative, before taking absolute values. -/
def secondJet (t x : ℝ) : ℂ :=
  phase t x * ((bumpD2 x : ℂ) +
    2 * (bumpD1 x : ℂ) * (Complex.I * (t : ℂ)) / (x : ℂ) +
    (cutoff x : ℂ) * ((Complex.I * (t : ℂ)) ^ 2 - Complex.I * (t : ℂ)) /
      (x : ℂ) ^ 2)

theorem twist_secondDeriv (t : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (deriv (twist t)) x = secondJet t x := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hd0 := (cutoff_smooth.differentiable (by norm_num) x).hasDerivAt
  have hd1 := (bumpD1_smooth.differentiable (by norm_num) x).hasDerivAt
  have hi : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x :=
    (hasDerivAt_id x).ofReal_comp
  have hquot := ((hd0.ofReal_comp).const_mul (Complex.I * (t : ℂ))).div hi hxC
  have ha := hd1.ofReal_comp.add hquot
  have hp := ha.mul (phase_hasDerivAt t hx)
  have heq : deriv (twist t) =ᶠ[𝓝 x] firstJet t := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (twist_hasDerivAt t hy).deriv
  have hp' : HasDerivAt (firstJet t) (secondJet t x) x := by
    convert hp using 1 <;>
      simp only [firstJet, secondJet, bumpD1, bumpD2] <;>
      field_simp [hxC] <;> ring
  exact (hp'.congr_of_eventuallyEq heq).deriv

/-- Quantitative local second-derivative bound. The factors 4 are the
fixed costs of x^-1<=2 and x^-2<=4 on the CORRECT support interval. -/
theorem secondJet_norm_le (t : ℝ) {x : ℝ}
    (hx : x ∈ Icc (1 / 2 : ℝ) (5 / 2)) :
    ‖secondJet t x‖ ≤ |bumpD2 x| + 4 * |bumpD1 x| * |t| +
      4 * cutoff x * (|t| ^ 2 + |t|) := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hrec : 1 / x ≤ 2 := (div_le_iff₀ hx0).2 (by linarith [hx.1])
  have hrec2 : 1 / x ^ 2 ≤ 4 := by
    apply (div_le_iff₀ (pow_pos hx0 2)).2
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hc : ‖Complex.I * (t : ℂ)‖ = |t| := by simp
  have hcc : ‖(Complex.I * (t : ℂ)) ^ 2 - Complex.I * (t : ℂ)‖ ≤
      |t| ^ 2 + |t| := by
    calc
      _ ≤ ‖(Complex.I * (t : ℂ)) ^ 2‖ + ‖Complex.I * (t : ℂ)‖ := norm_sub_le _ _
      _ = _ := by rw [norm_pow, hc]
  rw [secondJet, norm_mul, phase_norm, one_mul]
  calc
    _ ≤ ‖(bumpD2 x : ℂ)‖ +
        ‖2 * (bumpD1 x : ℂ) * (Complex.I * (t : ℂ)) / (x : ℂ)‖ +
        ‖(cutoff x : ℂ) * ((Complex.I * (t : ℂ)) ^ 2 - Complex.I * (t : ℂ)) /
          (x : ℂ) ^ 2‖ := (norm_add_le _ _).trans
            (add_le_add_right (norm_add_le _ _) _)
    _ ≤ |bumpD2 x| + (2 * |bumpD1 x| * |t|) / x +
        cutoff x * (|t| ^ 2 + |t|) / x ^ 2 := by
      simp only [norm_div, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, norm_ofNat, hc, abs_of_pos hx0,
        abs_of_nonneg (cutoff_nonneg x)]
      gcongr
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_left hrec
        (by positivity : 0 ≤ 2 * |bumpD1 x| * |t|)
      have h2 := mul_le_mul_of_nonneg_left hrec2
        (mul_nonneg (cutoff_nonneg x) (by positivity : 0 ≤ |t| ^ 2 + |t|))
      simp only [div_eq_mul_inv, one_div] at h1 h2 ⊢
      nlinarith

/-- This is a GLOBAL derivative bound, including zero and the cutoff joins. -/
theorem twist_second_norm_le (t x : ℝ) :
    ‖deriv (deriv (twist t)) x‖ ≤ |bumpD2 x| + 4 * |bumpD1 x| * |t| +
      4 * cutoff x * (|t| ^ 2 + |t|) := by
  by_cases hx : x ∈ Icc (1 / 2 : ℝ) (5 / 2)
  · rw [twist_secondDeriv t (by linarith [hx.1])]
    exact secondJet_norm_le t hx
  · have hs : tsupport (twist t) ⊆ Icc (1 / 2 : ℝ) (5 / 2) :=
      closure_minimal (twist_support t) isClosed_Icc
    have hs2 : tsupport (deriv (twist t)) ⊆ Icc (1 / 2 : ℝ) (5 / 2) :=
      tsupport_deriv_subset.trans hs
    rw [deriv_of_notMem_tsupport (fun h => hx (hs2 h)), norm_zero]
    have hc := cutoff_nonneg x
    positivity

/-- The exact P2 norm, on the normalized profile; no scale U/d appears. -/
def N2 (f : ℝ → ℂ) : ℝ :=
  (∫ x : ℝ, ‖f x‖) + (∫ x : ℝ, ‖deriv (deriv f) x‖)

def L0 : ℝ := ∫ x : ℝ, cutoff x
def L1 : ℝ := ∫ x : ℝ, |bumpD1 x|
def L2 : ℝ := ∫ x : ℝ, |bumpD2 x|

theorem L0_nonneg : 0 ≤ L0 := integral_nonneg cutoff_nonneg
theorem L1_nonneg : 0 ≤ L1 := integral_nonneg (fun _ => abs_nonneg _)
theorem L2_nonneg : 0 ≤ L2 := integral_nonneg (fun _ => abs_nonneg _)

theorem twist_integrable (t : ℝ) : Integrable (twist t) :=
  (twist_smooth t).continuous.integrable_of_hasCompactSupport (twist_compact t)

theorem twist_second_integrable (t : ℝ) : Integrable (deriv (deriv (twist t))) := by
  have hd := (contDiff_infty_iff_deriv.mp (twist_smooth t)).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  exact hdd.continuous.integrable_of_hasCompactSupport (twist_compact t).deriv.deriv

theorem twist_N2_nonneg (t : ℝ) : 0 ≤ N2 (twist t) := by
  exact add_nonneg (integral_nonneg (fun _ => norm_nonneg _))
    (integral_nonneg (fun _ => norm_nonneg _))

/-- The frequency dependence is DERIVED, not inserted as a mode-bank norm
premise. All three constants are fixed integrals of a Mathlib bump. -/
theorem twist_N2_le (t : ℝ) :
    N2 (twist t) ≤ L0 + L2 + 4 * L1 * |t| + 4 * L0 * (|t| ^ 2 + |t|) := by
  have h0 := cutoff_smooth.continuous.integrable_of_hasCompactSupport cutoff_compact
  have h1 := bumpD1_smooth.continuous.integrable_of_hasCompactSupport bumpD1_compact
  have h2 := bumpD2_smooth.continuous.integrable_of_hasCompactSupport bumpD2_compact
  have hR : Integrable (fun x : ℝ => |bumpD2 x| + 4 * |bumpD1 x| * |t| +
      4 * cutoff x * (|t| ^ 2 + |t|)) :=
    (h2.norm.add ((h1.norm.const_mul 4).mul_const |t|)).add
      ((h0.const_mul 4).mul_const (|t| ^ 2 + |t|))
  have hb := integral_mono (twist_second_integrable t).norm hR (twist_second_norm_le t)
  have heq : (∫ x : ℝ, ‖twist t x‖) = L0 := by
    simp_rw [twist_norm]
    rfl
  unfold N2
  rw [heq]
  calc
    _ ≤ L0 + ∫ x : ℝ, |bumpD2 x| + 4 * |bumpD1 x| * |t| +
        4 * cutoff x * (|t| ^ 2 + |t|) := add_le_add_left hb _
    _ = _ := by
      rw [integral_add (h2.norm.add ((h1.norm.const_mul 4).mul_const |t|))
        ((h0.const_mul 4).mul_const (|t| ^ 2 + |t|)),
        integral_add h2.norm ((h1.norm.const_mul 4).mul_const |t|)]
      simp only [integral_mul_const, integral_const_mul, Real.norm_eq_abs, L0, L1, L2]
      ring

def modeConstant : ℝ := L0 + L2 + 4 * L1 + 8 * L0

theorem modeConstant_nonneg : 0 ≤ modeConstant := by
  have h0 := L0_nonneg
  have h1 := L1_nonneg
  have h2 := L2_nonneg
  dsimp [modeConstant]
  positivity

/-- In a retained frequency cube the mode norms cost a FIXED polynomial
in H, not the number/volume of the frequency points. -/
theorem twist_N2_le_cube {H t : ℝ} (hH : 0 ≤ H) (ht : |t| ≤ H) :
    N2 (twist t) ≤ modeConstant * (1 + H) ^ 2 := by
  have h0 := L0_nonneg
  have h1 := L1_nonneg
  have h2 := L2_nonneg
  have ht0 := abs_nonneg t
  have hunit : (1 : ℝ) ≤ (1 + H) ^ 2 := by nlinarith
  have hlinear : |t| ≤ (1 + H) ^ 2 := by nlinarith
  have hsq : |t| ^ 2 ≤ H ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (add_nonneg hH ht0)]
  have hquad : |t| ^ 2 + |t| ≤ 2 * (1 + H) ^ 2 := by nlinarith [sq_nonneg H]
  calc
    N2 (twist t) ≤ L0 + L2 + 4 * L1 * |t| + 4 * L0 * (|t| ^ 2 + |t|) :=
      twist_N2_le t
    _ ≤ (L0 + L2) * (1 + H) ^ 2 +
        4 * L1 * (1 + H) ^ 2 + 8 * L0 * (1 + H) ^ 2 := by
      have hbase := mul_le_mul_of_nonneg_left hunit (add_nonneg h0 h2)
      have hlin := mul_le_mul_of_nonneg_left hlinear (mul_nonneg (by norm_num) h1)
      have hq := mul_le_mul_of_nonneg_left hquad (mul_nonneg (by norm_num) h0)
      nlinarith only [hbase, hlin, hq]
    _ = modeConstant * (1 + H) ^ 2 := by unfold modeConstant; ring

/-- The correct two-long support class from manuscript section 7. -/
structure LiteralMode where
  alpha : ℂ
  f : ℝ → ℂ
  g : ℝ → ℂ
  fC2 : ContDiff ℝ 2 f
  gC2 : ContDiff ℝ 2 g
  fSupport : Function.support f ⊆ Icc (1 / 2 : ℝ) (5 / 2)
  gSupport : Function.support g ⊆ Icc (1 / 2 : ℝ) (5 / 2)

/-- An ACTUAL selected mode, with no unsupported separability witness. -/
def literalMode (alpha : ℂ) (t₁ t₂ : ℝ) : LiteralMode where
  alpha := alpha
  f := twist t₁
  g := twist t₂
  fC2 := (twist_smooth t₁).of_le (by norm_num)
  gC2 := (twist_smooth t₂).of_le (by norm_num)
  fSupport := twist_support t₁
  gSupport := twist_support t₂

/-- A finite integer cover valid for [1/2,5/2], including endpoints. -/
def wideWindow (A : ℝ) : Finset ℕ := Finset.Icc 0 (Nat.ceil ((5 / 2) * A))

theorem nonzero_mem_wideWindow {A : ℝ} (hA : 0 < A) {f : ℝ → ℂ}
    (hf : Function.support f ⊆ Icc (1 / 2 : ℝ) (5 / 2)) {u : ℕ}
    (hu : f ((u : ℝ) / A) ≠ 0) : u ∈ wideWindow A := by
  have hs := hf hu
  have huA : (u : ℝ) ≤ (5 / 2) * A := (div_le_iff₀ hA).mp hs.2
  have hceil := huA.trans (Nat.le_ceil ((5 / 2) * A))
  exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, by exact_mod_cast hceil⟩

def literalModeCore (alpha : ℂ) (t₁ t₂ U V : ℝ) (m d₁ d₂ a q : ℕ) : ℂ :=
  fixedMCore (wideWindow (U / d₁)) (wideWindow (V / d₂))
    (m * d₁ * d₂) a q alpha (twist t₁) (twist t₂) (U / d₁) (V / d₂)

/-- The same explicit q-independent alpha and profiles occur in BOTH
literal AP count and exact 1/phi(q) coprime mean. -/
theorem literalModeCore_exact (alpha : ℂ) (t₁ t₂ U V : ℝ) (m d₁ d₂ a q : ℕ) :
    literalModeCore alpha t₁ t₂ U V m d₁ d₂ a q =
      (∑ u ∈ wideWindow (U / d₁), ∑ v ∈ wideWindow (V / d₂),
        if (m * d₁ * d₂) * u * v % q = a % q then
          alpha * twist t₁ ((u : ℝ) / (U / d₁)) * twist t₂ ((v : ℝ) / (V / d₂))
        else 0) -
      (((Nat.totient q : ℝ)⁻¹ : ℂ) *
        ∑ u ∈ wideWindow (U / d₁), ∑ v ∈ wideWindow (V / d₂),
          if Nat.Coprime ((m * d₁ * d₂) * u * v) q then
            alpha * twist t₁ ((u : ℝ) / (U / d₁)) * twist t₂ ((v : ℝ) / (V / d₂))
          else 0) := by
  exact fixedMCore_exact _ _ _ _ _ _ _ _ _ _

/-- In particular the P2 multiplier for a finite retained bank is paid
by its L1 amplitude mass. There is no H^rank frequency-volume charge. -/
theorem finite_mode_N2_mass {ι : Type*} (s : Finset ι)
    (alpha : ι → ℂ) (t₁ t₂ : ι → ℝ) {H : ℝ} (hH : 0 ≤ H)
    (h₁ : ∀ i ∈ s, |t₁ i| ≤ H) (h₂ : ∀ i ∈ s, |t₂ i| ≤ H) :
    (∑ i ∈ s, ‖alpha i‖ * N2 (twist (t₁ i)) * N2 (twist (t₂ i))) ≤
      modeConstant ^ 2 * (1 + H) ^ 4 * ∑ i ∈ s, ‖alpha i‖ := by
  have hC := modeConstant_nonneg
  calc
    _ ≤ ∑ i ∈ s, ‖alpha i‖ * (modeConstant * (1 + H) ^ 2) *
        (modeConstant * (1 + H) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (twist_N2_le_cube hH (h₁ i hi)) (norm_nonneg _))
        (twist_N2_le_cube hH (h₂ i hi)) (twist_N2_nonneg _)
        (by positivity)
    _ = ∑ i ∈ s, (modeConstant ^ 2 * (1 + H) ^ 4) * ‖alpha i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [Finset.mul_sum]

/-- Exact actual HB support after division by a POSITIVE Brun divisor.
The endpoint proof uses the literal `Owns` of d*u in the same long block. -/
theorem owned_brun_ratio_mem
    {b : ImbalancedChen.P5Z.HBRightClosedDyadicRoles.Block} {d u : ℕ}
    (hd : 0 < d)
    (hOwn : ImbalancedChen.P5Z.HBRightClosedDyadicRoles.Owns b (d * u)) :
    (u : ℝ) / ((ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b : ℝ) / d) ∈
      Icc (1 : ℝ) 2 := by
  let U : ℝ := ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b
  have hU : 0 < U := by
    exact_mod_cast ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower_pos b
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hb := ImbalancedChen.P5Z.ActualHBDyadicProductWindow.owns_bounds hOwn
  have hlo : U ≤ (d : ℝ) * (u : ℝ) := by exact_mod_cast hb.1
  have hhi : (d : ℝ) * (u : ℝ) ≤ 2 * U := by exact_mod_cast hb.2
  have heq : (u : ℝ) / (U / (d : ℝ)) = (d : ℝ) * (u : ℝ) / U := by
    field_simp [hU.ne', hdR.ne']
  change (u : ℝ) / (U / (d : ℝ)) ∈ Icc (1 : ℝ) 2
  rw [heq]
  exact ⟨(le_div_iff₀ hU).2 (by simpa using hlo), (div_le_iff₀ hU).2 hhi⟩

/-- On the ORIGINAL HB long rectangle, multiplying by the actual cutoff
does not alter the mode, INCLUDING equality at dyadic endpoints. -/
theorem actual_owned_mode_identity
    (alpha : ℂ) (t₁ t₂ : ℝ)
    (b₁ b₂ : ImbalancedChen.P5Z.HBRightClosedDyadicRoles.Block)
    {d₁ d₂ u v : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hOwn₁ : ImbalancedChen.P5Z.HBRightClosedDyadicRoles.Owns b₁ (d₁ * u))
    (hOwn₂ : ImbalancedChen.P5Z.HBRightClosedDyadicRoles.Owns b₂ (d₂ * v)) :
    alpha * twist t₁ ((u : ℝ) /
        ((ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b₁ : ℝ) / d₁)) *
      twist t₂ ((v : ℝ) /
        ((ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b₂ : ℝ) / d₂)) =
    alpha * phase t₁ ((u : ℝ) /
        ((ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b₁ : ℝ) / d₁)) *
      phase t₂ ((v : ℝ) /
        ((ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b₂ : ℝ) / d₂)) := by
  rw [twist_on_dyadic t₁ (owned_brun_ratio_mem hd₁ hOwn₁),
    twist_on_dyadic t₂ (owned_brun_ratio_mem hd₂ hOwn₂)]

/-- A finite occurrence-word identity that isolates two distinct original
long coordinates. It never identifies independent test coordinates with
physical marked-modulus coordinates. -/
theorem prod_split_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → ℂ) (i j : ι) (hij : i ≠ j) :
    (∏ a, F a) = F i * F j * ∏ a ∈ (Finset.univ.erase i).erase j, F a := by
  have hj : j ∈ (Finset.univ : Finset ι).erase i :=
    Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase (Finset.univ : Finset ι) F (Finset.mem_univ i),
    ← Finset.mul_prod_erase ((Finset.univ : Finset ι).erase i) F hj]
  ring

/-- Construct the selected amplitude from the ACTUAL Fourier coefficient
A(ξ) and the fixed other occurrences. No q occurs in this definition. -/
def selectedAmplitude {r : ℕ} (A : (Fin r → ℝ) → ℂ)
    (xi z : Fin r → ℝ) (i j : Fin r) : ℂ :=
  A xi * ∏ a ∈ (Finset.univ.erase i).erase j,
    Complex.exp (Complex.I * (xi a : ℂ) * (z a : ℂ))

/-- Pointwise exact factorization of the actual Fourier integrand into
q-independent short amplitude and two explicit smooth P2 profiles. -/
theorem selected_fourier_mode_exact {r : ℕ}
    (A : (Fin r → ℝ) → ℂ) (xi : Fin r → ℝ) (x : Fin r → ℝ)
    (i j : Fin r) (hij : i ≠ j)
    (hi : x i ∈ Icc (1 : ℝ) 2) (hj : x j ∈ Icc (1 : ℝ) 2) :
    selectedAmplitude A xi (fun a => Real.log (x a)) i j *
        twist (xi i) (x i) * twist (xi j) (x j) =
      A xi * ∏ a : Fin r, phase (xi a) (x a) := by
  rw [twist_on_dyadic (xi i) hi, twist_on_dyadic (xi j) hj]
  rw [prod_split_two (fun a => phase (xi a) (x a)) i j hij]
  simp only [selectedAmplitude, phase]
  ring

/-- The short phase has unit norm: P2 mode mass is charged by |A(ξ)|,
not by the number of fixed short occurrences. -/
theorem selectedAmplitude_norm {r : ℕ} (A : (Fin r → ℝ) → ℂ)
    (xi z : Fin r → ℝ) (i j : Fin r) :
    ‖selectedAmplitude A xi z i j‖ = ‖A xi‖ := by
  simp [selectedAmplitude, norm_mul, norm_prod, Complex.norm_exp]


end
end ImbalancedChen.Part3.TwoLongLiteralMellinModes
