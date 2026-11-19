import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The adopted coarse two-chart second-prefix saving

SOURCE CANDIDATE: not yet compiled or replayed by the pinned Lean kernel.

Source: `chen-imbalanced-semiprimes` at
`ba6ec11d800eccc54406490631895e174de85766`,
`proof-library/source/second-prefix-upper-fallback-20261009.tex`.
Source SHA-256: `355954ab0d4d1d23ce6045a4baa2dee3b71f124a8550e8f1eae71fbcae70821d`.
The adopted upper-policy ledger selects `above_mu_second_coarse_only`, namely
`no_grid_coarse_lower` in the independent review JSON. The finer 2048-cell
estimate is an alternative estimate of this same saving and is not added here.

The objects below are the literal real integrals of the two rational kernels
in that source, with their actual chart coordinates, old and new residuals,
and coefficient including the physical density factor 4. The numerical lower
bounds follow from positivity, four proved denominator bounds, Fubini, and the
exact integral of `u^2 * (1-v)`. No stored lower endpoint is an input premise.

Connecting this chart saving with a limiting actual first-exit tree is a
separate Part 1 obligation. In particular, no equality with an arbitrary
frozen finite old tree is asserted here.

`chartKernel_eq_physical_pullback` is a pointwise algebraic identity with the
specified factor `|k| * step^2 * u`. It is not a change-of-variables theorem:
injectivity, coverage up to null boundaries, the derivative/Jacobian theorem,
and the physical-domain integral dictionary remain the minimal Part 1 input
if that interface starts from the `(x,y)` integral instead of the adopted
two-chart integral itself.
-/

namespace ImbalancedChen.Certificates.AboveMuSecondCoarse

noncomputable section

open MeasureTheory Set
open scoped Interval

def mu : ℝ := 25 / 128
def rho : ℝ := 19 / 96
def step : ℝ := 1 / 384

/-- The actual reference upper endpoint, including its change of branch. -/
def endpointEnvelope (t : ℝ) : ℝ := min ((1 + t) / 2) (57 / 64 - 3 * t / 2)

/-- The physical rank-two improvement region, in coordinate order `(x,y)`. -/
def physicalDomain : Set (ℝ × ℝ) :=
  {p | mu < p.1 ∧ p.1 < rho ∧ 25 / 32 - 3 * p.1 < p.2 ∧ p.2 < p.1}

/-- The first coordinate is common to the negative and positive charts. -/
def chartX (u : ℝ) : ℝ := (75 + u) / 384

/-- `k = -3` is the part below `mu`; `k = 1` is the part above `mu`. -/
def chartY (k u v : ℝ) : ℝ := (75 + k * u * v) / 384

def oldResidual (k u v : ℝ) : ℝ := (159 - 5 * u - 2 * k * u * v) / 768
def newResidual (k u v : ℝ) : ℝ := (159 - 2 * u - (2 * k + 3) * u * v) / 768

def chartDenominator (k u v : ℝ) : ℝ :=
  chartX u * chartY k u v * oldResidual k u v * newResidual k u v

/-- The literal pulled-back physical saving, including its Jacobian factor. -/
def chartKernel (k u v : ℝ) : ℝ :=
  6 * |k| * step ^ 3 * u ^ 2 * (1 - v) / chartDenominator k u v

def squareIntegral (f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, f u v

/-- A genuine iterated Lebesgue integral, independent of stored certificate data. -/
def chartIntegral (k : ℝ) : ℝ := squareIntegral (chartKernel k)

def totalChartIntegral : ℝ := chartIntegral (-3) + chartIntegral 1

theorem chartIntegral_eq_literal (k : ℝ) :
    chartIntegral k = (6 * |k| * step ^ 3) *
      ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1,
        u ^ 2 * (1 - v) /
          (chartX u * chartY k u v * oldResidual k u v * newResidual k u v) := by
  simp only [chartIntegral, squareIntegral, chartKernel, chartDenominator,
    mul_div_assoc, mul_assoc, intervalIntegral.integral_const_mul]

theorem step_eq : step = rho - mu := by norm_num [step, rho, mu]

theorem chartX_eq (u : ℝ) : chartX u = mu + step * u := by
  dsimp [chartX, mu, step]
  ring

theorem chartY_eq (k u v : ℝ) : chartY k u v = mu + k * step * u * v := by
  dsimp [chartY, mu, step]
  ring

/-- All four factors stay uniformly positive on both complete closed charts. -/
theorem chart_bounds {k u v : ℝ} (hk : k = -3 ∨ k = 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    mu ≤ chartX u ∧ chartX u ≤ rho ∧
      (3 / 16 : ℝ) ≤ chartY k u v ∧ chartY k u v ≤ rho ∧
      rho ≤ oldResidual k u v ∧ rho ≤ newResidual k u v := by
  have huv0 : 0 ≤ u * v := mul_nonneg hu.1 hv.1
  have huv1 : u * v ≤ u := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hv.2 hu.1
  rcases hk with rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      dsimp [mu, rho, chartX, chartY, oldResidual, newResidual] <;>
      nlinarith [hu.1, hu.2, hv.1, hv.2]

theorem chart_factors_pos {k u v : ℝ} (hk : k = -3 ∨ k = 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < chartX u ∧ 0 < chartY k u v ∧
      0 < oldResidual k u v ∧ 0 < newResidual k u v := by
  rcases chart_bounds hk hu hv with ⟨hx, _, hy, _, ho, hn⟩
  exact ⟨lt_of_lt_of_le (by norm_num [mu]) hx,
    lt_of_lt_of_le (by norm_num) hy,
    lt_of_lt_of_le (by norm_num [rho]) ho,
    lt_of_lt_of_le (by norm_num [rho]) hn⟩

theorem chartDenominator_pos {k u v : ℝ} (hk : k = -3 ∨ k = 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < chartDenominator k u v := by
  rcases chart_factors_pos hk hu hv with ⟨hx, hy, ho, hn⟩
  exact mul_pos (mul_pos (mul_pos hx hy) ho) hn

theorem negative_chart_upper_bounds {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    chartY (-3) u v ≤ mu ∧ oldResidual (-3) u v ≤ 5 / 24 ∧
      newResidual (-3) u v ≤ 5 / 24 := by
  have huv0 : 0 ≤ u * v := mul_nonneg hu.1 hv.1
  have huv1 : u * v ≤ u := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hv.2 hu.1
  refine ⟨?_, ?_, ?_⟩ <;>
    dsimp [chartY, mu, oldResidual, newResidual] <;>
    nlinarith [hu.1, hu.2]

theorem positive_chart_upper_bounds {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    oldResidual 1 u v ≤ 53 / 256 ∧ newResidual 1 u v ≤ 53 / 256 := by
  have huv0 : 0 ≤ u * v := mul_nonneg hu.1 hv.1
  constructor <;> dsimp [oldResidual, newResidual] <;> nlinarith [hu.1]

theorem chartInterior_mem_physicalDomain {k u v : ℝ} (hk : k = -3 ∨ k = 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    (chartX u, chartY k u v) ∈ physicalDomain := by
  have huv0 : 0 < u * v := mul_pos hu.1 hv.1
  have huv1 : 0 < u * (1 - v) := mul_pos hu.1 (sub_pos.mpr hv.2)
  rcases hk with rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      dsimp [physicalDomain, chartX, chartY, mu, rho] <;>
      nlinarith [hu.1, hu.2]

private theorem envelope_of_ge_mu {t : ℝ} (ht : mu ≤ t) :
    endpointEnvelope t = 57 / 64 - 3 * t / 2 := by
  apply min_eq_right
  dsimp [mu] at ht
  linarith

private theorem envelope_of_le_mu {t : ℝ} (ht : t ≤ mu) :
    endpointEnvelope t = (1 + t) / 2 := by
  apply min_eq_left
  dsimp [mu] at ht
  linarith

theorem endpointEnvelope_chartX {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    endpointEnvelope (chartX u) = 153 / 256 - (3 / 2 : ℝ) * step * u := by
  rw [envelope_of_ge_mu (show mu ≤ chartX u by
    dsimp [mu, chartX]
    linarith [hu.1])]
  dsimp [chartX, step]
  ring

theorem endpointEnvelope_chartY {k u v : ℝ} (hk : k = -3 ∨ k = 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    endpointEnvelope (chartY k u v) =
      153 / 256 - (3 / 2 : ℝ) * step * u * v := by
  rcases hk with rfl | rfl
  · rw [envelope_of_le_mu (negative_chart_upper_bounds hu hv).1]
    dsimp [chartY, step]
    ring
  · have hy : mu ≤ chartY 1 u v := by
      have huv0 : 0 ≤ u * v := mul_nonneg hu.1 hv.1
      dsimp [mu, chartY]
      nlinarith
    rw [envelope_of_ge_mu hy]
    dsimp [chartY, step]
    ring

/-- The actual open chart points satisfy the full initial and selected-square
gates and strictly improve the old endpoint. Closed boundaries are retained
only for continuous integration, not for a claim of uniform strict margins. -/
theorem chartInterior_gates {k u v : ℝ} (hk : k = -3 ∨ k = 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    2 * chartX u < endpointEnvelope (chartX u) ∧
      chartX u + 2 * chartY k u v < endpointEnvelope (chartX u) ∧
      2 * chartX u + chartY k u v < endpointEnvelope (chartX u) ∧
      endpointEnvelope (chartX u) < endpointEnvelope (chartY k u v) := by
  have huc : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
  have hvc : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2.le⟩
  have hxy : chartY k u v < chartX u :=
    (chartInterior_mem_physicalDomain hk hu hv).2.2.2
  have hxpos : 0 < chartX u := (chart_factors_pos hk huc hvc).1
  have hold : 3 * chartX u < endpointEnvelope (chartX u) := by
    rw [endpointEnvelope_chartX huc]
    dsimp [chartX, step]
    linarith [hu.2]
  have himprove : endpointEnvelope (chartX u) < endpointEnvelope (chartY k u v) := by
    rw [endpointEnvelope_chartX huc, endpointEnvelope_chartY hk huc hvc]
    have hmul : 0 < u * (1 - v) := mul_pos hu.1 (sub_pos.mpr hv.2)
    dsimp [step]
    nlinarith
  exact ⟨by linarith, by linarith, by linarith, himprove⟩

/-- The old chart denominator is the actual old total endpoint minus `x+y`. -/
theorem oldResidual_semantics {k u : ℝ} (v : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    oldResidual k u v = endpointEnvelope (chartX u) - chartX u - chartY k u v := by
  rw [endpointEnvelope_chartX hu]
  dsimp [oldResidual, chartX, chartY, step]
  ring

/-- The new chart denominator is the actual new total endpoint minus `x+y`. -/
theorem newResidual_semantics {k u v : ℝ} (hk : k = -3 ∨ k = 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    newResidual k u v =
      endpointEnvelope (chartY k u v) - chartX u - chartY k u v := by
  rw [endpointEnvelope_chartY hk hu hv]
  dsimp [newResidual, chartX, chartY, step]
  ring

/-- Exact pointwise algebra with the physical saving kernel and the source's
specified chart factor. This does not prove injective coverage or an integral
change of variables. The factor 4 is present; there is no slot factorial. -/
theorem chartKernel_eq_physical_pullback {k u v : ℝ} (hk : k = -3 ∨ k = 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    chartKernel k u v =
      (4 * (endpointEnvelope (chartY k u v) - endpointEnvelope (chartX u)) /
        (chartX u * chartY k u v *
          (endpointEnvelope (chartX u) - chartX u - chartY k u v) *
          (endpointEnvelope (chartY k u v) - chartX u - chartY k u v))) *
        (|k| * step ^ 2 * u) := by
  rw [← oldResidual_semantics v hu, ← newResidual_semantics hk hu hv]
  rw [endpointEnvelope_chartY hk hu hv, endpointEnvelope_chartX hu]
  dsimp [chartKernel, chartDenominator]
  ring

theorem continuousOn_chartKernel {k : ℝ} (hk : k = -3 ∨ k = 1) :
    ContinuousOn (fun p : ℝ × ℝ => chartKernel k p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  have hn : Continuous (fun p : ℝ × ℝ =>
      6 * |k| * step ^ 3 * p.1 ^ 2 * (1 - p.2)) := by fun_prop
  have hd : Continuous (fun p : ℝ × ℝ => chartDenominator k p.1 p.2) := by
    unfold chartDenominator chartX chartY oldResidual newResidual
    fun_prop
  exact hn.continuousOn.div hd.continuousOn fun p hp =>
    (chartDenominator_pos hk hp.1 hp.2).ne'

private theorem squareIntegral_eq_setIntegral (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :
    squareIntegral f = ∫ p in Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1,
      f p.1 p.2 ∂(volume.prod volume) := by
  have hi : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) (volume.prod volume) :=
    (hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  unfold squareIntegral
  simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact (MeasureTheory.setIntegral_prod _ hi).symm

private theorem squareIntegral_mono {f g : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hfg : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, f u v ≤ g u v) :
    squareIntegral f ≤ squareIntegral g := by
  rw [squareIntegral_eq_setIntegral f hf, squareIntegral_eq_setIntegral g hg]
  apply MeasureTheory.setIntegral_mono_on
    ((hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self))
    ((hg.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self))
    (measurableSet_Ioc.prod measurableSet_Ioc)
  intro p hp
  exact hfg p.1 ⟨hp.1.1.le, hp.1.2⟩ p.2 ⟨hp.2.1.le, hp.2.2⟩

/-- Exact real integration of the polynomial numerator; this is not a stored mass. -/
theorem squareIntegral_weightedMass (C : ℝ) :
    squareIntegral (fun u v => C * u ^ 2 * (1 - v)) = C / 6 := by
  have hv : (∫ v in (0 : ℝ)..1, (1 : ℝ) - v) = 1 / 2 := by
    rw [intervalIntegral.integral_sub (μ := volume)
      (f := fun _ : ℝ => (1 : ℝ)) (g := fun v : ℝ => v)
      (continuous_const.intervalIntegrable 0 1)
      (continuous_id.intervalIntegrable 0 1), intervalIntegral.integral_const,
      integral_id]
    norm_num
  calc
    squareIntegral (fun u v => C * u ^ 2 * (1 - v)) =
        C * ((∫ u in (0 : ℝ)..1, u ^ 2) * (∫ v in (0 : ℝ)..1, (1 : ℝ) - v)) := by
      simp only [squareIntegral, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_mul_const]
      ring
    _ = C / 6 := by
      rw [hv, integral_pow]
      norm_num; ring

/-- A proved denominator cap gives a lower bound on the actual chart integral. -/
theorem chartIntegral_lower_of_denominatorCap {k D : ℝ} (hk : k = -3 ∨ k = 1)
    (hD : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      chartDenominator k u v ≤ D) :
    |k| * step ^ 3 / D ≤ chartIntegral k := by
  let C : ℝ := 6 * |k| * step ^ 3 / D
  have hc : Continuous (fun p : ℝ × ℝ => C * p.1 ^ 2 * (1 - p.2)) := by fun_prop
  have hbound : squareIntegral (fun u v => C * u ^ 2 * (1 - v)) ≤
      squareIntegral (chartKernel k) := by
    apply squareIntegral_mono hc.continuousOn (continuousOn_chartKernel hk)
    intro u hu v hv
    have hs : 0 ≤ step := by norm_num [step]
    have hv1 : 0 ≤ 1 - v := sub_nonneg.mpr hv.2
    have hn : 0 ≤ 6 * |k| * step ^ 3 * u ^ 2 * (1 - v) := by positivity
    calc
      C * u ^ 2 * (1 - v) =
          (6 * |k| * step ^ 3 * u ^ 2 * (1 - v)) / D := by dsimp [C]; ring
      _ ≤ chartKernel k u v :=
        div_le_div_of_nonneg_left hn (chartDenominator_pos hk hu hv) (hD u hu v hv)
  rw [squareIntegral_weightedMass] at hbound
  change |k| * step ^ 3 / D ≤ squareIntegral (chartKernel k)
  convert hbound using 1
  dsimp [C]
  ring

def negativeDenominatorCap : ℝ := rho * mu * (5 / 24 : ℝ) ^ 2
def positiveDenominatorCap : ℝ := rho ^ 2 * (53 / 256 : ℝ) ^ 2

theorem negative_denominator_le {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    chartDenominator (-3) u v ≤ negativeDenominatorCap := by
  rcases chart_bounds (Or.inl rfl) hu hv with ⟨_, hx, _, _, _, _⟩
  rcases chart_factors_pos (Or.inl rfl) hu hv with ⟨_, hy0, ho0, hn0⟩
  rcases negative_chart_upper_bounds hu hv with ⟨hy, ho, hn⟩
  have hxy := mul_le_mul hx hy hy0.le (show 0 ≤ rho by norm_num [rho])
  have hxyo := mul_le_mul hxy ho ho0.le (show 0 ≤ rho * mu by norm_num [rho, mu])
  have hxyon := mul_le_mul hxyo hn hn0.le
    (show 0 ≤ rho * mu * (5 / 24 : ℝ) by norm_num [rho, mu])
  change chartX u * chartY (-3) u v * oldResidual (-3) u v *
    newResidual (-3) u v ≤ rho * mu * (5 / 24 : ℝ) ^ 2
  simpa only [pow_two, mul_assoc] using hxyon

theorem positive_denominator_le {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    chartDenominator 1 u v ≤ positiveDenominatorCap := by
  rcases chart_bounds (Or.inr rfl) hu hv with ⟨_, hx, _, hy, _, _⟩
  rcases chart_factors_pos (Or.inr rfl) hu hv with ⟨_, hy0, ho0, hn0⟩
  rcases positive_chart_upper_bounds hu hv with ⟨ho, hn⟩
  have hxy := mul_le_mul hx hy hy0.le (show 0 ≤ rho by norm_num [rho])
  have hxyo := mul_le_mul hxy ho ho0.le (show 0 ≤ rho * rho by norm_num [rho])
  have hxyon := mul_le_mul hxyo hn hn0.le
    (show 0 ≤ rho * rho * (53 / 256 : ℝ) by norm_num [rho])
  change chartX u * chartY 1 u v * oldResidual 1 u v *
    newResidual 1 u v ≤ rho ^ 2 * (53 / 256 : ℝ) ^ 2
  simpa only [pow_two, mul_assoc] using hxyon

/-- The negative chart contributes at least the adopted exact coarse lower bound. -/
theorem negative_chart_lower : (3 / 95000 : ℝ) ≤ chartIntegral (-3) := by
  have hh := chartIntegral_lower_of_denominatorCap (k := -3) (D := negativeDenominatorCap)
    (Or.inl rfl) (fun _ hu _ hv => negative_denominator_le hu hv)
  norm_num [step, negativeDenominatorCap, mu, rho] at hh
  exact hh

/-- The positive chart contributes at least the adopted exact coarse lower bound. -/
theorem positive_chart_lower : (32 / 3042147 : ℝ) ≤ chartIntegral 1 := by
  have hh := chartIntegral_lower_of_denominatorCap (k := 1) (D := positiveDenominatorCap)
    (Or.inr rfl) (fun _ hu _ hv => positive_denominator_le hu hv)
  norm_num [step, positiveDenominatorCap, rho] at hh
  exact hh

/-- The adopted A22 entry, proved as a bound on its genuine two-chart integral. -/
theorem adopted_coarse_lower :
    (640339 / 15210735000 : ℝ) ≤ totalChartIntegral := by
  calc
    (640339 / 15210735000 : ℝ) = 3 / 95000 + 32 / 3042147 := by norm_num
    _ ≤ totalChartIntegral := add_le_add negative_chart_lower positive_chart_lower

end

end ImbalancedChen.Certificates.AboveMuSecondCoarse
