import ImbalancedChen.ActualSieveGapTailBounds
import ImbalancedChen.LogPrimeBoxIntegral
import ImbalancedChen.VariableEnvelopeTailFloor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The canonical noncompact third-prefix tail and a positive majorant

The physical kernel is `4 * (fbar(sOld) - fbar(sNew)) / (x*y*z^2)`.
Here fbar is the actual canonical Suzuki lower factor divided by `2 exp gamma`.
The elementary margin below uses only the baseline entry in the real coarse
Gamma construction, not an assumed approximation to its full gated envelope.

The rounded coarse selector's genuine lower floor is supplied separately by
VariableEnvelopeTailFloor. The ordered tail is integrated as a nonnegative
Lebesgue integral, so finiteness is a conclusion rather than an implicit
default-zero convention for a divergent real integral.

This module uses the actual canonical sieve factors and the literal rounded
extended cap. The identification with the finite prime-tuple density profile is
kept separately in ActualThirdPrefixTailIntegral so the noncompact integral
estimate does not import the compact arithmetic-density normalization chain.
The adopted selector, its measurable partition, and its density assembly remain
separate obligations. This is candidate source, not a compilation receipt.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology Set MeasureTheory
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped BigOperators ENNReal

def thirdPrefixRho : ℝ := 19 / 96
def thirdPrefixTheta : ℝ := 299 / 500
def thirdPrefixTailMargin : ℝ := 19 / 192

/-- The actual single-variable baseline tent, including the above-mu branch. -/
def thirdPrefixBaselineTent (x : ℝ) : ℝ :=
  min ((1 + x) / 2) (57 / 64 - 3 * x / 2)

theorem thirdPrefixBaselineTent_ge_half {x : ℝ}
    (hx : 0 ≤ x) (hxrho : x ≤ thirdPrefixRho) :
    (1 / 2 : ℝ) ≤ thirdPrefixBaselineTent x := by
  unfold thirdPrefixBaselineTent
  apply le_min
  · linarith
  · dsimp [thirdPrefixRho] at hxrho
    linarith

/-- This sharper endpoint inequality is independent of every other branch. -/
theorem thirdPrefixBaselineTent_residual_margin {x y : ℝ}
    (hyx : y ≤ x) (hxrho : x ≤ thirdPrefixRho) :
    thirdPrefixRho ≤ thirdPrefixBaselineTent x - x - y := by
  have h : thirdPrefixRho + x + y ≤ thirdPrefixBaselineTent x := by
    unfold thirdPrefixBaselineTent
    apply le_min <;> dsimp [thirdPrefixRho] at * <;> linarith
  linarith

/-- Literal baseline entry of a nonempty closed first-coordinate coarse box. -/
def thirdPrefixCoarseBaseline (lo hi : ℝ) : ℝ :=
  sInf (thirdPrefixBaselineTent '' Icc lo hi)

theorem thirdPrefixCoarseBaseline_ge_half {lo hi : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ thirdPrefixRho) :
    (1 / 2 : ℝ) ≤ thirdPrefixCoarseBaseline lo hi := by
  apply le_csInf
  · exact ⟨thirdPrefixBaselineTent lo, ⟨lo, ⟨le_rfl, hlohi⟩, rfl⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact thirdPrefixBaselineTent_ge_half (hlo.trans hx.1) (hx.2.trans hhi)

/-- The manuscript uses this same actual cap for history and density. -/
def thirdPrefixBufferedCap (e gamma : ℝ) : ℝ :=
  min (thirdPrefixTheta - 2 * e) (gamma - 2 * e)

theorem thirdPrefixBufferedCap_le_root (e gamma : ℝ) :
    thirdPrefixBufferedCap e gamma ≤ thirdPrefixTheta - 2 * e :=
  min_le_left _ _

/-- No full-envelope Lipschitz estimate is needed for the noncompact tail.
The manuscript's `e < 3/25600` is stronger than the bound used here. -/
theorem thirdPrefixBufferedCap_residual_margin {e gamma x y : ℝ}
    (he : e ≤ 1 / 384) (hgamma : 1 / 2 ≤ gamma)
    (hx : x ≤ thirdPrefixRho) (hy : y ≤ thirdPrefixRho) :
    thirdPrefixTailMargin ≤ thirdPrefixBufferedCap e gamma - x - y := by
  have hc : (1 / 2 : ℝ) - 2 * e ≤ thirdPrefixBufferedCap e gamma := by
    unfold thirdPrefixBufferedCap
    apply le_min
    · dsimp [thirdPrefixTheta]
      linarith
    · linarith
  dsimp [thirdPrefixRho] at hx hy
  dsimp [thirdPrefixTailMargin]
  linarith

/-- A coarse Gamma containing the baseline entry has the required margin. -/
theorem thirdPrefixBufferedCap_margin_of_coarse_baseline
    {e gamma lo hi x y : ℝ} (he : e ≤ 1 / 384)
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ thirdPrefixRho)
    (hgamma : thirdPrefixCoarseBaseline lo hi ≤ gamma)
    (hx : x ≤ thirdPrefixRho) (hy : y ≤ thirdPrefixRho) :
    thirdPrefixTailMargin ≤ thirdPrefixBufferedCap e gamma - x - y :=
  thirdPrefixBufferedCap_residual_margin he
    ((thirdPrefixCoarseBaseline_ge_half hlo hlohi hhi).trans hgamma) hx hy

/-- Monotonicity of the actual lower factor follows from its convergent even
source layers. No monotonicity of finite signed sieve weights is asserted. -/
theorem thirdTail_lowerFactor_monotone :
    MonotoneOn suzukiContinuousLowerFactor (Ici 2) := by
  intro x hx y hy hxy
  have hminus : suzukiProposition118SourceTMinus y ≤
      suzukiProposition118SourceTMinus x := by
    apply Summable.tsum_le_tsum _
      (summable_suzukiProposition118SourceTMinus_of_sourceContract
        jr1965Section13HatSourceContract hy)
      (summable_suzukiProposition118SourceTMinus_of_sourceContract
        jr1965Section13HatSourceContract hx)
    intro k
    exact suzukiLayer_one_antitoneOn_parityDomain (by norm_num) (2 * (k + 1))
      (by simpa [suzukiParityDomainOne, KappaOneModel.parityDomain] using hx)
      (by simpa [suzukiParityDomainOne, KappaOneModel.parityDomain] using hy) hxy
  change 1 - suzukiProposition118SourceTMinus x ≤
    1 - suzukiProposition118SourceTMinus y
  linarith

def thirdTailLowerFactor (s : ℝ) : ℝ :=
  suzukiContinuousLowerFactor s / (2 * Real.exp Real.eulerMascheroniConstant)

/-- The lower-factor increment is bounded by the actual gap at the smaller
argument. Positivity and the common value one are supplied by actual layers. -/
theorem thirdTailLowerFactor_difference {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) :
    0 ≤ thirdTailLowerFactor t - thirdTailLowerFactor s ∧
      thirdTailLowerFactor t - thirdTailLowerFactor s ≤
        actualSieveGap s / (2 * Real.exp Real.eulerMascheroniConstant) := by
  have ht : 2 ≤ t := hs.trans hst
  have hmono := thirdTail_lowerFactor_monotone hs ht hst
  have hminus : 0 ≤ suzukiProposition118SourceTMinus t :=
    tsum_nonneg (fun k => suzukiLayer_one_two_even_nonneg ht k)
  have hplus : 0 ≤ suzukiProposition118SourceTPlus s :=
    tsum_nonneg (suzukiLayer_one_two_odd_nonneg (by linarith : 1 < s))
  have hbound : suzukiContinuousLowerFactor t - suzukiContinuousLowerFactor s ≤
      actualSieveGap s := by
    change (1 - suzukiProposition118SourceTMinus t) -
      (1 - suzukiProposition118SourceTMinus s) ≤
        (1 + suzukiProposition118SourceTPlus s) - (1 - suzukiProposition118SourceTMinus s)
    linarith
  have hden : 0 < 2 * Real.exp Real.eulerMascheroniConstant := by positivity
  unfold thirdTailLowerFactor
  rw [← sub_div]
  exact ⟨div_nonneg (sub_nonneg.mpr hmono) hden.le,
    (div_le_div_iff_of_pos_right hden).mpr hbound⟩

def thirdPrefixCorrectionKernel (old cap x y z : ℝ) : ℝ :=
  4 * (thirdTailLowerFactor ((old - x - y - z) / z) -
    thirdTailLowerFactor ((cap - x - y - z) / z)) / (x * y * z ^ 2)

theorem thirdPrefixTail_argument_ge_three {u h cap x y z : ℝ}
    (_hu : 0 < u) (hh : h ≤ u / 4) (hz : 0 < z) (hzh : z ≤ h)
    (hcap : u ≤ cap - x - y) :
    3 ≤ (cap - x - y - z) / z := by
  apply (le_div_iff₀ hz).mpr
  linarith only [hh, hzh, hcap]

/-- The strict own-cube gate is automatically open throughout this tail. -/
theorem thirdPrefixTail_ownCube_lt {u h cap x y z : ℝ}
    (hh : h ≤ u / 4) (hz : 0 < z) (hzh : z ≤ h)
    (hcap : u ≤ cap - x - y) : x + y + 3 * z < cap := by
  linarith

/-- A stronger constant twelve allows the ordered triangle to be enlarged to
a square later. This avoids needing an ordered-domain factor of one half. -/
theorem thirdPrefixCorrectionKernel_tail_bound {u h old cap x y z : ℝ}
    (hu : 0 < u) (hh : h ≤ u / 4) (hz : 0 < z) (hzh : z ≤ h)
    (hx : 0 < x) (hy : 0 < y) (hcap : u ≤ cap - x - y)
    (hlevels : cap ≤ old) :
    0 ≤ thirdPrefixCorrectionKernel old cap x y z ∧
      thirdPrefixCorrectionKernel old cap x y z ≤ 12 / (x * y * (u - h) ^ 2) := by
  have hs := thirdPrefixTail_argument_ge_three hu hh hz hzh hcap
  have hst : (cap - x - y - z) / z ≤ (old - x - y - z) / z :=
    (div_le_div_iff_of_pos_right hz).mpr (by linarith)
  have hd := thirdTailLowerFactor_difference (by linarith :
    2 ≤ (cap - x - y - z) / z) hst
  have hgap := actualSieveGap_normalized_le_three_div_sq hs
  have hdiff := hd.2.trans hgap
  have huh : 0 < u - h := by linarith
  have ha : u - h ≤ cap - x - y - z := by linarith
  have hapos : 0 < cap - x - y - z := huh.trans_le ha
  have hden : 0 < x * y * z ^ 2 := by positivity
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) hd.1) hden.le
  · unfold thirdPrefixCorrectionKernel
    calc
      _ ≤ 4 * (3 / ((cap - x - y - z) / z) ^ 2) / (x * y * z ^ 2) :=
        (div_le_div_iff_of_pos_right hden).mpr
          (mul_le_mul_of_nonneg_left hdiff (by norm_num))
      _ = 12 / (x * y * (cap - x - y - z) ^ 2) := by
        field_simp [hx.ne', hy.ne', hz.ne', hapos.ne']
        ring
      _ ≤ 12 / (x * y * (u - h) ^ 2) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        gcongr

/-- The exact primitive for the radial logarithmic majorant. -/
def thirdTailLogPrimitive (rho h : ℝ) : ℝ :=
  h * (Real.log (rho / h) ^ 2 + 2 * Real.log (rho / h) + 2)

theorem hasDerivAt_thirdTailLogPrimitive {rho z : ℝ} (hrho : 0 < rho) (hz : 0 < z) :
    HasDerivAt (thirdTailLogPrimitive rho) (Real.log (rho / z) ^ 2) z := by
  have hlog : HasDerivAt (fun t : ℝ => Real.log (rho / t)) (-1 / z) z := by
    apply (((hasDerivAt_const z rho).fun_div (hasDerivAt_id z) hz.ne').log
      (div_ne_zero hrho.ne' hz.ne')).congr_deriv
    simp only [id_eq]
    field_simp [hrho.ne', hz.ne']
    ring
  unfold thirdTailLogPrimitive
  apply ((hasDerivAt_id z).fun_mul
    (((hlog.fun_pow 2).fun_add (hlog.const_mul 2)).add_const 2)).congr_deriv
  simp only [id_eq]
  field_simp [hz.ne']
  ring

theorem tendsto_thirdTailLogPrimitive_zero {rho : ℝ} (hrho : 0 < rho) :
    Tendsto (thirdTailLogPrimitive rho) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  have h₂ := tendsto_mul_log_div_pow_zero 2 hrho
  have h₁ : Tendsto (fun h : ℝ => h * Real.log (rho / h)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [pow_one] using tendsto_mul_log_div_pow_zero 1 hrho
  have hId : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hSum := (h₂.add (h₁.const_mul 2)).add (hId.const_mul 2)
  simp only [mul_zero, add_zero] at hSum
  convert hSum using 1
  ext h
  unfold thirdTailLogPrimitive
  ring

theorem continuousOn_thirdTailLogPrimitive {rho h : ℝ} (hrho : 0 < rho) :
    ContinuousOn (thirdTailLogPrimitive rho) (Icc 0 h) := by
  intro z hz
  rcases eq_or_lt_of_le hz.1 with rfl | hzpos
  · have hc : ContinuousWithinAt (thirdTailLogPrimitive rho) (Ioi 0) 0 := by
      simpa [ContinuousWithinAt, thirdTailLogPrimitive] using
        tendsto_thirdTailLogPrimitive_zero hrho
    apply hc.insert.mono
    intro z hz
    rcases eq_or_lt_of_le hz.1 with rfl | hzpos
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ hzpos
  · exact (hasDerivAt_thirdTailLogPrimitive hrho hzpos).continuousAt.continuousWithinAt

/-- Integrability is proved, so the improper real integral is not Lean's
default zero for a nonintegrable function. -/
theorem integrableOn_thirdTailLogSq {rho h : ℝ} (hrho : 0 < rho) :
    IntegrableOn (fun z : ℝ => Real.log (rho / z) ^ 2) (Ioc 0 h) := by
  exact intervalIntegral.integrableOn_deriv_of_nonneg
    (continuousOn_thirdTailLogPrimitive hrho)
    (fun z hz => hasDerivAt_thirdTailLogPrimitive hrho hz.1)
    (fun z _ => sq_nonneg _)

theorem integral_thirdTailLogSq {rho h : ℝ} (hrho : 0 < rho) (hh : 0 < h) :
    (∫ z in Ioc 0 h, Real.log (rho / z) ^ 2) = thirdTailLogPrimitive rho h := by
  have hint : IntervalIntegrable (fun z : ℝ => Real.log (rho / z) ^ 2) volume 0 h := by
    constructor
    · exact integrableOn_thirdTailLogSq hrho
    · simp [Ioc_eq_empty (not_lt.mpr hh.le)]
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hh
    (fun z hz => hasDerivAt_thirdTailLogPrimitive hrho hz.1) hint
    (tendsto_thirdTailLogPrimitive_zero hrho)
    (tendsto_nhdsWithin_of_tendsto_nhds
      (hasDerivAt_thirdTailLogPrimitive hrho hh).continuousAt.tendsto)
  simpa only [intervalIntegral.integral_of_le hh.le, sub_zero] using heq

/-- The existing logarithmic prime-box integral supplies the inner radial
factor, with the harmless half-open endpoint changed by its null singleton. -/
theorem thirdTail_lintegral_one_div {z rho : ℝ} (hz : 0 < z) (hzrho : z ≤ rho) :
    (∫⁻ x in Ioc z rho, ENNReal.ofReal (1 / x)) =
      ENNReal.ofReal (Real.log (rho / z)) := by
  have hcont : ContinuousOn (fun x : ℝ => 1 / x) (Icc z rho) :=
    continuousOn_const.div continuousOn_id (fun x hx => (hz.trans_le hx.1).ne')
  have hint : IntegrableOn (fun x : ℝ => 1 / x) (Ioc z rho) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc z rho)] (fun x : ℝ => 1 / x) := by
    apply (ae_restrict_iff' measurableSet_Ioc).2
    exact ae_of_all _ (fun x hx => one_div_nonneg.mpr (hz.trans hx.1).le)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ← integral_Ico_eq_integral_Ioc, integral_one_div_Ico hz hzrho]

theorem thirdTail_lintegral_const_mul_one_div {c z rho : ℝ}
    (hc : 0 ≤ c) (hz : 0 < z) (hzrho : z ≤ rho) :
    (∫⁻ x in Ioc z rho, ENNReal.ofReal (c * (1 / x))) =
      ENNReal.ofReal (c * Real.log (rho / z)) := by
  simp_rw [ENNReal.ofReal_mul hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    thirdTail_lintegral_one_div hz hzrho]

/-- The square costs a full logarithm squared. No factor one half from the
ordered triangle is used, which leaves slack in the final constant eighteen. -/
theorem thirdTail_lintegral_square {c z rho : ℝ}
    (hc : 0 ≤ c) (hz : 0 < z) (hzrho : z ≤ rho) :
    (∫⁻ x in Ioc z rho, ∫⁻ y in Ioc z rho,
      ENNReal.ofReal (c * (1 / x) * (1 / y))) =
      ENNReal.ofReal (c * Real.log (rho / z) ^ 2) := by
  have hlog : 0 ≤ Real.log (rho / z) :=
    Real.log_nonneg ((le_div_iff₀ hz).2 (by simpa using hzrho))
  calc
    _ = ∫⁻ x in Ioc z rho,
        ENNReal.ofReal ((c * Real.log (rho / z)) * (1 / x)) := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro x hx
      change (∫⁻ y in Ioc z rho, ENNReal.ofReal (c * (1 / x) * (1 / y))) =
        ENNReal.ofReal ((c * Real.log (rho / z)) * (1 / x))
      rw [thirdTail_lintegral_const_mul_one_div
        (mul_nonneg hc (one_div_nonneg.mpr (hz.trans hx.1).le)) hz hzrho]
      congr 1
      ring
    _ = ENNReal.ofReal ((c * Real.log (rho / z)) * Real.log (rho / z)) :=
      thirdTail_lintegral_const_mul_one_div (mul_nonneg hc hlog) hz hzrho
    _ = _ := by congr 1; ring

theorem thirdTail_lintegral_logSq {rho h : ℝ} (hrho : 0 < rho) (hh : 0 < h) :
    (∫⁻ z in Ioc 0 h, ENNReal.ofReal (Real.log (rho / z) ^ 2)) =
      ENNReal.ofReal (thirdTailLogPrimitive rho h) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_thirdTailLogSq hrho) (ae_of_all _ (fun _ => sq_nonneg _)),
    integral_thirdTailLogSq hrho hh]

/-- A genuine improper threefold integral of the explicit positive majorant. -/
theorem thirdTail_lintegral_majorant {c rho h : ℝ}
    (hc : 0 ≤ c) (hrho : 0 < rho) (hh : 0 < h) (hhrho : h ≤ rho) :
    (∫⁻ z in Ioc 0 h, ∫⁻ x in Ioc z rho, ∫⁻ y in Ioc z rho,
      ENNReal.ofReal (c * (1 / x) * (1 / y))) =
      ENNReal.ofReal (c * thirdTailLogPrimitive rho h) := by
  calc
    _ = ∫⁻ z in Ioc 0 h, ENNReal.ofReal (c * Real.log (rho / z) ^ 2) := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro z hz
      exact thirdTail_lintegral_square hc hz.1 (hz.2.trans hhrho)
    _ = ENNReal.ofReal c *
        ∫⁻ z in Ioc 0 h, ENNReal.ofReal (Real.log (rho / z) ^ 2) := by
      simp_rw [ENNReal.ofReal_mul hc]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (c * thirdTailLogPrimitive rho h) := by
      rw [thirdTail_lintegral_logSq hrho hh, ENNReal.ofReal_mul hc]

/-- Literal ordered third-prefix tail, with its old strict own-cube gate.
The cap may be piecewise constant, as it is on the adopted coarse boxes.
The integral is a nonnegative Lebesgue integral before conversion to a real. -/
def thirdPrefixTailMass (old : ℝ) (cap : ℝ → ℝ → ℝ → ℝ) (rho h : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Ioc 0 h, ∫⁻ x in Ioc z rho, ∫⁻ y in Ioc z x,
    ENNReal.ofReal (if x + y + 3 * z < old then
      thirdPrefixCorrectionKernel old (cap x y z) x y z else 0)

/-- Only the actual geometric cap margin is a premise. The canonical sieve
factor, its gap decay, all three integrals, and their finiteness are proved. -/
theorem thirdPrefixTailMass_le_twelve {u rho h old : ℝ}
    {cap : ℝ → ℝ → ℝ → ℝ} (hu : 0 < u) (hrho : 0 < rho)
    (hh : 0 < h) (hsmall : h ≤ u / 4) (hhrho : h ≤ rho)
    (hcap : ∀ x y z, 0 < z → z ≤ h → z ≤ y → y ≤ x → x ≤ rho →
      u ≤ cap x y z - x - y ∧ cap x y z ≤ old) :
    thirdPrefixTailMass old cap rho h ≤
      ENNReal.ofReal (12 / (u - h) ^ 2 * thirdTailLogPrimitive rho h) := by
  have huh : 0 < u - h := by linarith
  have hc : 0 ≤ (12 : ℝ) / (u - h) ^ 2 := by positivity
  rw [← thirdTail_lintegral_majorant hc hrho hh hhrho]
  unfold thirdPrefixTailMass
  apply setLIntegral_mono' measurableSet_Ioc
  intro z hz
  apply setLIntegral_mono' measurableSet_Ioc
  intro x hx
  calc
    _ ≤ ∫⁻ y in Ioc z x,
        ENNReal.ofReal ((12 / (u - h) ^ 2) * (1 / x) * (1 / y)) := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro y hy
      have hypos : 0 < y := hz.1.trans hy.1
      have hxpos : 0 < x := hz.1.trans hx.1
      have hgeom := hcap x y z hz.1 hz.2 hy.1.le hy.2 hx.2
      have hk := thirdPrefixCorrectionKernel_tail_bound hu hsmall hz.1 hz.2
        hxpos hypos hgeom.1 hgeom.2
      apply ENNReal.ofReal_le_ofReal
      split_ifs with hgate
      · calc
          _ ≤ 12 / (x * y * (u - h) ^ 2) := hk.2
          _ = _ := by field_simp [hxpos.ne', hypos.ne', huh.ne']
      · positivity
    _ ≤ ∫⁻ y in Ioc z rho,
        ENNReal.ofReal ((12 / (u - h) ^ 2) * (1 / x) * (1 / y)) :=
      lintegral_mono_set (fun y hy => ⟨hy.1, hy.2.trans hx.2⟩)

/-- The displayed manuscript envelope, with an explicit small-cutoff gate. -/
theorem thirdPrefixTailMass_le_eighteen {h old : ℝ} {cap : ℝ → ℝ → ℝ → ℝ}
    (hh : 0 < h) (hsmall : h ≤ thirdPrefixTailMargin / 4)
    (hcap : ∀ x y z, 0 < z → z ≤ h → z ≤ y → y ≤ x → x ≤ thirdPrefixRho →
      thirdPrefixTailMargin ≤ cap x y z - x - y ∧ cap x y z ≤ old) :
    thirdPrefixTailMass old cap thirdPrefixRho h ≤
      ENNReal.ofReal (18 * h / (thirdPrefixTailMargin - h) ^ 2 *
        (Real.log (thirdPrefixRho / h) ^ 2 + 2 * Real.log (thirdPrefixRho / h) + 2)) := by
  have hhrho : h ≤ thirdPrefixRho := by
    dsimp [thirdPrefixTailMargin] at hsmall
    dsimp [thirdPrefixRho]
    linarith
  have hbound := thirdPrefixTailMass_le_twelve
    (by norm_num [thirdPrefixTailMargin]) (by norm_num [thirdPrefixRho])
    hh hsmall hhrho hcap
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  have hl : 0 ≤ Real.log (thirdPrefixRho / h) :=
    Real.log_nonneg ((le_div_iff₀ hh).2 (by simpa using hhrho))
  have hp : 0 ≤ Real.log (thirdPrefixRho / h) ^ 2 +
      2 * Real.log (thirdPrefixRho / h) + 2 := by positivity
  have hc : (12 : ℝ) * h / (thirdPrefixTailMargin - h) ^ 2 ≤
      18 * h / (thirdPrefixTailMargin - h) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith
  calc
    _ = (12 * h / (thirdPrefixTailMargin - h) ^ 2) *
        (Real.log (thirdPrefixRho / h) ^ 2 + 2 * Real.log (thirdPrefixRho / h) + 2) := by
      unfold thirdTailLogPrimitive
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hp

theorem thirdPrefixTailMass_ne_top {h old : ℝ} {cap : ℝ → ℝ → ℝ → ℝ}
    (hh : 0 < h) (hsmall : h ≤ thirdPrefixTailMargin / 4)
    (hcap : ∀ x y z, 0 < z → z ≤ h → z ≤ y → y ≤ x → x ≤ thirdPrefixRho →
      thirdPrefixTailMargin ≤ cap x y z - x - y ∧ cap x y z ≤ old) :
    thirdPrefixTailMass old cap thirdPrefixRho h ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (thirdPrefixTailMass_le_eighteen hh hsmall hcap)

/-- This real tail is the finite nonnegative Lebesgue mass just bounded. -/
def thirdPrefixTail (old : ℝ) (cap : ℝ → ℝ → ℝ → ℝ) (rho h : ℝ) : ℝ :=
  (thirdPrefixTailMass old cap rho h).toReal

theorem thirdPrefixTail_le_eighteen {h old : ℝ} {cap : ℝ → ℝ → ℝ → ℝ}
    (hh : 0 < h) (hsmall : h ≤ thirdPrefixTailMargin / 4)
    (hcap : ∀ x y z, 0 < z → z ≤ h → z ≤ y → y ≤ x → x ≤ thirdPrefixRho →
      thirdPrefixTailMargin ≤ cap x y z - x - y ∧ cap x y z ≤ old) :
    thirdPrefixTail old cap thirdPrefixRho h ≤
      18 * h / (thirdPrefixTailMargin - h) ^ 2 *
        (Real.log (thirdPrefixRho / h) ^ 2 + 2 * Real.log (thirdPrefixRho / h) + 2) := by
  have hbound := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (thirdPrefixTailMass_le_eighteen hh hsmall hcap)
  have hhrho : h ≤ thirdPrefixRho := by
    dsimp [thirdPrefixTailMargin] at hsmall
    dsimp [thirdPrefixRho]
    linarith
  have hl : 0 ≤ Real.log (thirdPrefixRho / h) :=
    Real.log_nonneg ((le_div_iff₀ hh).2 (by simpa using hhrho))
  have hnonneg : 0 ≤ 18 * h / (thirdPrefixTailMargin - h) ^ 2 *
      (Real.log (thirdPrefixRho / h) ^ 2 + 2 * Real.log (thirdPrefixRho / h) + 2) := by
    positivity
  simpa only [thirdPrefixTail, ENNReal.toReal_ofReal hnonneg] using hbound

/-- Literal cap computation of the frozen extended-prefix certificate. -/
def currentExtendedThirdCap (e : ℝ) (b : VariableEnvelope.ScaledBox) : ℝ :=
  VariableEnvelope.bufferedCoarseCap e
    (b.extendedClippedLower 805306368000 157286400000 481573208064)

/-- The actual rounded certificate cap supplies both geometric premises. -/
theorem currentExtendedThirdCap_tail_geometry (b : VariableEnvelope.ScaledBox)
    (hl : 0 ≤ b.lx) (hu : b.ux ≤ 159383552000)
    {e x y : ℝ} (he : e ≤ 1 / 768)
    (hx : x ≤ thirdPrefixRho) (hy : y ≤ thirdPrefixRho) :
    thirdPrefixTailMargin ≤ currentExtendedThirdCap e b - x - y ∧
      currentExtendedThirdCap e b ≤ thirdPrefixTheta - 2 * e := by
  constructor
  · exact b.currentExtended_buffered_residual_floor hl hu he hx hy
  · exact min_le_left _ _

/-- The full noncompact bound for any actual coarse-box selector with the
literal endpoint range. No generic `Gamma` lower bound remains a hypothesis.
This does not yet identify a particular adopted finite selector with `select`.
-/
theorem currentExtendedThirdPrefixTail_le_eighteen
    (select : ℝ → ℝ → ℝ → VariableEnvelope.ScaledBox)
    {e h : ℝ} (he : e ≤ 1 / 768) (hh : 0 < h)
    (hsmall : h ≤ thirdPrefixTailMargin / 4)
    (hboxes : ∀ x y z, 0 < z → z ≤ h → z ≤ y → y ≤ x → x ≤ thirdPrefixRho →
      0 ≤ (select x y z).lx ∧ (select x y z).ux ≤ 159383552000) :
    thirdPrefixTail (thirdPrefixTheta - 2 * e)
      (fun x y z => currentExtendedThirdCap e (select x y z)) thirdPrefixRho h ≤
      18 * h / (thirdPrefixTailMargin - h) ^ 2 *
        (Real.log (thirdPrefixRho / h) ^ 2 + 2 * Real.log (thirdPrefixRho / h) + 2) := by
  apply thirdPrefixTail_le_eighteen hh hsmall
  intro x y z hz hzh hzy hyx hx
  have hb := hboxes x y z hz hzh hzy hyx hx
  exact currentExtendedThirdCap_tail_geometry (select x y z) hb.1 hb.2 he hx (hyx.trans hx)

/-- The tail estimate is uniform in the cap: the finite partition and its cap
may be chosen again for each activation cutoff.  The conclusion concerns the
nonnegative mass itself, before any conversion from `ENNReal` to `Real`.
Thus it cannot hold merely because the real value of an infinite mass is zero.
Only the actual geometric cap inequalities are supplied by the caller. -/
theorem thirdPrefixTailMass_tendsto_zero_of_cutoffDependentCap
    (old : ℝ) (cap : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hcap : ∀ h, 0 < h → h ≤ thirdPrefixTailMargin / 4 →
      ∀ x y z, 0 < z → z ≤ h → z ≤ y → y ≤ x → x ≤ thirdPrefixRho →
      thirdPrefixTailMargin ≤ cap h x y z - x - y ∧ cap h x y z ≤ old) :
    Tendsto (fun h => thirdPrefixTailMass old (cap h) thirdPrefixRho h)
      (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
  have hupper : Tendsto (fun h : ℝ => ENNReal.ofReal
      (18 * h / (thirdPrefixTailMargin - h) ^ 2 *
        (Real.log (thirdPrefixRho / h) ^ 2 +
          2 * Real.log (thirdPrefixRho / h) + 2)))
      (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
      (tendsto_roughActivationTailEnvelope_zero
        (a := thirdPrefixRho) (c := thirdPrefixTailMargin)
        (by norm_num [thirdPrefixRho]) (by norm_num [thirdPrefixTailMargin]))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · exact Filter.Eventually.of_forall (fun _ => bot_le)
  · have hsmall : Iio (thirdPrefixTailMargin / 4) ∈ 𝓝[>] (0 : ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num [thirdPrefixTailMargin]))
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hs
    exact thirdPrefixTailMass_le_eighteen hh hs.le (hcap h hh hs.le)

/-- Real-valued convergence follows from the genuine nonnegative mass limit.
In particular the selector may vary with the accuracy of the finite compiler.
The earlier pointwise bound also proves that every sufficiently small member
of this family is finite. -/
theorem thirdPrefixTail_tendsto_zero_of_cutoffDependentCap
    (old : ℝ) (cap : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hcap : ∀ h, 0 < h → h ≤ thirdPrefixTailMargin / 4 →
      ∀ x y z, 0 < z → z ≤ h → z ≤ y → y ≤ x → x ≤ thirdPrefixRho →
      thirdPrefixTailMargin ≤ cap h x y z - x - y ∧ cap h x y z ≤ old) :
    Tendsto (fun h => thirdPrefixTail old (cap h) thirdPrefixRho h)
      (𝓝[>] 0) (𝓝 0) := by
  have hmass := thirdPrefixTailMass_tendsto_zero_of_cutoffDependentCap old cap hcap
  simpa only [Function.comp_def, thirdPrefixTail, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hmass

/-- Uniform activation for the literal rounded extended-prefix cap.  This
allows a new finite coarse-box selector for each cutoff, with no assumed
continuity or convergence of the selectors themselves.  Endpoint coverage
of an adopted selector remains an explicit separate obligation. -/
theorem currentExtendedThirdPrefixTailMass_tendsto_zero_of_cutoffDependentSelector
    (select : ℝ → ℝ → ℝ → ℝ → VariableEnvelope.ScaledBox)
    {e : ℝ} (he : e ≤ 1 / 768)
    (hboxes : ∀ h, 0 < h → h ≤ thirdPrefixTailMargin / 4 →
      ∀ x y z, 0 < z → z ≤ h → z ≤ y → y ≤ x → x ≤ thirdPrefixRho →
      0 ≤ (select h x y z).lx ∧ (select h x y z).ux ≤ 159383552000) :
    Tendsto (fun h => thirdPrefixTailMass (thirdPrefixTheta - 2 * e)
      (fun x y z => currentExtendedThirdCap e (select h x y z)) thirdPrefixRho h)
      (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
  apply thirdPrefixTailMass_tendsto_zero_of_cutoffDependentCap
  intro h hh hsmall x y z hz hzh hzy hyx hx
  have hb := hboxes h hh hsmall x y z hz hzh hzy hyx hx
  exact currentExtendedThirdCap_tail_geometry (select h x y z) hb.1 hb.2 he hx (hyx.trans hx)

theorem currentExtendedThirdPrefixTail_tendsto_zero_of_cutoffDependentSelector
    (select : ℝ → ℝ → ℝ → ℝ → VariableEnvelope.ScaledBox)
    {e : ℝ} (he : e ≤ 1 / 768)
    (hboxes : ∀ h, 0 < h → h ≤ thirdPrefixTailMargin / 4 →
      ∀ x y z, 0 < z → z ≤ h → z ≤ y → y ≤ x → x ≤ thirdPrefixRho →
      0 ≤ (select h x y z).lx ∧ (select h x y z).ux ≤ 159383552000) :
    Tendsto (fun h => thirdPrefixTail (thirdPrefixTheta - 2 * e)
      (fun x y z => currentExtendedThirdCap e (select h x y z)) thirdPrefixRho h)
      (𝓝[>] 0) (𝓝 0) := by
  apply thirdPrefixTail_tendsto_zero_of_cutoffDependentCap
  intro h hh hsmall x y z hz hzh hzy hyx hx
  have hb := hboxes h hh hsmall x y z hz hzh hzy hyx hx
  exact currentExtendedThirdCap_tail_geometry (select h x y z) hb.1 hb.2 he hx (hyx.trans hx)

/-- The proved integral comparison, not an assumed T3 estimate, now supplies
the activation limit. The cap and the selector are fixed before `h` varies. -/
theorem thirdPrefixTail_tendsto_zero (old : ℝ) (cap : ℝ → ℝ → ℝ → ℝ)
    (hcap : ∀ x y z, 0 < z → z ≤ thirdPrefixTailMargin / 4 →
      z ≤ y → y ≤ x → x ≤ thirdPrefixRho →
      thirdPrefixTailMargin ≤ cap x y z - x - y ∧ cap x y z ≤ old) :
    Tendsto (thirdPrefixTail old cap thirdPrefixRho) (𝓝[>] 0) (𝓝 0) := by
  have hupper : Tendsto (fun h : ℝ => 18 * h / (thirdPrefixTailMargin - h) ^ 2 *
      (Real.log (thirdPrefixRho / h) ^ 2 + 2 * Real.log (thirdPrefixRho / h) + 2))
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_roughActivationTailEnvelope_zero
      (by norm_num [thirdPrefixRho]) (by norm_num [thirdPrefixTailMargin])
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)
  · have hsmall : Iio (thirdPrefixTailMargin / 4) ∈ 𝓝[>] (0 : ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num [thirdPrefixTailMargin]))
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hs
    apply thirdPrefixTail_le_eighteen hh hs.le
    intro x y z hz hzh hzy hyx hx
    exact hcap x y z hz (hzh.trans hs.le) hzy hyx hx

theorem currentExtendedThirdPrefixTail_tendsto_zero
    (select : ℝ → ℝ → ℝ → VariableEnvelope.ScaledBox)
    {e : ℝ} (he : e ≤ 1 / 768)
    (hboxes : ∀ x y z, 0 < z → z ≤ thirdPrefixTailMargin / 4 →
      z ≤ y → y ≤ x → x ≤ thirdPrefixRho →
      0 ≤ (select x y z).lx ∧ (select x y z).ux ≤ 159383552000) :
    Tendsto (thirdPrefixTail (thirdPrefixTheta - 2 * e)
      (fun x y z => currentExtendedThirdCap e (select x y z)) thirdPrefixRho)
      (𝓝[>] 0) (𝓝 0) := by
  apply thirdPrefixTail_tendsto_zero
  intro x y z hz hzh hzy hyx hx
  have hb := hboxes x y z hz hzh hzy hyx hx
  exact currentExtendedThirdCap_tail_geometry (select x y z) hb.1 hb.2 he hx (hyx.trans hx)

end

end ImbalancedChen
