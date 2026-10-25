import ImbalancedChen.Part3ActualParabolicHighSeedLocalFinite
import ImbalancedChen.Part3Gamma0CompactTensorPoincareC2Core
import ImbalancedChen.Part3Gamma0ModularFiniteCoverMeasure

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The literal smooth modular cusp cutoff 1-sum rho(Im(gz)/Y), summed over
the ACTUAL parabolic left cosets. Its neighborhood-finite formula is
proved using the unbounded-high-seed geometric theorem. Distinct high
cosets give at most one nonzero summand, so its range is [0,1]. An actual
right-translation equivalence of the nonnormal parabolic coset space
proves full modular invariance. The real upper-half-plane chart is C∞.
No form-core or energy-completion membership follows from these facts.
-/

namespace ImbalancedChen.Part3.ActualModularSmoothCuspCutoff20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane Pointwise
open Gamma0ParabolicCosetRows20261025a Gamma0ParabolicEffectiveDecomposition20261025a
open Gamma0ActualHighCuspTail20261025a ActualCuspStripCutoff20261025a
open ActualParabolicHighSeedLocalFinite20261025a
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0ModularFiniteCoverMeasure20261025a

def highTrace (N : ℕ) (Y : ℝ) (z : UpperHalfPlane) : ℝ :=
  ∑' q : GammaInfinityCosets N, highProfile Y (parabolicRepresentative N q • z).im

theorem highTrace_locally_eq_finsetSum (N : ℕ) (Y : ℝ) (hY : 0 < Y)
    (z : UpperHalfPlane) :
    ∃ U ∈ 𝓝 z, ∃ S : Finset (GammaInfinityCosets N), ∀ w ∈ U,
      highTrace N Y w = ∑ q ∈ S, highProfile Y (parabolicRepresentative N q • w).im := by
  obtain ⟨U, hU, S, hS⟩ := highProfile_seed_locally_finite N Y hY z
  refine ⟨U, hU, S, ?_⟩
  intro w hw
  exact tsum_eq_sum (fun q hq => hS w hw q hq)

theorem highTrace_continuous (N : ℕ) (Y : ℝ) (hY : 0 < Y) :
    Continuous (highTrace N Y) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨U, hU, S, hS⟩ := highTrace_locally_eq_finsetSum N Y hY z
  have hc : Continuous (fun w : UpperHalfPlane =>
      ∑ q ∈ S, highProfile Y (parabolicRepresentative N q • w).im) := by
    apply continuous_finsetSum S
    intro q _
    apply (highProfile_cinfty Y).continuous.comp
    apply UpperHalfPlane.continuous_im.comp
    change Continuous (fun w : UpperHalfPlane =>
      (SpecialLinearGroup.mapGL ℝ (parabolicRepresentative N q : SL(2, ℤ))) • w)
    exact continuous_const_smul _
  apply hc.continuousAt.congr_of_eventuallyEq
  exact Filter.eventually_of_mem hU hS

theorem highProfile_nonzero_height (Y : ℝ) (hY : 0 < Y)
    (z : UpperHalfPlane) (hz : highProfile Y z.im ≠ 0) : Y < z.im := by
  by_contra h
  exact hz (highProfile_eq_zero Y hY z.im z.im_pos.le (le_of_not_gt h))

/-- Exact uniqueness of the nonzero smooth tail contribution, not merely
an a.e. overlap statement or a supplied multiplicity constant. -/
theorem nonzero_highProfile_coset_unique (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y)
    (q r : GammaInfinityCosets N) (z : UpperHalfPlane)
    (hq : highProfile Y (parabolicRepresentative N q • z).im ≠ 0)
    (hr : highProfile Y (parabolicRepresentative N r • z).im ≠ 0) : q = r := by
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  exact strict_high_coset_unique N Y hY q r z
    (highProfile_nonzero_height Y hYpos _ hq)
    (highProfile_nonzero_height Y hYpos _ hr)

theorem highTrace_eq_single_of_nonzero (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y)
    (q : GammaInfinityCosets N) (z : UpperHalfPlane)
    (hq : highProfile Y (parabolicRepresentative N q • z).im ≠ 0) :
    highTrace N Y z = highProfile Y (parabolicRepresentative N q • z).im := by
  apply tsum_eq_single q
  intro r hr
  by_contra hnonzero
  exact hr (nonzero_highProfile_coset_unique N Y hY r q z hnonzero hq)

theorem highTrace_bounds (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y) (z : UpperHalfPlane) :
    0 ≤ highTrace N Y z ∧ highTrace N Y z ≤ 1 := by
  by_cases hex : ∃ q : GammaInfinityCosets N,
      highProfile Y (parabolicRepresentative N q • z).im ≠ 0
  · obtain ⟨q, hq⟩ := hex
    rw [highTrace_eq_single_of_nonzero N Y hY q z hq]
    exact ⟨highProfile_nonneg _ _, highProfile_le_one _ _⟩
  · have hzero : highTrace N Y z = 0 := by
      apply tsum_eq_zero.mpr
      intro q
      exact not_ne_iff.mp (fun h => hex ⟨q, h⟩)
    rw [hzero]
    norm_num

/-- Right multiplication is a well-defined bijection on the genuine
NONNORMAL left parabolic quotient. No normality is used. -/
def cosetRight (N : ℕ) (gamma : CongruenceSubgroup.Gamma0 N) :
    GammaInfinityCosets N → GammaInfinityCosets N :=
  Quotient.lift (fun g => Quotient.mk'' (g * gamma)) (by
    intro g h hrel
    apply Quotient.sound
    apply (parabolic_orbit_iff_relative N (g * gamma) (h * gamma)).mpr
    have heq : (g * gamma) * (h * gamma)⁻¹ = g * h⁻¹ := by group
    rw [heq]
    exact (parabolic_orbit_iff_relative N g h).mp hrel)

def cosetRightEquiv (N : ℕ) (gamma : CongruenceSubgroup.Gamma0 N) :
    GammaInfinityCosets N ≃ GammaInfinityCosets N where
  toFun := cosetRight N gamma
  invFun := cosetRight N gamma⁻¹
  left_inv q := by
    refine Quotient.inductionOn q (fun g => ?_)
    change Quotient.mk'' ((g * gamma) * gamma⁻¹) = Quotient.mk'' g
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  right_inv q := by
    refine Quotient.inductionOn q (fun g => ?_)
    change Quotient.mk'' ((g * gamma⁻¹) * gamma) = Quotient.mk'' g
    simp only [mul_assoc, inv_mul_cancel, mul_one]

theorem highProfile_periodic (N : ℕ) (Y : ℝ) (k : ℤ) (z : UpperHalfPlane) :
    highProfile Y (((k : ℝ) +ᵥ z).im) = highProfile Y z.im := by
  rw [UpperHalfPlane.vadd_im]

theorem periodicProfile_eq_representative (N : ℕ) (Y : ℝ) (z : UpperHalfPlane)
    (q : GammaInfinityCosets N) :
    periodicSeedOnCosets N (fun w => highProfile Y w.im) (highProfile_periodic N Y) z q =
      highProfile Y (parabolicRepresentative N q • z).im := by
  rw [← parabolicRepresentative_class N q]
  rfl

theorem periodicProfile_right (N : ℕ) (Y : ℝ) (gamma : CongruenceSubgroup.Gamma0 N)
    (z : UpperHalfPlane) (q : GammaInfinityCosets N) :
    periodicSeedOnCosets N (fun w => highProfile Y w.im) (highProfile_periodic N Y)
      (gamma • z) q =
    periodicSeedOnCosets N (fun w => highProfile Y w.im) (highProfile_periodic N Y)
      z (cosetRightEquiv N gamma q) := by
  refine Quotient.inductionOn q (fun g => ?_)
  change highProfile Y (g • (gamma • z)).im = highProfile Y ((g * gamma) • z).im
  rw [mul_smul]

theorem highTrace_gamma0_invariant (N : ℕ) (Y : ℝ)
    (gamma : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    highTrace N Y (gamma • z) = highTrace N Y z := by
  calc
    highTrace N Y (gamma • z) = ∑' q : GammaInfinityCosets N,
        periodicSeedOnCosets N (fun w => highProfile Y w.im) (highProfile_periodic N Y)
          (gamma • z) q := by simp only [periodicProfile_eq_representative, highTrace]
    _ = ∑' q : GammaInfinityCosets N,
        periodicSeedOnCosets N (fun w => highProfile Y w.im) (highProfile_periodic N Y)
          z (cosetRightEquiv N gamma q) := tsum_congr (periodicProfile_right N Y gamma z)
    _ = ∑' q : GammaInfinityCosets N,
        periodicSeedOnCosets N (fun w => highProfile Y w.im) (highProfile_periodic N Y) z q :=
      (cosetRightEquiv N gamma).tsum_eq _
    _ = highTrace N Y z := by simp only [periodicProfile_eq_representative, highTrace]

theorem complexOfPair_cinfty : ContDiff ℝ ∞ complexOfPair := by
  have heq : complexOfPair = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by
    funext p
    ext <;> simp [complexOfPair]
  rw [heq]
  fun_prop

theorem chartLift_continuousAt_positive {p : ℝ × ℝ} (hp : 0 < p.2) :
    ContinuousAt chartLift p :=
  (UpperHalfPlane.contMDiffAt_ofComplex (n := ∞) hp).continuousAt.comp
    complexOfPair_cinfty.continuous.continuousAt

/-- The actual Mobius chart is smooth to every order on positive heights. -/
theorem mobiusChart_cinftyAt (g : SL(2, ℤ)) {p : ℝ × ℝ} (hp : 0 < p.2) :
    ContDiffAt ℝ ∞ (mobiusChart g) p := by
  have hn : ContDiff ℝ ∞ (fun p =>
      UpperHalfPlane.num (SpecialLinearGroup.mapGL ℝ g) (complexOfPair p)) := by
    unfold UpperHalfPlane.num
    exact (contDiff_const.mul complexOfPair_cinfty).add contDiff_const
  have hd : ContDiff ℝ ∞ (fun p =>
      UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ g) (complexOfPair p)) := by
    unfold UpperHalfPlane.denom
    exact (contDiff_const.mul complexOfPair_cinfty).add contDiff_const
  have hm : ContDiffAt ℝ ∞ (mobiusComplex g) p :=
    hn.contDiffAt.div hd.contDiffAt (mobius_denom_ne_zero g hp)
  exact ((Complex.reCLM.contDiff.contDiffAt).comp p hm).prodMk
    ((Complex.imCLM.contDiff.contDiffAt).comp p hm)

/-- Local finite differentiation applies to the TRUE unbounded-high
parabolic sum, without a desired smoothness hypothesis. -/
theorem highTrace_chart_cinfty (N : ℕ) (Y : ℝ) (hY : 0 < Y) :
    ContDiffOn ℝ ∞ (fun p => highTrace N Y (chartLift p)) positiveChart := by
  intro p hp
  obtain ⟨U, hU, S, hS⟩ := highTrace_locally_eq_finsetSum N Y hY (chartLift p)
  have heq : (fun r => highTrace N Y (chartLift r)) =ᶠ[𝓝 p]
      (fun r => ∑ q ∈ S,
        highProfile Y (mobiusChart (parabolicRepresentative N q : SL(2, ℤ)) r).2) := by
    filter_upwards [(chartLift_continuousAt_positive hp).eventually hU,
      (isOpen_lt continuous_const continuous_snd).mem_nhds hp] with r hr hrpos
    rw [hS (chartLift r) hr]
    apply Finset.sum_congr rfl
    intro q _
    rw [mobiusChart_eq_actual _ hrpos]
  have hsum : ContDiffAt ℝ ∞ (fun r => ∑ q ∈ S,
      highProfile Y (mobiusChart (parabolicRepresentative N q : SL(2, ℤ)) r).2) p := by
    apply ContDiffAt.sum
    intro q _
    exact (highProfile_cinfty Y).contDiffAt.comp p
      (contDiffAt_snd.comp p (mobiusChart_cinftyAt _ hp))
  exact (hsum.congr_of_eventuallyEq heq).contDiffWithinAt

/-- Global modular low-cusp cutoff: no assumed gluing or global cutoff. -/
def globalCutoff (Y : ℝ) (z : UpperHalfPlane) : ℝ := 1 - highTrace 1 Y z

theorem globalCutoff_bounds (Y : ℝ) (hY : 1 ≤ Y) (z : UpperHalfPlane) :
    0 ≤ globalCutoff Y z ∧ globalCutoff Y z ≤ 1 := by
  have hb := highTrace_bounds 1 Y hY z
  dsimp [globalCutoff]
  constructor <;> linarith

theorem globalCutoff_sl2_invariant (Y : ℝ) (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    globalCutoff Y (g • z) = globalCutoff Y z := by
  exact congrArg (fun a : ℝ => 1 - a) (highTrace_gamma0_invariant 1 Y (levelOneMatrix g) z)

theorem globalCutoff_chart_cinfty (Y : ℝ) (hY : 0 < Y) :
    ContDiffOn ℝ ∞ (fun p => globalCutoff Y (chartLift p)) positiveChart :=
  contDiffOn_const.sub (highTrace_chart_cinfty 1 Y hY)

end
end ImbalancedChen.Part3.ActualModularSmoothCuspCutoff20261025a
