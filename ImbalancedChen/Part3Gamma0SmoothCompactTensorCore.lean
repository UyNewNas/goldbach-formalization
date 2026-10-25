import ImbalancedChen.Part3Gamma0CompactTensorQuotientL2Core

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

This is the genuinely smooth subfamily of the actual effective-Gamma0
Poincare core.  The old CompactTensor only supplies C2 regularity; here
the two seed factors are required to be smooth, and the actual locally
finite sum is proved smooth in positive coordinates.  Its quotient L2
vector is the existing actual quotient vector, not a whole-plane L2
vector with a different name.  No density, Green identity, domain of a
closed operator, or spectral conclusion is asserted.
-/

namespace ImbalancedChen.Part3.Gamma0SmoothCompactTensorCore20261025a

noncomputable section

open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorQuotientL2Core20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a

/-- Actual compact positive-height tensor data, strengthened from C2 to C∞. -/
structure SmoothCompactTensor extends CompactTensor where
  horizontal_cinfty : ContDiff ℝ ∞ horizontal
  vertical_cinfty : ContDiff ℝ ∞ vertical

/-- There is no analytically new seed function hidden in this adapter. -/
def smoothFinitePoincare (N : ℕ) {ι : Type*} (s : Finset ι)
    (T : ι → SmoothCompactTensor) : UpperHalfPlane → ℂ :=
  finiteCompactTensorPoincare N s (fun i => (T i).toCompactTensor)

theorem complexOfPair_contDiff_infty : ContDiff ℝ ∞ complexOfPair := by
  have heq : complexOfPair =
      (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by
    funext p
    ext <;> simp [complexOfPair]
  rw [heq]
  fun_prop

/-- Rational Mobius maps are smooth on the true positive-height chart. -/
theorem mobiusChart_contDiffAt_infty (g : SL(2, ℤ))
    {p : ℝ × ℝ} (hp : 0 < p.2) :
    ContDiffAt ℝ ∞ (mobiusChart g) p := by
  have hn : ContDiff ℝ ∞ (fun p =>
      UpperHalfPlane.num (SpecialLinearGroup.mapGL ℝ g) (complexOfPair p)) := by
    unfold UpperHalfPlane.num
    exact (contDiff_const.mul complexOfPair_contDiff_infty).add contDiff_const
  have hd : ContDiff ℝ ∞ (fun p =>
      UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ g) (complexOfPair p)) := by
    unfold UpperHalfPlane.denom
    exact (contDiff_const.mul complexOfPair_contDiff_infty).add contDiff_const
  have hm : ContDiffAt ℝ ∞ (mobiusComplex g) p :=
    hn.contDiffAt.div hd.contDiffAt (mobius_denom_ne_zero g hp)
  exact ((Complex.reCLM.contDiff.contDiffAt).comp p hm).prodMk
    ((Complex.imCLM.contDiff.contDiffAt).comp p hm)

theorem finiteSmoothChart_contDiff {ι : Type*} (s : Finset ι)
    (T : ι → SmoothCompactTensor) :
    ContDiff ℝ ∞ (finiteChartFunction s (fun i => (T i).toCompactTensor)) := by
  apply ContDiff.sum
  intro i _
  exact ((T i).horizontal_cinfty.comp contDiff_fst).mul
    ((T i).vertical_cinfty.comp contDiff_snd)

theorem translatedSmoothChart_contDiffAt (N : ℕ) (q : effectiveGamma0 N)
    {ι : Type*} (s : Finset ι) (T : ι → SmoothCompactTensor)
    {p : ℝ × ℝ} (hp : 0 < p.2) :
    ContDiffAt ℝ ∞
      (translatedFiniteTensorChart N q s (fun i => (T i).toCompactTensor)) p :=
  (finiteSmoothChart_contDiff s T).contDiffAt.comp p
    (mobiusChart_contDiffAt_infty (effectiveRepresentative N q : SL(2, ℤ)) hp)

private theorem chartLift_continuousAt_positive {p : ℝ × ℝ} (hp : 0 < p.2) :
    ContinuousAt chartLift p :=
  (UpperHalfPlane.contMDiffAt_ofComplex (n := 2) hp).continuousAt.comp
    complexOfPair_contDiff_infty.continuous.continuousAt

/-- The actual sum is C∞ because it agrees near each positive point with
one finite sum of the genuine smooth Mobius pullbacks. -/
theorem smoothFinitePoincare_contDiffOn_chart (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → SmoothCompactTensor) :
    ContDiffOn ℝ ∞ (extendUpper (smoothFinitePoincare N s T)) positiveChart := by
  intro p hp
  let U : ι → CompactTensor := fun i => (T i).toCompactTensor
  obtain ⟨V, hV, S, hS⟩ :=
    finiteCompactTensorPoincare_locally_eq_finsetSum N s U (chartLift p)
  have hpre : ∀ᶠ p' in 𝓝 p, chartLift p' ∈ V :=
    (chartLift_continuousAt_positive hp) hV
  have hpos : ∀ᶠ p' in 𝓝 p, 0 < p'.2 :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hp
  have heq : extendUpper (smoothFinitePoincare N s T) =ᶠ[𝓝 p]
      (fun p' => ∑ q ∈ S, translatedFiniteTensorChart N q s U p') := by
    filter_upwards [hpre, hpos] with p' hpV hp'
    have hext : extendUpper (smoothFinitePoincare N s T) p' =
        finiteCompactTensorPoincare N s U (chartLift p') := by
      rw [extendUpper, dif_pos hp', chartLift_of_positive hp']
      rfl
    rw [hext, hS (chartLift p') hpV]
    apply Finset.sum_congr rfl
    intro q _
    exact (translatedFiniteTensorChart_eq_actual N q s U hp').symm
  have hsum : ContDiffAt ℝ ∞
      (fun p' => ∑ q ∈ S, translatedFiniteTensorChart N q s U p') p :=
    ContDiffAt.sum (fun q _ => translatedSmoothChart_contDiffAt N q s T hp)
  exact (hsum.congr_of_eventuallyEq heq).contDiffWithinAt

theorem smoothFinitePoincare_gamma0_invariant (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → SmoothCompactTensor)
    (γ : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    smoothFinitePoincare N s T (γ • z) = smoothFinitePoincare N s T z :=
  finiteCompactTensorPoincare_gamma0_invariant N s
    (fun i => (T i).toCompactTensor) γ z

/-- The quotient vector is literally the already constructed vector for
this seed, with its actual carrier-pushforward measure. -/
def smoothQuotientPoincareL2 (N : ℕ) [NeZero N] {ι : Type*}
    (s : Finset ι) (T : ι → SmoothCompactTensor) :
    Lp ℂ 2 (carrierPushforward N) :=
  quotientTensorPoincareL2 N s (fun i => (T i).toCompactTensor)

theorem smoothQuotientPoincare_pullback_cinfty (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → SmoothCompactTensor) :
    ContDiffOn ℝ ∞
      (extendUpper (fun z => quotientTensorPoincare N s
        (fun i => (T i).toCompactTensor) (orbitProjection N z))) positiveChart := by
  simpa only [quotientTensorPoincare_projection] using
    smoothFinitePoincare_contDiffOn_chart N s T

end
end ImbalancedChen.Part3.Gamma0SmoothCompactTensorCore20261025a
