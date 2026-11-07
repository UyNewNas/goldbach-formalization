import ImbalancedChen.Part3Gamma0CompactTensorPoincareLocalFinite
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual locally finite effective-Gamma0 Poincare sum of the existing
finite CompactTensor seed is Gamma0 invariant by a true effective-group
permutation of the summation index. Its positive-coordinate chart is C2:
actual Mobius denominators are nonzero by pinned UpperHalfPlane APIs,
each translated finite tensor chart is C2, and the proved local finite
formula identifies the actual Poincare chart with one finite C2 sum near
every positive-height coordinate point.

This supplies an actual automorphic C2 family. It does not turn the old
whole-plane tensor operator into an automorphic operator, and no quotient
operator closure, integration identity, spectral theorem or normalization
is claimed here.
-/

namespace ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a

noncomputable section

open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a

/-- Actual representative matrices act multiplicatively on H because
their classes agree in the proven effective action quotient. -/
theorem effectiveMatrixAction_mul (N : ℕ) (q r : effectiveGamma0 N)
    (z : UpperHalfPlane) :
    effectiveMatrixAction N (q * r) z =
      effectiveMatrixAction N q (effectiveMatrixAction N r z) := by
  change effectiveRepresentative N (q * r) • z =
    effectiveRepresentative N q • (effectiveRepresentative N r • z)
  rw [← mul_smul]
  apply same_effective_class_action N
  rw [QuotientGroup.mk_mul, effectiveRepresentative_class,
    effectiveRepresentative_class, effectiveRepresentative_class]

theorem effectiveMatrixAction_mk_gamma (N : ℕ)
    (γ : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    effectiveMatrixAction N (QuotientGroup.mk γ) z = γ • z :=
  same_effective_class_action N (effectiveRepresentative N (QuotientGroup.mk γ)) γ
    (effectiveRepresentative_class N (QuotientGroup.mk γ)) z

/-- This is invariance of the actual new Poincare object, obtained by
right multiplication on the actual effective Gamma0 summation group. -/
theorem finiteCompactTensorPoincare_gamma0_invariant (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor)
    (γ : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    finiteCompactTensorPoincare N s T (γ • z) = finiteCompactTensorPoincare N s T z := by
  unfold finiteCompactTensorPoincare
  calc
    (∑' q : effectiveGamma0 N,
        finiteCoreFunction s T (effectiveMatrixAction N q (γ • z))) =
      ∑' q : effectiveGamma0 N,
        finiteCoreFunction s T
          (effectiveMatrixAction N (q * QuotientGroup.mk γ) z) := by
      apply tsum_congr
      intro q
      rw [← effectiveMatrixAction_mk_gamma N γ z, ← effectiveMatrixAction_mul]
    _ = ∑' q : effectiveGamma0 N,
        finiteCoreFunction s T (effectiveMatrixAction N q z) :=
      (Equiv.mulRight (QuotientGroup.mk γ : effectiveGamma0 N)).tsum_eq
        (fun q => finiteCoreFunction s T (effectiveMatrixAction N q z))

/-- The literal real coordinate chart, with positive-height domain below. -/
def complexOfPair (p : ℝ × ℝ) : ℂ := ⟨p.1, p.2⟩

def positiveChart : Set (ℝ × ℝ) := {p | 0 < p.2}

def chartLift (p : ℝ × ℝ) : UpperHalfPlane :=
  UpperHalfPlane.ofComplex (complexOfPair p)

private theorem complexOfPair_contDiff : ContDiff ℝ 2 complexOfPair := by
  have heq : complexOfPair = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by
    funext p
    ext <;> simp [complexOfPair]
  rw [heq]
  fun_prop

theorem chartLift_of_positive {p : ℝ × ℝ} (hp : 0 < p.2) :
    chartLift p = (⟨complexOfPair p, hp⟩ : UpperHalfPlane) :=
  UpperHalfPlane.ofComplex_apply ⟨complexOfPair p, hp⟩

private theorem chartLift_continuousAt {p : ℝ × ℝ} (hp : 0 < p.2) :
    ContinuousAt chartLift p := by
  exact (UpperHalfPlane.contMDiffAt_ofComplex (n := 2) hp).continuousAt.comp
    complexOfPair_contDiff.continuous.continuousAt

/-- Rational Mobius formula for an actual integral special-linear matrix. -/
def mobiusComplex (g : SL(2, ℤ)) (p : ℝ × ℝ) : ℂ :=
  UpperHalfPlane.num (SpecialLinearGroup.mapGL ℝ g) (complexOfPair p) /
    UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ g) (complexOfPair p)

def mobiusChart (g : SL(2, ℤ)) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((mobiusComplex g p).re, (mobiusComplex g p).im)

/-- The real matrix has determinant one; its denominator cannot vanish
at a genuine positive-height point by the pinned SL/GL action theorem. -/
theorem mobius_denom_ne_zero (g : SL(2, ℤ)) {p : ℝ × ℝ} (hp : 0 < p.2) :
    UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ g) (complexOfPair p) ≠ 0 :=
  UpperHalfPlane.denom_ne_zero (SpecialLinearGroup.mapGL ℝ g)
    (⟨complexOfPair p, hp⟩ : UpperHalfPlane)

/-- The true coordinate action is C2 at every positive-height point. -/
theorem mobiusChart_contDiffAt (g : SL(2, ℤ)) {p : ℝ × ℝ} (hp : 0 < p.2) :
    ContDiffAt ℝ 2 (mobiusChart g) p := by
  have hn : ContDiff ℝ 2 (fun p =>
      UpperHalfPlane.num (SpecialLinearGroup.mapGL ℝ g) (complexOfPair p)) := by
    unfold UpperHalfPlane.num
    exact (contDiff_const.mul complexOfPair_contDiff).add contDiff_const
  have hd : ContDiff ℝ 2 (fun p =>
      UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ g) (complexOfPair p)) := by
    unfold UpperHalfPlane.denom
    exact (contDiff_const.mul complexOfPair_contDiff).add contDiff_const
  have hm : ContDiffAt ℝ 2 (mobiusComplex g) p :=
    hn.contDiffAt.div hd.contDiffAt (mobius_denom_ne_zero g hp)
  exact ((Complex.reCLM.contDiff.contDiffAt).comp p hm).prodMk
    ((Complex.imCLM.contDiff.contDiffAt).comp p hm)

/-- The rational coordinates agree with the actual integral action. -/
theorem mobiusChart_eq_actual (g : SL(2, ℤ)) {p : ℝ × ℝ} (hp : 0 < p.2) :
    mobiusChart g p = ((g • chartLift p).re, (g • chartLift p).im) := by
  rw [chartLift_of_positive hp]
  let z : UpperHalfPlane := ⟨complexOfPair p, hp⟩
  have hcoe : ((g • z : UpperHalfPlane) : ℂ) = mobiusComplex g p := by
    change (((SpecialLinearGroup.mapGL ℝ g) • z : UpperHalfPlane) : ℂ) = _
    exact UpperHalfPlane.coe_smul_of_det_pos (by simp) z
  exact Prod.ext (congrArg Complex.re hcoe.symm) (congrArg Complex.im hcoe.symm)

private theorem finiteChartFunction_contDiff {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    ContDiff ℝ 2 (finiteChartFunction s T) := by
  apply ContDiff.sum
  intro i _
  exact ((T i).horizontal_smooth.comp contDiff_fst).mul
    ((T i).vertical_smooth.comp contDiff_snd)

/-- A single actual effective translate of the literal finite seed in coordinates. -/
def translatedFiniteTensorChart (N : ℕ) (q : effectiveGamma0 N) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (p : ℝ × ℝ) : ℂ :=
  finiteChartFunction s T (mobiusChart (effectiveRepresentative N q : SL(2, ℤ)) p)

theorem translatedFiniteTensorChart_contDiffAt (N : ℕ) (q : effectiveGamma0 N)
    {ι : Type*} (s : Finset ι) (T : ι → CompactTensor)
    {p : ℝ × ℝ} (hp : 0 < p.2) :
    ContDiffAt ℝ 2 (translatedFiniteTensorChart N q s T) p :=
  (finiteChartFunction_contDiff s T).contDiffAt.comp p
    (mobiusChart_contDiffAt (effectiveRepresentative N q : SL(2, ℤ)) hp)

theorem translatedFiniteTensorChart_eq_actual (N : ℕ) (q : effectiveGamma0 N)
    {ι : Type*} (s : Finset ι) (T : ι → CompactTensor)
    {p : ℝ × ℝ} (hp : 0 < p.2) :
    translatedFiniteTensorChart N q s T p =
      finiteCoreFunction s T (effectiveMatrixAction N q (chartLift p)) := by
  unfold translatedFiniteTensorChart
  rw [mobiusChart_eq_actual _ hp]
  rfl

/-- Genuine C2 regularity of the actual automorphic Poincare object on
all positive real coordinates, using the proved local finite sum identity. -/
theorem finiteCompactTensorPoincare_contDiffOn_chart (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    ContDiffOn ℝ 2 (extendUpper (finiteCompactTensorPoincare N s T)) positiveChart := by
  intro p hp
  obtain ⟨U, hU, S, hS⟩ :=
    finiteCompactTensorPoincare_locally_eq_finsetSum N s T (chartLift p)
  have hpre : ∀ᶠ p' in 𝓝 p, chartLift p' ∈ U := (chartLift_continuousAt hp) hU
  have hpos : ∀ᶠ p' in 𝓝 p, 0 < p'.2 :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hp
  have heq : extendUpper (finiteCompactTensorPoincare N s T) =ᶠ[𝓝 p]
      (fun p' => ∑ q ∈ S, translatedFiniteTensorChart N q s T p') := by
    filter_upwards [hpre, hpos] with p' hpU hp'
    have hext : extendUpper (finiteCompactTensorPoincare N s T) p' =
        finiteCompactTensorPoincare N s T (chartLift p') := by
      rw [extendUpper, dif_pos hp', chartLift_of_positive hp']
      rfl
    rw [hext, hS (chartLift p') hpU]
    apply Finset.sum_congr rfl
    intro q _
    exact (translatedFiniteTensorChart_eq_actual N q s T hp').symm
  have hsum : ContDiffAt ℝ 2
      (fun p' => ∑ q ∈ S, translatedFiniteTensorChart N q s T p') p :=
    ContDiffAt.sum (fun q _ => translatedFiniteTensorChart_contDiffAt N q s T hp)
  exact (hsum.congr_of_eventuallyEq heq).contDiffWithinAt

end
end ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
