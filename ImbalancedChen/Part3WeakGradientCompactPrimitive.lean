import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! SOURCE ONLY / UNCOMPILED / NO FORMAL CREDIT.
The missing one-dimensional compact primitive for weak-gradient rigidity.
Every smooth compact test of mean zero inside an open interval is the derivative
of a smooth compact test inside that same interval. No rigidity or regular
representative is assumed. -/
namespace ImbalancedChen.Part3.WeakGradientCompactPrimitive20261026a
noncomputable section
open Set Function MeasureTheory
open scoped ContDiff

def primitiveFrom (a : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in a..x, g t

theorem primitiveFrom_hasDerivAt (a : ℝ) {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
    HasDerivAt (primitiveFrom a g) (g x) x :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable a x)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

theorem primitiveFrom_deriv (a : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    deriv (primitiveFrom a g) = g := by
  funext x
  exact (primitiveFrom_hasDerivAt a hg x).deriv

theorem primitiveFrom_contDiff (a : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (primitiveFrom a g) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (primitiveFrom_hasDerivAt a hg.continuous x).differentiableAt, ?_⟩
  rw [primitiveFrom_deriv a hg.continuous]
  exact hg

theorem primitiveFrom_eq_zero_left {a b x : ℝ} {g : ℝ → ℝ}
    (hs : tsupport g ⊆ Ioo a b) (hx : x ≤ a) : primitiveFrom a g x = 0 := by
  change (∫ t in a..x, g t) = 0
  calc
    _ = ∫ _t in a..x, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_ge hx] at ht
      exact image_eq_zero_of_notMem_tsupport (fun h => not_lt_of_ge ht.2 (hs h).1)
    _ = 0 := by simp

theorem primitiveFrom_eq_zero_right {a b x : ℝ} {g : ℝ → ℝ}
    (hs : tsupport g ⊆ Ioo a b) (hmean : (∫ t, g t) = 0) (hx : b ≤ x) :
    primitiveFrom a g x = 0 := by
  change (∫ t in a..x, g t) = 0
  rw [intervalIntegral.integral_eq_integral_of_support_subset]
  · exact hmean
  · intro t ht
    have h := hs (subset_tsupport g ht)
    exact ⟨h.1, h.2.le.trans hx⟩

theorem primitiveFrom_support_subset {a b : ℝ} {g : ℝ → ℝ}
    (hs : tsupport g ⊆ Ioo a b) (hmean : (∫ t, g t) = 0) :
    support (primitiveFrom a g) ⊆ Icc a b := by
  intro x hx
  by_contra hnot
  simp only [mem_Icc, not_and_or, not_le] at hnot
  rcases hnot with hleft | hright
  · exact hx (primitiveFrom_eq_zero_left hs hleft.le)
  · exact hx (primitiveFrom_eq_zero_right hs hmean hright.le)

theorem primitiveFrom_tsupport_subset {a b : ℝ} {g : ℝ → ℝ}
    (hs : tsupport g ⊆ Ioo a b) (hmean : (∫ t, g t) = 0) :
    tsupport (primitiveFrom a g) ⊆ Icc a b :=
  closure_minimal (primitiveFrom_support_subset hs hmean) isClosed_Icc

theorem primitiveFrom_hasCompactSupport {a b : ℝ} {g : ℝ → ℝ}
    (hs : tsupport g ⊆ Ioo a b) (hmean : (∫ t, g t) = 0) :
    HasCompactSupport (primitiveFrom a g) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (primitiveFrom_support_subset hs hmean)

/-- Compactness gives a strictly smaller interval containing the support.
Both margins are genuine, so no boundary test is smuggled into the weak PDE. -/
theorem exists_inner_support_interval {a b : ℝ} {g : ℝ → ℝ}
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ioo a b)
    (hne : (tsupport g).Nonempty) :
    ∃ A B : ℝ, a < A ∧ B < b ∧ tsupport g ⊆ Ioo A B := by
  obtain ⟨l, hl, hmin⟩ := hc.exists_isMinOn hne (f := fun x : ℝ => x) continuous_id.continuousOn
  obtain ⟨r, hr, hmax⟩ := hc.exists_isMaxOn hne (f := fun x : ℝ => x) continuous_id.continuousOn
  refine ⟨(a + l) / 2, (r + b) / 2, ?_, ?_, ?_⟩
  · linarith [(hs hl).1]
  · linarith [(hs hr).2]
  · intro t ht
    have hlow : l ≤ t := hmin ht
    have hupp : t ≤ r := hmax ht
    constructor <;> linarith [(hs hl).1, (hs hr).2]

/-- The complete compact-antiderivative lemma used to turn a zero weak
derivative into annihilation of every zero-mean test on an interval. -/
theorem exists_compact_primitive_on_interval {a b : ℝ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ioo a b) (hmean : (∫ t, g t) = 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ioo a b ∧ deriv ψ = g := by
  rcases (tsupport g).eq_empty_or_nonempty with hempty | hne
  · have hgzero : g = 0 := by
      funext x
      exact image_eq_zero_of_notMem_tsupport (by simp [hempty])
    refine ⟨0, contDiff_const, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp [hgzero]
  · obtain ⟨A, B, haA, hBb, hsupport⟩ := exists_inner_support_interval hc hs hne
    refine ⟨primitiveFrom A g, primitiveFrom_contDiff A hg,
      primitiveFrom_hasCompactSupport hsupport hmean, ?_, primitiveFrom_deriv A hg.continuous⟩
    intro x hx
    have h := primitiveFrom_tsupport_subset hsupport hmean hx
    exact ⟨haA.trans_le h.1, h.2.trans_lt hBb⟩

/-- Weak derivative data, rather than a constancy premise, kills every
smooth compact zero-mean test. This is the analytic input to the fundamental lemma. -/
theorem integral_zero_mean_test_eq_zero {a b : ℝ} {f : ℝ → ℂ}
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ x, deriv ψ x • f x) = 0)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ioo a b) (hmean : (∫ x, g x) = 0) :
    (∫ x, g x • f x) = 0 := by
  obtain ⟨ψ, hψ, hψc, hψs, hderiv⟩ := exists_compact_primitive_on_interval hg hc hs hmean
  simpa only [hderiv] using hweak ψ hψ hψc hψs

end
end ImbalancedChen.Part3.WeakGradientCompactPrimitive20261026a