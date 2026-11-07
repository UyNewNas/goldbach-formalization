import ImbalancedChen.Part3GammaActualCutoffWeakSeedReconstruction
import ImbalancedChen.Part3WholeUpperChartWeakH1Patching
import ImbalancedChen.Part3CoordinateLocalH1CompactProducts
import ImbalancedChen.Part3CompactSeedSmoothPlaneExtension

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
For an actual native minimal-adjoint defect, multiplication by ANY
compact smooth H coefficient produces a genuine compact planar H1 jet.
The coordinate rectangle and positive margins are constructed from its
compact support. Both weak first derivatives and their compact supports
come from the actual whole-chart H1 theorem and the proved weak Leibniz
construction. No adjoint form membership or weak gradient is assumed.
-/

namespace ImbalancedChen.Part3.GammaActualCompactWeakSeedH120261026b
noncomputable section
open Set Function Filter MeasureTheory
open scoped UpperHalfPlane Topology ContDiff
open MaassWeakOperatorCore20261024zz Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMinimalShiftRange20261025a
open Gamma0CompactDefectMollifier20261026a Gamma0CompactUpperChartExtension20261025a
open CompactSeedSmoothPlaneExtension20261025a WholeUpperChartWeakH1Patching20261026b
open ActualPullbackLocalH1Transfer20261026b CoordinateLocalH1CompactProducts20261026b
open GammaActualCutoffWeakSeedReconstruction20261026b
open WeakH1ProductMollifierDerivative20261026a LocalH1Tests20261026b

theorem coefficientSeed_zero_extension (N : ℕ) [NeZero N]
    (σ : UpperHalfPlane → ℂ) (f : QuotientL2 N) :
    extendUpper (compactCoefficientSeed N σ f) =
      fun p => extendUpper σ p * actualPlanePullback N f p := by
  funext p
  by_cases hp : 0 < p.2
  · simp [extendUpper, compactCoefficientSeed, actualPlanePullback, hp]
  · simp [extendUpper, actualPlanePullback, hp]

/-- Actual compact H1 seed with constructed rectangle, full first-jet
support control, and the literal original nonsmooth product value. -/
theorem actual_defect_compact_coefficient_H1 (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N)
    (σ : UpperHalfPlane → ℂ) (hc : HasCompactSupport σ)
    (hsm : ContDiffOn ℝ ∞ (extendUpper σ) positiveChart) :
    ∃ (L R a b : ℝ) (J : CompactH1Jet),
      0 < a ∧ L < R ∧ a < b ∧
      J.value = extendUpper (compactCoefficientSeed N σ f) ∧
      HasCompactSupport J.dx ∧ HasCompactSupport J.dy ∧
      tsupport J.value ⊆ openRect L R a b ∧
      tsupport J.dx ⊆ openRect L R a b ∧ tsupport J.dy ⊆ openRect L R a b := by
  obtain ⟨hχ, hχc, hχpos⟩ := extendUpper_compact_cinfty_positive σ hc hsm
  obtain ⟨n, hn⟩ := compact_subset_chartRectangle hχc hχpos
  let L : ℝ := -((n : ℝ) + 1)
  let R : ℝ := (n : ℝ) + 1
  let a : ℝ := mollifierRadius (n+1)
  let b : ℝ := (n : ℝ) + 1
  have ha : 0 < a := mollifierRadius_pos _
  have hLR : L < R := by dsimp [L,R]; have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hab : a < b := by
    have hhalf : mollifierRadius (n+1) ≤ (1/2 : ℝ) := by
      unfold mollifierRadius
      apply one_div_le_one_div_of_le (by norm_num)
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      push_cast
      linarith
    dsimp [a,b]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hχrect : tsupport (extendUpper σ) ⊆ Icc L R ×ˢ Icc a b :=
    hn.trans (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hloc := actual_defect_every_positive_rectangle_H1 N f hf L R a b hLR.le hab.le ha
  obtain ⟨gx,gy,J,hval,hdx,hdy,hsv,hsx,hsy⟩ := coordinate_local_compact_product
    (measurableSet_Icc.prod measurableSet_Icc) hloc hχ hχc hχrect
  have hx : HasCompactSupport J.dx := hχc.of_isClosed_subset isClosed_tsupport hsx
  have hy : HasCompactSupport J.dy := hχc.of_isClosed_subset isClosed_tsupport hsy
  refine ⟨L,R,a,b,J,ha,hLR,hab,?_,hx,hy,hsv.trans hn,hsx.trans hn,hsy.trans hn⟩
  rw [coefficientSeed_zero_extension]
  exact hval

end
end ImbalancedChen.Part3.GammaActualCompactWeakSeedH120261026b
