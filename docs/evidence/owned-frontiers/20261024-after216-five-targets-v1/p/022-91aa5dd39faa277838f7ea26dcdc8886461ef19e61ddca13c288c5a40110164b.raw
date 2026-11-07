import ImbalancedChen.Part4ActualThirdTailBound
import ImbalancedChen.ActualExtendedThirdFunctionalConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
SOURCEONLY / UNCOMPILED. One actual third-correction approximation endpoint.
The original h=1/100, rho=19/96, cap and Tnew are unchanged. The buffer and
mesh belong to the existing actual finite robust lookup. Its proved absolute
L1 approximation pays at most one quarter of the original density reserve, apart from
the compilation reserve. No full22 policy, compact numerical enclosure,
arithmetic density, compiler error or K bound is claimed or assumed.
The signed-ledger substitution already in the earlier104-line draft is reused
by reference, not copied or promoted. This adds a different finite-functional
consumer of the actual original tail. P4 uses the linear-sieve negative-delay
gap; none of the positive-delay Buchstab suppliers from P5 is imported.
-/

namespace ImbalancedChen.OriginalThirdFiniteReserveSourceOnly

noncomputable section
open Set MeasureTheory

/-- The original density-approximation reserve u, not the compiler reserve. -/
def originalDensityReserve : ℝ :=
  145007961227048312210593427530128000784681 /
    11807308407697609823574244952794825721118720000

/-- Actual compact part of the original third correction. The old-cube gate
is retained in the original gated kernel. The face z=1/100 belongs to tail. -/
def originalCompactThirdCorrection : ℝ :=
  ∫ t in actualExtendedThirdClosedOrderRegion thirdPrefixRho \
      actualExtendedThirdClosedOrderRegion (1 / 100),
    actualExtendedThirdGatedKernel 0 (t 0) (t 1) (t 2)

/-- Exact domain split; no integrability or integral-identity premise. -/
theorem idealFunctional_eq_compact_add_original_tail :
    actualExtendedThirdIdealFunctional = originalCompactThirdCorrection +
      (∫ t in actualExtendedThirdManuscriptTailRegion 0 (1 / 100),
        actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2)) := by
  have hI := integrableOn_actualExtendedThirdGatedKernel_full
    (e := 0) (by norm_num) (by norm_num)
  have hsub : actualExtendedThirdClosedOrderRegion (1 / 100) ⊆
      actualExtendedThirdClosedOrderRegion thirdPrefixRho := by
    intro t ht
    rcases ht with ⟨hz, hzh, hzy, hyx, hx⟩
    exact ⟨hz, hzh.trans (by norm_num [thirdPrefixRho]), hzy, hyx, hx⟩
  have htail :
      (∫ t in actualExtendedThirdClosedOrderRegion (1 / 100),
        actualExtendedThirdGatedKernel 0 (t 0) (t 1) (t 2)) =
      (∫ t in actualExtendedThirdManuscriptTailRegion 0 (1 / 100),
        actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2)) := by
    symm
    rw [← integral_indicator
      (measurableSet_actualExtendedThirdManuscriptTailRegion 0 (1 / 100)),
      ← integral_indicator (measurableSet_actualExtendedThirdClosedOrderRegion (1 / 100))]
    exact integral_congr_ae
      (Filter.Eventually.of_forall (actualExtendedThirdManuscript_indicator 0 (1 / 100)))
  rw [actualExtendedThirdIdealFunctional_eq_gated]
  unfold originalCompactThirdCorrection
  rw [setIntegral_sdiff
    (measurableSet_actualExtendedThirdClosedOrderRegion (1 / 100)) hI hsub, htail]
  ring

/-- The proved original tail endpoint appears exactly once. -/
theorem idealFunctional_le_compact_add_Tnew :
    actualExtendedThirdIdealFunctional ≤ originalCompactThirdCorrection +
      (319683857488126290909150567 / 2^111 : ℝ) := by
  rw [idealFunctional_eq_compact_add_original_tail]
  linarith only
    [OriginalThirdTailActualIdealSourceOnly.original_manuscript_tail_integral_le_Tnew]

/-- A concrete actual finite-kernel endpoint charging only u/4 of original u.
One buffer threshold and one mesh threshold work for every subsequent e,m.
No ideal-cap bound, final integral, numerical compact bound or density premise
is passed in by the caller. This is a third-correction analytic error only. -/
theorem finiteFunctional_le_compact_add_Tnew_add_original_density_quarter :
    ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 384 ∧ ∃ m₀ : ℕ,
      ∀ e : ℝ, 0 ≤ e → e ≤ e₀ → ∀ m : ℕ, m₀ ≤ m →
        actualExtendedThirdFiniteFunctional e m ≤ originalCompactThirdCorrection +
          (319683857488126290909150567 / 2^111 : ℝ) + originalDensityReserve / 4 := by
  obtain ⟨e₀, he₀, he₀cap, m₀, happ⟩ :=
    actualExtendedThirdFiniteFunctional_uniform_approx
      (by norm_num [originalDensityReserve] : 0 < originalDensityReserve / 4)
  refine ⟨e₀, he₀, he₀cap, m₀, ?_⟩
  intro e he0 he m hm
  have hdiff : actualExtendedThirdFiniteFunctional e m -
      actualExtendedThirdIdealFunctional ≤ originalDensityReserve / 4 :=
    (le_abs_self _).trans (happ e he0 he m hm)
  calc
    actualExtendedThirdFiniteFunctional e m ≤
        actualExtendedThirdIdealFunctional + originalDensityReserve / 4 := by
      linarith only [hdiff]
    _ ≤ _ := by linarith only [idealFunctional_le_compact_add_Tnew]

end
end ImbalancedChen.OriginalThirdFiniteReserveSourceOnly
