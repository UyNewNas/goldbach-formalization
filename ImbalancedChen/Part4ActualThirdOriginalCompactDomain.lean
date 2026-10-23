import ImbalancedChen.Part4ActualThirdFiniteDensityReserve

/-!
SOURCEONLY / UNCOMPILED. One exact semantic endpoint for the original
compact-third numerical obligation U2. The existing finite-reserve module
uses z > 1/100 and the strict old-cube gated kernel. The original numerical
review uses z >= 1/100 and the non-strict old cube. The lower face is a
proved proper affine null wall; the old-cube face is already paid pointwise
by actualExtendedThirdManuscript_indicator. No integral bound is assumed.

This equality does not prove the quoted compact allowance
144590669409566793572719 / 2^80. It changes no error allocation: the existing
u/4 analytic approximation, remaining 3u/4, and separate compiler reserve
are retained. The kernel uses the actual negative-delay linear sieve, with
the literal ideal cap and all its original gates. No P5 Buchstab is used.
-/

namespace ImbalancedChen.OriginalThirdCompactEndpointSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalThirdFiniteReserveSourceOnly

/-- The exact whole compact integral used by the original numerical review.
The right domain is 1/100 <= z <= y <= x <= 19/96 with
x+y+3z <= 299/500; the factor 4 is already in OrderedKernel. -/
theorem originalCompactThirdCorrection_eq_literal_closed_compact :
    originalCompactThirdCorrection =
      ∫ t in actualExtendedThirdManuscriptTailRegion 0 thirdPrefixRho ∩
          {t : Fin 3 → ℝ | (1 / 100 : ℝ) ≤ t 2},
        actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2) := by
  let A := actualExtendedThirdClosedOrderRegion thirdPrefixRho
  let B := actualExtendedThirdClosedOrderRegion (1 / 100)
  let T := actualExtendedThirdManuscriptTailRegion 0 thirdPrefixRho
  let S := A \ B
  let R := T ∩ {t : Fin 3 → ℝ | (1 / 100 : ℝ) ≤ t 2}
  let f : (Fin 3 → ℝ) → ℝ :=
    fun t => actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2)
  let g : (Fin 3 → ℝ) → ℝ :=
    fun t => actualExtendedThirdGatedKernel 0 (t 0) (t 1) (t 2)
  have hS : MeasurableSet S :=
    (measurableSet_actualExtendedThirdClosedOrderRegion thirdPrefixRho).diff
      (measurableSet_actualExtendedThirdClosedOrderRegion (1 / 100))
  have hcut : MeasurableSet {t : Fin 3 → ℝ | (1 / 100 : ℝ) ≤ t 2} :=
    (isClosed_le continuous_const (continuous_apply 2)).measurableSet
  have hR : MeasurableSet R :=
    (measurableSet_actualExtendedThirdManuscriptTailRegion 0 thirdPrefixRho).inter hcut
  let L : (Fin 3 → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) (2 : Fin 3)
  have hL : L ≠ 0 := by
    intro hzero
    have h := congrArg (fun J : (Fin 3 → ℝ) →L[ℝ] ℝ => J (fun _ => 1)) hzero
    norm_num [L] at h
  have hwall : volume {t : Fin 3 → ℝ | t 2 = (1 / 100 : ℝ)} = 0 := by
    simpa [L] using affinePrimeWall_volume_zero L hL (1 / 100)
  have hne : ∀ᵐ t : Fin 3 → ℝ ∂volume, t 2 ≠ (1 / 100 : ℝ) := by
    rw [ae_iff]
    simpa only [not_not] using hwall
  change (∫ t in S, g t) = ∫ t in R, f t
  rw [← integral_indicator hS, ← integral_indicator hR]
  apply integral_congr_ae
  filter_upwards [hne] with t htne
  by_cases htA : t ∈ A
  · by_cases hge : (1 / 100 : ℝ) ≤ t 2
    · have htS : t ∈ S := by
        refine ⟨htA, ?_⟩
        intro htB
        exact htne (le_antisymm htB.2.1 hge)
      have hRindicator : R.indicator f t = T.indicator f t := by
        by_cases htT : t ∈ T
        · rw [indicator_of_mem (show t ∈ R from ⟨htT, hge⟩),
            indicator_of_mem htT]
        · rw [indicator_of_notMem (show t ∉ R from fun ht => htT ht.1),
            indicator_of_notMem htT]
      rw [indicator_of_mem htS, hRindicator]
      have hman : T.indicator f t = A.indicator g t :=
        actualExtendedThirdManuscript_indicator 0 thirdPrefixRho t
      rw [indicator_of_mem htA] at hman
      exact hman.symm
    · have htB : t ∈ B := ⟨htA.1, (lt_of_not_ge hge).le, htA.2.2⟩
      have htS : t ∉ S := fun ht => ht.2 htB
      have htR : t ∉ R := fun ht => hge ht.2
      rw [indicator_of_notMem htS, indicator_of_notMem htR]
  · have htS : t ∉ S := fun ht => htA ht.1
    have htR : t ∉ R := fun ht => htA ht.1.1
    rw [indicator_of_notMem htS, indicator_of_notMem htR]

end
end ImbalancedChen.OriginalThirdCompactEndpointSourceOnly
