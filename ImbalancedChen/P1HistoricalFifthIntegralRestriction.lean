import ImbalancedChen.P1HistoricalLevelCheckPreservation
import ImbalancedChen.HistoricalFifthJointIntegralSupportP1

/-!
Fifth-only restrictions of the actual historical data, and their integrals.
Imports above name the eventual staged modules; both dependencies currently
live in the source-only P1 draft tree. No actual source is edited here.

Only the fifth selected finset changes. In particular the old fourth
ancestry, third parent gate and both literal own-cube factors are retained.
-/

namespace ImbalancedChen

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace HistoricalPrefixCapData

theorem p1RestrictFifth_cell3_unchanged (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) (j : Fin 3 → Fin (D.m + 1)) :
    (D.p1RestrictFifth I).cell3 j = D.cell3 j := by
  rfl

theorem p1RestrictFifth_old4_unchanged (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) (j : Fin 4 → Fin (D.m + 1)) :
    (D.p1RestrictFifth I).old4 j = D.old4 j := by
  rfl

theorem p1RestrictFifth_cell4_unchanged (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) (j : Fin 4 → Fin (D.m + 1)) :
    (D.p1RestrictFifth I).cell4 j = D.cell4 j := by
  rfl

theorem p1RestrictFifth_old5_ancestry (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) (j : Fin 5 → Fin (D.m + 1)) :
    (D.p1RestrictFifth I).old5 j =
      D.cell4 (historicalPrefixProject (by omega : 4 ≤ 5) j) := by
  rfl

theorem p1RestrictFifth_exponent3_unchanged (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) (t : Fin 3 → ℝ) :
    (D.p1RestrictFifth I).exponent3 t = D.exponent3 t := by
  rfl

theorem p1RestrictFifth_exponent4_unchanged (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) (t : Fin 4 → ℝ) :
    (D.p1RestrictFifth I).exponent4 t = D.exponent4 t := by
  rfl

theorem p1RestrictFifth_parentGateBounds (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) (j : Fin 5 → Fin (D.m + 1)) :
    (D.p1RestrictFifth I).fifthParentGateBounds j = D.fifthParentGateBounds j := by
  rfl

theorem p1RestrictFifth_jointCell (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) (j : Fin 5 → Fin (D.m + 1)) :
    (D.p1RestrictFifth I).p1FifthJointCell j = D.p1FifthJointCell j := by
  rfl

theorem p1RestrictFifth_historicalParent (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) :
    (D.p1RestrictFifth I).p1FifthHistoricalParent = D.p1FifthHistoricalParent := by
  rfl

theorem p1RestrictFifth_cellProfile (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) (j : Fin 5 → Fin (D.m + 1)) :
    (D.p1RestrictFifth I).p1FifthCellProfile j = D.p1FifthCellProfile j := by
  rfl

/-- This displays the literal profile: its old term is still the original
complete fourth history, and only the new fifth selector is restricted. -/
theorem p1RestrictFifth_literalProfile (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) (t : Fin 5 → ℝ) :
    (D.p1RestrictFifth I).p1FifthHistoricalProfile t =
      (primeOwnCubeGatedProfile ((D.p1RestrictFifth I).exponent5 t : ℝ) t -
        primeOwnCubeGatedProfile
          (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t) : ℝ) t) *
        ∏ i, 1 / t i := by
  rfl

/-- The raw cell integral does not depend on fifth selection. The old5
value and the earlier historical gate are unchanged by this construction. -/
theorem p1RestrictFifth_cellIntegral (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) (j : Fin 5 → Fin (D.m + 1)) :
    (D.p1RestrictFifth I).fifthCellIntegral j = D.fifthCellIntegral j := by
  rfl

theorem p1RestrictFifth_correctionIntegral_eq_sum (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) :
    (D.p1RestrictFifth I).fifthCorrectionIntegral =
      ∑ j ∈ D.cells5 ∩ I, D.fifthCellIntegral j := by
  rfl

theorem p1RestrictFifth_correctionIntegral_empty (D : HistoricalPrefixCapData) :
    (D.p1RestrictFifth ∅).fifthCorrectionIntegral = 0 := by
  rw [D.p1RestrictFifth_correctionIntegral_eq_sum]
  simp

theorem p1RestrictFifth_correctionIntegral_all (D : HistoricalPrefixCapData) :
    (D.p1RestrictFifth D.cells5).fifthCorrectionIntegral = D.fifthCorrectionIntegral := by
  rw [D.p1RestrictFifth_correctionIntegral_eq_sum, Finset.inter_self]
  rfl

/-- Additivity is for actual restricted historical data, not independent
copies of the old correction. No cap comparison or mean assumption is used. -/
theorem p1RestrictFifth_correctionIntegral_union (D : HistoricalPrefixCapData)
    (I J : Finset (Fin 5 → Fin (D.m + 1))) (hIJ : Disjoint I J) :
    (D.p1RestrictFifth (I ∪ J)).fifthCorrectionIntegral =
      (D.p1RestrictFifth I).fifthCorrectionIntegral +
        (D.p1RestrictFifth J).fifthCorrectionIntegral := by
  rw [D.p1RestrictFifth_correctionIntegral_eq_sum,
    D.p1RestrictFifth_correctionIntegral_eq_sum,
    D.p1RestrictFifth_correctionIntegral_eq_sum]
  have hset : D.cells5 ∩ (I ∪ J) = (D.cells5 ∩ I) ∪ (D.cells5 ∩ J) := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  rw [hset]
  apply Finset.sum_union
  apply Finset.disjoint_left.mpr
  intro j hi hj
  exact (Finset.disjoint_left.mp hIJ) (Finset.mem_inter.mp hi).2
    (Finset.mem_inter.mp hj).2

theorem p1RestrictFifth_correctionIntegral_partition (D : HistoricalPrefixCapData)
    (I J : Finset (Fin 5 → Fin (D.m + 1))) (hIJ : Disjoint I J)
    (hcover : I ∪ J = D.cells5) :
    D.fifthCorrectionIntegral =
      (D.p1RestrictFifth I).fifthCorrectionIntegral +
        (D.p1RestrictFifth J).fifthCorrectionIntegral := by
  have h := D.p1RestrictFifth_correctionIntegral_union I J hIJ
  rw [hcover, D.p1RestrictFifth_correctionIntegral_all] at h
  exact h

/-- Any fifth subfamily and its complement within the original selected
family partition the existing correction integral. -/
theorem p1RestrictFifth_correctionIntegral_complement (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) :
    D.fifthCorrectionIntegral =
      (D.p1RestrictFifth I).fifthCorrectionIntegral +
        (D.p1RestrictFifth (D.cells5 \ I)).fifthCorrectionIntegral := by
  have hdis : Disjoint (D.cells5 ∩ I) (D.cells5 \ I) := by
    apply Finset.disjoint_left.mpr
    intro j hi hj
    exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_inter.mp hi).2
  have hcover : (D.cells5 ∩ I) ∪ (D.cells5 \ I) = D.cells5 := by
    ext j
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hsame : D.p1RestrictFifth (D.cells5 ∩ I) = D.p1RestrictFifth I := by
    unfold p1RestrictFifth
    simp only [← Finset.inter_assoc, Finset.inter_self]
  rw [← hsame]
  exact D.p1RestrictFifth_correctionIntegral_partition _ _ hdis hcover

theorem p1RestrictFifth_jointUnion (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) :
    (D.p1RestrictFifth I).p1FifthJointUnion =
      ⋃ j ∈ D.cells5 ∩ I, D.p1FifthJointCell j := by
  rfl

theorem p1RestrictFifth_jointUnion_union (D : HistoricalPrefixCapData)
    (I J : Finset (Fin 5 → Fin (D.m + 1))) :
    (D.p1RestrictFifth (I ∪ J)).p1FifthJointUnion =
      (D.p1RestrictFifth I).p1FifthJointUnion ∪
        (D.p1RestrictFifth J).p1FifthJointUnion := by
  ext t
  simp only [p1RestrictFifth_jointUnion, Set.mem_union, Set.mem_iUnion,
    Finset.mem_inter, Finset.mem_union]
  aesop

theorem p1RestrictFifth_jointUnion_disjoint (D : HistoricalPrefixCapData)
    (I J : Finset (Fin 5 → Fin (D.m + 1))) (hIJ : Disjoint I J)
    (hab : D.a ≤ D.b) :
    Disjoint (D.p1RestrictFifth I).p1FifthJointUnion
      (D.p1RestrictFifth J).p1FifthJointUnion := by
  apply Set.disjoint_left.mpr
  intro t htI htJ
  obtain ⟨j, hj, htj⟩ : ∃ j ∈ D.cells5 ∩ I, t ∈ D.p1FifthJointCell j := by
    simpa only [p1RestrictFifth_jointUnion, Set.mem_iUnion] using htI
  obtain ⟨k, hk, htk⟩ : ∃ k ∈ D.cells5 ∩ J, t ∈ D.p1FifthJointCell k := by
    simpa only [p1RestrictFifth_jointUnion, Set.mem_iUnion] using htJ
  have hjk : j = k := logPrimeMeshCell_unique (by exact_mod_cast hab) htj.1 htk.1
  subst k
  exact (Finset.disjoint_left.mp hIJ) (Finset.mem_inter.mp hj).2
    (Finset.mem_inter.mp hk).2

theorem p1RestrictFifth_profile_on_kept_cell (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) (hab : D.a ≤ D.b)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5 ∩ I) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.p1RestrictFifth I).p1FifthHistoricalProfile t = D.p1FifthHistoricalProfile t := by
  rw [(D.p1RestrictFifth I).p1FifthHistoricalProfile_on_cell hab j hj t ht,
    D.p1FifthHistoricalProfile_on_cell hab j (Finset.mem_inter.mp hj).1 t ht]
  rfl

theorem p1RestrictFifth_profile_on_jointUnion (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) (hab : D.a ≤ D.b)
    (t : Fin 5 → ℝ) (ht : t ∈ (D.p1RestrictFifth I).p1FifthJointUnion) :
    (D.p1RestrictFifth I).p1FifthHistoricalProfile t = D.p1FifthHistoricalProfile t := by
  obtain ⟨j, hj, htj⟩ : ∃ j ∈ D.cells5 ∩ I, t ∈ D.p1FifthJointCell j := by
    simpa only [D.p1RestrictFifth_jointUnion, Set.mem_iUnion] using ht
  exact D.p1RestrictFifth_profile_on_kept_cell I hab j hj t htj.1

/-- Outside the retained mesh family the literal new5-old4 profile
cancels, including points outside the ambient cube. -/
theorem p1RestrictFifth_profile_outside (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) (t : Fin 5 → ℝ)
    (hout : ∀ j ∈ D.cells5 ∩ I,
      t ∉ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.p1RestrictFifth I).p1FifthHistoricalProfile t = 0 := by
  exact (D.p1RestrictFifth I).p1FifthHistoricalProfile_outside t hout

theorem p1RestrictFifth_profile_deleted (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) (hab : D.a ≤ D.b)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∉ I) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.p1RestrictFifth I).p1FifthHistoricalProfile t = 0 := by
  have hmem : j ∉ (D.p1RestrictFifth I).cells5 := by
    intro h
    exact hj (Finset.mem_inter.mp h).2
  exact (D.p1RestrictFifth I).p1FifthHistoricalProfile_on_unselected_cell
    hab j hmem t ht

theorem p1RestrictFifth_kernel_eq_indicator (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) (hab : D.a ≤ D.b) (t : Fin 5 → ℝ) :
    (D.p1RestrictFifth I).p1FifthCorrectionKernel t =
      ((D.p1RestrictFifth I).p1FifthJointUnion).indicator D.p1FifthCorrectionKernel t := by
  by_cases ht : t ∈ (D.p1RestrictFifth I).p1FifthJointUnion
  · rw [Set.indicator_of_mem ht]
    unfold p1FifthCorrectionKernel
    rw [D.p1RestrictFifth_historicalParent,
      D.p1RestrictFifth_profile_on_jointUnion I hab t ht]
  · rw [Set.indicator_of_notMem ht]
    exact (D.p1RestrictFifth I).p1FifthCorrectionKernel_outside_union hab t ht

theorem integrableOn_p1RestrictFifth_originalProfile (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) (ha : 0 < D.a) (hab : D.a < D.b) :
    IntegrableOn D.p1FifthHistoricalProfile (D.p1RestrictFifth I).p1FifthJointUnion := by
  have hk := (D.p1RestrictFifth I).integrable_p1FifthCorrectionKernel ha hab
  apply hk.integrableOn.congr
  filter_upwards [ae_restrict_mem
    (D.p1RestrictFifth I).measurableSet_p1FifthJointUnion] with t ht
  rw [D.p1RestrictFifth_kernel_eq_indicator I hab.le t, Set.indicator_of_mem ht]
  obtain ⟨j, _hj, htj⟩ : ∃ j ∈ D.cells5 ∩ I, t ∈ D.p1FifthJointCell j := by
    simpa only [p1RestrictFifth_jointUnion, Set.mem_iUnion] using ht
  exact if_pos ((D.p1FifthHistoricalParent_on_cell hab.le j t htj.1).mpr htj.2)

theorem p1RestrictFifth_correctionIntegral_eq_original_profile
    (D : HistoricalPrefixCapData) (I : Finset (Fin 5 → Fin (D.m + 1)))
    (ha : 0 < D.a) (hab : D.a < D.b) :
    (D.p1RestrictFifth I).fifthCorrectionIntegral =
      ∫ t in (D.p1RestrictFifth I).p1FifthJointUnion, D.p1FifthHistoricalProfile t := by
  rw [(D.p1RestrictFifth I).p1FifthCorrectionIntegral_eq_integral_historicalProfile ha hab]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem
    (D.p1RestrictFifth I).measurableSet_p1FifthJointUnion] with t ht
  exact D.p1RestrictFifth_profile_on_jointUnion I hab.le t ht

theorem p1RestrictFifth_correctionIntegral_eq_original_kernel
    (D : HistoricalPrefixCapData) (I : Finset (Fin 5 → Fin (D.m + 1)))
    (ha : 0 < D.a) (hab : D.a < D.b) :
    (D.p1RestrictFifth I).fifthCorrectionIntegral =
      ∫ t in (D.p1RestrictFifth I).p1FifthJointUnion, D.p1FifthCorrectionKernel t := by
  rw [(D.p1RestrictFifth I).p1FifthCorrectionIntegral_eq_integral_kernel ha hab,
    ← integral_indicator (D.p1RestrictFifth I).measurableSet_p1FifthJointUnion]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (D.p1RestrictFifth_kernel_eq_indicator I hab.le)

theorem p1RestrictFifth_integral_union_additive (D : HistoricalPrefixCapData)
    (I J : Finset (Fin 5 → Fin (D.m + 1))) (hIJ : Disjoint I J)
    (ha : 0 < D.a) (hab : D.a < D.b) :
    (∫ t in (D.p1RestrictFifth (I ∪ J)).p1FifthJointUnion,
      D.p1FifthHistoricalProfile t) =
      (∫ t in (D.p1RestrictFifth I).p1FifthJointUnion, D.p1FifthHistoricalProfile t) +
        (∫ t in (D.p1RestrictFifth J).p1FifthJointUnion, D.p1FifthHistoricalProfile t) := by
  rw [← D.p1RestrictFifth_correctionIntegral_eq_original_profile (I ∪ J) ha hab,
    ← D.p1RestrictFifth_correctionIntegral_eq_original_profile I ha hab,
    ← D.p1RestrictFifth_correctionIntegral_eq_original_profile J ha hab]
  exact D.p1RestrictFifth_correctionIntegral_union I J hIJ

theorem p1RestrictFifth_integral_complement (D : HistoricalPrefixCapData)
    (I : Finset (Fin 5 → Fin (D.m + 1))) (ha : 0 < D.a) (hab : D.a < D.b) :
    D.fifthCorrectionIntegral =
      (∫ t in (D.p1RestrictFifth I).p1FifthJointUnion, D.p1FifthHistoricalProfile t) +
        (∫ t in (D.p1RestrictFifth (D.cells5 \ I)).p1FifthJointUnion,
          D.p1FifthHistoricalProfile t) := by
  rw [← D.p1RestrictFifth_correctionIntegral_eq_original_profile I ha hab,
    ← D.p1RestrictFifth_correctionIntegral_eq_original_profile (D.cells5 \ I) ha hab]
  exact D.p1RestrictFifth_correctionIntegral_complement I

end HistoricalPrefixCapData

end

end ImbalancedChen
