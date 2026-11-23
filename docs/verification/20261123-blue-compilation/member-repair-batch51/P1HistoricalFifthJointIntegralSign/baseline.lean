import ImbalancedChen.HistoricalFifthJointIntegralSupportP1
import ImbalancedChen.ActualExtendedThirdLowerFactorRegularity

/-!
Signs of the genuine historical fifth integrals.

The canonical continuous LOWER factor has an existing source-layer
monotonicity theorem. This does not assert monotonicity or positivity of
the finite signed arithmetic Rosser densities. All tuple sign statements
below retain positive-coordinate hypotheses or the actual positive Ico cell.
The two strict own-cube gates are also separated into their new annulus
and overlap, using the original inherited `old5` and stored `cap5`.
-/

namespace ImbalancedChen

noncomputable section

open MeasureTheory Set
open MathlibNt.SieveTheory
open scoped Classical BigOperators

/-- Arbitrary-rank version of the existing rank-three normalization. -/
theorem p1PrimeTupleMinusProfile_eq_lowerFactor {k : ℕ} (lambda : ℝ)
    (t : Fin (k + 1) → ℝ) (ht : 0 < t (Fin.last k)) :
    primeTupleMinusProfile lambda t =
      4 * actualExtendedThirdLowerFactor
        ((lambda - ∑ i, t i) / t (Fin.last k)) / t (Fin.last k) := by
  unfold primeTupleMinusProfile actualExtendedThirdLowerFactor thirdTailLowerFactor
  rw [Real.exp_neg]
  field_simp [ne_of_gt ht, ne_of_gt (Real.exp_pos Real.eulerMascheroniConstant)]
  <;> ring

theorem p1PrimeTupleMinusProfile_nonneg {k : ℕ} (lambda : ℝ)
    (t : Fin (k + 1) → ℝ) (ht : 0 < t (Fin.last k)) :
    0 ≤ primeTupleMinusProfile lambda t := by
  rw [p1PrimeTupleMinusProfile_eq_lowerFactor lambda t ht]
  exact div_nonneg (mul_nonneg (by norm_num)
    (actualExtendedThirdLowerFactor_nonneg _)) ht.le

/-- Monotonicity follows from the actual canonical lower-factor supplier. -/
theorem p1PrimeTupleMinusProfile_mono {k : ℕ} (t : Fin (k + 1) → ℝ)
    (ht : 0 < t (Fin.last k)) {old new : ℝ} (hlevel : old ≤ new) :
    primeTupleMinusProfile old t ≤ primeTupleMinusProfile new t := by
  rw [p1PrimeTupleMinusProfile_eq_lowerFactor old t ht,
    p1PrimeTupleMinusProfile_eq_lowerFactor new t ht]
  apply div_le_div_of_nonneg_right _ ht.le
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  apply monotone_actualExtendedThirdLowerFactor
  exact div_le_div_of_nonneg_right (sub_le_sub_right hlevel _) ht.le

theorem p1PrimeOwnCubeGatedProfile_eq_profile {k : ℕ} (lambda : ℝ)
    (t : Fin (k + 1) → ℝ) (ht : 0 < t (Fin.last k)) :
    primeOwnCubeGatedProfile lambda t = primeTupleMinusProfile lambda t := by
  unfold primeOwnCubeGatedProfile
  split_ifs with hg
  · rfl
  · have hratio : (lambda - ∑ i, t i) / t (Fin.last k) ≤ 2 := by
      apply (div_le_iff₀ ht).mpr
      have hh : lambda ≤ primeTupleOwnCubeForm t := le_of_not_gt hg
      unfold primeTupleOwnCubeForm at hh
      linarith
    rw [p1PrimeTupleMinusProfile_eq_lowerFactor lambda t ht,
      actualExtendedThirdLowerFactor_of_le_two hratio, mul_zero, zero_div]

theorem p1PrimeOwnCubeGatedProfile_nonneg {k : ℕ} (lambda : ℝ)
    (t : Fin (k + 1) → ℝ) (ht : 0 < t (Fin.last k)) :
    0 ≤ primeOwnCubeGatedProfile lambda t := by
  rw [p1PrimeOwnCubeGatedProfile_eq_profile lambda t ht]
  exact p1PrimeTupleMinusProfile_nonneg lambda t ht

theorem p1PrimeOwnCubeGatedProfile_mono {k : ℕ} (t : Fin (k + 1) → ℝ)
    (ht : 0 < t (Fin.last k)) {old new : ℝ} (hlevel : old ≤ new) :
    primeOwnCubeGatedProfile old t ≤ primeOwnCubeGatedProfile new t := by
  rw [p1PrimeOwnCubeGatedProfile_eq_profile old t ht,
    p1PrimeOwnCubeGatedProfile_eq_profile new t ht]
  exact p1PrimeTupleMinusProfile_mono t ht hlevel

namespace HistoricalPrefixCapData

theorem p1FifthJointCell_coordinates_pos (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 5 → Fin (D.m + 1))
    (t : Fin 5 → ℝ) (ht : t ∈ D.p1FifthJointCell j) (i : Fin 5) : 0 < t i := by
  have hx := logPrimeMeshCell_subset_box (by exact_mod_cast hab) D.m j ht.1
  exact (by exact_mod_cast ha : (0 : ℝ) < D.a).trans_le (mem_logPrimeBox.mp hx i).1

theorem p1FifthCellProfile_nonneg (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5)
    (t : Fin 5 → ℝ) (ht : t ∈ D.p1FifthJointCell j) :
    0 ≤ D.p1FifthCellProfile j t := by
  have hlevel : (D.old5 j : ℝ) ≤ D.cap5 j := by
    exact_mod_cast (D.levelCheck_sound hcheck).2.2 j hj
  exact mul_nonneg (sub_nonneg.mpr (p1PrimeOwnCubeGatedProfile_mono t
    (D.p1FifthJointCell_coordinates_pos ha hab j t ht _) hlevel))
    (Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr
      (D.p1FifthJointCell_coordinates_pos ha hab j t ht i).le))

theorem p1FifthCellIntegral_nonneg (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5) :
    0 ≤ D.fifthCellIntegral j := by
  rw [D.fifthCellIntegral_eq_integral ha hab j]
  exact setIntegral_nonneg (D.measurableSet_p1FifthJointCell j)
    (fun t ht => D.p1FifthCellProfile_nonneg ha hab hcheck j hj t ht)

theorem p1FifthCorrectionIntegral_nonneg (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true) :
    0 ≤ D.fifthCorrectionIntegral := by
  exact Finset.sum_nonneg (fun j hj => D.p1FifthCellIntegral_nonneg ha hab hcheck j hj)

theorem p1FifthHistoricalProfile_nonneg (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (hcheck : D.levelCheck = true) (t : Fin 5 → ℝ)
    (ht : ∀ i, 0 < t i) : 0 ≤ D.p1FifthHistoricalProfile t := by
  have hlevel : (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t) : ℝ) ≤
      D.exponent5 t := by
    exact_mod_cast D.exponent4_le_exponent5 hab hcheck t
  exact mul_nonneg (sub_nonneg.mpr (p1PrimeOwnCubeGatedProfile_mono t
    (ht _) hlevel)) (Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (ht i).le))

/-- Global kernel positivity uses its true compact support, rather than
assuming every point of the ambient tuple space has positive coordinates. -/
theorem p1FifthCorrectionKernel_nonneg (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (t : Fin 5 → ℝ) : 0 ≤ D.p1FifthCorrectionKernel t := by
  by_cases ht : t ∈ D.p1FifthJointUnion
  · obtain ⟨j, hj, htj⟩ : ∃ j ∈ D.cells5, t ∈ D.p1FifthJointCell j := by
      simpa only [p1FifthJointUnion, Set.mem_iUnion] using ht
    rw [D.p1FifthCorrectionKernel_on_jointCell hab.le j hj t htj]
    exact D.p1FifthCellProfile_nonneg ha hab hcheck j hj t htj
  · rw [D.p1FifthCorrectionKernel_outside_union hab.le t ht]

def p1FifthOwnCubeAnnulus (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : Set (Fin 5 → ℝ) :=
  D.p1FifthJointCell j ∩
    {t | (D.old5 j : ℝ) ≤ primeTupleOwnCubeForm t ∧
      primeTupleOwnCubeForm t < (D.cap5 j : ℝ)}

def p1FifthOwnCubeOverlap (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : Set (Fin 5 → ℝ) :=
  D.p1FifthJointCell j ∩ {t | primeTupleOwnCubeForm t < (D.old5 j : ℝ)}

def p1FifthAnnulusGainIntegral (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : ℝ :=
  ∫ t in D.p1FifthOwnCubeAnnulus j,
    primeTupleMinusProfile (D.cap5 j : ℝ) t * ∏ i, 1 / t i

def p1FifthOverlapIncrementIntegral (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : ℝ :=
  ∫ t in D.p1FifthOwnCubeOverlap j,
    (primeTupleMinusProfile (D.cap5 j : ℝ) t -
      primeTupleMinusProfile (D.old5 j : ℝ) t) * ∏ i, 1 / t i

theorem measurableSet_p1FifthOwnCubeAnnulus (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : MeasurableSet (D.p1FifthOwnCubeAnnulus j) := by
  have hf : Continuous (primeTupleOwnCubeForm (k := 4)) := by
    unfold primeTupleOwnCubeForm
    fun_prop
  exact (D.measurableSet_p1FifthJointCell j).inter
    (((isClosed_le continuous_const hf).measurableSet).inter
      (isOpen_lt hf continuous_const).measurableSet)

theorem measurableSet_p1FifthOwnCubeOverlap (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : MeasurableSet (D.p1FifthOwnCubeOverlap j) := by
  have hf : Continuous (primeTupleOwnCubeForm (k := 4)) := by
    unfold primeTupleOwnCubeForm
    fun_prop
  exact (D.measurableSet_p1FifthJointCell j).inter
    (isOpen_lt hf continuous_const).measurableSet

theorem p1FifthOwnCubeAnnulus_disjoint_overlap (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) :
    Disjoint (D.p1FifthOwnCubeAnnulus j) (D.p1FifthOwnCubeOverlap j) := by
  apply Set.disjoint_left.mpr
  intro t ha ho
  exact not_lt_of_ge ha.2.1 ho.2

theorem p1FifthOwnCubeDomain_eq_annulus_union_overlap (D : HistoricalPrefixCapData)
    (hcheck : D.levelCheck = true) (j : Fin 5 → Fin (D.m + 1))
    (hj : j ∈ D.cells5) :
    D.p1FifthJointCell j ∩ {t | primeTupleOwnCubeForm t < (D.cap5 j : ℝ)} =
      D.p1FifthOwnCubeAnnulus j ∪ D.p1FifthOwnCubeOverlap j := by
  have hlevel : (D.old5 j : ℝ) ≤ D.cap5 j := by
    exact_mod_cast (D.levelCheck_sound hcheck).2.2 j hj
  ext t
  constructor
  · rintro ⟨hm, hn⟩
    by_cases ho : primeTupleOwnCubeForm t < (D.old5 j : ℝ)
    · exact Or.inr ⟨hm, ho⟩
    · exact Or.inl ⟨hm, le_of_not_gt ho, hn⟩
  · rintro (⟨hm, _hlo, hn⟩ | ⟨hm, ho⟩)
    · exact ⟨hm, hn⟩
    · exact ⟨hm, ho.trans_le hlevel⟩

theorem p1FifthCellProfile_on_annulus (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (t : Fin 5 → ℝ)
    (ht : t ∈ D.p1FifthOwnCubeAnnulus j) :
    D.p1FifthCellProfile j t =
      primeTupleMinusProfile (D.cap5 j : ℝ) t * ∏ i, 1 / t i := by
  simp only [p1FifthCellProfile, primeOwnCubeGatedProfile,
    if_pos ht.2.2, if_neg (not_lt.mpr ht.2.1), sub_zero]

theorem p1FifthCellProfile_on_overlap (D : HistoricalPrefixCapData)
    (hcheck : D.levelCheck = true) (j : Fin 5 → Fin (D.m + 1))
    (hj : j ∈ D.cells5) (t : Fin 5 → ℝ)
    (ht : t ∈ D.p1FifthOwnCubeOverlap j) :
    D.p1FifthCellProfile j t =
      (primeTupleMinusProfile (D.cap5 j : ℝ) t -
        primeTupleMinusProfile (D.old5 j : ℝ) t) * ∏ i, 1 / t i := by
  have hlevel : (D.old5 j : ℝ) ≤ D.cap5 j := by
    exact_mod_cast (D.levelCheck_sound hcheck).2.2 j hj
  simp only [p1FifthCellProfile, primeOwnCubeGatedProfile,
    if_pos (ht.2.trans_le hlevel), if_pos ht.2]

theorem integrableOn_p1FifthRawWeightedProfile (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (lambda : ℝ)
    (j : Fin 5 → Fin (D.m + 1)) :
    IntegrableOn (fun t => primeTupleMinusProfile lambda t * ∏ i, 1 / t i)
      (D.p1FifthJointCell j) := by
  exact (integrableOn_logPrimeBox_test_cube (by exact_mod_cast ha)
    (primeTupleMinusProfile lambda)
    (continuousOn_primeTupleMinusProfile (by exact_mod_cast ha) lambda)).mono_set
      (fun _ ht => logPrimeMeshCell_subset_box (by exact_mod_cast hab) D.m j ht.1)

theorem p1FifthOwnCubeIcoIntegral_eq_rawDomain (D : HistoricalPrefixCapData)
    (lambda : ℝ) (j : Fin 5 → Fin (D.m + 1)) :
    primeOwnCubeIcoIntegral (D.a : ℝ) (D.b : ℝ) lambda D.m j
        ordinaryUpperFiveGateForms (D.fifthParentGateBounds j) =
      ∫ t in D.p1FifthJointCell j ∩ {t | primeTupleOwnCubeForm t < lambda},
        primeTupleMinusProfile lambda t * ∏ i, 1 / t i := by
  unfold primeOwnCubeIcoIntegral
  have hset : logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
      primeAffineGateRegion (primeOwnCubeGateForms ordinaryUpperFiveGateForms)
        (primeOwnCubeGateBounds lambda (D.fifthParentGateBounds j)) =
      D.p1FifthJointCell j ∩ {t | primeTupleOwnCubeForm t < lambda} := by
    ext t
    simp only [p1FifthJointCell, Set.mem_inter_iff,
      mem_primeOwnCubeGateRegion, Set.mem_setOf_eq]
    tauto
  rw [hset]

/-- Every new-only candidate is retained; the old/new overlap has its
literal profile difference. No integration wall is discarded. -/
theorem p1FifthCellIntegral_eq_annulus_add_overlap (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5) :
    D.fifthCellIntegral j =
      D.p1FifthAnnulusGainIntegral j + D.p1FifthOverlapIncrementIntegral j := by
  have hn := D.integrableOn_p1FifthRawWeightedProfile ha hab (D.cap5 j : ℝ) j
  have ho := D.integrableOn_p1FifthRawWeightedProfile ha hab (D.old5 j : ℝ) j
  have hnA := hn.mono_set
    (show D.p1FifthOwnCubeAnnulus j ⊆ D.p1FifthJointCell j from fun _ ht => ht.1)
  have hnO := hn.mono_set
    (show D.p1FifthOwnCubeOverlap j ⊆ D.p1FifthJointCell j from fun _ ht => ht.1)
  have hoO := ho.mono_set
    (show D.p1FifthOwnCubeOverlap j ⊆ D.p1FifthJointCell j from fun _ ht => ht.1)
  have hoverlap : D.p1FifthOverlapIncrementIntegral j =
      (∫ t in D.p1FifthOwnCubeOverlap j,
        primeTupleMinusProfile (D.cap5 j : ℝ) t * ∏ i, 1 / t i) -
      (∫ t in D.p1FifthOwnCubeOverlap j,
        primeTupleMinusProfile (D.old5 j : ℝ) t * ∏ i, 1 / t i) := by
    rw [p1FifthOverlapIncrementIntegral, ← integral_sub hnO hoO]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by ring)
  rw [fifthCellIntegral, D.p1FifthOwnCubeIcoIntegral_eq_rawDomain,
    D.p1FifthOwnCubeIcoIntegral_eq_rawDomain,
    D.p1FifthOwnCubeDomain_eq_annulus_union_overlap hcheck j hj,
    setIntegral_union (D.p1FifthOwnCubeAnnulus_disjoint_overlap j)
      (D.measurableSet_p1FifthOwnCubeOverlap j) hnA hnO,
    hoverlap, p1FifthAnnulusGainIntegral]
  change (_ + _) - _ = _ + (_ - _)
  ring

theorem p1FifthAnnulusGainIntegral_nonneg (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 5 → Fin (D.m + 1)) :
    0 ≤ D.p1FifthAnnulusGainIntegral j := by
  apply setIntegral_nonneg (D.measurableSet_p1FifthOwnCubeAnnulus j)
  intro t ht
  exact mul_nonneg (p1PrimeTupleMinusProfile_nonneg _ t
    (D.p1FifthJointCell_coordinates_pos ha hab j t ht.1 _))
    (Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr
      (D.p1FifthJointCell_coordinates_pos ha hab j t ht.1 i).le))

theorem p1FifthOverlapIncrementIntegral_nonneg (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5) :
    0 ≤ D.p1FifthOverlapIncrementIntegral j := by
  have hlevel : (D.old5 j : ℝ) ≤ D.cap5 j := by
    exact_mod_cast (D.levelCheck_sound hcheck).2.2 j hj
  apply setIntegral_nonneg (D.measurableSet_p1FifthOwnCubeOverlap j)
  intro t ht
  exact mul_nonneg (sub_nonneg.mpr (p1PrimeTupleMinusProfile_mono t
    (D.p1FifthJointCell_coordinates_pos ha hab j t ht.1 _) hlevel))
    (Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr
      (D.p1FifthJointCell_coordinates_pos ha hab j t ht.1 i).le))

theorem p1FifthCorrectionIntegral_eq_annulus_add_overlap (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true) :
    D.fifthCorrectionIntegral =
      (∑ j ∈ D.cells5, D.p1FifthAnnulusGainIntegral j) +
        ∑ j ∈ D.cells5, D.p1FifthOverlapIncrementIntegral j := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact D.p1FifthCellIntegral_eq_annulus_add_overlap ha hab hcheck j hj

end HistoricalPrefixCapData

end

end ImbalancedChen
