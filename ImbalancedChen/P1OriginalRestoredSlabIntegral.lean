import ImbalancedChen.P1ActualVariableFourthFifthCellTestLimit
import ImbalancedChen.P1CorrectedFifthStoredH45Check

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Exact common-old-gate/restored-new-gate partition of the ORIGINAL selected
corrected fifth integral. The moving old4 is the actual producer maximum.
Its strict gate is measurable by the true face-owning producer atoms.
Actual old/new own-cube suppliers give integrability; no desired integral
or signed finite-density monotonicity is an input. Old-wall equality is
retained in the restored slab, while the new own-cube gate stays strict.
-/

namespace ImbalancedChen.P1OriginalRestoredSlabIntegral
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1CorrectedFifthDensityDictionary
open P1ActualVariableFourthFifthCellTestLimit
open P1OriginalVariableFourthEligibilityPartition

abbrev Point5 := Fin 5 → ℝ

def oldGate (old4 : Point5 → ℝ) : Set Point5 := {t | primeTupleOwnCubeForm t < old4 t}
def newGate (new5 : ℝ) : Set Point5 := {t | primeTupleOwnCubeForm t < new5}
def commonRegion (K : Set Point5) (old4 : Point5 → ℝ) : Set Point5 := K ∩ oldGate old4
/-- The complement of the strict old gate includes its equality wall. -/
def restoredRegion (K : Set Point5) (old4 : Point5 → ℝ) (new5 : ℝ) : Set Point5 :=
  (K ∩ newGate new5) \ commonRegion K old4

def commonKernel (old4 : Point5 → ℝ) (new5 : ℝ) (t : Point5) : ℝ :=
  (primeTupleMinusProfile new5 t - primeTupleMinusProfile (old4 t) t) * ∏ i, 1 / t i

def restoredKernel (new5 : ℝ) (t : Point5) : ℝ :=
  primeTupleMinusProfile new5 t * ∏ i, 1 / t i

theorem measurableSet_newGate (new5 : ℝ) : MeasurableSet (newGate new5) := by
  have hc : Continuous (primeTupleOwnCubeForm (k := 4)) := by
    unfold primeTupleOwnCubeForm
    fun_prop
  exact (isOpen_lt hc continuous_const).measurableSet

theorem kernel_on_common (old4 : Point5 → ℝ) (new5 : ℝ) (t : Point5)
    (hlevel : old4 t ≤ new5) (hgate : t ∈ oldGate old4) :
    correctedCellKernel old4 new5 t = commonKernel old4 new5 t := by
  have hn : primeTupleOwnCubeForm t < new5 := hgate.trans_le hlevel
  simp only [correctedCellKernel, primeOwnCubeGatedProfile, if_pos hgate, if_pos hn,
    commonKernel]

theorem kernel_on_restored (K : Set Point5) (old4 : Point5 → ℝ) (new5 : ℝ)
    (t : Point5) (ht : t ∈ restoredRegion K old4 new5) :
    correctedCellKernel old4 new5 t = restoredKernel new5 t := by
  have ho : ¬ primeTupleOwnCubeForm t < old4 t := fun h => ht.2 ⟨ht.1.1, h⟩
  simp only [correctedCellKernel, primeOwnCubeGatedProfile, if_pos ht.1.2, if_neg ho,
    sub_zero, restoredKernel]

/-- Exact zero, including the entire old equality wall. This is why a
restored slab receives no old fifth term a second time. -/
theorem old_term_zero_on_restored (K : Set Point5) (old4 : Point5 → ℝ) (new5 : ℝ)
    (t : Point5) (ht : t ∈ restoredRegion K old4 new5) :
    primeOwnCubeGatedProfile (old4 t) t * (∏ i, 1 / t i) = 0 := by
  have ho : ¬ primeTupleOwnCubeForm t < old4 t := fun h => ht.2 ⟨ht.1.1, h⟩
  simp only [primeOwnCubeGatedProfile, if_neg ho, zero_mul]

theorem kernel_zero_outside_new (old4 : Point5 → ℝ) (new5 : ℝ) (t : Point5)
    (hlevel : old4 t ≤ new5) (hn : t ∉ newGate new5) :
    correctedCellKernel old4 new5 t = 0 := by
  have ho : ¬ primeTupleOwnCubeForm t < old4 t := fun h => hn (h.trans_le hlevel)
  simp only [correctedCellKernel, primeOwnCubeGatedProfile, if_neg hn, if_neg ho,
    sub_self, zero_mul]

/-- The common-kernel sign uses the canonical lower-factor monotonicity. -/
theorem commonKernel_nonneg (old4 : Point5 → ℝ) (new5 : ℝ) (t : Point5)
    (hpos : ∀ i, 0 < t i) (hlevel : old4 t ≤ new5) :
    0 ≤ commonKernel old4 new5 t := by
  exact mul_nonneg (sub_nonneg.mpr
    (p1PrimeTupleMinusProfile_mono t (hpos (Fin.last 4)) hlevel))
    (Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (hpos i).le))

theorem restoredKernel_nonneg (new5 : ℝ) (t : Point5) (hpos : ∀ i, 0 < t i) :
    0 ≤ restoredKernel new5 t := by
  exact mul_nonneg (p1PrimeTupleMinusProfile_nonneg new5 t (hpos (Fin.last 4)))
    (Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (hpos i).le))

/-- Measure-theoretic partition with no discarded boundary. The concrete
original-cell theorem below constructs every hypothesis from its sources. -/
theorem integral_partition (K : Set Point5) (old4 : Point5 → ℝ) (new5 : ℝ)
    (hK : MeasurableSet K) (hC : MeasurableSet (commonRegion K old4))
    (hint : IntegrableOn (correctedCellKernel old4 new5) K)
    (hlevel : ∀ t ∈ K, old4 t ≤ new5) :
    (∫ t in K, correctedCellKernel old4 new5 t) =
      (∫ t in commonRegion K old4, commonKernel old4 new5 t) +
        ∫ t in restoredRegion K old4 new5, restoredKernel new5 t := by
  have hR : MeasurableSet (restoredRegion K old4 new5) :=
    (hK.inter (measurableSet_newGate new5)).diff hC
  have hdis : Disjoint (commonRegion K old4) (restoredRegion K old4 new5) := by
    apply Set.disjoint_left.mpr
    intro t hc hr
    exact hr.2 hc
  have hunion : commonRegion K old4 ∪ restoredRegion K old4 new5 = K ∩ newGate new5 := by
    ext t
    constructor
    · rintro (hc | hr)
      · exact ⟨hc.1, hc.2.trans_le (hlevel t hc.1)⟩
      · exact hr.1
    · intro hn
      by_cases hc : t ∈ commonRegion K old4
      · exact Or.inl hc
      · exact Or.inr ⟨hn, hc⟩
  have hintC := hint.mono_set (show commonRegion K old4 ⊆ K from fun _ ht => ht.1)
  have hintR := hint.mono_set (show restoredRegion K old4 new5 ⊆ K from fun _ ht => ht.1.1)
  have hsplit := setIntegral_union hdis hR hintC hintR
  rw [hunion] at hsplit
  have hcommon : (∫ t in commonRegion K old4, correctedCellKernel old4 new5 t) =
      ∫ t in commonRegion K old4, commonKernel old4 new5 t := by
    apply setIntegral_congr_fun hC
    intro t ht
    exact kernel_on_common old4 new5 t (hlevel t ht.1) ht.2
  have hrestored : (∫ t in restoredRegion K old4 new5, correctedCellKernel old4 new5 t) =
      ∫ t in restoredRegion K old4 new5, restoredKernel new5 t := by
    apply setIntegral_congr_fun hR
    exact kernel_on_restored K old4 new5
  calc
    (∫ t in K, correctedCellKernel old4 new5 t) =
        ∫ t in K, (newGate new5).indicator (correctedCellKernel old4 new5) t := by
      apply setIntegral_congr_fun hK
      intro t ht
      by_cases hn : t ∈ newGate new5
      · rw [indicator_of_mem hn]
      · rw [indicator_of_not_mem hn]
        exact kernel_zero_outside_new old4 new5 t (hlevel t ht) hn
    _ = ∫ t in K ∩ newGate new5, correctedCellKernel old4 new5 t :=
      setIntegral_indicator (measurableSet_newGate new5)
    _ = _ := hsplit.trans (congrArg₂ (fun x y : ℝ => x + y) hcommon hrestored)

/-- The moving OLD4 gate is measurable on the true original cell. Its
producer eligibility is obtained from the existing complete face partition. -/
theorem measurable_common_actual_old4
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J5 : Finset (P1OriginalCoarseFifthContinuation.Label5 m))
    (j : P1OriginalCoarseFifthContinuation.Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    MeasurableSet (commonRegion (correctedOriginalCell e chi omega a m j)
      (originalVariableFourthProfile e chi omega m j rows licensed)) := by
  let K := correctedOriginalCell e chi omega a m j
  have hK : MeasurableSet K := P1OriginalFifthIntegral.truncatedCell_measurable e chi m omega a j
  have hform : Continuous (primeTupleOwnCubeForm (k := 4)) := by
    unfold primeTupleOwnCubeForm
    fun_prop
  have heq : commonRegion K (originalVariableFourthProfile e chi omega m j rows licensed) =
      ⋃ s : Pattern rows, (K ∩ liftedAtom rows s) ∩
        {t | primeTupleOwnCubeForm t < fixedOld4 (e : ℝ) (selectedSeed e m j) rows licensed s t} := by
    ext t
    constructor
    · intro ht
      have ha : t ∈ liftedAtom rows (actualPattern rows (firstFour t)) :=
        mem_actual_wallAtom rows (firstFour t)
      apply mem_iUnion.mpr
      refine ⟨actualPattern rows (firstFour t), ⟨ht.1, ha⟩, ?_⟩
      rw [← actualOld4_eq_fixed_on_atom e chi m omega J5 j hj rows licensed _ ht.1.2.1 ha]
      exact ht.2
    · intro ht
      obtain ⟨s, hs⟩ := mem_iUnion.mp ht
      refine ⟨hs.1.1, ?_⟩
      rw [actualOld4_eq_fixed_on_atom e chi m omega J5 j hj rows licensed s hs.1.1.2.1 hs.1.2]
      exact hs.2
  rw [heq]
  exact MeasurableSet.iUnion fun s =>
    (hK.inter (measurableSet_liftedAtom rows s)).inter
      ((isOpen_lt hform (continuous_fixedOld4 (e : ℝ) (selectedSeed e m j)
        rows licensed s)).measurableSet)

/-- Concrete original selected integral: both actual old/new weighted
profiles are integrable by their canonical suppliers, and finite h45
soundness supplies the comparison on the same true original cell. -/
theorem corrected_selected_integral_common_add_restored
    (D : HistoricalPrefixCapData)
    (J : Finset (P1CorrectedFifthDensityDictionary.Label5 D.m))
    (e : ℚ) (chi omega a : ℝ) (ha : 0 < a)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (hcheck : P1CorrectedFifthStoredH45Check.storedH45Check D J e rows = true)
    (j : P1CorrectedFifthDensityDictionary.Label5 D.m) (hj : j ∈ D.cells5 ∩ J) :
    correctedSelectedStoredIntegral D e chi omega a j rows licensed =
      (∫ t in commonRegion (correctedOriginalCell e chi omega a D.m j)
          (originalVariableFourthProfile e chi omega D.m j rows licensed),
        commonKernel (originalVariableFourthProfile e chi omega D.m j rows licensed) (D.cap5 j : ℝ) t) +
      ∫ t in restoredRegion (correctedOriginalCell e chi omega a D.m j)
          (originalVariableFourthProfile e chi omega D.m j rows licensed) (D.cap5 j : ℝ),
        restoredKernel (D.cap5 j : ℝ) t := by
  have hselected : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells
      e chi D.m omega (D.cells5 ∩ J) :=
    (P1OriginalCoarseFifthContinuation.mem_selectedFifthCells e chi D.m omega (D.cells5 ∩ J) j).mpr
      ⟨hj, (howned.2.2 j hj).1, (howned.2.2 j hj).2⟩
  have hK := P1OriginalFifthIntegral.truncatedCell_measurable e chi D.m omega a j
  have hC := measurable_common_actual_old4 e chi D.m omega a (D.cells5 ∩ J) j hselected rows licensed
  have hnew := P1OriginalFifthIntegral.integrableOn_gatedWeightedProfile e chi D.m omega ha j (D.cap5 j : ℝ)
  have hold := integrableOn_actualOld4_weight e chi D.m omega a ha (D.cells5 ∩ J) j hselected rows licensed
  have hint : IntegrableOn
      (correctedCellKernel (originalVariableFourthProfile e chi omega D.m j rows licensed) (D.cap5 j : ℝ))
      (correctedOriginalCell e chi omega a D.m j) := by
    simpa only [correctedCellKernel, actualOldTest, P1OriginalFifthIntegral.reciprocalWeight, sub_mul]
      using hnew.sub hold
  exact integral_partition _ _ _ hK hC hint (fun t ht =>
    P1CorrectedFifthStoredH45Check.originalVariableFourthProfile_le_storedCap
      D J e chi omega rows licensed howned hcheck j hj t ht.2.1)

/-- Both pieces have canonical lower-kernel signs on the actual original
cell. This does not use monotonicity of a finite signed density. -/
theorem corrected_split_integrals_nonneg
    (D : HistoricalPrefixCapData)
    (J : Finset (P1CorrectedFifthDensityDictionary.Label5 D.m))
    (e : ℚ) (chi omega a : ℝ) (ha : 0 < a)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (hcheck : P1CorrectedFifthStoredH45Check.storedH45Check D J e rows = true)
    (j : P1CorrectedFifthDensityDictionary.Label5 D.m) (hj : j ∈ D.cells5 ∩ J) :
    (0 ≤ ∫ t in commonRegion (correctedOriginalCell e chi omega a D.m j)
        (originalVariableFourthProfile e chi omega D.m j rows licensed),
      commonKernel (originalVariableFourthProfile e chi omega D.m j rows licensed) (D.cap5 j : ℝ) t) ∧
    (0 ≤ ∫ t in restoredRegion (correctedOriginalCell e chi omega a D.m j)
        (originalVariableFourthProfile e chi omega D.m j rows licensed) (D.cap5 j : ℝ),
      restoredKernel (D.cap5 j : ℝ) t) := by
  let K := correctedOriginalCell e chi omega a D.m j
  let old4 := originalVariableFourthProfile e chi omega D.m j rows licensed
  let new5 := (D.cap5 j : ℝ)
  have hselected : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells
      e chi D.m omega (D.cells5 ∩ J) :=
    (P1OriginalCoarseFifthContinuation.mem_selectedFifthCells e chi D.m omega (D.cells5 ∩ J) j).mpr
      ⟨hj, (howned.2.2 j hj).1, (howned.2.2 j hj).2⟩
  have hK : MeasurableSet K := P1OriginalFifthIntegral.truncatedCell_measurable e chi D.m omega a j
  have hC : MeasurableSet (commonRegion K old4) :=
    measurable_common_actual_old4 e chi D.m omega a (D.cells5 ∩ J) j hselected rows licensed
  have hR : MeasurableSet (restoredRegion K old4 new5) :=
    (hK.inter (measurableSet_newGate new5)).diff hC
  have hpos : ∀ t ∈ K, ∀ i, 0 < t i := by
    intro t ht i
    exact ha.trans_le (mem_logPrimeBox.mp ht.1 i).1
  have hlevel : ∀ t ∈ K, old4 t ≤ new5 := fun t ht =>
    P1CorrectedFifthStoredH45Check.originalVariableFourthProfile_le_storedCap
      D J e chi omega rows licensed howned hcheck j hj t ht.2.1
  constructor
  · exact setIntegral_nonneg hC (fun t ht =>
      commonKernel_nonneg old4 new5 t (hpos t ht.1) (hlevel t ht.1))
  · exact setIntegral_nonneg hR (fun t ht => restoredKernel_nonneg new5 t (hpos t ht.1.1))
/-- The OLD fifth weighted term integrates to exactly zero on the actual
restored slab. No boundary-measure exception is invoked. -/
theorem corrected_restored_old_integral_eq_zero
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a new5 : ℝ)
    (J5 : Finset (P1OriginalCoarseFifthContinuation.Label5 m))
    (j : P1OriginalCoarseFifthContinuation.Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    (∫ t in restoredRegion (correctedOriginalCell e chi omega a m j)
        (originalVariableFourthProfile e chi omega m j rows licensed) new5,
      primeOwnCubeGatedProfile (originalVariableFourthProfile e chi omega m j rows licensed t) t *
        (∏ i, 1 / t i)) = 0 := by
  have hC := measurable_common_actual_old4 e chi m omega a J5 j hj rows licensed
  have hR : MeasurableSet (restoredRegion (correctedOriginalCell e chi omega a m j)
      (originalVariableFourthProfile e chi omega m j rows licensed) new5) :=
    ((P1OriginalFifthIntegral.truncatedCell_measurable e chi m omega a j).inter
      (measurableSet_newGate new5)).diff hC
  calc
    _ = ∫ t in restoredRegion (correctedOriginalCell e chi omega a m j)
        (originalVariableFourthProfile e chi omega m j rows licensed) new5, (0 : ℝ) := by
      apply setIntegral_congr_fun hR
      exact old_term_zero_on_restored _ _ _
    _ = 0 := by simp

end
end ImbalancedChen.P1OriginalRestoredSlabIntegral