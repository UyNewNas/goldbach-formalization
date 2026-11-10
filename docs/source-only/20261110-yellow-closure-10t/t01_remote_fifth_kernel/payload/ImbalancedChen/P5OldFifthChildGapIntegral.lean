import ImbalancedChen.P5OldFifthFiveCoordinateBarycentric

/-! SOURCE ONLY / UNCOMPILED / READY=false / ZERO FORMAL CREDIT.
The actual grid1600 child frozen gap integral dominates its exact
32-vertex arithmetic mean times product child volume. This source does
not postulate an integral lower bound. The first-interval profile/Q_b
Jensen step and saved integer d payload remain separate. -/

namespace ImbalancedChen.P5OldFifthChildGapIntegral
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open VariableEnvelope
open P1OriginalVariableFourthContinuation
open P1OriginalFifthRawBoxSelectorEquivalence
open P1LiteralVariableFifthCompactSupplier
open P5OldFifthExact64ChildTiling
open P5OldFifthFrozenUpperSurrogate
open P5OldFifthFrozenGapConcavity
open P5OldFifthOneCoordinateVertexChord
open P5OldFifthFiveCoordinateTree
open P5OldFifthFiveCoordinateBarycentric

abbrev Word := Bool × Bool × Bool × Bool × Bool

def wordChoice (w : Word) : VertexChoice :=
  ![w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2]

theorem tree_eq_word_sum (picks : ParentPicks) (raw : FifthWireRow)
    (c : ChildIndex) (t : Point) :
    weightedVertexTree picks raw c allFiveCoordinates t =
      ∑ w : Word, vertexWeight raw c (wordChoice w) t *
        frozenGap picks raw (vertexPoint raw c (wordChoice w)) := by
  rw [weightedVertexTree_eq_32_words]
  simp only [Fintype.sum_prod_type]
  simp [wordChoice, corner_eq_vertexPoint, wordWeight_eq_vertexWeight]

theorem integrableOn_vertexWeight (raw : FifthWireRow)
    (c : ChildIndex) (ε : VertexChoice) :
    IntegrableOn (vertexWeight raw c ε) (childBox raw c) := by
  have hbox : childBox raw c =
      logPrimeBox (childLeft raw c) (childRight raw c) := by
    ext t
    simp [childBox, mem_logPrimeBox, childLeft, childRight]
  rw [hbox]
  unfold IntegrableOn vertexWeight coordinateFraction logPrimeBox
  rw [volume_pi, Measure.restrict_pi_pi]
  apply Integrable.fintype_prod
  intro i
  have hf : Continuous (fun x : ℝ =>
      if ε i then (x - childLeft raw c i) /
          (childRight raw c i - childLeft raw c i)
      else 1 - (x - childLeft raw c i) /
          (childRight raw c i - childLeft raw c i)) := by
    by_cases he : ε i <;> simp [he] <;> fun_prop
  exact hf.integrableOn_Icc.mono_set Ico_subset_Icc_self

private theorem finiteMax_insert_all {ι : Type*} (rows : Finset ι)
    (f : ι → ℝ) (a : ℝ) (r : ι) :
    finiteMax (insert r rows) (fun _ => True) f a =
      max (f r) (finiteMax rows (fun _ => True) f a) := by
  simp [finiteMax, finiteValues, Finset.image_insert,
    Finset.insert_comm, Finset.max'_insert]

private theorem continuous_finiteMax_moving {ι : Type*} (rows : Finset ι)
    (f : ι → Point → ℝ) (a : Point → ℝ) (ha : Continuous a) :
    (∀ r ∈ rows, Continuous (f r)) →
      Continuous (fun t => finiteMax rows (fun _ => True)
        (fun r => f r t) (a t)) := by
  induction rows using Finset.induction_on with
  | empty =>
      intro _
      simpa [finiteMax, finiteValues] using ha
  | @insert r rows hr ih =>
      intro hf
      have hcont := (hf r (Finset.mem_insert_self _ _)).sup
        (ih (fun s hs => hf s (Finset.mem_insert_of_mem hs)))
      simpa only [finiteMax_insert_all] using hcont

theorem continuous_frozenParentUpper (picks : ParentPicks) :
    Continuous (frozenParentUpper picks) := by
  unfold frozenParentUpper
  apply continuous_finiteMax_moving
  · unfold VariableEnvelope.B
    fun_prop
  · intro I _
    have hs : Continuous (fun t : Point => oldSubsetSum I t) := by
      unfold oldSubsetSum
      fun_prop
    have hp : Continuous (pickedUpperPlane (picks I)) := by
      fin_cases (picks I) <;>
        simp [pickedUpperPlane, VariableEnvelope.A,
          VariableEnvelope.C, VariableEnvelope.cap] <;> fun_prop
    exact hp.comp hs

theorem continuous_frozenGap (picks : ParentPicks)
    (raw : FifthWireRow) : Continuous (frozenGap picks raw) := by
  have hnew : Continuous (rawCandidate 0 raw) := by
    simp only [rawCandidate, mul_zero, sub_zero]
    apply continuous_v.comp
    fun_prop
  have hthreshold : Continuous ownCubeThreshold := by
    unfold ownCubeThreshold
    fun_prop
  exact hnew.sub ((continuous_frozenParentUpper picks).sup hthreshold)

theorem integrableOn_frozenGap (picks : ParentPicks)
    (raw : FifthWireRow) (c : ChildIndex) :
    IntegrableOn (frozenGap picks raw) (childBox raw c) := by
  have hclosed : IntegrableOn (frozenGap picks raw)
      (Icc (childLeft raw c) (childRight raw c)) :=
    (continuous_frozenGap picks raw).integrableOn_Icc
  apply hclosed.mono_set
  intro t ht
  exact ⟨fun i => (ht i).1, fun i => (ht i).2.le⟩

theorem integral_frozenGap_ge_32_vertex_mean
    (picks : ParentPicks) (raw : FifthWireRow) (c : ChildIndex) :
    (childVolume raw c / 32) *
        (∑ w : Word, frozenGap picks raw
          (vertexPoint raw c (wordChoice w))) ≤
      ∫ t in childBox raw c, frozenGap picks raw t := by
  let C := childBox raw c
  have hword : ∀ w : Word, IntegrableOn
      (fun t : Point => vertexWeight raw c (wordChoice w) t *
        frozenGap picks raw (vertexPoint raw c (wordChoice w))) C := by
    intro w
    exact (integrableOn_vertexWeight raw c (wordChoice w)).mul_const _
  have htree : IntegrableOn
      (weightedVertexTree picks raw c allFiveCoordinates) C := by
    simp only [tree_eq_word_sum]
    exact integrable_finset_sum _ (fun w _ => hword w)
  have hgap := integrableOn_frozenGap picks raw c
  have hmono :
      (∫ t in C, weightedVertexTree picks raw c allFiveCoordinates t) ≤
        ∫ t in C, frozenGap picks raw t := by
    apply setIntegral_mono_on htree hgap (childBox_measurable raw c)
    intro t ht
    exact fiveCoordinateTree_le_gap picks raw c t ht
  have htreeIntegral :
      (∫ t in C, weightedVertexTree picks raw c allFiveCoordinates t) =
        (childVolume raw c / 32) *
          ∑ w : Word, frozenGap picks raw
            (vertexPoint raw c (wordChoice w)) := by
    rw [tree_eq_word_sum,
      integral_finset_sum _ (fun w _ => hword w)]
    simp_rw [integral_mul_const,
      integral_vertexWeight_eq_childVolume_div_32]
    rw [Finset.mul_sum]
  exact htreeIntegral.symm.trans_le hmono

/-- This is the script's d-scale before binding a stored integer row:
each of the 32 actual vertex gaps is scaled by 32*1600. -/
def vertexD (picks : ParentPicks) (raw : FifthWireRow)
    (c : ChildIndex) : ℝ :=
  ∑ w : Word, (32 * 1600 : ℝ) *
    frozenGap picks raw (vertexPoint raw c (wordChoice w))

theorem integral_frozenGap_ge_vertexD
    (picks : ParentPicks) (raw : FifthWireRow) (c : ChildIndex) :
    childVolume raw c * vertexD picks raw c / (1024 * 1600) ≤
      ∫ t in childBox raw c, frozenGap picks raw t := by
  have h := integral_frozenGap_ge_32_vertex_mean picks raw c
  unfold vertexD
  rw [← Finset.mul_sum]
  convert h using 1 <;> ring

theorem integral_frozenGap_ge_saved_integer_d
    (picks : ParentPicks) (raw : FifthWireRow) (c : ChildIndex)
    (d : ℤ) (hd : (d : ℝ) = vertexD picks raw c) :
    childVolume raw c * (d : ℝ) / (1024 * 1600) ≤
      ∫ t in childBox raw c, frozenGap picks raw t := by
  rw [hd]
  exact integral_frozenGap_ge_vertexD picks raw c

end
end ImbalancedChen.P5OldFifthChildGapIntegral
