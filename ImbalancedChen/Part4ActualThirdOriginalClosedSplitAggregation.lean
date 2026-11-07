import ImbalancedChen.Part4ActualThirdOriginalCompactDomain
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
SOURCEONLY / UNCOMPILED / OPEN30. Exact closed-split aggregation for original U2.
This is a new partition soundness step, not another proof of the already actual
strict/closed-domain equality. It imports that equality only at its final endpoint.
The actual kernel includes its factor 4, literal ideal cap, original old-cube gate,
and negative-delay linear-sieve lower function. Positive-delay Buchstab is absent.
Original K=8452171/1250000, C=1.96176252, rho=19/96, h=1/100 and both reserves
are untouched. No table-query interval or final numerical enclosure is a premise.
Every tree cut is an integer divided by the certifier's exact DEN=48000*2^24.
The trees represent actual closed cells intersected with the original domain.
Shared faces are proved null, not silently treated as disjoint closed sets.
A concrete complete tree and sound leaf numerical bounds remain necessary to
obtain 144590669409566793572719/2^80. No such numerical claim is made here.
-/

namespace ImbalancedChen.OriginalThirdCompactPartitionSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalThirdFiniteReserveSourceOnly

abbrev Point := Fin 3 → ℝ

def compactRegion : Set Point :=
  actualExtendedThirdManuscriptTailRegion 0 thirdPrefixRho ∩
    {t : Point | (1 / 100 : ℝ) ≤ t 2}

def compactKernel (t : Point) : ℝ :=
  actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2)

theorem measurableSet_compactRegion : MeasurableSet compactRegion := by
  exact (measurableSet_actualExtendedThirdManuscriptTailRegion 0 thirdPrefixRho).inter
    (isClosed_le continuous_const (continuous_apply 2)).measurableSet

/-- Integrability is obtained from the actual proved full gated kernel, rather
than supplied by a numerical certificate or assumed for the compact integral. -/
theorem integrableOn_compactKernel : IntegrableOn compactKernel compactRegion := by
  let A := actualExtendedThirdClosedOrderRegion thirdPrefixRho
  let T := actualExtendedThirdManuscriptTailRegion 0 thirdPrefixRho
  let g : Point → ℝ := fun t => actualExtendedThirdGatedKernel 0 (t 0) (t 1) (t 2)
  have hA : MeasurableSet A :=
    measurableSet_actualExtendedThirdClosedOrderRegion thirdPrefixRho
  have hT : MeasurableSet T :=
    measurableSet_actualExtendedThirdManuscriptTailRegion 0 thirdPrefixRho
  have hg : IntegrableOn g A :=
    integrableOn_actualExtendedThirdGatedKernel_full (by norm_num) (by norm_num)
  have hgi : Integrable (A.indicator g) := (integrable_indicator_iff hA).2 hg
  have heq : A.indicator g =ᵐ[volume] T.indicator compactKernel :=
    Filter.Eventually.of_forall fun t =>
      (actualExtendedThirdManuscript_indicator 0 thirdPrefixRho t).symm
  have hf : IntegrableOn compactKernel T :=
    (integrable_indicator_iff hT).1 (hgi.congr heq)
  exact hf.mono_set inter_subset_left

/-- Every coordinate face, including every integer-midpoint split face, is null. -/
theorem coordinate_face_volume_zero (j : Fin 3) (q : ℝ) :
    volume {t : Point | t j = q} = 0 := by
  let L : Point →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j
  have hL : L ≠ 0 := by
    intro hzero
    have h := congrArg (fun J : Point →L[ℝ] ℝ => J (fun _ => 1)) hzero
    norm_num [L] at h
  simpa [L] using affinePrimeWall_volume_zero L hL q

/-- The exact parent-removal/two-children-addition identity. Both children use
closed inequalities, exactly as the original rectangle subdivision does.
No integrability, null-face, enclosure, or final integral premise is assumed. -/
theorem compact_integral_closed_split {s : Set Point}
    (hs : MeasurableSet s) (hsub : s ⊆ compactRegion) (j : Fin 3) (q : ℝ) :
    (∫ t in s, compactKernel t) =
      (∫ t in s ∩ {t : Point | t j ≤ q}, compactKernel t) +
      (∫ t in s ∩ {t : Point | q ≤ t j}, compactKernel t) := by
  let sL := s ∩ {t : Point | t j ≤ q}
  let sR := s ∩ {t : Point | q ≤ t j}
  have hR : MeasurableSet sR :=
    hs.inter (isClosed_le continuous_const (continuous_apply j)).measurableSet
  have hI : IntegrableOn compactKernel s := integrableOn_compactKernel.mono_set hsub
  have hIL : IntegrableOn compactKernel sL := hI.mono_set inter_subset_left
  have hIR : IntegrableOn compactKernel sR := hI.mono_set inter_subset_left
  have hdis : AEDisjoint volume sL sR := by
    change volume (sL ∩ sR) = 0
    apply measure_mono_null _ (coordinate_face_volume_zero j q)
    intro t ht
    exact le_antisymm ht.1.2 ht.2.2
  have hcover : sL ∪ sR = s := by
    ext t
    constructor
    · intro ht
      rcases ht with ht | ht
      · exact ht.1
      · exact ht.1
    · intro ht
      rcases le_total (t j) q with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr ⟨ht, h⟩
  have hsum := setIntegral_union₀ hdis hR.nullMeasurableSet hIL hIR
  rw [hcover] at hsum
  exact hsum

/-- The original physical coordinate denominator, not a replacement mesh. -/
def coordinateDenominator : ℝ := 805306368000

theorem coordinateDenominator_eq_original :
    coordinateDenominator = 48000 * 2^24 := by
  norm_num [coordinateDenominator]

/-- A finite adaptive split history. Arbitrary priority selection does not affect
soundness; the certifier's midpoint integers instantiate the `cut` field. -/
inductive ClosedCutTree where
  | leaf : ClosedCutTree
  | split (axis : Fin 3) (cut : ℤ) (left right : ClosedCutTree) : ClosedCutTree

/-- The leaf list retains every child, including zero-contribution children.
This separates a covering partition from the certifier's positive-width heap. -/
def closedLeaves : ClosedCutTree → Set Point → List (Set Point) :=
  ClosedCutTree.rec
    (fun s => [s])
    (fun j m _left _right leftLeaves rightLeaves s =>
      leftLeaves (s ∩ {t : Point | t j ≤ (m : ℝ) / coordinateDenominator}) ++
      rightLeaves (s ∩ {t : Point | (m : ℝ) / coordinateDenominator ≤ t j}))

/-- Finite aggregation over the original-domain portions of all closed leaves.
This proves the measure/integral invariant for every finite adaptive history. -/
theorem integral_eq_sum_closedLeaves (tree : ClosedCutTree) {s : Set Point}
    (hs : MeasurableSet s) (hsub : s ⊆ compactRegion) :
    (∫ t in s, compactKernel t) =
      ((closedLeaves tree s).map (fun c => ∫ t in c, compactKernel t)).sum := by
  induction tree generalizing s with
  | leaf =>
      simp [closedLeaves]
  | split j m left right ihL ihR =>
      change (∫ t in s, compactKernel t) =
        ((closedLeaves left
          (s ∩ {t : Point | t j ≤ (m : ℝ) / coordinateDenominator}) ++
          closedLeaves right
          (s ∩ {t : Point | (m : ℝ) / coordinateDenominator ≤ t j})).map
          (fun c => ∫ t in c, compactKernel t)).sum
      rw [List.map_append, List.sum_append]
      have hmL : MeasurableSet
          (s ∩ {t : Point | t j ≤ (m : ℝ) / coordinateDenominator}) :=
        hs.inter (isClosed_le (continuous_apply j) continuous_const).measurableSet
      have hmR : MeasurableSet
          (s ∩ {t : Point | (m : ℝ) / coordinateDenominator ≤ t j}) :=
        hs.inter (isClosed_le continuous_const (continuous_apply j)).measurableSet
      rw [← ihL hmL (fun t ht => hsub ht.1),
        ← ihR hmR (fun t ht => hsub ht.1)]
      exact compact_integral_closed_split hs hsub j ((m : ℝ) / coordinateDenominator)

/-- U2's actual compact correction is exactly the leaf sum for any complete
finite closed split tree. The previously actual domain equality is only used,
not reproved. This makes no assertion about numerical bounds for those leaves. -/
theorem originalCompactThirdCorrection_eq_sum_closedLeaves (tree : ClosedCutTree) :
    originalCompactThirdCorrection =
      ((closedLeaves tree compactRegion).map
        (fun c => ∫ t in c, compactKernel t)).sum := by
  calc
    originalCompactThirdCorrection = ∫ t in compactRegion, compactKernel t :=
      OriginalThirdCompactEndpointSourceOnly.originalCompactThirdCorrection_eq_literal_closed_compact
    _ = _ := integral_eq_sum_closedLeaves tree measurableSet_compactRegion (fun _ ht => ht)

end
end ImbalancedChen.OriginalThirdCompactPartitionSourceOnly
