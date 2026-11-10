import ImbalancedChen.P1OriginalFourthCommonHistoricalMesh
import ImbalancedChen.P1OriginalVariableFourthFullActiveIntegral
import ImbalancedChen.P4AOriginalCompleteSixthChronology

/-! SOURCE_ONLY / UNCOMPILED.
Every original fourth row, not just an already licensed subset, enters
the actual positive active physical source on one pre-N common refinement.
The existing full-active source/admitted-prime dictionary supplies the
actual first/rank-three history and the inactive rank-four admission.
No integral bound, first-match partition or N-table soundness is assumed.
-/
namespace ImbalancedChen.P1OriginalFourthActualSourceCoverage
noncomputable section
open scoped Classical Topology
open Set VariableEnvelope HistoricalThirdCoarse
open P2OriginalFourthCapProducerInterface
open P5OriginalFourthFifthSourceInputs
open P1OriginalFourthAllRowsAdmission P1OriginalFourthUniformRowMargins
open P1OriginalFourthCommonHistoricalMesh
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthFullSourceActivation
open P1OriginalVariableFourthActiveOnly P1OriginalVariableFourthFullActiveIntegral
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)

private theorem source_of_actual_mesh
    (delta e chi omega : ℝ) (hd : 0 < delta) (he : 0 < e)
    (he0 : e < commonE0 delta) (homega : omega ≤ 3 / 200)
    (m : ℕ) (r : ProducerRow) (hr : r ∈ originalRows4) (t : Point)
    (ht : t ∈ trimmedBox r delta) (j3 : Cell m) (hj3 : j3 ∈ cells e chi m)
    (ht3 : P1OriginalFourthCommonHistoricalMesh.prefix3 t ∈ logPrimeMeshCell 0 (19 / 96) m j3)
    (hfirst : 3 * t 0 < exponent e chi m (P1OriginalFourthCommonHistoricalMesh.prefix3 t))
    (hcube : oldCube.eval t < exponent e chi m (P1OriginalFourthCommonHistoricalMesh.prefix3 t)) :
    ∃ label ∈ activeAdoptedLabels e chi m,
      t ∈ sourceBranch e chi m omega label := by
  have htbox := trimmedBox_subset r hd.le ht
  have hgeom := originalRows4_geometry r hr
  have ho := r.ordered hgeom t htbox
  have htop : t 0 ≤ (39 / 200 : ℝ) := by
    have hR : (r.upper 0 : ℝ) ≤ (39 / 200 : ℝ) := by exact_mod_cast hgeom.2.2.2.2.2.1
    exact (htbox.2 0).trans hR
  have hcut : (3 / 200 : ℝ) ≤ t 3 := by
    have hR : (3 / 200 : ℝ) ≤ (r.lower 3 : ℝ) := by exact_mod_cast hgeom.2.2.2.2.1
    exact hR.trans (htbox.1 3)
  have hrough : omega ≤ t 2 := homega.trans (hcut.trans ho.2.2)
  have hbox : t ∈ logPrimeBox (fun _ => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) := by
    apply mem_logPrimeBox.mpr
    intro i
    fin_cases i <;> constructor <;> linarith [ho.1.1,ho.1.2.1,ho.1.2.2.1,ho.2.2]
  obtain ⟨j4, ht4⟩ := exists_logPrimeMeshCell 0 (19 / 96) m hbox
  have hproj : HistoricalThirdCoarse.P1OriginalFourth.prefix3 j4 = j3 := by
    apply logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96)
    · exact mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht4
    · exact ht3
  let label : Label m := (j4,true)
  have hl : label ∈ activeAdoptedLabels e chi m := by
    apply (mem_activeAdoptedLabels e chi m label).mpr
    exact ⟨rfl, by simpa only [label,hproj] using hj3⟩
  have hbranch : t ∈ meshBranch m omega label := ⟨ht4,hrough⟩
  have hseed : branchSeed e chi m label =
      exponent e chi m (P1OriginalFourthCommonHistoricalMesh.prefix3 t) := by
    rw [← coordinateSeed_on_meshBranch e chi m omega label hbranch]
    exact if_pos hrough
  have hinit : 3 * t 0 < initial e := by
    have heB := (commonE0_bounds he0).2.2.2
    dsimp only [initial,extendedDistributionCap]
    linarith
  have hstop : t ∈ HistoricalThirdCoarse.P1OriginalFourth.firstStopRegion e m := by
    have ht0 := mem_logPrimeMeshCell.mp ht3 (0 : Fin 3)
    have hs := ((mem_cells e chi m j3).mp hj3).2.2.2.2.1
    refine ⟨j3 0, ?_, ?_, ?_⟩
    · simpa only [P1OriginalFourthCommonHistoricalMesh.prefix3,logPrimeMeshLo] using ht0.1
    · simpa only [P1OriginalFourthCommonHistoricalMesh.prefix3,logPrimeMeshHi] using ht0.2
    · simpa [box,qLogPrimeMeshHi] using hs
  refine ⟨label,hl,hbranch,?_,hstop⟩
  apply (HistoricalThirdCoarse.P1OriginalFourth.mem_gateRegion _ _ _).mpr
  rw [hseed]
  exact ⟨trimmedBox_strictAnti r hr hd t ht,hinit,hfirst,by simpa only [oldCube_eval] using hcube⟩

/-- Actual physical SOURCE coverage, with no caller row licence. Both
the source label and its historical gates are derived for each original
row, using ONE q-threshold for the entire 3,699,127-row input.
-/
theorem exists_common_original_source_cover (delta : ℝ) (hd : 0 < delta)
    (e : ℚ) (he : 0 < e) (he0 : (e : ℝ) < commonE0 delta)
    (omega : ℝ) (homega : omega ≤ 3 / 200) (mMin qMin : ℕ) :
    ∃ q0 : ℕ, qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q →
      mMin ≤ refinedMesh q ∧ ∀ r ∈ originalRows4, ∀ t : Point,
      t ∈ trimmedBox r delta →
      ∃ label ∈ activeAdoptedLabels (e : ℝ) ((e : ℝ)/20) (refinedMesh q),
        t ∈ positiveActiveCell e ((e : ℝ)/20) (refinedMesh q) omega label := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  obtain ⟨q0,hq0,hq⟩ := exists_common_actual_refined_mesh delta hd (e : ℝ) heR he0
    ((e : ℝ)/20) (by positivity) le_rfl mMin qMin
  refine ⟨q0,hq0,?_⟩
  intro q hqq
  refine ⟨(hq q hqq).1,?_⟩
  intro r hr t ht
  obtain ⟨j3,hj3,ht3,hfirst,hcube,_⟩ := (hq q hqq).2 r hr t ht
  obtain ⟨label,hl,hs⟩ := source_of_actual_mesh delta (e : ℝ) ((e : ℝ)/20) omega
    hd heR he0 homega (refinedMesh q) r hr t ht j3 hj3 ht3 hfirst hcube
  refine ⟨label,hl,?_,hs⟩
  have ho := r.ordered (originalRows4_geometry r hr) t (trimmedBox_subset r hd.le ht)
  intro i
  fin_cases i <;> linarith [ho.1.1,ho.1.2.1,ho.1.2.2.1,ho.2.1,ho.2.2]

/-- These are literally the fourth fields of the complete original
constructor consumed by the later original bank. No replacement licence
or fourth action is inserted by this attachment.
-/
theorem complete_data_fourth_fields (e : ℚ) (q : ℕ) (omega : ℝ) :
    (P4AOriginalCompleteSixthChronology.data e q omega).rows4 = originalRows4 ∧
    (P4AOriginalCompleteSixthChronology.data e q omega).licensed4 = originalAdmission4 ∧
    (P4AOriginalCompleteSixthChronology.data e q omega).m = refinedMesh q ∧
    (P4AOriginalCompleteSixthChronology.data e q omega).chi = (e : ℝ)/20 :=
  ⟨rfl,rfl,rfl,rfl⟩

/-- Each original row's endpoint occurs in the true common fourth
maximum, whose seed is the actual common third parent. This statement
does not equate that parent with an archived or ideal one.
-/
theorem original_row_le_complete_fourth (e : ℚ) (q : ℕ) (omega N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 4) (r : ProducerRow) (hr : r ∈ originalRows4)
    (ht : primeHistoryLogCoordinates N 4 pre ∈ r.box) :
    r.bufferedCandidate (e : ℝ) (primeHistoryLogCoordinates N 4 pre) ≤
      P5OriginalCommonRefinedConstructor.exponent4
        (P4AOriginalCompleteSixthChronology.data e q omega) N pre := by
  rw [P5OriginalCommonRefinedConstructor.exponent4,if_pos hlen]
  exact finiteMax_row_le _ _ _ _ r hr ⟨originalRows4_all_admitted r hr,ht⟩

/-- Actual prime admission follows from the physical source dictionary.
The rank-one stop, old third own first cube and third cube are not input;
they were derived by the common source coverage. Fourth rank is even.
-/
theorem exists_common_original_prime_admission (delta : ℝ) (hd : 0 < delta)
    (e : ℚ) (he : 0 < e) (he0 : (e : ℝ) < commonE0 delta)
    (omega : ℝ) (homega : omega ≤ 3 / 200) (mMin qMin : ℕ) :
    ∃ q0 : ℕ, qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q → mMin ≤ refinedMesh q ∧
      ∀ r ∈ originalRows4, ∀ N cap : ℕ, 1 < N →
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) → ∀ p : Fin 4 → ℕ,
      p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) →
      actualPrimeTupleLog N p ∈ trimmedBox r delta →
      p ∈ firstExitAdmittedTuples 4
        (HistoricalThirdCoarse.policy (e : ℝ) ((e : ℝ)/20) (refinedMesh q) omega (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) := by
  obtain ⟨q0,hq0,hq⟩ := exists_common_original_source_cover delta hd e he he0 omega homega mMin qMin
  refine ⟨q0,hq0,?_⟩
  intro q hqq
  refine ⟨(hq q hqq).1,?_⟩
  intro r hr N cap hN hcap p hpbox ht
  obtain ⟨label,_hl,hpositive,hs⟩ := (hq q hqq).2 r hr _ ht
  exact (mem_admitted_on_meshBranch_iff (e : ℝ) ((e : ℝ)/20) (refinedMesh q) omega 0
    N cap hN hcap p hpbox label hs.1).mpr hs

private theorem validSelection_mono_through_four
    (P R : Bool → List ℕ → Bool)
    (hPR : ∀ positive pre, pre.length ≤ 4 → P positive pre = true → R positive pre = true)
    (chosen pre : List ℕ) (positive : Bool) (hlen : pre.length + chosen.length ≤ 4)
    (hv : FirstExitValidSelection P pre positive chosen) :
    FirstExitValidSelection R pre positive chosen := by
  induction chosen generalizing pre positive with
  | nil => trivial
  | cons p ps ih =>
    refine ⟨hPR (!positive) (p :: pre) (by simp only [List.length_cons] at *; omega) hv.1,?_⟩
    apply ih (p :: pre) (!positive) (by simp only [List.length_cons] at *; omega) hv.2

/-- The actual common fourth policy retains the incoming old first and
third approvals. The rank-four even step introduces no extra rejection.
Only a real already-proved old word is transported here; the preceding
cofinal theorem obtains that word from the original row geometry.
-/
theorem original_valid_fourth_enters_complete_fourth
    (e : ℚ) (q : ℕ) (omega N : ℝ) (p : Fin 4 → ℕ)
    (hv : FirstExitValidSelection
      (HistoricalThirdCoarse.policy (e : ℝ) ((e : ℝ)/20) (refinedMesh q) omega N)
      [] true (List.ofFn p)) :
    FirstExitValidSelection
      (P5OriginalCommonRefinedConstructor.policy4 (P4AOriginalCompleteSixthChronology.data e q omega) N)
      [] true (List.ofFn p) := by
  apply validSelection_mono_through_four _ _ ?_ (List.ofFn p) [] true (by simp) hv
  intro positive pre hlen hp
  simp only [P5OriginalCommonRefinedConstructor.policy4,firstExitDepthSplicePolicy,if_pos hlen]
  change (HistoricalThirdCoarse.policy (e : ℝ) ((e : ℝ)/20) (refinedMesh q) omega N
    positive pre || _) = true
  simp only [hp,Bool.true_or]

/-- Off the original union, the old original fourth rule is inherited;
future prefixes retain the same selected own-four ancestor.
These are the existing policy's actual equalities, specialized to the
complete original licence now established in both directions.
-/
theorem original_fourth_policy_off_union (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (positive : Bool) (pre : List ℕ)
    (hout : primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre) ∉ originalBoxUnion) :
    producerPolicy4 e chi m omega N originalRows4 originalAdmission4 positive pre =
      HistoricalThirdCoarse.policy e chi m omega N positive pre := by
  apply producerPolicy4_outside_rows
  intro r hr ht
  apply hout
  rw [originalBoxUnion_eq_actual_eligible]
  exact ⟨r,hr,originalRows4_all_admitted r hr,ht⟩

theorem original_fourth_selected_ancestor_frozen (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (later pre : List ℕ) (hlen : 4 ≤ pre.length) :
    producerFrozenLevel4 e chi m omega N originalRows4 originalAdmission4 (later ++ pre) =
      producerFrozenLevel4 e chi m omega N originalRows4 originalAdmission4 pre :=
  producerFrozenLevel4_append e chi m omega N originalRows4 originalAdmission4 later pre hlen

end
end ImbalancedChen.P1OriginalFourthActualSourceCoverage
