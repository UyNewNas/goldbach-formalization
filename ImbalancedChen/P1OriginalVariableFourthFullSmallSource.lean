import ImbalancedChen.P1OriginalVariableFourthActiveMeshCover
import ImbalancedChen.P1OriginalVariableFourthSmallRemainder

/-!
Actual full original variable-fourth small-coordinate source and its
finite mesh partition. SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

Fallback cancellation is exact before any estimate. Every surviving
active branch is embedded in the ORIGINAL enlarged-cutoff small cell,
with equality of its actual signed residual. No signed subset-sum
inequality is asserted: the subsequent bound must sum absolute terms.
-/

namespace ImbalancedChen.P1OriginalVariableFourthFullSmallRemainder

noncomputable section
open scoped Classical BigOperators
open Set HistoricalThirdCoarse
open HistoricalThirdCoarse.P1OriginalUpperResidual
open HistoricalThirdCoarse.P1OriginalFourth
open P1OriginalCoarseContinuation P1OriginalCoarseFourthResidual
open P1OriginalFourthSmallPrimeStratification
open P1OriginalVariableFourthContinuation P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthFullSourceActivation P1OriginalVariableFourthActiveOnly
open P1OriginalVariableFourthActiveMeshCover

def fullSmallTuples (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (N cap : ℕ) : Finset (Fin 4 → ℕ) :=
  (admitted e chi m omega N cap).filter fun p => ∃ i, actualPrimeTupleLog N p i < a

/-- Literal omitted source on ALL originally admitted fourth tuples. -/
def fullSmallSource (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (N cap : ℕ) : ℝ :=
  ∑ p ∈ fullSmallTuples e chi m omega a N cap,
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      literalTupleResidualDifference (rawLevel (e : ℝ) chi m omega (N : ℝ))
        (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed) N cap p

def branchSmallTuples (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (N cap : ℕ) (label : Label m) : Finset (Fin 4 → ℕ) :=
  (fullSmallTuples e chi m omega a N cap).filter fun p =>
    actualPrimeTupleLog N p ∈ meshBranch m omega label

/-- Every actually admitted tuple has strictly positive log coordinates
and belongs to the original upper log-prime box, independently of cap. -/
theorem admitted_log_mem_original_box
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < N)
    (p : Fin 4 → ℕ) (hp : p ∈ admitted e chi m omega N cap) :
    actualPrimeTupleLog N p ∈ logPrimeBox (fun _ => 0) (fun _ => (19 / 96 : ℝ)) := by
  have hd := admitted_tuple_data (e : ℝ) chi m omega (19 / 96 : ℝ) N cap p hp
  have htpos := (admitted_log_data e chi m omega N cap hN p hp).2.2
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  apply mem_logPrimeBox.mpr
  intro i
  refine ⟨(htpos i).le, ?_⟩
  have hprimePos : (0 : ℝ) < p i := by exact_mod_cast (hd.2.1 i).pos
  have hu := Real.log_lt_log hprimePos (mem_roughPrimeUniverse_upper (hd.2.2.1 i))
  rw [Real.log_rpow (by exact_mod_cast (show 0 < N by omega))] at hu
  exact (div_lt_iff₀ hlogN).mpr (by simpa [actualPrimeTupleLog] using hu)

/-- Exact finite partition by the original half-open mesh and inclusive
activation flag, valid for arbitrary real arithmetic summands. -/
theorem sum_fullSmallTuples_eq_sum_branches
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (N cap : ℕ) (hN : 1 < N)
    (f : (Fin 4 → ℕ) → ℝ) :
    (∑ p ∈ fullSmallTuples e chi m omega a N cap, f p) =
      ∑ label : Label m, ∑ p ∈ branchSmallTuples e chi m omega a N cap label, f p := by
  simp only [branchSmallTuples, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hb := admitted_log_mem_original_box e chi m omega N cap hN p (Finset.mem_filter.mp hp).1
  obtain ⟨label, ht⟩ := exists_meshBranch m omega hb
  symm
  rw [Finset.sum_eq_single label]
  · rw [if_pos ht]
  · intro other _ho hne
    exact if_neg (fun hother => hne (meshBranch_unique m omega hother ht))
  · simp

/-- Both Theta branches vanish pointwise, with no arithmetic PLUS-sign
assumption and no estimate for an enlarged signed sum. -/
theorem literalResidual_zero_on_fallback_branch
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (N cap : ℕ) (hN : 1 < N) (label : Label m)
    (hl : label ∉ activeAdoptedLabels (e : ℝ) chi m)
    (p : Fin 4 → ℕ) (hp : p ∈ branchSmallTuples e chi m omega a N cap label) :
    literalTupleResidualDifference (rawLevel (e : ℝ) chi m omega (N : ℝ))
      (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed) N cap p = 0 := by
  obtain ⟨hp, ht⟩ := Finset.mem_filter.mp hp
  have hprime := (admitted_log_data e chi m omega N cap hN p (Finset.mem_filter.mp hp).1).2.1
  rw [literalResidual_eq_branch_profile (e : ℝ) chi m omega label N cap hN p
    (fun i => (hprime i).pos) ht]
  exact branch_residual_difference_zero (e : ℝ) chi m label hl rows licensed N cap p

/-- Actual surviving tuples are in the same fourth cell at omega/2.
This is a subset of a genuine nonnegative absolute/moment carrier, never
a licence to bound an absolute subset sum by an absolute signed total. -/
theorem active_branch_small_subset_half_cell
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (homega : 0 ≤ omega)
    (hmesh : logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2)
    (N cap : ℕ) (hN : 1 < N) (label : Label m)
    (hl : label ∈ activeAdoptedLabels (e : ℝ) chi m) :
    branchSmallTuples e chi m omega a N cap label ⊆
      smallCellTuples e chi m (omega / 2) a N cap label.1 := by
  intro p hp
  obtain ⟨hp, ht⟩ := Finset.mem_filter.mp hp
  obtain ⟨had, hsmall⟩ := Finset.mem_filter.mp hp
  have hd := admitted_tuple_data (e : ℝ) chi m omega (19 / 96 : ℝ) N cap p had
  have hflag := ((mem_activeAdoptedLabels (e : ℝ) chi m label).mp hl).1
  have hactive : omega ≤ actualPrimeTupleLog N p 2 := by
    simpa only [activationRegion, mem_setOf_eq, hflag, if_true] using ht.2
  have hadHalf : p ∈ admitted e chi m (omega / 2) N cap :=
    (admitted_cutoff_iff_on_active (e : ℝ) chi m (omega / 2) omega (by linarith)
      N cap hN p (fun i => (hd.2.1 i).pos) hd.1 hactive).mp had
  apply Finset.mem_filter.mpr
  exact ⟨hadHalf, (exists_small_iff_last
    (admitted_log_data e chi m omega N cap hN p had).1 a).mp hsmall, ht.1⟩

theorem active_branch_label_selected_half_of_occupied
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (hmesh : logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2)
    (N cap : ℕ) (label : Label m)
    (hl : label ∈ activeAdoptedLabels (e : ℝ) chi m)
    (p : Fin 4 → ℕ) (hp : p ∈ branchSmallTuples e chi m omega a N cap label) :
    label.1 ∈ selectedFourthCells e chi m (omega / 2) Finset.univ := by
  have ht := (Finset.mem_filter.mp hp).2
  have hlic := (mem_activeAdoptedLabels (e : ℝ) chi m label).mp hl
  have hactive : omega ≤ actualPrimeTupleLog N p 2 := by
    simpa only [activationRegion, mem_setOf_eq, hlic.1, if_true] using ht.2
  have hlo := meshLo_ge_half_of_active m label.1 ht.1 omega hactive hmesh
  apply (mem_selectedFourthCells e chi m (omega / 2) Finset.univ label.1).mpr
  refine ⟨Finset.mem_univ _, hlic.2, ?_⟩
  have hcast : (qLogPrimeMeshLo 0 (19 / 96) m (prefix3 label.1) 2 : ℝ) =
      logPrimeMeshLo 0 (19 / 96) m (prefix3 label.1) 2 := by
    simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using
      congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m (prefix3 label.1)) 2
  simpa only [hcast] using hlo

/-- The actual signed residual agrees after lowering the rough cutoff
on every surviving original tuple, before summation or absolute values. -/
theorem active_branch_literalResidual_eq_half
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (homega : 0 ≤ omega)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (N cap : ℕ) (hN : 1 < N) (label : Label m)
    (hl : label ∈ activeAdoptedLabels (e : ℝ) chi m)
    (p : Fin 4 → ℕ) (hp : p ∈ branchSmallTuples e chi m omega a N cap label) :
    literalTupleResidualDifference (rawLevel (e : ℝ) chi m omega (N : ℝ))
        (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed) N cap p =
      literalTupleResidualDifference (rawLevel (e : ℝ) chi m (omega / 2) (N : ℝ))
        (producerLevel4 (e : ℝ) chi m (omega / 2) (N : ℝ) rows licensed) N cap p := by
  obtain ⟨hp, ht⟩ := Finset.mem_filter.mp hp
  have had := (Finset.mem_filter.mp hp).1
  have hprime := (admitted_log_data e chi m omega N cap hN p had).2.1
  have hflag := ((mem_activeAdoptedLabels (e : ℝ) chi m label).mp hl).1
  have hactive : omega ≤ actualPrimeTupleLog N p 2 := by
    simpa only [activationRegion, mem_setOf_eq, hflag, if_true] using ht.2
  exact literalResidual_cutoff_eq_on_active (e : ℝ) chi m (omega / 2) omega
    (by linarith) N cap hN p (fun i => (hprime i).pos) hactive rows licensed

end
end ImbalancedChen.P1OriginalVariableFourthFullSmallRemainder
