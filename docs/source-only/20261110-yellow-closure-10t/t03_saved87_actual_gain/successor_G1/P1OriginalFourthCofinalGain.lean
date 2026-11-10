import ImbalancedChen.P1OriginalFourthTrimmedLimit
import ImbalancedChen.P1OriginalFourthGuillotine
import ImbalancedChen.P4AOriginalNewFifthUnion
import ImbalancedChen.P5OriginalCommonFourthSourceLedger

/-! The original stronger fourth-prefix scalar on the actual common
fourth integral used by beforeEight. Positive interior trims share
one e threshold and one q threshold; no integration over an unowned
rectangle or independent initial/third decision occurs. -/
namespace ImbalancedChen.P1OriginalFourthCofinalGain
noncomputable section
open Set Filter Topology MeasureTheory
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface P1OriginalPrefixRowDecodeSoundness
open P1OriginalFourthRowGap P1OriginalFourthTrimmedLimit P1OriginalFourthGuillotine
open P1OriginalFourthSavedQ80Total P5OriginalFourthFifthSourceInputs
open P1OriginalFourthUniformRowMargins P1OriginalFourthCommonHistoricalMesh
open P1OriginalFourthActualSourceCoverage P1OriginalFourthPhysicalKernelComparison
open P1OriginalVariableFourthContinuation P1OriginalVariableFourthFullSourceActivation
open P1OriginalVariableFourthActiveOnly P1OriginalVariableFourthFullActiveIntegral
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)
open P5OriginalCommonFourthSourceLedger (originalFourthIntegral)

def rowTest (r : FourthWireRow) (n : ℕ) : Point → ℝ := (box r).indicator (test r n)
def rowSum (xs : List FourthWireRow) (n : ℕ) (t : Point) : ℝ := (xs.map (fun r => rowTest r n t)).sum

private theorem integrable_rows (xs : List FourthWireRow) (n : ℕ)
    (hm : ∀ r ∈ xs, r ∈ originalFourthWireRows) :
    Integrable (rowSum xs n) := by
  induction xs with
  | nil => simpa [rowSum] using (integrable_zero Point ℝ volume)
  | cons r xs ih =>
    have h := (test_integrable r (hm _ List.mem_cons_self) n).integrable_indicator
      (measurableSet_logPrimeBox (left r) (right r))
    exact h.add (ih (fun y hy => hm _ (List.mem_cons_of_mem _ hy)))

theorem integral_rows (xs : List FourthWireRow) (n : ℕ)
    (hm : ∀ r ∈ xs, r ∈ originalFourthWireRows) :
    (∫ t, rowSum xs n t) = (xs.map (fun r => testIntegral r n)).sum := by
  induction xs with
  | nil => simp [rowSum]
  | cons r xs ih =>
    have hm' := fun y hy => hm y (List.mem_cons_of_mem _ hy)
    change (∫ t, rowTest r n t+rowSum xs n t) = testIntegral r n+_
    rw [integral_add ((test_integrable r (hm _ List.mem_cons_self) n).integrable_indicator
      (measurableSet_logPrimeBox _ _)) (integrable_rows xs n hm'),ih hm',rowTest,
      integral_indicator (measurableSet_logPrimeBox _ _)]
    <;> rfl

private theorem disjoint_sum_le (xs : List FourthWireRow) (n : ℕ) (t : Point) (C : ℝ)
    (hsep : xs.Pairwise Sep) (hC : 0 ≤ C) (hrow : ∀ r ∈ xs, rowTest r n t ≤ C) :
    rowSum xs n t ≤ C := by
  induction xs with
  | nil => simpa [rowSum] using hC
  | cons r xs ih =>
    have hs := List.pairwise_cons.mp hsep
    by_cases ht : t ∈ box r
    · have hz : ∀ x ∈ xs, rowTest x n t = 0 := by
        intro x hx
        exact indicator_of_notMem (fun ht' => (Set.disjoint_left.mp (hs.1 x hx)) ht ht') _
      have he : (xs.map (fun x => rowTest x n t)).sum = 0 := by
        suffices h : ∀ ys : List FourthWireRow, (∀ x ∈ ys, rowTest x n t = 0) →
            (ys.map (fun x => rowTest x n t)).sum = 0 from h xs hz
        intro ys
        induction ys with
        | nil => simp
        | cons y ys ih =>
          intro hy
          simp only [List.map_cons,List.sum_cons,hy y List.mem_cons_self,zero_add]
          exact ih (fun x hx => hy x (List.mem_cons_of_mem _ hx))
      simpa only [rowSum,List.map_cons,List.sum_cons,he,add_zero] using hrow r List.mem_cons_self
    · have hz : rowTest r n t = 0 := indicator_of_notMem ht _
      simpa only [rowSum,List.map_cons,List.sum_cons,hz,zero_add] using
        ih hs.2 (fun q hq => hrow _ (List.mem_cons_of_mem _ hq))

def branchTest (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (l : Label m) : Point → ℝ :=
  (positiveActiveCell e chi m omega l).indicator (branchRawKernel e chi m l originalRows4 originalAdmission4)
def branchSum (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (t : Point) : ℝ :=
  ∑ l ∈ activeAdoptedLabels (e:ℝ) chi m, branchTest e chi m omega l t

theorem test_le_actual (n : ℕ) (e : ℚ) (he : 0 < e) (hbe : (e:ℝ) ≤ buffer n)
    (chi : ℝ) (m : ℕ) (omega : ℝ) (hw : 0 < omega) (hw' : omega < 19/96)
    (hm : logPrimeMeshStep 0 (19/96) m ≤ omega/2)
    (hcover : ∀ r ∈ originalRows4, ∀ t ∈ trimmedBox r (trimWidth n),
      ∃ l ∈ activeAdoptedLabels (e:ℝ) chi m, t ∈ positiveActiveCell e chi m omega l) :
    testTotal n ≤ fullActiveIntegral e chi m omega originalRows4 originalAdmission4 := by
  have hb : 2*(e:ℝ) < commonMargin := by linarith only [hbe,buffer_margin n]
  have hI (l : Label m) (hl : l ∈ activeAdoptedLabels (e:ℝ) chi m) :
      Integrable (branchTest e chi m omega l) :=
    (integrableOn_branchRawKernel_full_active e he.le chi m omega hw hw' hm l hl _ _).integrable_indicator
      (positiveActiveCell_measurable _ _ _ _ _)
  have hG (l : Label m) (hl : l ∈ activeAdoptedLabels (e:ℝ) chi m) (t : Point) :
      0 ≤ branchTest e chi m omega l t := by
    by_cases ht : t ∈ positiveActiveCell e chi m omega l
    · simpa only [branchTest,indicator_of_mem ht] using
        (branchRawKernel_nonneg_le_initial_majorant e he.le chi m omega hw.le hm l hl _ _ ht).1
    · simp only [branchTest,indicator_of_notMem ht,le_refl]
  have hpt (t : Point) : rowSum originalFourthWireRows n t ≤ branchSum e chi m omega t := by
    have hnon : 0 ≤ branchSum e chi m omega t := Finset.sum_nonneg (fun l hl => hG l hl t)
    apply disjoint_sum_le _ _ _ _ original_half_open_disjoint hnon
    intro raw hr
    by_cases ht : t ∈ box raw
    · by_cases hit : t ∈ trimmedBox raw.toProducerRow (trimWidth n)
      · obtain ⟨l,hl,hcell⟩ := hcover _ (row_mem raw hr) t hit
        have h1 := raw_antitone raw hr hbe (buffer_margin n) t (box_subset raw ht)
        have h2 := buffered_row_kernel_le_actual_branch e he.le hb chi m omega l hl raw.toProducerRow
          (row_mem raw hr) t (box_subset raw ht) hcell
        have h3 : branchTest e chi m omega l t ≤ branchSum e chi m omega t :=
          Finset.single_le_sum (fun l hl => hG l hl t) hl
        rw [branchTest,indicator_of_mem hcell] at h3
        simpa only [rowTest,test,indicator_of_mem ht,indicator_of_mem hit] using h1.trans (h2.trans h3)
      · simpa only [rowTest,indicator_of_mem ht,test,indicator_of_notMem hit] using hnon
    · simpa only [rowTest,indicator_of_notMem ht] using hnon
  have hi := integral_mono (integrable_rows originalFourthWireRows n (fun _ h => h))
    (integrable_finset_sum _ (fun l hl => hI l hl)) hpt
  rw [integral_rows _ n (fun _ h => h)] at hi
  have hresult : (∫ t, branchSum e chi m omega t) =
      fullActiveIntegral e chi m omega originalRows4 originalAdmission4 := by
    rw [branchSum,integral_finset_sum _ (fun l hl => hI l hl),fullActiveIntegral]
    exact Finset.sum_congr rfl (fun l _ => integral_indicator (positiveActiveCell_measurable _ _ _ _ _))
  exact hi.trans_eq hresult

/-- G1 on the very scalar subtracted by beforeEight. The common
cutoff is free after e, the one common q may have any prior lower
threshold, and every larger q remains valid. -/
theorem exists_cofinal_original_fourth_gain (epsilon : ℝ) (heps : 0 < epsilon) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e:ℝ) < e0 →
      ∀ omega : ℝ, 0 < omega → omega ≤ 3/200 → ∀ mMin qMin : ℕ,
      ∃ q0 : ℕ, qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q →
        mMin ≤ refinedMesh q ∧ currentUpperEighteenGains 0-epsilon <
          originalFourthIntegral (P4AOriginalNewFifthUnion.original e q omega) := by
  have hs : currentUpperEighteenGains 0-epsilon <
      (originalFourthWireRows.map P1OriginalFourthRowQ80Integral.limitingRowIntegral).sum :=
    (sub_lt_self _ heps).trans_le adopted_gain_le_sum_limiting_row_integrals
  obtain ⟨n,hn⟩ := (finite_total_limit.eventually (lt_mem_nhds hs)).exists
  refine ⟨min (buffer n) (commonE0 (trimWidth n)),lt_min (buffer_pos n) (commonE0_pos (width_pos n)),?_⟩
  intro e he he0 omega hw hw' mMin qMin
  have hcut := lt_min_iff.mp he0
  obtain ⟨m0,hm0⟩ := eventually_atTop.1 ((tendsto_logPrimeMeshStep 0 (19/96:ℝ)).eventually
    (gt_mem_nhds (show 0 < omega/2 by positivity)))
  obtain ⟨q0,hq0,hq⟩ := exists_common_original_source_cover (trimWidth n) (width_pos n)
    e he hcut.2 omega hw' (max mMin m0) qMin
  refine ⟨q0,hq0,?_⟩
  intro q hqq
  obtain ⟨hm,hcover⟩ := hq q hqq
  have hstep := (hm0 _ ((le_max_right _ _).trans hm)).le
  exact ⟨(le_max_left _ _).trans hm,hn.trans_le (test_le_actual n e he hcut.1.le _ _ omega hw
    (by linarith only [hw']) hstep hcover)⟩

theorem exists_cofinal_union_fourth_gain (epsilon : ℝ) (heps : 0 < epsilon) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e:ℝ) < e0 →
      ∀ omega : ℝ, 0 < omega → omega ≤ 3/200 → ∀ mMin qMin : ℕ,
      ∃ q0 : ℕ, qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q →
        mMin ≤ refinedMesh q ∧ currentUpperEighteenGains 0-epsilon <
          originalFourthIntegral (P4AOriginalNewFifthUnion.data e q omega) :=
  exists_cofinal_original_fourth_gain epsilon heps

end
end ImbalancedChen.P1OriginalFourthCofinalGain
