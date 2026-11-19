import ImbalancedChen.P2Saving16ActionGatesClosedBox
import ImbalancedChen.PrimeHistoryLogCoordinates

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED. The actual y-prefix primes
use the same label upper corner, and one upper-corner cap works for their
square gates and all selected tents if the original eta pays the width. -/
namespace ImbalancedChen.P2Saving16ActualUpperCornerCap
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P4AFull87SamePieceCapVariation (coord_ancestor)
open P4AFull87CompilerChangedPartition P4AUpperTaggedFrozenAdmissionCatalogue
open P2CanonicalWallFullResidualPayment
open P4AOriginalFull87StrictActionTrim (trim trim_subset_source)
open P4AOriginalFull87SourceDictionary (Source selected newCap comparison)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P2OriginalSaving16Full87SourceBinding (sourceCell sourceRows_iff_full87_source)
open P4AOriginalOrderedThirdActualCoefficient (keep)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalR17EighthParent (orderedSixth)
open P4AOriginalFull87UnionHistory (sixthPolicy policy)
open P2Saving16FirstRowCompilerFibre P2Saving16SecondRowCompilerFibre
open P2Saving16SevenOrderRowsCarrier P2Saving16All96ClosedBox
open P2Saving16ActionGatesClosedBox

def upperCorner (N : ℕ) (tau : ℝ) (x : ℕ) : Fin 8 → ℝ := slotUpper N tau x

/-- The canonical prefix consists of actual prime factors, with no zero
padding when the original rank hypothesis holds. -/
theorem canonical_prime_pos {d : ℕ} (hrank : 8 ≤ d.primeFactorsList.length) (k : Fin 8) :
    0 < canonicalPrefix 8 d k := by
  have hm : canonicalPrefix 8 d k ∈ List.ofFn (canonicalPrefix 8 d) :=
    List.mem_ofFn.mpr ⟨k, rfl⟩
  rw [canonicalPrefix_ofFn hrank] at hm
  have hm' : canonicalPrefix 8 d k ∈ d.primeFactorsList.reverse :=
    (List.take_sublist 8 d.primeFactorsList.reverse).subset hm
  exact (Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hm')).pos

/-- Exact recovery of the actual canonical prime, before any endpoint
rounding or source-cell membership test. -/
theorem actual_prefix_rpow (N d : ℕ) (hN : 1 < (N : ℝ))
    (hrank : 8 ≤ d.primeFactorsList.length) (k : Fin 8) :
    (N : ℝ) ^ firstEightCoordinates N d k = (canonicalPrefix 8 d k : ℝ) := by
  have hp : (0 : ℝ) < (canonicalPrefix 8 d k : ℝ) := by
    exact_mod_cast canonical_prime_pos hrank k
  dsimp only [firstEightCoordinates]
  rw [coord_ancestor hrank]
  change (N : ℝ) ^ (Real.log (canonicalPrefix 8 d k : ℝ) / Real.log (N : ℝ)) = _
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hN),
    mul_div_cancel₀ _ (Real.log_pos hN).ne', Real.exp_log hp]

/-- The upper corner is in the very same closed label box. -/
theorem upperCorner_in_box (N x : ℕ) (tau : ℝ) (htau : 0 < tau) :
    ∀ k : Fin 8, slotLower N tau x k ≤ upperCorner N tau x k ∧
      upperCorner N tau x k ≤ slotUpper N tau x k := by
  intro k
  constructor
  · dsimp only [slotLower, upperCorner, slotUpper]
    linarith
  · rfl

/-- Both the witness and every member of its actual compiler fibre have
coordinates in the witness's own closed label box. -/
theorem witness_in_box (N x : ℕ) (tau : ℝ) (htau : 0 < tau)
    (hrank : 8 ≤ x.primeFactorsList.length) :
    ∀ k : Fin 8, slotLower N tau x k ≤ firstEightCoordinates N x k ∧
      firstEightCoordinates N x k ≤ slotUpper N tau x k := by
  intro k
  have hb := P2LowerFiniteCellRounding.primeLabel_halfopen N htau (canonicalPrefix 8 x k)
  have he : firstEightCoordinates N x k =
      Real.log (canonicalPrefix 8 x k : ℝ) / Real.log (N : ℝ) := by
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hrank]
    rfl
  rw [← he] at hb
  exact ⟨by simpa [slotLower] using hb.1, by simpa [slotUpper] using hb.2.le⟩

theorem fibre_in_box (N : ℕ) (w tau : ℝ) (htau : 0 < tau) {x y : ℕ}
    (hrank : 8 ≤ x.primeFactorsList.length)
    (hy : y ∈ cell (fun _ => []) N N w (cutoff N) tau x) :
    ∀ k : Fin 8, slotLower N tau x k ≤ firstEightCoordinates N y k ∧
      firstEightCoordinates N y k ≤ slotUpper N tau x k := by
  have hyrank : 8 ≤ y.primeFactorsList.length := by
    rw [cell_rank_preserved _ _ _ _ _ _ hy]
    exact hrank
  intro k
  have heq := cell_canonicalPrefix_label_eq (fun _ => []) N N w (cutoff N) tau hy hrank k
  have hb := P2LowerFiniteCellRounding.primeLabel_halfopen N htau (canonicalPrefix 8 y k)
  have he : firstEightCoordinates N y k =
      Real.log (canonicalPrefix 8 y k : ℝ) / Real.log (N : ℝ) := by
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hyrank]
    rfl
  rw [← heq, ← he] at hb
  exact ⟨by simpa [slotLower] using hb.1, by simpa [slotUpper] using hb.2.le⟩

/-- The cap corner is constant throughout this literal compiler fibre. -/
theorem upperCorner_eq_on_fibre (N : ℕ) (w tau : ℝ) {x y : ℕ}
    (hrank : 8 ≤ x.primeFactorsList.length)
    (hy : y ∈ cell (fun _ => []) N N w (cutoff N) tau x) :
    upperCorner N tau x = upperCorner N tau y := by
  funext k
  have h := cell_canonicalPrefix_label_eq (fun _ => []) N N w (cutoff N) tau hy hrank k
  simp only [upperCorner, slotUpper, h]

/-- The actual canonical prime tuple of every fibre member is bounded at
each slot by the witness's identical upper corner. -/
theorem actual_fibre_primes_le_upper (N : ℕ) (w tau : ℝ) (hN : 1 < (N : ℝ))
    (htau : 0 < tau) {x y : ℕ} (hrank : 8 ≤ x.primeFactorsList.length)
    (hy : y ∈ cell (fun _ => []) N N w (cutoff N) tau x) :
    ∀ k : Fin 8, (canonicalPrefix 8 y k : ℝ) ≤ (N : ℝ) ^ upperCorner N tau x k := by
  have hyrank : 8 ≤ y.primeFactorsList.length := by
    rw [cell_rank_preserved _ _ _ _ _ _ hy]
    exact hrank
  intro k
  rw [← actual_prefix_rpow N y hN hyrank k]
  exact Real.rpow_le_rpow_of_exponent_le hN.le ((fibre_in_box N w tau htau hrank hy k).2)

/-- In an ascending cell the upper-corner cap exceeds the same actual
R17 parent. No identification of their coefficients is asserted. -/
theorem actual_parent_lt_upper_cap
    (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (he : 0 ≤ e) (hcut : omega ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) (tau : ℝ) (htau : 0 < tau)
    (i : Fin 14) (x : ℕ) (hrank : 8 ≤ x.primeFactorsList.length)
    (htrim : firstEightCoordinates N x ∈ trim (sourceCell i) (width r)) :
    P4AOriginalR17EighthParent.parent n e q a omega N (rosserAncestor 8 x.primeFactorsList) <
      newCap (sourceCell i) (upperCorner N tau x) := by
  have hp := (source_witness_inherited_parent r n e q a omega he hcut hh N hN i x hrank htrim).2
  have hs : Source (sourceCell i) (firstEightCoordinates N x) :=
    trim_subset_source (sourceCell i) (width_pos r) htrim
  have hi := (P4AOriginalFull87SourceDictionary.source_improvement_terminal hs).1
  have hx := witness_in_box N x tau htau hrank
  have h0 := (hx 0).2
  have h7 := (hx 7).2
  have hm : newCap (sourceCell i) (firstEightCoordinates N x) ≤
      newCap (sourceCell i) (upperCorner N tau x) := by
    norm_num [sourceCell, newCap, P4AOriginalFull87SourceDictionary.newCap,
      P4AOriginalRemainingEighthSources.newCap, P4AOriginalRemainingEighthSources.descendingNew,
      P4AOriginalRemainingEighthSources.selectedSum, P4AOriginalRemainingEighthSources.selected,
      P4AOriginalRemainingEighthSources.eta, VariableEnvelope.A, Fin.sum_univ_succ] <;> linarith
  exact hp.trans_lt (hi.trans_le hm)

/-- The original eta pays the variation of one upper-corner cap across
all selected tents in the same closed box. The explicit lower bound is
eta-tau; it is positive only when `tau<eta`. -/
theorem upper_cap_selected_tent_gap (i : Fin 14) (N x : ℕ) (tau delta : ℝ)
    (htau : 0 < tau) (hwidth : 12*tau < delta) (hrank : 8 ≤ x.primeFactorsList.length)
    (htrim : firstEightCoordinates N x ∈ trim (sourceCell i) delta)
    (u : Fin 8 → ℝ)
    (hu : ∀ k : Fin 8, slotLower N tau x k ≤ u k ∧ u k ≤ slotUpper N tau x k) :
    P4AOriginalRemainingEighthSources.eta - tau ≤
      VariableEnvelope.v (∑ j ∈ selected (sourceCell i), u j) -
        newCap (sourceCell i) (upperCorner N tau x) := by
  have hs : Source (sourceCell i) u := (sourceRows_iff_full87_source i u).mp
    (original_all96_closed_box i N x tau delta htau hwidth hrank htrim u hu)
  have hbuf : newCap (sourceCell i) u =
      VariableEnvelope.v (∑ j ∈ selected (sourceCell i), u j) -
        P4AOriginalRemainingEighthSources.eta := by
    change P4AOriginalRemainingEighthSources.newCap (.ascending i) u =
      VariableEnvelope.v (P4AOriginalRemainingEighthSources.selectedSum (.ascending i) u) -
        P4AOriginalRemainingEighthSources.eta
    exact P4AOriginalRemainingEighthSources.source_newCap_eq_tent_buffer hs
  have h0 := (hu 0).1
  have h7 := (hu 7).1
  have hd0 : upperCorner N tau x 0 - u 0 ≤ tau := by
    dsimp only [upperCorner, slotUpper, slotLower] at h0 ⊢
    linarith
  have hd7 : upperCorner N tau x 7 - u 7 ≤ tau := by
    dsimp only [upperCorner, slotUpper, slotLower] at h7 ⊢
    linarith
  have hdiff : newCap (sourceCell i) (upperCorner N tau x) - newCap (sourceCell i) u ≤ tau := by
    norm_num [sourceCell, newCap, P4AOriginalFull87SourceDictionary.newCap,
      P4AOriginalRemainingEighthSources.newCap, P4AOriginalRemainingEighthSources.descendingNew,
      P4AOriginalRemainingEighthSources.selectedSum, P4AOriginalRemainingEighthSources.selected,
      P4AOriginalRemainingEighthSources.eta, VariableEnvelope.A, Fin.sum_univ_succ] <;> linarith
  linarith

/-- The actual prime tuple of a fibre member satisfies the full and
unselected-complement integer square gates at one upper-corner cap. -/
theorem actual_fibre_integer_gates
    (i : Fin 14) (N x : ℕ) (hN : 1 < (N : ℝ)) (w tau delta : ℝ)
    (htau : 0 < tau) (hwidth : 12*tau < delta)
    (hrank : 8 ≤ x.primeFactorsList.length)
    (htrim : firstEightCoordinates N x ∈ trim (sourceCell i) delta) {y : ℕ}
    (hy : y ∈ cell (fun _ => []) N N w (cutoff N) tau x) :
    (∀ j, ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j), canonicalPrefix 8 y k : ℕ) : ℝ) *
      (canonicalPrefix 8 y j : ℝ)^2 < (N : ℝ)^newCap (sourceCell i) (upperCorner N tau x)) ∧
    (∀ j ∉ selected (sourceCell i), ((∏ k ∈ selected (sourceCell i), canonicalPrefix 8 y k : ℕ) : ℝ) *
      ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j ∧ k ∉ selected (sourceCell i)), canonicalPrefix 8 y k : ℕ) : ℝ) *
      (canonicalPrefix 8 y j : ℝ)^2 < (N : ℝ)^newCap (sourceCell i) (upperCorner N tau x)) := by
  exact integer_gates_on_closed_box i N x hN tau delta htau hwidth hrank htrim
    (upperCorner N tau x) (upperCorner_in_box N x tau htau)
    (canonicalPrefix 8 y) (actual_fibre_primes_le_upper N w tau hN htau hrank hy)


/-- One physical fibre, one upper-corner exponent, the strict tent
licence, and the unaltered same-Q signed compiler expression. The
compiler identity here does not identify original corner coefficients. -/
theorem actual_upper_cap_same_Q_signed_product
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (he : 0 ≤ e) (hcut : nu * beta ^ 2 ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) (htau : 0 < tau)
    (hwidth : 12*tau < width r) (heta : tau < P4AOriginalRemainingEighthSources.eta)
    (i : Fin 14) {x y b : ℕ}
    (hx : x ∈ universe N N ((N : ℝ) ^ (nu * beta ^ 2)) (cutoff N))
    (hrank : 8 ≤ x.primeFactorsList.length)
    (htrim : firstEightCoordinates N x ∈ trim (sourceCell i) (width r))
    (hy : y ∈ cell (fun _ => []) N N ((N : ℝ) ^ (nu * beta ^ 2)) (cutoff N) tau x)
    (hb : b ∈ actualSmallRosserSupport N N ((N : ℝ) ^ (nu * beta ^ 2))) (G : ℕ → ℝ) :
    let omega := nu * beta ^ 2
    let w := (N : ℝ) ^ omega
    let z := cutoff N
    let L := (N : ℝ) ^ (nu * beta)
    let f := keep r n e q a omega N
    (∀ u : Fin 8 → ℝ, (∀ k : Fin 8, slotLower N tau x k ≤ u k ∧ u k ≤ slotUpper N tau x k) →
      newCap (sourceCell i) (upperCorner N tau x) <
        VariableEnvelope.v (∑ j ∈ selected (sourceCell i), u j)) ∧
    P4AOriginalR17EighthParent.parent n e q a omega N (rosserAncestor 8 x.primeFactorsList) <
      newCap (sourceCell i) (upperCorner N tau x) ∧
    (∀ j, ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j), canonicalPrefix 8 y k : ℕ) : ℝ) *
      (canonicalPrefix 8 y j : ℝ)^2 < (N : ℝ)^newCap (sourceCell i) (upperCorner N tau x)) ∧
    (∀ j ∉ selected (sourceCell i), ((∏ k ∈ selected (sourceCell i), canonicalPrefix 8 y k : ℕ) : ℝ) *
      ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j ∧ k ∉ selected (sourceCell i)), canonicalPrefix 8 y k : ℕ) : ℝ) *
      (canonicalPrefix 8 y j : ℝ)^2 < (N : ℝ)^newCap (sourceCell i) (upperCorner N tau x)) ∧
    b*y ∈ P4AOriginalFull87CompiledCounting.moduli N w ∧
    P4AOriginalOrderedThirdActualCoefficient.coefficient r n e q a omega N tau L (b*y) * G (b*y) =
      (actualSmallRoughRho (orderedSixth n e q a omega N false) N N w z L (b*y) -
        (actualSmallRoughRho (sixthPolicy n e q a N false) N N w z L (b*y) -
         actualSmallRoughRho (policy (width r) n e q a N false) N N w z L (b*y)) +
       (if changed f (fun _ => []) N N w z tau y then
        (if 0 ≤ (ArithmeticFunction.moebius y : ℝ) then actualSmallRosserPlus N N w L b
         else actualSmallRosserMinus N N w L b)
       else 0)) * G (b*y) := by
  have hs := action_slacks_same_Q_signed_product r n e q a nu beta tau he hcut hh
    N hN htau hwidth i hx hrank htrim hy hb G
  have hg := actual_fibre_integer_gates i N x hN ((N : ℝ) ^ (nu * beta ^ 2))
    tau (width r) htau hwidth hrank htrim hy
  refine ⟨?_, actual_parent_lt_upper_cap r n e q a (nu * beta ^ 2) he hcut hh
    N hN tau htau i x hrank htrim, hg.1, hg.2, hs.2.2.1, hs.2.2.2.2⟩
  intro u hu
  have hgap := upper_cap_selected_tent_gap i N x tau (width r) htau hwidth hrank htrim u hu
  linarith

end
end ImbalancedChen.P2Saving16ActualUpperCornerCap
