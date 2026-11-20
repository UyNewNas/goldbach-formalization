import ImbalancedChen.P2Saving16ScheduledOriginalEight
import ImbalancedChen.P4AOrderedThirdEighthTrimProgram
import ImbalancedChen.P2OriginalSaving16Full87SourceBinding

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
Transport the actual 96 ordered row margins from the full87 trim to the
original fourteen-cell trim at the SAME positive width, and feed that
inclusion into the existing scheduled negative-inner consumer. -/
namespace ImbalancedChen.P2Saving16CommonTrimNegativeFibre
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P1FiniteAffineDecisionProgram P4AOrderedThirdEighthTrimProgram
open P2OriginalSaving16Full87SourceBinding
open P2OriginalSaving16FourteenPhysicalAtlas P2OriginalSaving16TrimmedHistory
open P2Saving16ScheduledOriginalEight P2Saving16OriginalEightNegativeFibre
open P2Saving16FirstRowCompilerFibre P2Saving16SameRhoDistributionFrontier
open P2Saving16ActualCompilerDifference P2Saving16SignedCorrectionFamilies
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P4AUpperTaggedFrozenAdmissionCatalogue P2CanonicalWallFullResidualPayment
open P5OriginalCommonRefinedConstructor
open P4AOriginalFull87StrictActionTrim (trim trim_subset_source)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P4AOriginalOrderedThirdActualCoefficient (coefficient keep)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalR17EighthParent (orderedSixth)
open P4AOriginalFull87UnionHistory (sixthPolicy policy)
open P4AOriginalFull87CompiledCounting (moduli)

/-- Every one of the original 96 ordered rows at the same cell and point
is the literal affine row read by the full87 trim program. -/
theorem original_trim_row_eq (i : Fin 14) (k : Fin 96) (t : Fin 8 → ℝ) :
    P2OriginalSaving16FourteenPhysicalAtlas.evalRow
      (P2OriginalSaving16FourteenPhysicalAtlas.rows (atlasCell i) k).2 t =
    (rowForm (sourceCell i) k).eval t := by
  rw [original_row_eq i k]
  rfl

/-- Fixed-width inclusion, at the same original cell index. Nothing here
identifies distinct cells or changes their multiplicity. -/
theorem full87_trim_subset_original_cell
    (i : Fin 14) (delta : ℝ) (hdelta : 0 < delta) :
    trim (sourceCell i) delta ⊆ trimmedCell delta (atlasCell i) := by
  intro t ht
  have hs := trim_subset_source (sourceCell i) hdelta ht
  have hsOld := (sourceRows_iff_full87_source i t).mpr hs
  have hbox := (cell_subset_safeCarrier (atlasCell i) hsOld).1
  have htest := (trim_exact delta (sourceCell i) t).mpr ht
  simp only [trimTests, passed_append] at htest
  have hrows := htest.1.2
  simp only [passed_indexed, Finset.mem_univ, true_implies, holds_LE,
    Program.eval, Affine.eval_const] at hrows
  refine ⟨hbox, mem_iInter.mpr ?_⟩
  intro k
  have hk := hrows k
  rw [original_trim_row_eq i k t]
  exact hk

/-- The original region receives the very same width uniformly for all
fourteen indices and all points, before any N or prime tuple is chosen. -/
theorem full87_trim_subset_original_region
    (i : Fin 14) (delta : ℝ) (hdelta : 0 < delta) :
    trim (sourceCell i) delta ⊆ trimmedRegion delta := by
  intro t ht
  exact mem_iUnion.mpr ⟨atlasCell i, full87_trim_subset_original_cell i delta hdelta ht⟩

/-- Fix r before e and the common historical threshold. An actual
negative-inner summand in a full87 trim now needs no second trim premise.
The actual bank fields are reduced at chi=e/20; q is chosen before N
and the full signed summand is unchanged. -/
theorem scheduled_negative_inner_one_trim (r : ℕ) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, ∀ (n q : ℕ) (a nu beta tau : ℝ),
        let bank := P4AOriginalFull87UnionHistory.bank e q a
        q0 ≤ q → a ≤ 1 / 100 →
        nu * beta^2 ≤ a → HistoryOnTrim r e q a →
        ∀ (N : ℕ), 1 < N → ∀ (i : Fin 14) {d s : ℕ},
          8 ≤ d.primeFactorsList.length →
          firstEightCoordinates N d ∈ trim (sourceCell i) (width r) →
          s ∈ actualSmallRosserSupport N N ((N : ℝ)^(nu * beta^2)) →
          (ArithmeticFunction.moebius d : ℝ) < 0 →
          changed (keep r n e q a (nu * beta^2) N) (fun _ => []) N N
            ((N : ℝ)^(nu * beta^2)) (P4AOriginalFull87RawChronology.cutoff N) tau d → ∀ b T : ℝ,
          let omega := nu * beta^2
          let w := (N : ℝ)^omega
          let z := P4AOriginalFull87RawChronology.cutoff N
          let L := (N : ℝ)^(nu*beta)
          let f := keep r n e q a omega N
          let word := P2OriginalFourteenRetainedTupleOwnership.history (canonicalPrefix 8 d)
          let G := realHalfProductDiscrepancy b N T
          canonicalPrefix 8 d ∈ firstExitAdmittedTuples 8 (policy6 bank (N : ℝ))
            (roughPrimeUniverse N N w z) ∧
          primeHistoryTuple 4 (rosserAncestor 4 word) ∈
            firstExitAdmittedTuples 4 (oddFirstExitPolicy f) (roughPrimeUniverse N N w z) ∧
          P4AOriginalFull87DataPolicy.level4Exponent n bank N (rosserAncestor 4 word) ≤
            P4AOriginalR17EighthParent.parent n e q a omega N word ∧
          s*d ∈ moduli N w ∧
          coefficient r n e q a omega N tau L (s*d) * G (s*d) =
            (actualSmallRoughRho (orderedSixth n e q a omega N false) N N w z L (s*d) -
              (actualSmallRoughRho (sixthPolicy n e q a N false) N N w z L (s*d) -
                actualSmallRoughRho (policy (width r) n e q a N false) N N w z L (s*d)) +
              actualSmallRosserMinus N N w L s) * G (s*d) := by
  obtain ⟨e0, he0, h⟩ := scheduled_negative_inner_same_Q_summand (width r) (width_pos r)
  refine ⟨e0, he0, ?_⟩
  intro e he he0e
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hchi : (0 : ℝ) < (e : ℝ) / 20 := by positivity
  have hchile : (e : ℝ) / 20 ≤ (e : ℝ) / 10 := by linarith
  obtain ⟨m0, hm0⟩ := h e he he0e ((e : ℝ) / 20) hchi hchile
  refine ⟨max 1 m0, ?_⟩
  intro n q a nu beta tau
  dsimp only
  intro hq ha hcut hh N hN i d s hrank ht hs hneg hchanged b T
  let bank := P4AOriginalFull87UnionHistory.bank e q a
  have hde : bank.e = e := rfl
  have hdc : bank.chi = (e : ℝ) / 20 := rfl
  have homega : bank.omega ≤ 1 / 100 := ha
  have hq1 : 1 ≤ q := (le_max_left 1 m0).trans hq
  have hqm : m0 ≤ q := (le_max_right 1 m0).trans hq
  have hdm : m0 ≤ bank.m := by
    change m0 ≤ P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q
    unfold P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh
    omega
  have htOld := full87_trim_subset_original_region i (width r) (width_pos r) ht
  exact hm0 r n q a nu beta tau hde hdc hdm homega hcut hh N hN i
    hrank htOld ht hs hneg hchanged b T

end
end ImbalancedChen.P2Saving16CommonTrimNegativeFibre
