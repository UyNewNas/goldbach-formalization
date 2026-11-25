import ImbalancedChen.P2Saving16Full87SourceBinding
import ImbalancedChen.P4AOrderedThirdEighthTrimProgram
import ImbalancedChen.P4AFull87SamePieceCapVariation
import ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.

The first original ascending-family row on a single actual untagged
compiler fibre. A buffered source witness and a strictly smaller fine
width preserve the first row throughout that fibre. This is only one
row, not all ninety-six rows, corner equality, or a PP estimate. -/
namespace ImbalancedChen.P2Saving16FirstRowCompilerFibre
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P4AFull87SamePieceCapVariation (coord_ancestor)
open P4AFull87CompilerChangedPartition P4AUpperTaggedFrozenAdmissionCatalogue
open P2CanonicalWallFullResidualPayment
open P4AOrderedThirdEighthTrimProgram
open P4AOriginalFull87StrictActionTrim (trim)
open P4AOriginalFull87HistoryCore (core)
open P2OriginalSaving16Full87SourceBinding (sourceCell)
open P4AOriginalOrderedThirdActualCoefficient (keep)
open P4AOriginalFull87RawChronology (cutoff)

def firstEightCoordinates (N d : ℕ) : Fin 8 → ℝ :=
  primeHistoryLogCoordinates (N : ℝ) 8 (rosserAncestor 8 d.primeFactorsList)

/-- The geometric upper endpoint of the first original fine-label slot. -/
def firstUpperEndpoint (N : ℕ) (tau : ℝ) (d : ℕ) : ℝ :=
  ((P2LowerFiniteCellRounding.primeLabel N tau (canonicalPrefix 8 d 0) : ℝ) + 1) * tau

/-- The first of the 96 original rational rows is exactly mu-t_1,
in the original order for all fourteen indices. -/
theorem original_first_row (i : Fin 14) (t : Fin 8 → ℝ) :
    (rowForm (sourceCell i) (0 : Fin 96)).eval t = VariableEnvelope.mu - t 0 := by
  fin_cases i <;>
    norm_num [rowForm, rowCoeffs, sourceCell,
      P4AOriginalRemainingEighthSources.row, P4AOriginalRemainingEighthSources.rowCount,
      P4AOriginalFull87StrictActionTrim.rowCount,
      P4AOriginalAscendingFourteenAffineSource.rows,
      P4AOriginalAscendingFourteenAffineSource.literalIndex,
      P4AOriginalAscendingFourteenAffineSource.literalPool,
      P1FiniteAffineDecisionProgram.Affine.eval, VariableEnvelope.mu,
      Fin.sum_univ_succ] <;> ring

/-- The first original row has at least the actual common trim margin. -/
theorem first_row_margin (i : Fin 14) (delta : ℝ) (t : Fin 8 → ℝ)
    (ht : t ∈ trim (sourceCell i) delta) : delta ≤ VariableEnvelope.mu - t 0 := by
  have hp := (trim_exact delta (sourceCell i) t).mpr ht
  simp only [trimTests, passed_append, core_exact] at hp
  have hc : t ∈ core delta := hp.1.1
  have hc' := (core_exact delta t).mpr hc
  simp only [coreTests, passed_append, passed_closedBox, passed_indexed,
    Finset.mem_univ, true_implies, holds_LE, Program.eval, Affine.eval_const] at hc'
  have h0 := hc'.1.2 (0 : Fin 3)
  simpa [orderForms] using h0

/-- The literal upper corner of the first fine interval satisfies the
first original row strictly, not merely its occupied prime points. -/
theorem first_upper_endpoint_strict (i : Fin 14) (N d : ℕ) (tau delta : ℝ)
    (htau : 0 < tau) (hwidth : tau < delta) (hrank : 8 ≤ d.primeFactorsList.length)
    (htrim : firstEightCoordinates N d ∈ trim (sourceCell i) delta) :
    0 < VariableEnvelope.mu - firstUpperEndpoint N tau d := by
  have hm := first_row_margin i delta (firstEightCoordinates N d) htrim
  have hl := (P2LowerFiniteCellRounding.primeLabel_halfopen N htau (canonicalPrefix 8 d 0)).1
  have he : firstEightCoordinates N d 0 =
      Real.log (canonicalPrefix 8 d 0 : ℝ) / Real.log (N : ℝ) := by
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hrank]
    rfl
  rw [← he] at hl
  dsimp only [firstUpperEndpoint]
  linarith

/-- Concrete first-row transport through the actual untagged fibre. The
second conclusion is the compiler's real signed rough coefficient at y,
with the shared fibre scalar and the original Mobius coefficient of y. -/
theorem first_row_and_signed_compiler_on_fibre
    (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ)
    (tau delta : ℝ) (htau : 0 < tau) (hwidth : tau < delta)
    (i : Fin 14) {x y : ℕ}
    (hx : x ∈ universe N N ((N : ℝ) ^ omega) (cutoff N))
    (hrank : 8 ≤ x.primeFactorsList.length)
    (htrim : firstEightCoordinates N x ∈ trim (sourceCell i) delta)
    (hy : y ∈ cell (fun _ => []) N N ((N : ℝ) ^ omega) (cutoff N) tau x) :
    0 < VariableEnvelope.mu - firstUpperEndpoint N tau x ∧
    0 < (rowForm (sourceCell i) (0 : Fin 96)).eval (firstEightCoordinates N y) ∧
    P4AUpperTaggedParityCompiler.coefficient (keep r n e q a omega N) (fun _ => [])
        N N ((N : ℝ) ^ omega) (cutoff N) tau y =
      (ArithmeticFunction.moebius y : ℝ) *
        P4AFull87TaggedAtomValue.occupied (keep r n e q a omega N) (fun _ => [])
          N N ((N : ℝ) ^ omega) (cutoff N) tau x := by
  have hyrank : 8 ≤ y.primeFactorsList.length := by
    rw [cell_rank_preserved _ _ _ _ _ _ hy]
    exact hrank
  have hclose : |firstEightCoordinates N x 0 - firstEightCoordinates N y 0| < tau := by
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hrank, coord_ancestor hyrank]
    exact same_primeLabel_coordinate_distance_lt N htau
      (cell_canonicalPrefix_label_eq _ _ _ _ _ _ hy hrank (0 : Fin 8))
  have hmargin := first_row_margin i delta (firstEightCoordinates N x) htrim
  have hyu : y ∈ universe N N ((N : ℝ) ^ omega) (cutoff N) := (Finset.mem_filter.mp hy).1
  have hlabels := (cell_prime_labels (fun _ => []) N N ((N : ℝ) ^ omega) (cutoff N) tau hy).symm
  have hscalar := P4AOriginalOrderedThirdActualCoefficient.cell_value_constant
    r n e q a omega N tau hx hyu hlabels
  refine ⟨first_upper_endpoint_strict i N x tau delta htau hwidth hrank htrim, ?_, ?_⟩
  · rw [original_first_row]
    have hh := (abs_lt.mp hclose).1
    linarith
  · rw [P4AFull87TaggedAtomValue.literal_value, ← hscalar]

/-- The same result at each occupied full modulus b*y, including the
actual sign-selected beta coefficient and the original full-q factor. -/
theorem first_row_full_modulus
    (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ)
    (tau delta L : ℝ) (htau : 0 < tau) (hwidth : tau < delta)
    (i : Fin 14) {x y b : ℕ}
    (hx : x ∈ universe N N ((N : ℝ) ^ omega) (cutoff N))
    (hrank : 8 ≤ x.primeFactorsList.length)
    (htrim : firstEightCoordinates N x ∈ trim (sourceCell i) delta)
    (hy : y ∈ cell (fun _ => []) N N ((N : ℝ) ^ omega) (cutoff N) tau x)
    (hb : b ∈ actualSmallRosserSupport N N ((N : ℝ) ^ omega)) (G : ℕ → ℝ) :
    let f := keep r n e q a omega N
    let rough := (ArithmeticFunction.moebius y : ℝ) *
      P4AFull87TaggedAtomValue.occupied f (fun _ => []) N N ((N : ℝ) ^ omega) (cutoff N) tau x
    0 < VariableEnvelope.mu - firstUpperEndpoint N tau x ∧
    0 < (rowForm (sourceCell i) (0 : Fin 96)).eval (firstEightCoordinates N y) ∧
    P4AOriginalOrderedThirdActualCoefficient.coefficient r n e q a omega N tau L (b * y) * G (b * y) =
      rough * (if 0 ≤ rough then actualSmallRosserPlus N N ((N : ℝ) ^ omega) L b
        else actualSmallRosserMinus N N ((N : ℝ) ^ omega) L b) * G (b * y) := by
  have h := first_row_and_signed_compiler_on_fibre r n e q a omega N tau delta htau hwidth
    i hx hrank htrim hy
  have hyu : y ∈ universe N N ((N : ℝ) ^ omega) (cutoff N) := (Finset.mem_filter.mp hy).1
  refine ⟨h.1, h.2.1, ?_⟩
  change rho (keep r n e q a omega N) (fun _ => []) N N ((N : ℝ) ^ omega)
    (cutoff N) tau L (b * y) * G (b * y) = _
  rw [rho_at_product (keep r n e q a omega N) (fun _ => []) N N
    ((N : ℝ) ^ omega) (cutoff N) tau L hb hyu, h.2.2]

end
end ImbalancedChen.P2Saving16FirstRowCompilerFibre
