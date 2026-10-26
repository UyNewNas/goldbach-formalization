import ImbalancedChen.OriginalFourthStoredCapRefinement
import ImbalancedChen.OriginalFourthBankAppendMaximum
import ImbalancedChen.P1OriginalVariableFourthActiveOnly

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The SAME stored cap retained under rational refinement is bound to the
actual original rawQ3 seed, actual full-row maximum and natural square
products. Coarse-cell and rough activation are tested on the TRUE third
ancestor; no whole-cell lower endpoint is substituted for the third prime.

All stored cap/box/buffer/row data precede N in the main theorem. The row's
original external distribution licence is a separate explicit input.
The stored cap is strictly BELOW the original variable row candidate and
full maximum; it is never asserted equal to either of them.
-/

namespace ImbalancedChen.OriginalFourthStoredActualParent20261026b

noncomputable section
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open OriginalFourthBankAppendMaximum20261026b
open OriginalFourthStoredCapRefinement20261026b

/-- Fixed finite cap data bind to each actual active/adopted original
third ancestor. The original licence is supplied separately from geometry. -/
theorem fixed_cap_actual_parent_and_squares
    (raw : FourthWireRow) (records : List FourthWireRow) (hraw : raw ∈ records)
    (licensed : ProducerRow → Prop) (hlicensed : licensed raw.toProducerRow)
    (e : ℚ) (chi : ℝ) (m : ℕ) (j : HistoricalThirdCoarse.Cell m)
    (hj : j ∈ HistoricalThirdCoarse.cells (e : ℝ) chi m)
    (nu cap : ℚ) (lo hi : QEndpoint)
    (hl : ∀ i, raw.toProducerRow.lower i ≤ lo i)
    (hu : ∀ i, hi i ≤ raw.toProducerRow.upper i)
    (hc : storedBoxCapCheck raw.toProducerRow.selected
      (HistoricalThirdCoarse.gamma (e : ℝ) (HistoricalThirdCoarse.box m j) - 2 * e)
      (min nu (VariableEnvelope.qVLo
        (∑ i ∈ raw.toProducerRow.selected, raw.toProducerRow.lower i)
        (∑ i ∈ raw.toProducerRow.selected, raw.toProducerRow.upper i) - 2 * e))
      raw.toProducerRow.lower raw.toProducerRow.upper cap = true)
    (omega N : ℝ) (hN : 1 < N) (history : List ℕ) (hlen : history.length = 4)
    (hpos : ∀ p ∈ history, 0 < p)
    (ha : HistoricalThirdCoarse.active omega N (rosserAncestor 3 history))
    (hparent : primeHistoryLogCoordinates N 3 (rosserAncestor 3 history) ∈
      logPrimeMeshCell 0 (19 / 96) m j)
    (htl : ∀ i, (lo i : ℝ) ≤ primeHistoryLogCoordinates N 4 history i)
    (htu : ∀ i, primeHistoryLogCoordinates N 4 history i ≤ (hi i : ℝ)) :
    seedExponent (e : ℝ) chi m omega N history < (cap : ℝ) ∧
      (cap : ℝ) < raw.toProducerRow.bufferedCandidate (e : ℝ)
        (primeHistoryLogCoordinates N 4 history) ∧
      (cap : ℝ) < producerProfile4 (e : ℝ) (fourthFamily records) licensed
        (seedExponent (e : ℝ) chi m omega N history) (primeHistoryLogCoordinates N 4 history) ∧
      HistoricalThirdCoarse.frozenLevel (e : ℝ) chi m omega N history < N ^ (cap : ℝ) ∧
      N ^ (cap : ℝ) < producerLevel4 (e : ℝ) chi m omega N (fourthFamily records) licensed history ∧
      (∀ k, ((∏ i ∈ Finset.univ.filter (fun i => i < k), primeHistoryTuple 4 history i : ℕ) : ℝ) *
        (primeHistoryTuple 4 history k : ℝ) ^ 2 < N ^ (cap : ℝ)) ∧
      (∀ k ∉ raw.toProducerRow.selected,
        ((∏ i ∈ raw.toProducerRow.selected, primeHistoryTuple 4 history i : ℕ) : ℝ) *
          ((∏ i ∈ Finset.univ.filter (fun i => i < k ∧ i ∉ raw.toProducerRow.selected),
            primeHistoryTuple 4 history i : ℕ) : ℝ) *
            (primeHistoryTuple 4 history k : ℝ) ^ 2 < N ^ (cap : ℝ)) := by
  have hs : P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N
      (rosserAncestor 3 history) := ⟨ha, j, hj, hparent⟩
  have hseed : seedExponent (e : ℝ) chi m omega N history =
      ((HistoricalThirdCoarse.gamma (e : ℝ) (HistoricalThirdCoarse.box m j) - 2 * e : ℚ) : ℝ) := by
    unfold seedExponent P1CoarseFirstCubeFallbackMargin.effectiveExponent
    rw [if_pos hs, HistoricalThirdCoarse.exponent_on_cell (e : ℝ) chi m _ j hj hparent]
    simp only [HistoricalThirdCoarse.levelExponent, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
  have hg := original_fourth_child_geometry raw
    (HistoricalThirdCoarse.gamma (e : ℝ) (HistoricalThirdCoarse.box m j) - 2 * e)
    nu e cap lo hi hl hu hc (primeHistoryLogCoordinates N 4 history) htl htu
  have hold : seedExponent (e : ℝ) chi m omega N history < (cap : ℝ) := by
    rw [hseed]
    exact hg.2.1
  have hfamily : raw.toProducerRow ∈ fourthFamily records :=
    (mem_fourthFamily_iff records _).mpr ⟨raw, hraw, rfl⟩
  have hrow : raw.toProducerRow.bufferedCandidate (e : ℝ) (primeHistoryLogCoordinates N 4 history) ≤
      producerProfile4 (e : ℝ) (fourthFamily records) licensed
        (seedExponent (e : ℝ) chi m omega N history) (primeHistoryLogCoordinates N 4 history) :=
    finiteMax_row_le (fourthFamily records) _ _ _ raw.toProducerRow hfamily ⟨hlicensed, hg.1⟩
  have hcap := hg.2.2.2.2.2.2.trans_le hrow
  have hpower : ∀ i : Fin 4, (primeHistoryTuple 4 history i : ℝ) ≤
      N ^ primeHistoryLogCoordinates N 4 history i :=
    fun i => (rpow_primeHistoryLogCoordinates N hN hlen hpos i).ge
  refine ⟨hold, hg.2.2.2.2.2.2, hcap, ?_, ?_, ?_, ?_⟩
  · rw [P1OriginalVariableFourthContinuation.frozenLevel_eq_rpow_seed]
    exact Real.rpow_lt_rpow_of_exponent_lt hN hold
  · rw [producerLevel4_rank_four _ _ _ _ _ _ _ _ hlen]
    exact Real.rpow_lt_rpow_of_exponent_lt hN hcap
  · intro k
    exact prefixSquareExpr_actual_gate N hN (primeHistoryTuple 4 history)
      (primeHistoryLogCoordinates N 4 history) hpower k (hg.2.2.2.2.1 k)
  · intro k hk
    exact selectedSquareExpr_actual_gate raw.toProducerRow.selected N hN (primeHistoryTuple 4 history)
      (primeHistoryLogCoordinates N 4 history) hpower k (hg.2.2.2.2.2.1 k hk)

/-- A genuine original Theta fallback cannot admit such a stored raising
cap on a nonempty row box. This prevents silently substituting the lower
unbuffered old envelope for the ACTUAL rawQ3 fallback branch. -/
theorem original_theta_fallback_cannot_pass (raw : FourthWireRow) (e nu cap : ℚ)
    (t : Point) (ht : t ∈ raw.toProducerRow.box) :
    storedBoxCapCheck raw.toProducerRow.selected ((299 / 500 : ℚ) - 2 * e)
      (min nu (VariableEnvelope.qVLo
        (∑ i ∈ raw.toProducerRow.selected, raw.toProducerRow.lower i)
        (∑ i ∈ raw.toProducerRow.selected, raw.toProducerRow.upper i) - 2 * e))
      raw.toProducerRow.lower raw.toProducerRow.upper cap = false := by
  cases hc : storedBoxCapCheck raw.toProducerRow.selected ((299 / 500 : ℚ) - 2 * e)
      (min nu (VariableEnvelope.qVLo
        (∑ i ∈ raw.toProducerRow.selected, raw.toProducerRow.lower i)
        (∑ i ∈ raw.toProducerRow.selected, raw.toProducerRow.upper i) - 2 * e))
      raw.toProducerRow.lower raw.toProducerRow.upper cap with
  | false => rfl
  | true =>
      exfalso
      have hg := original_fourth_child_geometry raw ((299 / 500 : ℚ) - 2 * e) nu e cap
        raw.toProducerRow.lower raw.toProducerRow.upper (fun _ => le_rfl) (fun _ => le_rfl)
        hc t ht.1 ht.2
      have hold : HistoricalThirdCoarse.initial (e : ℝ) < (cap : ℝ) := by
        simpa [HistoricalThirdCoarse.initial, VariableEnvelope.extendedDistributionCap] using hg.2.1
      have htent := P1OriginalVariableFourthActiveOnly.bufferedCandidate_lt_initial (e : ℝ) raw.toProducerRow t
      exact (not_lt_of_ge hold.le) (hg.2.2.2.2.2.2.trans htent)

end
end ImbalancedChen.OriginalFourthStoredActualParent20261026b
