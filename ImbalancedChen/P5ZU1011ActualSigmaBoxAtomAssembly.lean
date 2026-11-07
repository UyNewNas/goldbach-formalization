import ImbalancedChen.P5ZU1011NativeUnmaskedLowBoxAtoms

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact assembly of the ACTUAL selected-cell native sigma. Its unmasked U10
pieces and SAME-E retained U11 pieces are partitioned by the ORIGINAL
common states and unique native owner cells. This is before smoothing.
Each resulting coefficient has the preceding finite separated smooth-box
atom realization and exact full-modulus reserve error identity.
-/
namespace ImbalancedChen.P5Z.U1011ActualSigmaBoxAtomAssembly
noncomputable section
open Set Classical
open scoped BigOperators
open U11Integral U11Canonical
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenNativeHarmonic
open U1011OriginalFifteenNativeGridCells U1011OriginalSixteenAffineState
open U1011OriginalSixteenJointNearCapCompiler U1011OriginalSixteenJointNearCapModulusConvolution
open U1011OriginalSixteenStaticNativeCompiler (tupleTag ownerBox)
open U1011OriginalMaskSmoothBoxRealization
open U1011AffineSmoothBoxCover
open U1011NativeMaskPhysicalBoxAtoms U1011NativeUnmaskedLowBoxAtoms
open U1011OriginalPairedRowPrimeTests (nativeMask_log_dictionary originalDomain_mask_iff)
open U1011OriginalPairedFixedMaskHarmonic (outerUnion)
open P5U1011JointOverlap

def markTerm (m N : ℕ) (eta : ℚ) (a : Mark) (q : ℕ) : ℝ :=
  if modulus a = q then weight m N eta a else 0

def cellSigma (m N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) (k : Grid m) (q : ℕ) : ℝ :=
  ∑ a ∈ marks m N eta E, if coordinates N a.1 ∈ cell m k then markTerm m N eta a q else 0

private theorem mark_joint {m N : ℕ} {eta : ℚ} {E : ℕ × ℕ → Prop} {a : Mark}
    (ha : a ∈ marks m N eta E) : a.1 ∈ jointSelector N E :=
  (Finset.mem_filter.mp (Finset.mem_sigma.mp ha).1).1

private theorem source_log_band {N : ℕ} (hN : 1 < N) (S : Finset Row) {t : Four}
    (ht : t ∈ jointSelector N (actualE S N)) :
    coordinates N t ∈ U1011OriginalSixteenU10Geometry.domain10 ∪ originalDomain (outerUnion S) := by
  rw [jointSelector_eq_original_union N (actualE S N) (by exact_mod_cast (Nat.le_of_lt hN))] at ht
  rcases Finset.mem_union.mp ht with hl | hh
  · left
    have hp := (U1011OriginalSixteenU10Geometry.unslots_mem_selector_iff_tuples10 hN (slots t)).mp
      (by simpa only [unslots_slots] using hl)
    exact (Finset.mem_filter.mp hp).2
  · right
    have hp := (unslots_source_iff_kept_box hN (actualE S N) (slots t)).mp
      (by simpa only [U11Adaptive.source, unslots_slots] using hh)
    have hk := (Finset.mem_filter.mp hp).2
    apply (originalDomain_mask_iff (outerUnion S) _).mpr
    refine ⟨hk.1, ?_⟩
    exact fun he => hk.2 ((nativeMask_log_dictionary (outerUnion S) N (slots t)).mpr he)

/-- Exact one-owner state/band partition at a literal arithmetic point.
The common H248 clamp and all knots stay among the actual state cells. -/
theorem original_state_band_partition (S : Finset Row) (m : ℕ) (k : Grid m)
    {v : LogFour} (hv : v ∈ cube)
    (hband : v ∈ U1011OriginalSixteenU10Geometry.domain10 ∪ originalDomain (outerUnion S))
    (W : ℝ) :
    (∑ s : State, (if v ∈ lowGeometry s m k then W else 0) +
      (if v ∈ pieceGeometry S s m k then W else 0)) = if v ∈ cell m k then W else 0 := by
  have hw : 0 < v 3 := by
    have h := (mem_logPrimeBox.mp hv 3).1
    exact lt_of_lt_of_le (by norm_num [lower]) h
  let s₀ := chosenState v
  have hs₀ : v ∈ commonCell s₀ := chosenState_mem v hw
  rw [Finset.sum_eq_single s₀]
  · by_cases hk : v ∈ cell m k
    · by_cases hl : v ∈ U1011OriginalSixteenU10Geometry.domain10
      · have hh : v ∉ originalDomain (outerUnion S) := fun hh =>
          Set.disjoint_left.mp (U1011OriginalJointHarmonic.domain10_disjoint_originalDomain _) hl hh
        simp [lowGeometry, U1011OriginalSixteenU10FullHarmonic.piece,
          U1011OriginalSixteenU10FullHarmonic.domain, pieceGeometry, originalCell, hs₀, hk, hl, hh]
      · have hh : v ∈ originalDomain (outerUnion S) := hband.resolve_left hl
        simp [lowGeometry, U1011OriginalSixteenU10FullHarmonic.piece,
          U1011OriginalSixteenU10FullHarmonic.domain, pieceGeometry, originalCell, hs₀, hk, hl, hh]
    · simp [lowGeometry, pieceGeometry, hk]
  · intro s hs hne
    have hnot : v ∉ commonCell s := fun hs => hne (commonCell_unique hs hs₀)
    simp [lowGeometry, U1011OriginalSixteenU10FullHarmonic.piece,
      pieceGeometry, originalCell, hnot]
  · intro h
    exact (h (Finset.mem_univ s₀)).elim

theorem sigma_eq_sum_cellSigma {N : ℕ} (hN : 1 < N) (m : ℕ) (eta : ℚ)
    (E : ℕ × ℕ → Prop) (q : ℕ) : sigma m N eta E q = ∑ k : Grid m, cellSigma m N eta E k q := by
  unfold sigma fibre cellSigma
  rw [Finset.sum_filter, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hv := U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hN (mark_joint ha)
  change markTerm m N eta a q = _
  symm
  rw [Finset.sum_eq_single (owner m (coordinates N a.1))]
  · rw [if_pos (owner_mem m hv)]
  · intro k hk hne
    rw [if_neg]
    exact fun hcell => hne (owner_eq_of_mem m hcell).symm
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem fallback_cellSigma_zero (m N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop)
    (k : Grid m) (q : ℕ)
    (hk : U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) = 0) :
    cellSigma m N eta E k q = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  rw [if_neg]
  intro hg
  have htag := (Finset.mem_filter.mp (Finset.mem_sigma.mp ha).1).2
  have hzero : tupleTag m N a.1 = 0 := by
    simpa only [tupleTag, ownerBox, owner_eq_of_mem m hg] using hk
  exact htag hzero

/-- A true selected owner cell is exactly the sum of its actual low and
same-E high state pieces, with no multiplicity loss. -/
theorem cellSigma_eq_low_high {N : ℕ} (hN : 1 < N) (S : Finset Row) (m : ℕ) (eta : ℚ)
    (k : Grid m) (hactive : U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) ≠ 0)
    (q : ℕ) :
    cellSigma m N eta (actualE S N) k q =
      ∑ s : State, lowCoefficientPiece s m N eta k q + nativeCoefficientPiece S s m N eta k q := by
  have hpiece (s : State) : lowCoefficientPiece s m N eta k q + nativeCoefficientPiece S s m N eta k q =
      ∑ a ∈ marks m N eta (actualE S N),
        (if coordinates N a.1 ∈ lowGeometry s m k then markTerm m N eta a q else 0) +
        (if coordinates N a.1 ∈ pieceGeometry S s m k then markTerm m N eta a q else 0) := by
    rw [lowCoefficientPiece_eq_original_fibre hN s m eta (actualE S N) k hactive,
      nativeCoefficientPiece_eq_original_fibre hN S s m eta k hactive]
    unfold lowPieceMarks nativePieceMarks
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    rfl
  symm
  calc
    _ = ∑ s : State, ∑ a ∈ marks m N eta (actualE S N),
        (if coordinates N a.1 ∈ lowGeometry s m k then markTerm m N eta a q else 0) +
        (if coordinates N a.1 ∈ pieceGeometry S s m k then markTerm m N eta a q else 0) :=
      Finset.sum_congr rfl (fun s hs => hpiece s)
    _ = ∑ a ∈ marks m N eta (actualE S N), ∑ s : State,
        (if coordinates N a.1 ∈ lowGeometry s m k then markTerm m N eta a q else 0) +
        (if coordinates N a.1 ∈ pieceGeometry S s m k then markTerm m N eta a q else 0) := Finset.sum_comm
    _ = cellSigma m N eta (actualE S N) k q := by
      apply Finset.sum_congr rfl
      intro a ha
      have hj := mark_joint ha
      exact original_state_band_partition S m k
        (U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hN hj)
        (source_log_band hN S hj) _

/-- The actual native sigma, including BOTH true source bands, is now
assembled from literal physical coefficient pieces. Tag0 stays absent
from sigma, as in the original native compiler. -/
theorem actual_sigma_eq_native_box_pieces {N : ℕ} (hN : 1 < N)
    (S : Finset Row) (m : ℕ) (eta : ℚ) (q : ℕ) :
    sigma m N eta (actualE S N) q = ∑ k : Grid m,
      if U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) = 0 then 0 else
        ∑ s : State, lowCoefficientPiece s m N eta k q + nativeCoefficientPiece S s m N eta k q := by
  rw [sigma_eq_sum_cellSigma hN]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hz : U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) = 0
  · rw [if_pos hz, fallback_cellSigma_zero m N eta (actualE S N) k q hz]
  · rw [if_neg hz]
    exact cellSigma_eq_low_high hN S m eta k hz q

/-- No target PP premise occurs: this is an exact arithmetic identity on
the independent original four-prime carrier and original residual row. -/
theorem actual_sigma_eq_physical_tests {N : ℕ} (hN : 1 < N)
    (S : Finset Row) (m : ℕ) (eta : ℚ) (q : ℕ) :
    sigma m N eta (actualE S N) q = ∑ k : Grid m,
      if U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) = 0 then 0 else
        ∑ s : State,
          physicalTest m N eta k (regionIndicator (lowGates s m k)) q +
          physicalTest m N eta k (retainedIndicator S s m k) q := by
  rw [actual_sigma_eq_native_box_pieces hN]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs
  · rfl
  · apply Finset.sum_congr rfl
    intro s hs
    rw [lowCoefficientPiece_eq_physicalTest hN, nativeCoefficientPiece_eq_physicalTest hN]

theorem actual17572_sigma_eq_physical_tests {N : ℕ} (hN : 1 < N)
    (m : ℕ) (eta : ℚ) (q : ℕ) :
    sigma m N eta (Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ)) q =
      ∑ k : Grid m,
        if U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) = 0 then 0 else
          ∑ s : State,
            physicalTest m N eta k (regionIndicator (lowGates s m k)) q +
            physicalTest m N eta k (retainedIndicator Finset.univ s m k) q := by
  simpa only [actualE, U1011OriginalPairedFixedMaskHarmonic.outerUnion_all,
    U1011OriginalPairedRowPrimeTests.nativeMask_actual_adopted] using
      actual_sigma_eq_physical_tests hN (Finset.univ : Finset Row) m eta q

def smoothSigma (inner : Bool) (S : Finset Row) (m N : ℕ) (eta : ℚ)
    (n : ℕ) (δ : ℝ) (q : ℕ) : ℝ := ∑ k : Grid m,
  if U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) = 0 then 0 else
    ∑ s : State,
      physicalTest m N eta k (lowSmoothCover inner s m k n δ) q +
      physicalTest m N eta k (signedSmoothCover inner S s m k n δ) q

/-- Exact global atom/reserve decomposition of the ORIGINAL sigma.
Every term on the right has the proved actual reserve support; no small
error or PP estimate is assumed. The residual d-sums stay inside each
physicalTest, so their payment cannot be silently lost in assembly. -/
theorem actual_sigma_smooth_reserve_identity {N : ℕ} (hN : 1 < N)
    (inner : Bool) (S : Finset Row) (m : ℕ) (eta : ℚ) (n : ℕ) (δ : ℝ) (q : ℕ) :
    smoothSigma inner S m N eta n δ q - sigma m N eta (actualE S N) q =
      ∑ k : Grid m,
        if U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) = 0 then 0 else
          ∑ s : State,
            physicalTest m N eta k
              (fun v => lowSmoothCover inner s m k n δ v - regionIndicator (lowGates s m k) v) q +
            physicalTest m N eta k
              (fun v => signedSmoothCover inner S s m k n δ v - retainedIndicator S s m k v) q := by
  rw [actual_sigma_eq_native_box_pieces hN]
  unfold smoothSigma
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hz : U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) = 0
  · simp only [if_pos hz, sub_self]
  · simp only [if_neg hz]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have hl := low_native_error_identity hN inner s m eta k n δ q
    have hh := actual_native_error_identity hN inner S s m eta k n δ q
    linarith

end
end ImbalancedChen.P5Z.U1011ActualSigmaBoxAtomAssembly
