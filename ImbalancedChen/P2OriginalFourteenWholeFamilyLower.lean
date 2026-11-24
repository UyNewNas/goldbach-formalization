import ImbalancedChen.P2OriginalFourteenSignedRetainedLower

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The signed full-family-minus-strict-source complement is retained exactly.
Its negative part, rather than its absolute value, tends to zero uniformly.
This follows from the original uniform ordinary-residual comparison on ALL
CellGuard points, including weak old-plane faces, and bounded actual prime
box mass. No wall classification, selector/source equality, current=R,
finite Rosser monotonicity, or disappearance of positive complement mass
is asserted. The existing retained-source theorem supplies the source term.
-/
namespace ImbalancedChen.P2OriginalFourteenWholeFamilyLower
noncomputable section
open scoped Classical BigOperators Topology
open Set MeasureTheory Filter VariableEnvelope
open P2OriginalAscendingEighthCapDictionary
open P2OriginalSaving16FourteenPhysicalAtlas
open P2OriginalSaving16TrimmedHistory
open P2OriginalFourteenWeightedTrim
open P2OriginalFourteenRetainedTupleOwnership
open P2OriginalFourteenSignedRetainedLower
open P5OriginalCommonRefinedConstructor

/-- Exactly the original full selector and current-parent gate. -/
def fullSelectedFamilyGuard (data : OriginalData) (N : ℕ) (p : Fin 8 → ℕ) : Prop :=
  SelectedFamilyGuard P4AOriginalAscending14Literal42.literalPattern (actualPrimeTupleLog N p) ∧
    CurrentParentGuard (actualPrimeTupleLog N p) (tupleCurrent data N p)

theorem familyNextExponent_tuple (data : OriginalData) (N : ℕ) (p : Fin 8 → ℕ) :
    familyNextExponent (N : ℝ) (lambda6 data (N : ℝ))
        P4AOriginalAscending14Literal42.literalPattern (history p) =
      if fullSelectedFamilyGuard data N p then M (actualPrimeTupleLog N p)
        else tupleCurrent data N p := by
  simp only [familyNextExponent, history_log, fullSelectedFamilyGuard,
    tupleCurrent, inheritedExponent]

/-- The exact complement from M's signed source partition. -/
def signedComplement (data : OriginalData) (N cap : ℕ) (z : ℝ) : ℝ :=
  ∑ p ∈ admitted data N cap z, if actualPrimeTupleLog N p ∈ region then 0 else
    tupleWeight p * actualPrimeTupleInitialSaving N cap (tupleCurrent data N p)
      (familyNextExponent (N : ℝ) (lambda6 data (N : ℝ))
        P4AOriginalAscending14Literal42.literalPattern (history p)) p

/-- This is the actual admission submask. It is not replaced by the cube. -/
def complementCarrier (data : OriginalData) (N cap : ℕ) (z : ℝ) : Finset (Fin 8 → ℕ) :=
  (admitted data N cap z).filter (fun p => actualPrimeTupleLog N p ∉ region ∧
    fullSelectedFamilyGuard data N p)

theorem signedComplement_eq_active_sum (data : OriginalData) (N cap : ℕ) (z : ℝ) :
    signedComplement data N cap z =
      ∑ p ∈ complementCarrier data N cap z,
        tupleWeight p * actualPrimeTupleInitialSaving N cap (tupleCurrent data N p)
          (M (actualPrimeTupleLog N p)) p := by
  simp only [signedComplement, complementCarrier, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  rw [familyNextExponent_tuple]
  by_cases hr : actualPrimeTupleLog N p ∈ region
  · simp only [hr, if_true, not_true_eq_false, false_and, if_false]
  · by_cases hg : fullSelectedFamilyGuard data N p
    · simp only [hr, if_false, not_false_eq_true, true_and, hg, if_true]
    · simp only [hr, if_false, not_false_eq_true, true_and, hg,
        actualPrimeTupleInitialSaving, sub_self, zero_mul, zero_div, mul_zero]

/-- The original strict order/cutoff rows put every selected point in the
same fixed prime box, including points on weak old-plane faces. -/
theorem selectedFamilyGuard_coordinate_bounds {t : Point}
    (ht : SelectedFamilyGuard P4AOriginalAscending14Literal42.literalPattern t) :
    ∀ i, cutoff < t i ∧ t i < mu := by
  obtain ⟨c, hc, hg⟩ := ht
  intro i
  constructor
  · by_cases hi : i = 7
    · simpa only [hi, cutoff] using hg.compact_cutoff
    · have hi7 : i < 7 := by omega
      exact hg.compact_cutoff.trans (hg.order hi7)
  · by_cases hi : i = 0
    · simpa only [hi] using hg.largest
    · have hi0 : 0 < i := by omega
      exact (hg.order hi0).trans hg.largest

theorem complementCarrier_subset_box (data : OriginalData) (N cap : ℕ) (z : ℝ)
    (hN : 1 < N) (hcap : z ≤ (cap : ℝ)) :
    complementCarrier data N cap z ⊆
      actualPrimeBoxTuples N (fun _ : Fin 8 => cutoff) (fun _ => mu) := by
  intro p hp
  obtain ⟨ha, hr, hg⟩ := Finset.mem_filter.mp hp
  have hh := (mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 8 _ N cap 0 z hcap p).mp ha
  refine (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
    ⟨fun i => ⟨(hh.2.1 i).1, (hh.2.1 i).2.1⟩, ?_⟩
  exact mem_logPrimeBox.mpr (fun i =>
    ⟨(selectedFamilyGuard_coordinate_bounds hg.1 i).1.le,
      (selectedFamilyGuard_coordinate_bounds hg.1 i).2⟩)

/-- A nonnegative measure of the harmful part of the actual signed
complement. Positive current-parent surplus is kept in signedComplement. -/
def negativeComplementMass (data : OriginalData) (N cap : ℕ) (z : ℝ) : ℝ :=
  ∑ p ∈ complementCarrier data N cap z,
    tupleWeight p * max 0 (-actualPrimeTupleInitialSaving N cap (tupleCurrent data N p)
      (M (actualPrimeTupleLog N p)) p)

theorem negativeComplementMass_nonneg (data : OriginalData) (N cap : ℕ) (z : ℝ)
    (hN : 1 < N) (hcap : z ≤ (cap : ℝ)) :
    0 ≤ negativeComplementMass data N cap z := by
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (actualPrimeBoxWeight_nonneg
    (complementCarrier_subset_box data N cap z hN hcap hp)) (le_max_left _ _)

theorem neg_negativeComplementMass_le_signedComplement
    (data : OriginalData) (N cap : ℕ) (z : ℝ)
    (hN : 1 < N) (hcap : z ≤ (cap : ℝ)) :
    -negativeComplementMass data N cap z ≤ signedComplement data N cap z := by
  rw [signedComplement_eq_active_sum, negativeComplementMass, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hw : 0 ≤ tupleWeight p := actualPrimeBoxWeight_nonneg
    (complementCarrier_subset_box data N cap z hN hcap hp)
  have hh := mul_le_mul_of_nonneg_left
    (le_max_right (0 : ℝ) (-actualPrimeTupleInitialSaving N cap (tupleCurrent data N p)
      (M (actualPrimeTupleLog N p)) p)) hw
  linarith

/-- The geometric comparison profile is positive on the WHOLE selector.
Weak old-plane inequalities need no strengthening to establish this sign. -/
theorem selectedFamilyGuard_sourceGain_pos {t : Point}
    (ht : SelectedFamilyGuard P4AOriginalAscending14Literal42.literalPattern t) :
    0 < sourceGain (R t) (M t) t := by
  obtain ⟨c, hc, hg⟩ := ht
  have hR : 0 < R t - S t := by linarith [hg.last_pos, hg.old_residual]
  have hM : 0 < M t - S t := by linarith [hg.improvement]
  exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hg.improvement)) (mul_pos hR hM)

/-- One arithmetic threshold bounds the harmful part before selecting the
actual admission submask. No negligible-complement or sign premise occurs.
The width of a wall strip is unnecessary for this one-sided argument. -/
theorem exists_uniform_negativeComplementMass_lt (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ data : OriginalData, ∀ cap : ℕ, ∀ z : ℝ, z ≤ (cap : ℝ) →
        negativeComplementMass data N cap z < epsilon := by
  let B : ℝ := ∏ _i : Fin 8, Real.log (mu / cutoff)
  have hB : 0 ≤ B := Finset.prod_nonneg (fun _ _ =>
    Real.log_nonneg ((one_le_div cutoff_pos).mpr (by norm_num [cutoff, mu])))
  let gamma : ℝ := epsilon / (B + 1)
  have hgamma : 0 < gamma := div_pos hepsilon (by positivity)
  obtain ⟨Nr, hNr, hres⟩ :=
    P2OriginalFourteenUniformResidual.exists_uniform_comparison_gain gamma hgamma
  obtain ⟨Nb, hmass⟩ := eventually_atTop.mp
    ((tendsto_actualPrimeBoxMass (fun _ : Fin 8 => cutoff) (fun _ => mu)
      (fun _ => cutoff_pos) (fun _ => by norm_num [cutoff, mu])).eventually
        (gt_mem_nhds (lt_add_one B)))
  refine ⟨max Nr Nb, hNr.trans (le_max_left _ _), ?_⟩
  intro N hN hEven data cap z hcap
  have hNrN : Nr ≤ N := (le_max_left _ _).trans hN
  have hNbN : Nb ≤ N := (le_max_right _ _).trans hN
  have hN1 : 1 < N := by omega
  have hsub := complementCarrier_subset_box data N cap z hN1 hcap
  have hpoint : ∀ p ∈ complementCarrier data N cap z,
      max 0 (-actualPrimeTupleInitialSaving N cap (tupleCurrent data N p)
        (M (actualPrimeTupleLog N p)) p) ≤ gamma := by
    intro p hp
    obtain ⟨ha, hr, hg⟩ := Finset.mem_filter.mp hp
    have hpi := mem_actualPrimeBoxTuples_iff.mp (hsub hp)
    have hpos (i : Fin 8) : 0 < p i := (hpi i).1.pos
    have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by
      exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
    have hy : (0 : ℝ) < p 7 := by exact_mod_cast hpos 7
    have hadmit := (mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 8 _ N cap 0 z hcap p).mp ha
    have hycap : (p 7 : ℝ) ≤ (cap : ℝ) := (hadmit.2.1 7).2.2.2.le.trans hcap
    obtain ⟨c, hc, hcell⟩ := hg.1
    have hh := hres N hNrN hEven _ _ (tupleCurrent data N p)
      (∏ i, p i : ℕ) (p 7 : ℝ) hcell hg.2 hP hy
      (actualPrimeTupleLog_sum_prod p hpos).symm rfl cap hycap
    change sourceGain (R (actualPrimeTupleLog N p)) (M (actualPrimeTupleLog N p))
      (actualPrimeTupleLog N p) - gamma <
        actualPrimeTupleInitialSaving N cap (tupleCurrent data N p)
          (M (actualPrimeTupleLog N p)) p at hh
    have hgain := selectedFamilyGuard_sourceGain_pos hg.1
    exact max_le hgamma.le (by linarith)
  have hnegative : negativeComplementMass data N cap z ≤
      gamma * actualPrimeBoxMass N (fun _ : Fin 8 => cutoff) (fun _ => mu) := by
    calc
      _ ≤ ∑ p ∈ complementCarrier data N cap z, tupleWeight p * gamma := by
        apply Finset.sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_left (hpoint p hp) (actualPrimeBoxWeight_nonneg (hsub hp))
      _ = gamma * ∑ p ∈ complementCarrier data N cap z, tupleWeight p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        exact mul_comm _ _
      _ ≤ gamma * actualPrimeBoxMass N (fun _ : Fin 8 => cutoff) (fun _ => mu) := by
        apply mul_le_mul_of_nonneg_left _ hgamma.le
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p hp _ => actualPrimeBoxWeight_nonneg hp)
  have hbound := mul_lt_mul_of_pos_left (hmass N hNbN) hgamma
  have heq : gamma * (B + 1) = epsilon := by
    dsimp [gamma]
    field_simp [show B + 1 ≠ 0 by positivity]
  rw [heq] at hbound
  exact hnegative.trans_lt hbound

/-- The actual signed complement has uniformly vanishing negative part.
This is not a claim that its absolute value tends to zero. -/
theorem exists_uniform_signedComplement_lower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ data : OriginalData, ∀ cap : ℕ, ∀ z : ℝ, z ≤ (cap : ℝ) →
        -epsilon < signedComplement data N cap z := by
  obtain ⟨N0, hN0, hneg⟩ := exists_uniform_negativeComplementMass_lt epsilon hepsilon
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven data cap z hcap
  exact (neg_lt_neg (hneg N hN hEven data cap z hcap)).trans_le
    (neg_negativeComplementMass_le_signedComplement data N cap z (by omega) hcap)

/-- Whole ordinary selected-family lower bound, at the original larger
rough cutoff, using the same old policy, physical normalization and exact
signed source partition. M's retained theorem is consumed, not reproved. -/
theorem exists_actual_whole_family_lower_at_original_cutoff
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ, ∃ e0 : ℝ, 0 < e0 ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 → ∀ chi : ℝ, 0 < chi → chi ≤ (e : ℝ) / 10 →
      ∃ m0 N0 : ℕ, 2 ≤ N0 ∧
      ∀ data : OriginalData, data.e = e → data.chi = chi → m0 ≤ data.m → data.omega ≤ 1 / 100 →
      ∀ N cap : ℕ, N0 ≤ N → Even N → ∀ z : ℝ,
        (N : ℝ) ^ mu ≤ z → z ≤ (cap : ℝ) →
        |(∫ t in region, sourceDensity t) -
          (∫ t in trimmedRegion (width n), sourceDensity t)| < epsilon / 4 ∧
        (∫ t in region, sourceDensity t) - epsilon <
          P2OriginalFourteenSignedParentLedger.charge N cap 0 z
            (lambda6 data (N : ℝ)) P4AOriginalAscending14Literal42.literalPattern
            (policy5 data (N : ℝ)) * Real.log (N : ℝ) / singularSeries N := by
  obtain ⟨n, e0, he0, hsource⟩ :=
    exists_actual_source_frontier_lower_at_original_cutoff (epsilon / 2) (half_pos hepsilon)
  obtain ⟨Nc, hNc, hcomp⟩ :=
    exists_uniform_signedComplement_lower (epsilon / 2) (half_pos hepsilon)
  refine ⟨n, e0, he0, ?_⟩
  intro e he hee chi hchi hchie
  obtain ⟨m0, Ns, hNs, hretained⟩ := hsource e he hee chi hchi hchie
  refine ⟨m0, max Ns Nc, hNs.trans (le_max_left _ _), ?_⟩
  intro data hde hdc hdm homega N cap hN hEven z hz hcap
  have hNsN : Ns ≤ N := (le_max_left _ _).trans hN
  have hNcN : Nc ≤ N := (le_max_right _ _).trans hN
  have hs := hretained data hde hdc hdm homega N cap hNsN hEven z hz hcap
  have hc := hcomp N hNcN hEven data cap z hcap
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpartition := normalized_charge_eq_source_add_complement data N cap hNr z
  change _ = sourceFrontierAt data N cap z + signedComplement data N cap z at hpartition
  refine ⟨hs.1.trans (by linarith), ?_⟩
  rw [hpartition]
  linarith [hs.2]

end
end ImbalancedChen.P2OriginalFourteenWholeFamilyLower
