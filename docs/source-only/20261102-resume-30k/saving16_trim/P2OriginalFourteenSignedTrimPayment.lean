import ImbalancedChen.P2OriginalFourteenWeightedTrim
import ImbalancedChen.P2OriginalFourteenUniformResidual
import ImbalancedChen.OriginalEighthCommonBetaWidthPayment
import ImbalancedChen.ActualPrimeBoxInitialSavingIntegral

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The discarded ORIGINAL ordinary residual is paid in absolute value on
the actual target-linked prime carrier. Its bound is derived from the
closed compact ordinary density theorem, not postulated. The integral
and arithmetic strip payment share one trim, chosen before the threshold.
The actual14 physical beta pair is also attached to J's independent
positive-presieve charge, retaining the width correction with its sign.
No identification of that charge with the unpresieved integral is made.
-/
namespace ImbalancedChen.P2OriginalFourteenSignedTrimPayment
noncomputable section
open scoped Classical BigOperators Topology
open Set MeasureTheory Filter VariableEnvelope
open P2OriginalAscendingEighthCapDictionary
open P2OriginalSaving16FourteenPhysicalAtlas
open P2OriginalSaving16TrimmedHistory
open P2OriginalFourteenWeightedTrim

def normalizedResidual (N cap : ℕ) (P y current : ℝ) (t : Point) : ℝ :=
  (actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ current / P) -
    actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ M t / P)) *
      Real.log (N : ℝ) / singularSeries N

def residualBound : ℝ := 8 / cutoff + 2

theorem residualBound_pos : 0 < residualBound := by
  unfold residualBound
  exact add_pos (div_pos (by norm_num) cutoff_pos) (by norm_num)

private def residualWindow : Set (ℝ × ℝ) :=
  (Icc cutoff (3 * mu) ×ˢ Icc cutoff mu) ∩ {q | q.1 ≤ 3 * q.2}

/-- Absolute arithmetic control, uniform in all literal14 source points
and inherited sixth caps. The lower residual floor is supplied by the
real H7 history, not by replacing the actual parent with R. -/
theorem exists_uniform_absolute_residual_bound :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (t : Point) (current P y : ℝ), t ∈ region →
        CurrentParentGuard t current → 0 < P → 0 < y →
        Real.log P / Real.log (N : ℝ) = S t →
        Real.log y / Real.log (N : ℝ) = t 7 →
        ∀ cap : ℕ, y ≤ (cap : ℝ) →
          |normalizedResidual N cap P y current t| ≤ residualBound := by
  have hcompact : IsCompact residualWindow :=
    (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_fst (continuous_const.mul continuous_snd))
  have hlegal : ∀ q ∈ residualWindow, 0 < q.2 ∧ 0 < q.1 ∧ q.1 ≤ 3 * q.2 := by
    intro q hq
    exact ⟨cutoff_pos.trans_le hq.1.2.1, cutoff_pos.trans_le hq.1.1.1, hq.2⟩
  obtain ⟨N0, hN0, hb⟩ :=
    exists_p1_actualSmallRosserPlusDensity_cube_compact_normalized_threshold
      residualWindow hcompact hlegal 1 zero_lt_one
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven t current P y ht hc hP hy hlogP hlogy cap hcap
  obtain ⟨cellId, hcell⟩ := mem_iUnion.mp ht
  have hg := sourceRows_cellGuard cellId t hcell
  have hp := residual_parameter_range hg current hc
  have hu := sourceRows_coordinate_bounds cellId t hcell 7
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hparams (lambda : ℝ) : actualRosserQuotientParameters (N : ℝ) P y lambda =
      (lambda - S t, t 7) := by
    simp only [actualRosserQuotientParameters, hlogP, hlogy]
  have hsingle (lambda : ℝ) (hlow : t 7 ≤ lambda - S t)
      (hhigh : lambda - S t ≤ 3 * t 7) :
      |actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ lambda / P) *
        Real.log (N : ℝ) / singularSeries N| ≤ 4 / cutoff + 1 := by
    have hmem : (lambda - S t, t 7) ∈ residualWindow :=
      ⟨⟨⟨hu.1.le.trans hlow, hhigh.trans (by linarith [hu.2])⟩,
        ⟨hu.1.le, hu.2.le⟩⟩, hhigh⟩
    obtain ⟨hlevel, hcut⟩ :=
      actualRosserQuotientParameters_exact (N : ℝ) P y lambda hNr hP hy
    rw [hparams lambda] at hlevel hcut
    have herr := hb N hN hEven (lambda - S t, t 7) hmem cap
      (by simpa only [hcut] using hcap)
    rw [hlevel, hcut] at herr
    have hbeta : 0 < lambda - S t := hp.1.trans_le hlow
    have hrec : 4 / (lambda - S t) ≤ 4 / cutoff :=
      div_le_div_of_nonneg_left (by norm_num) cutoff_pos (hu.1.le.trans hlow)
    have htri := abs_sub_le
      (actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ lambda / P) *
        Real.log (N : ℝ) / singularSeries N) (4 / (lambda - S t)) 0
    rw [sub_zero, sub_zero, abs_of_pos (div_pos (by norm_num) hbeta)] at htri
    linarith
  have ho := hsingle current hp.2.1.le hp.2.2.1
  have hn := hsingle (M t) hp.2.2.2.1.le hp.2.2.2.2
  have hdist := abs_sub_le
    (actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ current / P) *
      Real.log (N : ℝ) / singularSeries N) 0
    (actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ M t / P) *
      Real.log (N : ℝ) / singularSeries N)
  simp only [sub_zero, zero_sub, abs_neg] at hdist
  have heq : normalizedResidual N cap P y current t =
      actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ current / P) *
        Real.log (N : ℝ) / singularSeries N -
      actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ M t / P) *
        Real.log (N : ℝ) / singularSeries N := by unfold normalizedResidual; ring
  rw [heq]
  dsimp [residualBound]
  linarith

/-- Literal signed residual on the actually discarded prime tuples.
No absolute value is inserted into the definition of the source. -/
def discardedResidual (N cap : ℕ) (delta : ℝ)
    (current P y : (Fin 8 → ℕ) → ℝ) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 8 => cutoff) (fun _ => mu),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ discarded delta then
        normalizedResidual N cap (P p) (y p) (current p) (actualPrimeTupleLog N p) else 0)

/-- The source interfaces are quotient/log identities and the genuine
inherited-parent guard. There is no error or rejected-mass hypothesis. -/
def ResidualSource (N cap : ℕ) (current P y : (Fin 8 → ℕ) → ℝ) : Prop :=
  ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin 8 => cutoff) (fun _ => mu),
    actualPrimeTupleLog N p ∈ region →
      CurrentParentGuard (actualPrimeTupleLog N p) (current p) ∧
      0 < P p ∧ 0 < y p ∧
      Real.log (P p) / Real.log (N : ℝ) = S (actualPrimeTupleLog N p) ∧
      Real.log (y p) / Real.log (N : ℝ) = actualPrimeTupleLog N p 7 ∧ y p ≤ (cap : ℝ)

private theorem discardedResidual_le_mass (N cap : ℕ) (delta : ℝ)
    (current P y : (Fin 8 → ℕ) → ℝ)
    (hb : ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin 8 => cutoff) (fun _ => mu),
      actualPrimeTupleLog N p ∈ discarded delta →
        |normalizedResidual N cap (P p) (y p) (current p) (actualPrimeTupleLog N p)| ≤ residualBound) :
    |discardedResidual N cap delta current P y| ≤ residualBound * discardedPrimeMass N delta := by
  unfold discardedResidual discardedPrimeMass actualPrimeBoxTestSum
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hw := actualPrimeBoxWeight_nonneg hp
  by_cases ht : actualPrimeTupleLog N p ∈ discarded delta
  · rw [if_pos ht, indicator_of_mem ht, mul_one, abs_mul, abs_of_nonneg hw]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb p hp ht) hw
  · simp only [if_neg ht, indicator_of_notMem ht, mul_zero, abs_zero, le_refl]

/-- One positive trim pays the actual signed ordinary residual omitted
from all14 cells, and the genuine source integral. It precedes one N0;
that N0 precedes every inherited level, quotient and covering cap. -/
theorem exists_trim_signedResidual_and_integral_paid (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ,
      (∫ t in discarded (width n), |sourceDensity t|) < epsilon ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        ∀ cap : ℕ, ∀ current P y : (Fin 8 → ℕ) → ℝ,
          ResidualSource N cap current P y →
            |discardedResidual N cap (width n) current P y| < epsilon := by
  have he : 0 < epsilon / (residualBound + 1) :=
    div_pos hepsilon (by linarith [residualBound_pos])
  obtain ⟨n, hn, Nm, hNm, hmass⟩ := exists_common_trim_integral_and_prime_mass _ he
  obtain ⟨Nr, hNr, hres⟩ := exists_uniform_absolute_residual_bound
  have hbudget : epsilon / (residualBound + 1) < epsilon := by
    exact (div_lt_self hepsilon (by linarith [residualBound_pos]))
  refine ⟨n, hn.trans hbudget, max Nm Nr, hNm.trans (le_max_left _ _), ?_⟩
  intro N hN hEven cap current P y hsource
  have hbound := discardedResidual_le_mass N cap (width n) current P y (by
    intro p hp ht
    obtain ⟨hc, hP, hy, hlogP, hlogy, hcap⟩ := hsource p hp ht.1
    exact hres N ((le_max_right _ _).trans hN) hEven _ _ _ _ ht.1 hc hP hy hlogP hlogy cap hcap)
  have hm := hmass N ((le_max_left _ _).trans hN)
  have hmul := mul_lt_mul_of_pos_left hm residualBound_pos
  have heq : (residualBound + 1) * (epsilon / (residualBound + 1)) = epsilon :=
    by field_simp [show residualBound + 1 ≠ 0 by linarith [residualBound_pos]]
  nlinarith

/-- Same finite source trim, same causal third cap, and one arithmetic
threshold. The actual old-policy installation remains a separate task. -/
theorem exists_paid_trim_causal_precision
    (epsilon accuracy : ℝ) (hepsilon : 0 < epsilon) (haccuracy : 0 < accuracy) :
    ∃ n : ℕ, ∃ tau : ℝ, 0 < tau ∧ 3 * tau < accuracy ∧
      (∀ t ∈ trimmedRegion (width n),
        P2OriginalFourteenCausalHistoryMesh.pointLabel tau t ∈
          P2OriginalFourteenCausalHistoryMesh.labels tau ∧
        3 * t 0 < P2OriginalFourteenCausalHistoryMesh.finiteThirdCap tau t ∧
        oddCube t 2 < P2OriginalFourteenCausalHistoryMesh.finiteThirdCap tau t ∧
        oddCube t 4 < P2OriginalFourteenCausalHistoryMesh.finiteThirdCap tau t ∧
        oddCube t 6 < P2OriginalFourteenCausalHistoryMesh.finiteThirdCap tau t ∧
        0 < R t - P2OriginalFourteenCausalHistoryMesh.finiteThirdCap tau t ∧
        R t - P2OriginalFourteenCausalHistoryMesh.finiteThirdCap tau t < accuracy) ∧
      (∫ t in discarded (width n), |sourceDensity t|) < epsilon ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        ∀ cap : ℕ, ∀ current P y : (Fin 8 → ℕ) → ℝ,
          ResidualSource N cap current P y →
            |discardedResidual N cap (width n) current P y| < epsilon := by
  obtain ⟨n, hn, N0, hN0, hpaid⟩ := exists_trim_signedResidual_and_integral_paid epsilon hepsilon
  obtain ⟨tau, htau, hacc, hhistory⟩ := actual_fourteen_trim_common_history_precision
    (width n) (width_pos n) accuracy haccuracy
  exact ⟨n, tau, htau, hacc, hhistory, hn, N0, hN0, hpaid⟩

/-- The true original prime quotient: P is the product of all eight
primes, y is the eighth prime, and the next level is the source cap M. -/
def actualDiscardedResidual (N cap : ℕ) (delta : ℝ)
    (current : (Fin 8 → ℕ) → ℝ) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 8 => cutoff) (fun _ => mu),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ discarded delta then
        actualPrimeTupleInitialSaving N cap (current p) (M (actualPrimeTupleLog N p)) p else 0)

theorem actualDiscardedResidual_eq (N cap : ℕ) (delta : ℝ)
    (current : (Fin 8 → ℕ) → ℝ) :
    actualDiscardedResidual N cap delta current =
      discardedResidual N cap delta current (fun p => ((∏ i, p i : ℕ) : ℝ))
        (fun p => (p 7 : ℝ)) := rfl

theorem actualTuple_residualSource (N cap : ℕ) (current : (Fin 8 → ℕ) → ℝ)
    (hcap : (N : ℝ) ^ mu ≤ (cap : ℝ))
    (hcurrent : ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin 8 => cutoff) (fun _ => mu),
      actualPrimeTupleLog N p ∈ region → CurrentParentGuard (actualPrimeTupleLog N p) (current p)) :
    ResidualSource N cap current (fun p => ((∏ i, p i : ℕ) : ℝ)) (fun p => (p 7 : ℝ)) := by
  intro p hp ht
  have hprime := mem_actualPrimeBoxTuples_iff.mp hp
  have hpos (i : Fin 8) : 0 < p i := (hprime i).1.pos
  refine ⟨hcurrent p hp ht, ?_, ?_, ?_, rfl, (hprime 7).2.2.2.le.trans hcap⟩
  · exact_mod_cast (Finset.prod_pos (fun i _ => hpos i))
  · exact_mod_cast hpos 7
  · exact (actualPrimeTupleLog_sum_prod p hpos).symm

/-- Source-specific payment at the actual eight-prime product and cutoff,
attached to the full real saving16 integral through its exact trim
partition. Only the genuine current-parent history remains as an input;
no source convergence, strip bound, or numerical saving is assumed. -/
theorem exists_actual_trim_residual_and_source_integral_paid
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ,
      |(∫ t in region, sourceDensity t) -
        (∫ t in trimmedRegion (width n), sourceDensity t)| < epsilon ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ mu ≤ (cap : ℝ) →
          ∀ current : (Fin 8 → ℕ) → ℝ,
            (∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin 8 => cutoff) (fun _ => mu),
              actualPrimeTupleLog N p ∈ region →
                CurrentParentGuard (actualPrimeTupleLog N p) (current p)) →
            |actualDiscardedResidual N cap (width n) current| < epsilon := by
  obtain ⟨n, hn, N0, hN0, hpaid⟩ := exists_trim_signedResidual_and_integral_paid epsilon hepsilon
  refine ⟨n, (abs_sourceIntegral_sub_trim_le _ (width_pos n)).trans_lt hn, N0, hN0, ?_⟩
  intro N hN hEven cap hcap current hcurrent
  rw [actualDiscardedResidual_eq]
  exact hpaid N hN hEven cap current _ _ (actualTuple_residualSource N cap current hcap hcurrent)

/-- The original conditional action is retained on the discarded source:
when its genuine inherited-parent guard fails, the cap inherits current
and the residual is exactly zero. No guard is imposed on discarded
histories merely to make an analytic estimate applicable. -/
def actualGuardedDiscardedResidual (N cap : ℕ) (delta : ℝ)
    (current : (Fin 8 → ℕ) → ℝ) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 8 => cutoff) (fun _ => mu),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ discarded delta then
        actualPrimeTupleInitialSaving N cap (current p)
          (if CurrentParentGuard (actualPrimeTupleLog N p) (current p)
            then M (actualPrimeTupleLog N p) else current p) p else 0)

/-- The guard above is exactly the original family selector on literal
source points; both inactive branches inherit the actual sixth level. -/
theorem literal_source_keeps_original_current_gate
    (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ)
    (ht : primeHistoryLogCoordinates N 8 pre ∈ region) :
    familyNextExponent N lambda6 P4AOriginalAscending14Literal42.literalPattern pre =
      if CurrentParentGuard (primeHistoryLogCoordinates N 8 pre) (inheritedExponent lambda6 pre)
        then M (primeHistoryLogCoordinates N 8 pre) else inheritedExponent lambda6 pre := by
  unfold familyNextExponent
  dsimp only
  simp only [region_selectedFamilyGuard ht, true_and]

private theorem guardedDiscardedResidual_le_mass
    (N cap : ℕ) (delta : ℝ) (current : (Fin 8 → ℕ) → ℝ)
    (hcap : (N : ℝ) ^ mu ≤ (cap : ℝ))
    (hb : ∀ (t : Point) (v P y : ℝ), t ∈ region →
      CurrentParentGuard t v → 0 < P → 0 < y →
      Real.log P / Real.log (N : ℝ) = S t →
      Real.log y / Real.log (N : ℝ) = t 7 →
      y ≤ (cap : ℝ) → |normalizedResidual N cap P y v t| ≤ residualBound) :
    |actualGuardedDiscardedResidual N cap delta current| ≤
      residualBound * discardedPrimeMass N delta := by
  unfold actualGuardedDiscardedResidual discardedPrimeMass actualPrimeBoxTestSum
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hw := actualPrimeBoxWeight_nonneg hp
  by_cases ht : actualPrimeTupleLog N p ∈ discarded delta
  · rw [if_pos ht, indicator_of_mem ht, mul_one]
    by_cases hc : CurrentParentGuard (actualPrimeTupleLog N p) (current p)
    · rw [if_pos hc, abs_mul, abs_of_nonneg hw]
      have hprime := mem_actualPrimeBoxTuples_iff.mp hp
      have hpos (i : Fin 8) : 0 < p i := (hprime i).1.pos
      have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by
        exact_mod_cast (Finset.prod_pos (fun i _ => hpos i))
      have hy : (0 : ℝ) < p 7 := by exact_mod_cast hpos 7
      have hlogP : Real.log (∏ i, p i : ℕ) / Real.log (N : ℝ) =
          S (actualPrimeTupleLog N p) := (actualPrimeTupleLog_sum_prod p hpos).symm
      have h := hb _ (current p) (∏ i, p i : ℕ) (p 7 : ℝ) ht.1 hc hP hy hlogP rfl
        ((hprime 7).2.2.2.le.trans hcap)
      change |actualPrimeTupleInitialSaving N cap (current p)
        (M (actualPrimeTupleLog N p)) p| ≤ residualBound at h
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left h hw
    · rw [if_neg hc]
      simp only [actualPrimeTupleInitialSaving, sub_self, zero_mul, zero_div, mul_zero, abs_zero]
      exact mul_nonneg residualBound_pos.le hw
  · simp only [if_neg ht, indicator_of_notMem ht, mul_zero, abs_zero, le_refl]

/-- This is the unconditional-current trim payment used with a common
old policy: delta is fixed first; the later current function is arbitrary.
The original current<=R and H7 gates are evaluated rather than assumed
on the discarded region. On the retained region the gluing theorem must
still prove them to obtain the positive comparison integral. -/
theorem exists_actual_guarded_trim_and_integral_paid
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ,
      |(∫ t in region, sourceDensity t) -
        (∫ t in trimmedRegion (width n), sourceDensity t)| < epsilon ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ mu ≤ (cap : ℝ) →
          ∀ current : (Fin 8 → ℕ) → ℝ,
            |actualGuardedDiscardedResidual N cap (width n) current| < epsilon := by
  have he : 0 < epsilon / (residualBound + 1) :=
    div_pos hepsilon (by linarith [residualBound_pos])
  obtain ⟨n, hn, Nm, hNm, hmass⟩ := exists_common_trim_integral_and_prime_mass _ he
  obtain ⟨Nr, hNr, hres⟩ := exists_uniform_absolute_residual_bound
  have hbudget : epsilon / (residualBound + 1) < epsilon :=
    div_lt_self hepsilon (by linarith [residualBound_pos])
  refine ⟨n, (abs_sourceIntegral_sub_trim_le _ (width_pos n)).trans_lt (hn.trans hbudget),
    max Nm Nr, hNm.trans (le_max_left _ _), ?_⟩
  intro N hN hEven cap hcap current
  have hb := guardedDiscardedResidual_le_mass N cap (width n) current hcap (by
    intro t v P y ht hc hP hy hlogP hlogy hycap
    exact hres N ((le_max_right _ _).trans hN) hEven t v P y ht hc hP hy hlogP hlogy cap hycap)
  have hm := mul_lt_mul_of_pos_left (hmass N ((le_max_left _ _).trans hN)) residualBound_pos
  have heq : (residualBound + 1) * (epsilon / (residualBound + 1)) = epsilon := by
    field_simp [show residualBound + 1 ≠ 0 by linarith [residualBound_pos]]
  nlinarith

/-- Exact actual14 specialization of the existing signed beta supplier.
The new contribution is the actual14 ledger binding, not a claimed new
fundamental-lemma estimate. Both the width and the full paired error are
paid on the manuscript target scale, with no sign claim for old-new
absolute rough mass. The unpresieved projection defect is not discarded. -/
theorem exists_actual14_signed_beta_charge_reserve
    (nu r epsilon epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (hepsilon : 0 < epsilon) (hmax : 0 < epsilonMax) :
    ∃ beta : ℝ, 0 < beta ∧ beta < 1 / 8 ∧ beta < epsilonMax ∧ beta ^ 2 ≤ r ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ (lambda6 : List ℕ → ℝ) (base : Bool → List ℕ → Bool),
            (∀ pre, base true pre = true) →
              let w := (N : ℝ) ^ (nu * beta ^ 2)
              let z := (N : ℝ) ^ (nu * r)
              let B := (N : ℝ) ^ (nu * beta)
              let old := P4AOriginalEighthParentPhysicalLedger.parentPolicy (N : ℝ) lambda6 base false
              let fresh := P2OriginalFourteenSignedParentLedger.policy (N : ℝ) lambda6
                P4AOriginalAscending14Literal42.literalPattern base false
              |OriginalEighthCommonBetaWidthPayment.widthTerm old fresh N cap w z B| ≤
                epsilon * singularSeries N / Real.log (N : ℝ) ∧
              |(physicalDensitySum (actualSmallRoughModuli old N cap w z)
                  (actualSmallRoughRho old N cap w z B) -
                physicalDensitySum (actualSmallRoughModuli fresh N cap w z)
                  (actualSmallRoughRho fresh N cap w z B)) -
                actualSmallEulerProduct N cap w *
                  P2OriginalFourteenSignedParentLedger.charge N cap w z lambda6
                    P4AOriginalAscending14Literal42.literalPattern base| ≤
                epsilon * singularSeries N / Real.log (N : ℝ) := by
  obtain ⟨beta, hb, hb8, hbmax, hbr, N0, hN0, hpair⟩ :=
    OriginalEighthCommonBetaWidthPayment.exists_pair_target_error_reserve
      nu r epsilon epsilonMax hnu hr hepsilon hmax
  refine ⟨beta, hb, hb8, hbmax, hbr, N0, hN0, ?_⟩
  intro N hN hEven cap hcap lambda6 base hbase
  let w := (N : ℝ) ^ (nu * beta ^ 2)
  let z := (N : ℝ) ^ (nu * r)
  let B := (N : ℝ) ^ (nu * beta)
  have hp := hpair N hN hEven cap hcap
    (P4AOriginalEighthParentPhysicalLedger.parentPolicy (N : ℝ) lambda6 base false)
    (P2OriginalFourteenSignedParentLedger.policy (N : ℝ) lambda6
      P4AOriginalAscending14Literal42.literalPattern base false)
  refine ⟨hp.1, ?_⟩
  have he := hp.2
  unfold OriginalEighthCommonBetaWidthPayment.pairedError at he
  have ho := UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (P4AOriginalEighthParentPhysicalLedger.parentPolicy (N : ℝ) lambda6 base)
    (P4AOriginalEighthParentPhysicalLedger.parent_even (N : ℝ) lambda6 base hbase) N cap w z
  have hn := UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (P2OriginalFourteenSignedParentLedger.policy (N : ℝ) lambda6
      P4AOriginalAscending14Literal42.literalPattern base)
    (P2OriginalFourteenSignedParentLedger.policy_even (N : ℝ) lambda6
      P4AOriginalAscending14Literal42.literalPattern base hbase) N cap w z
  rw [← ho, ← hn, P2OriginalFourteenSignedParentLedger.parent_sub_policy_eq_charge] at he
  exact he

/-- A common, honest schedule for all proved payments: first the literal
trim and beta parameter, then one threshold for every later target,
actual inherited cap function and original14 policy. The paired beta
error remains centered at its positive-w rough coefficient; the separate
charge theorem above identifies that coefficient on even-retaining bases.
This does not add these different defects into a claimed final saving. -/
theorem exists_common_actual14_trim_beta_payment
    (nu r epsilon epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (hepsilon : 0 < epsilon) (hmax : 0 < epsilonMax) :
    ∃ n : ℕ, ∃ beta : ℝ, ∃ N0 : ℕ,
      0 < beta ∧ beta < 1 / 8 ∧ beta < epsilonMax ∧ beta ^ 2 ≤ r ∧ 2 ≤ N0 ∧
      |(∫ t in region, sourceDensity t) -
        (∫ t in trimmedRegion (width n), sourceDensity t)| < epsilon ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ cap : ℕ,
        (N : ℝ) ^ mu ≤ (cap : ℝ) → (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
        ∀ (current : (Fin 8 → ℕ) → ℝ) (lambda6 : List ℕ → ℝ) (base : Bool → List ℕ → Bool),
          let w := (N : ℝ) ^ (nu * beta ^ 2)
          let z := (N : ℝ) ^ (nu * r)
          let B := (N : ℝ) ^ (nu * beta)
          let old := P4AOriginalEighthParentPhysicalLedger.parentPolicy (N : ℝ) lambda6 base false
          let fresh := P2OriginalFourteenSignedParentLedger.policy (N : ℝ) lambda6
            P4AOriginalAscending14Literal42.literalPattern base false
          |actualGuardedDiscardedResidual N cap (width n) current| < epsilon ∧
          |OriginalEighthCommonBetaWidthPayment.widthTerm old fresh N cap w z B| ≤
            epsilon * singularSeries N / Real.log (N : ℝ) ∧
          |OriginalEighthCommonBetaWidthPayment.pairedError old fresh N cap w z B| ≤
            epsilon * singularSeries N / Real.log (N : ℝ) := by
  obtain ⟨n, hn, Nt, hNt, ht⟩ := exists_actual_guarded_trim_and_integral_paid epsilon hepsilon
  obtain ⟨beta, hb, hb8, hbmax, hbr, Nb, hNb, hp⟩ :=
    OriginalEighthCommonBetaWidthPayment.exists_pair_target_error_reserve
      nu r epsilon epsilonMax hnu hr hepsilon hmax
  refine ⟨n, beta, max Nt Nb, hb, hb8, hbmax, hbr,
    hNt.trans (le_max_left _ _), hn, ?_⟩
  intro N hN hEven cap hcap hcapr current lambda6 base
  exact ⟨ht N ((le_max_left _ _).trans hN) hEven cap hcap current,
    hp N ((le_max_right _ _).trans hN) hEven cap hcapr _ _⟩

end
end ImbalancedChen.P2OriginalFourteenSignedTrimPayment
