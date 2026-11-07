import ImbalancedChen.CurrentChenUpsilon34OrdinaryUpperMean
import ImbalancedChen.Part5OriginalU34H430Integrable

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal U3/U4 prime source at the original physical upper cutoff.
The U3 tail level is 1/2-tau, with 0 <= tau <= 1/12; the enhanced
branch and U4 keep v(t). No adopted H430 count estimate is assumed.
The rowwise identities preserve Q, including the positive-measure clamp.
They do not assert that rowwise H430 bounds follow from an averaged licence.
-/

namespace ImbalancedChen.Part5UpperTables.OriginalU34

noncomputable section

open Set Filter
open Part5OriginalUpsilon5CausalDictionary
open scoped BigOperators
open Classical

def U3Residual (tau t : ℝ) : ℝ :=
  if t < tailCutoff then mainResidual t else tailResidual t - tau

def physicalExponent (r : ℝ → ℝ) (t : ℝ) : ℝ := min a (r t / 2)

def primeCoordinate (N p : ℕ) : ℝ := Real.log (p : ℝ) / Real.log (N : ℝ)

/-- Each row retains its original total level. A later box approximation
must freeze this level before calling a common-Q averaged theorem. -/
def rowTotalLevel (N p : ℕ) (r : ℝ → ℝ) : ℝ :=
  (N : ℝ) ^ (primeCoordinate N p + r (primeCoordinate N p))

/-- The physical zero-buffer source has exactly the coefficient already
used in the original integral module, including the strict tail split. -/
theorem U3H430Coefficient_eq_physical_branch (t : ℝ) :
    U3H430Coefficient t = branchCoefficient H430Numerators (U3Residual 0) t := by
  by_cases h : t < tailCutoff
  · have hn : ¬tailCutoff ≤ t := not_le.mpr h
    simp [U3H430Coefficient, branchCoefficient, rootArgument, branchWeight, U3Residual, h, hn]
  · have hl : tailCutoff ≤ t := le_of_not_gt h
    simp [U3H430Coefficient, branchCoefficient, rootArgument, branchWeight, U3Residual, h, hl]

theorem mainResidual_gt_two_a {t : ℝ} (ht : t < tailCutoff) :
    2 * a < mainResidual t := by
  have hv : t + 2 * a < VariableEnvelope.v t := by
    rw [VariableEnvelope.v_eq_min]
    apply lt_min <;> dsimp [VariableEnvelope.A, VariableEnvelope.C, a] <;>
      dsimp [tailCutoff] at ht <;> linarith
  dsimp [mainResidual]
  linarith

theorem U3Residual_bounds {tau t : ℝ} (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (ht : t ∈ coordinateInterval) :
    (1 / 12 : ℝ) ≤ U3Residual tau t ∧ U3Residual tau t ≤ 1 / 2 := by
  by_cases hte : t < tailCutoff
  · have ht0 : 0 ≤ t := le_trans (by norm_num [a]) ht.1
    have hlo : t + (1 / 6 : ℝ) ≤ VariableEnvelope.v t := by
      rw [VariableEnvelope.v_eq_min]
      apply le_min <;> dsimp [VariableEnvelope.A, VariableEnvelope.C] <;>
        dsimp [tailCutoff] at hte <;> linarith [ht.2]
    have hhi := (mainResidual_bounds ht).2
    simp only [U3Residual, if_pos hte]
    dsimp [mainResidual] at *
    constructor <;> linarith
  · simp only [U3Residual, if_neg hte]
    have ht0 : 0 ≤ t := le_trans (by norm_num [a]) ht.1
    dsimp [tailResidual]
    constructor <;> linarith [ht.2]

/-- The finite half-level reserve leaves a fixed cutoff power on the
ENTIRE actual U3 band, including its clamped part. -/
theorem U3_physicalExponent_bounds {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12) (ht : t ∈ coordinateInterval) :
    (1 / 24 : ℝ) ≤ physicalExponent (U3Residual tau) t ∧
      physicalExponent (U3Residual tau) t ≤ a := by
  have hr := U3Residual_bounds htau htauhi ht
  exact ⟨le_min (by norm_num [a]) (by linarith [hr.1]), min_le_left _ _⟩

theorem U3_rootArgument_mem {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12) (ht : t ∈ coordinateInterval) :
    rootArgument (U3Residual tau) t ∈ Icc (2 : ℝ) 6 := by
  refine rootArgument_mem (r := U3Residual tau) (fun x hx => ?_) ht
  have hr := U3Residual_bounds htau htauhi hx
  exact ⟨le_trans (by norm_num) hr.1, hr.2⟩

theorem U4_physicalExponent_bounds {t : ℝ} (ht : t ∈ Ico a (59 / 250 : ℝ)) :
    (11 / 384 : ℝ) ≤ physicalExponent mainResidual t ∧
      physicalExponent mainResidual t ≤ a := by
  have hc : t ∈ coordinateInterval := ⟨ht.1, ht.2.le.trans (by norm_num)⟩
  have hr := mainResidual_bounds hc
  exact ⟨le_min (by norm_num [a]) (by linarith [hr.1]), min_le_left _ _⟩

theorem U4_physicalExponent_eq_a {t : ℝ} (ht : t ∈ Ico a (59 / 250 : ℝ)) :
    physicalExponent mainResidual t = a := by
  have hr := mainResidual_gt_two_a (ht.2.trans (by norm_num [tailCutoff]))
  exact min_eq_left (by linarith)

/-- The original alpha is derived from the actual residual; it is not
reset to two. -/
theorem U3_alpha_ge_two {tau t : ℝ} (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (ht : t ∈ coordinateInterval) : 2 ≤ (1 - t) / U3Residual tau t := by
  have hr : 0 < U3Residual tau t :=
    lt_of_lt_of_le (by norm_num) (U3Residual_bounds htau htauhi ht).1
  apply (le_div_iff₀ hr).mpr
  by_cases hte : t < tailCutoff
  · have hv : VariableEnvelope.v t ≤ (1 + t) / 2 := by
      rw [VariableEnvelope.v_eq_min]
      exact min_le_left _ _
    simp only [U3Residual, if_pos hte]
    dsimp [mainResidual]
    linarith
  · have ht0 : 0 ≤ t := le_trans (by norm_num [a]) ht.1
    simp only [U3Residual, if_neg hte]
    dsimp [tailResidual]
    linarith

/-- Algebraic identity behind the physical clamp, with no table premise. -/
theorem residual_div_rootArgument {r : ℝ → ℝ} {t : ℝ} (hr : 0 < r t) :
    r t / rootArgument r t = physicalExponent r t := by
  have ha : 0 < a := by norm_num [a]
  by_cases h : r t ≤ 2 * a
  · have hq : r t / a ≤ 2 := (div_le_iff₀ ha).mpr h
    have hm : r t / 2 ≤ a := by linarith
    simp [rootArgument, physicalExponent, max_eq_left hq, min_eq_right hm]
  · have hh : 2 * a ≤ r t := le_of_not_ge h
    have hq : 2 ≤ r t / a := (le_div_iff₀ ha).mpr hh
    have hm : a ≤ r t / 2 := by linarith
    rw [rootArgument, physicalExponent, max_eq_right hq, min_eq_left hm]
    field_simp [ha.ne', hr.ne'] <;> ring

theorem primeCoordinate_mem {N p : ℕ} (hN : 2 ≤ N) {U : ℝ}
    (hp : p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ U)) :
    primeCoordinate N p ∈ Ico a U := by
  obtain ⟨hc, hlo, hhi⟩ := Finset.mem_filter.mp hp
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hpp : (0 : ℝ) < p := by
    exact_mod_cast (mem_chenAdditivePrimeCarrier.mp hc).2.1.pos
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hNp a) hlo
  have hu := Real.log_lt_log hpp hhi
  rw [Real.log_rpow hNp] at hl hu
  exact ⟨(le_div_iff₀ (Real.log_pos hNr)).mpr (by nlinarith only [hl]),
    (div_lt_iff₀ (Real.log_pos hNr)).mpr (by nlinarith only [hu])⟩

/-- Exact same-Q physical cutoff, on the original natural prime label. -/
theorem row_sameQ_cutoff {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p)
    {r : ℝ → ℝ} (hr : 0 < r (primeCoordinate N p)) :
    (rowTotalLevel N p r / (p : ℝ)) ^ (1 / rootArgument r (primeCoordinate N p)) =
      (N : ℝ) ^ physicalExponent r (primeCoordinate N p) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp
  have hrecover : (N : ℝ) ^ primeCoordinate N p = (p : ℝ) := by
    rw [primeCoordinate, Real.rpow_def_of_pos hNp]
    rw [mul_div_cancel₀ _ (Real.log_pos hNr).ne', Real.exp_log hpp]
  have hlevel : rowTotalLevel N p r / (p : ℝ) =
      (N : ℝ) ^ r (primeCoordinate N p) := by
    unfold rowTotalLevel
    rw [Real.rpow_add hNp, hrecover]
    field_simp [hpp.ne'] <;> ring
  rw [hlevel, ← Real.rpow_mul hNp.le]
  congr 1
  simpa only [div_eq_mul_inv, one_mul] using residual_div_rootArgument hr

/-- The same total Q also supplies a fixed residual power. -/
theorem U3_sameQ_residual_power {N p : ℕ} (hN : 2 ≤ N) {tau : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hp : p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (1 / 3 : ℝ))) :
    (N : ℝ) ^ (1 / 12 : ℝ) ≤ rowTotalLevel N p (U3Residual tau) / (p : ℝ) := by
  have hc := primeCoordinate_mem hN hp
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp := zero_lt_one.trans hNr
  have hpp : (0 : ℝ) < p := by
    exact_mod_cast (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1.pos
  have hrecover : (N : ℝ) ^ primeCoordinate N p = (p : ℝ) := by
    rw [primeCoordinate, Real.rpow_def_of_pos hNp]
    rw [mul_div_cancel₀ _ (Real.log_pos hNr).ne', Real.exp_log hpp]
  have hlevel : rowTotalLevel N p (U3Residual tau) / (p : ℝ) =
      (N : ℝ) ^ U3Residual tau (primeCoordinate N p) := by
    unfold rowTotalLevel
    rw [Real.rpow_add hNp, hrecover]
    field_simp [hpp.ne'] <;> ring
  rw [hlevel]
  exact Real.rpow_le_rpow_of_exponent_le hNr.le
    (U3Residual_bounds htau htauhi ⟨hc.1, hc.2.le⟩).1

private theorem source_antitone {N p : ℕ} {z w : ℝ} (hzw : z ≤ w) :
    chenSiftedQuotientPrimeSource N p w ⊆ chenSiftedQuotientPrimeSource N p z := by
  intro q hq
  obtain ⟨hq, hr⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨hq, fun ell hell hdiv => hzw.trans (hr ell hell hdiv)⟩

/-- This is a literal count comparison, not a normalized table licence.
The cutoff is lowered while the selected p, prime receiver, and Q remain
unchanged. The inequality has the upper-cost direction required by h34. -/
theorem original_row_le_sameQ_clamped_count {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p)
    {r : ℝ → ℝ} (hr : 0 < r (primeCoordinate N p)) :
    ((chenSiftedQuotientPrimeSource N p ((N : ℝ) ^ a)).card : ℝ) ≤
      ((chenSiftedQuotientPrimeSource N p
        ((rowTotalLevel N p r / (p : ℝ)) ^
          (1 / rootArgument r (primeCoordinate N p)))).card : ℝ) := by
  rw [row_sameQ_cutoff hN hp hr]
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  exact_mod_cast Finset.card_le_card (source_antitone
    (Real.rpow_le_rpow_of_exponent_le hNr (min_le_left a (r (primeCoordinate N p) / 2))))

/-- The selected prime lies above the new strict sieve cutoff. Thus the
clamp does not silently begin sieving by the selected prefix prime. -/
theorem row_sameQ_cutoff_le_selected_prime {N p : ℕ} (hN : 2 ≤ N) {U : ℝ}
    (hp : p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ U))
    {r : ℝ → ℝ} (hr : 0 < r (primeCoordinate N p)) :
    (rowTotalLevel N p r / (p : ℝ)) ^ (1 / rootArgument r (primeCoordinate N p)) ≤ p := by
  have hpp := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1.pos
  rw [row_sameQ_cutoff hN hpp hr]
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  exact (Real.rpow_le_rpow_of_exponent_le hNr
    (min_le_left a (r (primeCoordinate N p) / 2))).trans (Finset.mem_filter.mp hp).2.1

/-- U4 never reaches the clamp, so its physical source is the literal
original count, without any cardinality enlargement. -/
theorem original_U4_eq_sameQ_count {N : ℕ} (hN : 2 ≤ N) :
    currentChenUpsilon4 N =
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (59 / 250 : ℝ)),
        ((chenSiftedQuotientPrimeSource N p
          ((rowTotalLevel N p mainResidual / (p : ℝ)) ^
            (1 / rootArgument mainResidual (primeCoordinate N p)))).card : ℝ) := by
  rw [currentChenUpsilon4_eq_siftedQuotientPrimeSource]
  apply Finset.sum_congr rfl
  intro p hp
  have hc := primeCoordinate_mem hN hp
  have hr := mainResidual_gt_two_a (hc.2.trans (by norm_num [tailCutoff]))
  have hrp : 0 < mainResidual (primeCoordinate N p) :=
    lt_trans (by norm_num [a]) hr
  rw [row_sameQ_cutoff hN
      (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1.pos hrp,
    U4_physicalExponent_eq_a hc]

/-- The two original strict bands, with their multiplicity-two overlap,
are attached to their physical cutoff sources. No source mass is merged. -/
theorem original_U34_le_sameQ_clamped_counts {N : ℕ} (hN : 2 ≤ N) {tau : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12) :
    currentChenUpsilon3 N + currentChenUpsilon4 N ≤
      (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (1 / 3 : ℝ)),
        ((chenSiftedQuotientPrimeSource N p
          ((rowTotalLevel N p (U3Residual tau) / (p : ℝ)) ^
            (1 / rootArgument (U3Residual tau) (primeCoordinate N p)))).card : ℝ)) +
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (59 / 250 : ℝ)),
        ((chenSiftedQuotientPrimeSource N p
          ((rowTotalLevel N p mainResidual / (p : ℝ)) ^
            (1 / rootArgument mainResidual (primeCoordinate N p)))).card : ℝ) := by
  rw [currentChenUpsilon3_eq_siftedQuotientPrimeSource,
    currentChenUpsilon4_eq_siftedQuotientPrimeSource]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro p hp
    have hc := primeCoordinate_mem hN hp
    exact original_row_le_sameQ_clamped_count hN
      (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1.pos
      (lt_of_lt_of_le (by norm_num) (U3Residual_bounds htau htauhi ⟨hc.1, hc.2.le⟩).1)
  · apply Finset.sum_le_sum
    intro p hp
    have hc := primeCoordinate_mem hN hp
    have hc' : primeCoordinate N p ∈ coordinateInterval :=
      ⟨hc.1, hc.2.le.trans (by norm_num)⟩
    exact original_row_le_sameQ_clamped_count hN
      (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1.pos
      (lt_of_lt_of_le (by norm_num) (mainResidual_bounds hc').1)

end
end ImbalancedChen.Part5UpperTables.OriginalU34
