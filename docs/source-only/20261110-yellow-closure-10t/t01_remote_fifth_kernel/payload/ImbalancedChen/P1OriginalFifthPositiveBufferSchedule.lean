import ImbalancedChen.P1OriginalFifthCorrelatedDecodedGates
import ImbalancedChen.P1OriginalFifthGrid400RefinedFullBoxCover

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / HELD DEPENDENCIES.
-- Positive openness of the actual fifth raw-row gate checker, with one
-- explicit aligned mesh chosen after a rational loss budget and BEFORE N.
-- No historical table check is executed or asserted, and no integral
-- loss is inferred merely from the exponent loss proved below.
namespace ImbalancedChen.P1OriginalFifthPositiveBufferSchedule

noncomputable section
open scoped Classical
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation
open P1OriginalFifthCorrelatedRawBoxGates
open P1OriginalFifthCorrelatedDecodedGates
open P1OriginalFifthQuantitativeGateRefinement
open P1OriginalFifthGrid400RefinedFullBoxCover

def marginValues (records : Finset FifthWireRow) : Finset ℚ :=
  insert 1 (records.image (gateMarginQ 0))

theorem marginValues_nonempty (records : Finset FifthWireRow) :
    (marginValues records).Nonempty := ⟨1, Finset.mem_insert_self _ _⟩

def commonMargin (records : Finset FifthWireRow) : ℚ :=
  (marginValues records).min' (marginValues_nonempty records)

theorem commonMargin_pos (records : Finset FifthWireRow)
    (hzero : ∀ raw ∈ records, correlatedRawBoxGateCheck 0 raw = true) :
    0 < commonMargin records := by
  have hm := Finset.min'_mem (marginValues records) (marginValues_nonempty records)
  change commonMargin records ∈ marginValues records at hm
  rcases Finset.mem_insert.mp hm with h | h
  · rw [h]
    norm_num
  · obtain ⟨raw, hr, heq⟩ := Finset.mem_image.mp h
    rw [← heq]
    exact gateMarginQ_pos 0 raw (hzero raw hr)

theorem commonMargin_le (records : Finset FifthWireRow)
    (raw : FifthWireRow) (hr : raw ∈ records) :
    commonMargin records ≤ gateMarginQ 0 raw := by
  exact Finset.min'_le _ _ (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨raw, hr, rfl⟩))

theorem gateMarginQ_shift (e : ℚ) (raw : FifthWireRow) :
    gateMarginQ e raw = gateMarginQ 0 raw - 2 * e := by
  simp only [gateMarginQ]
  ring

def bufferQ (records : Finset FifthWireRow) (delta : ℚ) : ℚ :=
  min (commonMargin records / 16) (min (delta / 100) (3 / 51200))

def chi (records : Finset FifthWireRow) (delta : ℚ) : ℝ :=
  (bufferQ records delta : ℝ) / 20

def omega (records : Finset FifthWireRow) (delta : ℚ) : ℝ :=
  min (chi records delta / 1000) ((19 / 96 : ℝ) / 4)

def stepBudget (records : Finset FifthWireRow) (delta : ℚ) : ℝ :=
  min (chi records delta)
    (min (omega records delta) ((commonMargin records : ℝ) / 16))

def scheduleQ (records : Finset FifthWireRow) (delta : ℚ) : ℕ :=
  Nat.ceil (1 / (1200 * stepBudget records delta)) + 1

theorem bufferQ_pos (records : Finset FifthWireRow) (delta : ℚ) (hd : 0 < delta)
    (hzero : ∀ raw ∈ records, correlatedRawBoxGateCheck 0 raw = true) :
    0 < bufferQ records delta := by
  exact lt_min (div_pos (commonMargin_pos records hzero) (by norm_num))
    (lt_min (div_pos hd (by norm_num)) (by norm_num))

theorem positive_parameters (records : Finset FifthWireRow) (delta : ℚ) (hd : 0 < delta)
    (hzero : ∀ raw ∈ records, correlatedRawBoxGateCheck 0 raw = true) :
    0 < bufferQ records delta ∧
      (bufferQ records delta : ℝ) < (3 / 256 : ℝ) / 100 ∧
      0 < chi records delta ∧ chi records delta < (bufferQ records delta : ℝ) / 10 ∧
      0 < omega records delta ∧ omega records delta < (19 / 96 : ℝ) ∧
      4 * (bufferQ records delta : ℝ) + 6 * chi records delta < (delta : ℝ) / 16 := by
  have he := bufferQ_pos records delta hd hzero
  have heR : (0 : ℝ) < bufferQ records delta := by exact_mod_cast he
  have heCap : bufferQ records delta ≤ (3 / 51200 : ℚ) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have heDelta : bufferQ records delta ≤ delta / 100 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have heCapR : (bufferQ records delta : ℝ) ≤ 3 / 51200 := by exact_mod_cast heCap
  have heDeltaR : (bufferQ records delta : ℝ) ≤ (delta : ℝ) / 100 := by exact_mod_cast heDelta
  have hdR : (0 : ℝ) < delta := by exact_mod_cast hd
  have hc : 0 < chi records delta := div_pos heR (by norm_num)
  have hw : 0 < omega records delta :=
    lt_min (div_pos hc (by norm_num)) (by norm_num)
  refine ⟨he, ?_, hc, ?_, hw, ?_, ?_⟩
  · norm_num at heCapR ⊢
    linarith
  · dsimp only [chi]
    linarith
  · exact (min_le_right _ _).trans_lt (by norm_num)
  · dsimp only [chi]
    linarith

-- The zero-buffer finite checks imply positive-buffer checks, through an
-- explicit rational gap. This is not an assumed positive-e checker flag.
theorem positive_buffer_checks (records : Finset FifthWireRow) (delta : ℚ)
    (hzero : ∀ raw ∈ records, correlatedRawBoxGateCheck 0 raw = true)
    (raw : FifthWireRow) (hr : raw ∈ records) :
    correlatedRawBoxGateCheck (bufferQ records delta) raw = true := by
  have hg := commonMargin_pos records hzero
  have he : bufferQ records delta ≤ commonMargin records / 16 := min_le_left _ _
  have hz := correlatedRawBoxGateCheck_sound 0 raw (hzero raw hr)
  apply decide_eq_true
  refine ⟨hz.1, hz.2.1, ?_⟩
  intro p hp
  have ha : gateAllowed (maskSlots 5 raw.mask.toNat) p.2 = true :=
    (Finset.mem_filter.mp hp).2
  have hgap := gateMarginQ_le_gap 0 raw p.1 p.2 ha
  have hcommon := commonMargin_le records raw hr
  linarith

theorem remaining_gate_margin (records : Finset FifthWireRow) (delta : ℚ)
    (hzero : ∀ raw ∈ records, correlatedRawBoxGateCheck 0 raw = true)
    (raw : FifthWireRow) (hr : raw ∈ records) :
    commonMargin records / 2 ≤ gateMarginQ (bufferQ records delta) raw := by
  rw [gateMarginQ_shift]
  have hg := commonMargin_pos records hzero
  have he : bufferQ records delta ≤ commonMargin records / 16 := min_le_left _ _
  have hm := commonMargin_le records raw hr
  linarith

-- The explicit ceil schedule is stronger than the independent omega
-- requirement. Its exact step remains 1/(2400q), with grid400 alignment.
theorem scheduled_step_small (records : Finset FifthWireRow) (delta : ℚ) (hd : 0 < delta)
    (hzero : ∀ raw ∈ records, correlatedRawBoxGateCheck 0 raw = true) :
    0 < scheduleQ records delta ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh (scheduleQ records delta)) <
        stepBudget records delta / 2 := by
  have hp := positive_parameters records delta hd hzero
  have hg : (0 : ℝ) < commonMargin records := by
    exact_mod_cast commonMargin_pos records hzero
  have hs : 0 < stepBudget records delta :=
    lt_min hp.2.2.1 (lt_min hp.2.2.2.2.1 (div_pos hg (by norm_num)))
  have hq : 0 < scheduleQ records delta := by
    unfold scheduleQ
    omega
  have hqR : (0 : ℝ) < scheduleQ records delta := by exact_mod_cast hq
  have hceil := Nat.le_ceil (1 / (1200 * stepBudget records delta))
  have hlarge : 1 / (1200 * stepBudget records delta) <
      (scheduleQ records delta : ℝ) := by
    simp only [scheduleQ, Nat.cast_add, Nat.cast_one]
    linarith
  have hmult : 1 < (scheduleQ records delta : ℝ) *
      (1200 * stepBudget records delta) :=
    (div_lt_iff₀ (by positivity)).mp hlarge
  refine ⟨hq, ?_⟩
  rw [refined_step _ hq]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2400 * scheduleQ records delta)).mpr
  nlinarith

-- One q simultaneously preserves the original small-rough mesh reserve,
-- the coarse coordinate width, and every decoded literal fifth gate.
theorem scheduled_all_decoded_gates
    (records : Finset FifthWireRow) (delta : ℚ) (hd : 0 < delta)
    (hzero : ∀ raw ∈ records, correlatedRawBoxGateCheck 0 raw = true) :
    let q := scheduleQ records delta
    logPrimeMeshStep 0 (19 / 96) (refinedMesh q) < chi records delta / 2 ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) < omega records delta / 2 ∧
      ∀ raw ∈ records, ∀ r ∈ decodeFifthRows raw (refinedMesh q),
        gateCheck (bufferQ records delta) (refinedMesh q) r = true := by
  obtain ⟨hq, hstep⟩ := scheduled_step_small records delta hd hzero
  have hsChi : stepBudget records delta ≤ chi records delta := min_le_left _ _
  have hsOmega : stepBudget records delta ≤ omega records delta :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hsGate : stepBudget records delta ≤ (commonMargin records : ℝ) / 16 :=
    (min_le_right _ _).trans (min_le_right _ _)
  dsimp only
  refine ⟨by linarith, by linarith, ?_⟩
  intro raw hr r hdecode
  have hmargin : (commonMargin records : ℝ) / 2 ≤
      (gateMarginQ (bufferQ records delta) raw : ℝ) := by
    exact_mod_cast remaining_gate_margin records delta hzero raw hr
  have hsmallR : (16 : ℝ) * (meshStepQ (refinedMesh (scheduleQ records delta)) : ℝ) <
      (gateMarginQ (bufferQ records delta) raw : ℝ) := by
    rw [cast_meshStepQ]
    linarith
  have hsmall : 16 * meshStepQ (refinedMesh (scheduleQ records delta)) <
      gateMarginQ (bufferQ records delta) raw := by exact_mod_cast hsmallR
  exact all_decoded_gateCheck_eq_true (bufferQ records delta) raw _
    (positive_buffer_checks records delta hzero raw hr) hsmall r hdecode

-- Arbitrary real eta is fixed first. Rational delta, positive e, chi,
-- omega and q are then fixed before N (which does not occur in this file).
-- The last bound is an EXPONENT-approximation budget, not an integral.
theorem exists_positive_schedule_before_N
    (records : Finset FifthWireRow)
    (hzero : ∀ raw ∈ records, correlatedRawBoxGateCheck 0 raw = true)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℚ, 0 < delta ∧ (delta : ℝ) < eta ∧
      0 < bufferQ records delta ∧
      0 < chi records delta ∧ 0 < omega records delta ∧ 0 < scheduleQ records delta ∧
      4 * (bufferQ records delta : ℝ) + 6 * chi records delta < eta / 16 ∧
      ∀ raw ∈ records, ∀ r ∈ decodeFifthRows raw (refinedMesh (scheduleQ records delta)),
        gateCheck (bufferQ records delta) (refinedMesh (scheduleQ records delta)) r = true := by
  obtain ⟨delta, hdR, hdEta⟩ := exists_rat_btwn heta
  have hd : (0 : ℚ) < delta := by exact_mod_cast hdR
  have hp := positive_parameters records delta hd hzero
  have hm := scheduled_step_small records delta hd hzero
  have hall := scheduled_all_decoded_gates records delta hd hzero
  refine ⟨delta, hd, hdEta, hp.1, hp.2.2.1, hp.2.2.2.2.1, hm.1, ?_, hall.2.2⟩
  exact hp.2.2.2.2.2.2.trans (by linarith)

end
end ImbalancedChen.P1OriginalFifthPositiveBufferSchedule
