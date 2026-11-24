import ImbalancedChen.P2DegreeSixLogGapSoundness
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-!
SOURCE ONLY / NOT ELABORATED / no producer or numeric replay.
Literal frozen eighth-unequal-moment-independent-engine-20261009.py:
  factor: floor_Q80(sum_{k=2}^6 (moment[k]-moment[1]^k)/k);
  T=sum(factor_floor_integers)/2^80;
  old=4*actual_gap_mass/prod(weighted_factor_means);
  new=old*(1+T*(1+T*(1/2+T/6)));
  new_floor=floor_Q96(new).

There is NO Q112 step and no Q96-to-Q80 conversion in this source path.
Q80 is the log-gap scale; Q96 is the simplex lower-bound scale.  We preserve
that direction, including the exact Python numerator*2^bits//den operation.

Actual simplex mass, means and moments are explicit semantic equalities with
real integrals.  Stored fields alone never establish them.  Degree-six gap
soundness and weighted Jensen are proved in the preceding two modules; this
file connects them to the literal rational/floor evaluator without assuming
any final gain or reciprocal-integral lower bound.
-/

namespace ImbalancedChen.P2OriginalLogMomentQ96CheckerSourceOnly

noncomputable section

open Set MeasureTheory
open P2PositiveAffineSimplexLogJensenSourceOnly
open P2DegreeSixLogGapSoundnessSourceOnly

/-- Exactly Python Fraction.numerator*2^bits//Fraction.denominator. -/
def fixedNumerator (bits : ℕ) (r : ℚ) : ℤ := r.num * (2 : ℤ) ^ bits / (r.den : ℤ)

def roundDownQ (bits : ℕ) (r : ℚ) : ℚ := (fixedNumerator bits r : ℚ) / (2 : ℚ) ^ bits

theorem fixedNumerator_eq_floor (bits : ℕ) (r : ℚ) :
    fixedNumerator bits r = ⌊(r : ℝ) * (2 : ℝ) ^ bits⌋ := by
  have hr : (r : ℝ) * (2 : ℝ) ^ bits =
      ((r.num * (2 : ℤ) ^ bits : ℤ) : ℝ) / (r.den : ℝ) := by
    rw [Rat.cast_def]
    push_cast
    ring
  rw [hr]
  unfold fixedNumerator
  have h := Int.floor_div_cast_of_nonneg (k := ℝ) (Int.natCast_nonneg r.den)
    (((r.num * (2 : ℤ) ^ bits : ℤ) : ℝ))
  simpa using h.symm

theorem roundDownQ_le (bits : ℕ) (r : ℚ) : (roundDownQ bits r : ℝ) ≤ (r : ℝ) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ bits := pow_pos (by norm_num) _
  unfold roundDownQ
  push_cast
  apply (div_le_iff₀ hp).2
  rw [fixedNumerator_eq_floor]
  exact Int.floor_le _

theorem roundDownQ_nonneg (bits : ℕ) {r : ℚ} (hr : 0 ≤ r) : 0 ≤ roundDownQ bits r := by
  have hrr : (0 : ℝ) ≤ r := by exact_mod_cast hr
  have hn : 0 ≤ fixedNumerator bits r := by
    rw [fixedNumerator_eq_floor]
    exact Int.floor_nonneg.mpr (mul_nonneg hrr (pow_nonneg (by norm_num) _))
  exact div_nonneg (by exact_mod_cast hn) (pow_nonneg (by norm_num) _)

theorem fixedNumerator_mono (bits : ℕ) {r s : ℚ} (hrs : r ≤ s) :
    fixedNumerator bits r ≤ fixedNumerator bits s := by
  simp only [fixedNumerator_eq_floor]
  apply Int.floor_mono
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hrs) (pow_nonneg (by norm_num) _)

/-- Moments are still stored rational fields here. They acquire semantics
only through actual moment equalities supplied to gapEvaluator_cast. -/
def gapEvaluator (moments : ℕ → ℚ) : ℚ :=
  ∑ j ∈ Finset.range 5, (moments (j + 2) - moments 1 ^ (j + 2)) / ((j : ℚ) + 2)

def factorFloorQ80 (moments : ℕ → ℚ) : ℤ := fixedNumerator 80 (gapEvaluator moments)

def factorLowerQ80 (moments : ℕ → ℚ) : ℚ := roundDownQ 80 (gapEvaluator moments)

variable {α : Type*} [MeasurableSpace α]

theorem gapEvaluator_cast (ν : Measure α) (Y : α → ℝ) (moments : ℕ → ℚ)
    (hMom : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → (moments k : ℝ) = ∫ x, Y x ^ k ∂ν) :
    (gapEvaluator moments : ℝ) = gapSix ν Y := by
  have hm1 : (moments 1 : ℝ) = ∫ x, Y x ∂ν := by
    simpa only [pow_one] using hMom 1 (by norm_num) (by norm_num)
  unfold gapEvaluator gapSix
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  rw [hMom (j + 2) (by omega) (by have h := Finset.mem_range.mp hj; omega), hm1]

/-- Per-factor Q80 soundness is derived from actual degree-six moments and
the full log remainder. No log-gap or integral lower bound is presumed. -/
theorem factor_Q80_sound
    (ν : Measure α) [IsProbabilityMeasure ν] (L : α → ℝ) (top : ℝ) (hTop : 0 < top)
    (moments : ℕ → ℚ) {q : ℝ} (hq : q < 1)
    (hRange : ∀ᵐ x ∂ν, scaledDeviation top L x ∈ Icc (0 : ℝ) q)
    (hL0 : ∀ᵐ x ∂ν, 0 < L x) (hL : Integrable L ν)
    (hLog : Integrable (fun x => Real.log (L x)) ν)
    (hPow : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → Integrable (fun x => scaledDeviation top L x ^ k) ν)
    (hMom : ∀ k : ℕ, 1 ≤ k → k ≤ 6 →
      (moments k : ℝ) = ∫ x, scaledDeviation top L x ^ k ∂ν) :
    0 ≤ factorLowerQ80 moments ∧
      (∫ x, Real.log (L x) ∂ν) ≤
        Real.log (∫ x, L x ∂ν) - (factorLowerQ80 moments : ℝ) := by
  have he := gapEvaluator_cast ν (scaledDeviation top L) moments hMom
  have hg := probability_gapSix_nonneg ν (scaledDeviation top L)
    (hRange.mono fun x hx => hx.1) hPow
  have hgQ : 0 ≤ gapEvaluator moments := by
    have h : (0 : ℝ) ≤ (gapEvaluator moments : ℝ) := by rw [he]; exact hg
    exact_mod_cast h
  have hFloor : (factorLowerQ80 moments : ℝ) ≤ gapSix ν (scaledDeviation top L) := by
    simpa only [factorLowerQ80, he] using roundDownQ_le 80 (gapEvaluator moments)
  have hLogBound := probability_factor_log_bound ν top hTop L hq hRange hL0 hL hLog hPow
  exact ⟨roundDownQ_nonneg 80 hgQ, by linarith⟩

variable {ι : Type*} [Fintype ι]

def totalLowerQ80 (moments : ι → ℕ → ℚ) : ℚ := ∑ i, factorLowerQ80 (moments i)

/-- The actual engine's sum of Q80 integer floors is this same rational. -/
theorem totalLowerQ80_integer_formula (moments : ι → ℕ → ℚ) :
    totalLowerQ80 moments = ((∑ i, factorFloorQ80 (moments i) : ℤ) : ℚ) / (2 : ℚ) ^ 80 := by
  simp only [totalLowerQ80, factorLowerQ80, roundDownQ, factorFloorQ80,
    Int.cast_sum, Finset.sum_div]

def cubicQ (T : ℚ) : ℚ := 1 + T * (1 + T * (1 / 2 + T / 6))

def oldEvaluator (actualMass : ℚ) (means : ι → ℚ) : ℚ := 4 * actualMass / ∏ i, means i

def newEvaluator (actualMass : ℚ) (means : ι → ℚ) (moments : ι → ℕ → ℚ) : ℚ :=
  oldEvaluator actualMass means * cubicQ (totalLowerQ80 moments)

def oldFloorQ96 (actualMass : ℚ) (means : ι → ℚ) : ℤ :=
  fixedNumerator 96 (oldEvaluator actualMass means)

def newFloorQ96 (actualMass : ℚ) (means : ι → ℚ) (moments : ι → ℕ → ℚ) : ℤ :=
  fixedNumerator 96 (newEvaluator actualMass means moments)

def simplexLowerQ96 (actualMass : ℚ) (means : ι → ℚ) (moments : ι → ℕ → ℚ) : ℚ :=
  roundDownQ 96 (newEvaluator actualMass means moments)

theorem cubicQ_cast (T : ℚ) : (cubicQ T : ℝ) = cubicCorrection (T : ℝ) := by
  simp [cubicQ, cubicCorrection]

theorem newEvaluator_cast (m : ℚ) (means : ι → ℚ) (moments : ι → ℕ → ℚ) :
    (newEvaluator m means moments : ℝ) =
      (4 * (m : ℝ) / ∏ i, (means i : ℝ)) *
        cubicCorrection (∑ i, (factorLowerQ80 (moments i) : ℝ)) := by
  simp [newEvaluator, oldEvaluator, cubicQ_cast, totalLowerQ80]

theorem old_le_newEvaluator {m : ℚ} (hm : 0 ≤ m) (means : ι → ℚ)
    (hMeans : ∀ i, 0 < means i) (moments : ι → ℕ → ℚ)
    (hGaps : ∀ i, 0 ≤ factorLowerQ80 (moments i)) :
    oldEvaluator m means ≤ newEvaluator m means moments := by
  have hp : 0 < ∏ i, means i := Finset.prod_pos (fun i hi => hMeans i)
  have ho : 0 ≤ oldEvaluator m means := div_nonneg (mul_nonneg (by norm_num) hm) hp.le
  have hT : 0 ≤ totalLowerQ80 moments := Finset.sum_nonneg (fun i hi => hGaps i)
  have hc : 1 ≤ cubicQ (totalLowerQ80 moments) := by
    dsimp [cubicQ]
    have h : 0 ≤ totalLowerQ80 moments *
        (1 + totalLowerQ80 moments * (1 / 2 + totalLowerQ80 moments / 6)) := by positivity
    linarith
  simpa only [mul_one, newEvaluator] using mul_le_mul_of_nonneg_left hc ho

/-- The original source assertion new_floor>=old_floor follows from the
actual nonnegative correction and monotonic integer floor, without replay. -/
theorem oldFloorQ96_le_newFloorQ96 {m : ℚ} (hm : 0 ≤ m) (means : ι → ℚ)
    (hMeans : ∀ i, 0 < means i) (moments : ι → ℕ → ℚ)
    (hGaps : ∀ i, 0 ≤ factorLowerQ80 (moments i)) :
    oldFloorQ96 m means ≤ newFloorQ96 m means moments := by
  exact fixedNumerator_mono 96 (old_le_newEvaluator hm means hMeans moments hGaps)

/-- Literal source old numerator when the physical gap mass has its actual
simplex moment value volume*G/(9*den). This identity alone is not a mass proof. -/
theorem source_old_mass_dictionary (volume G den : ℚ) (means : ι → ℚ) :
    oldEvaluator (volume * G / (9 * den)) means =
      4 * volume * (G / (9 * den)) / ∏ i, means i := by
  unfold oldEvaluator
  ring

def checkStoredQ96 (stored : ℤ) (m : ℚ) (means : ι → ℚ) (moments : ι → ℕ → ℚ) : Bool :=
  decide (stored ≤ newFloorQ96 m means moments)

/-- A stored integer is first compared with the exact computed floor. Passing
this finite arithmetic check gives only a rational-to-rational inequality;
the separate actual moment and integral theorem is still required. -/
theorem storedQ96_le_computed (stored : ℤ) (m : ℚ) (means : ι → ℚ)
    (moments : ι → ℕ → ℚ) (hStored : checkStoredQ96 stored m means moments = true) :
    (stored : ℚ) / (2 : ℚ) ^ 96 ≤ simplexLowerQ96 m means moments := by
  have hn : stored ≤ newFloorQ96 m means moments := by
    simpa only [checkStoredQ96, decide_eq_true_eq] using hStored
  change (stored : ℚ) / (2 : ℚ) ^ 96 ≤
    (newFloorQ96 m means moments : ℚ) / (2 : ℚ) ^ 96
  apply (div_le_div_iff_of_pos_right (pow_pos (by norm_num : (0 : ℚ) < 2) 96)).2
  exact_mod_cast hn

/-- Complete actual per-simplex Q96 lower rule.  Inputs are genuine mass,
weighted mean and degree-six moment equalities, never a target gain bound. -/
theorem simplex_Q96_sound
    (μ : Measure α) (g : α → ℝ) (L : ι → α → ℝ)
    (m : ℚ) (means top : ι → ℚ) (moments : ι → ℕ → ℚ)
    (hgMeas : Measurable g) (hgInt : Integrable g μ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hm : 0 < mass μ g)
    (hMass : (m : ℝ) = mass μ g) (hMeansPos : ∀ i, 0 < means i) (hTop : ∀ i, 0 < top i)
    (hMeans : ∀ i, (means i : ℝ) = (∫ x, g x * L i x ∂μ) / mass μ g)
    (hL0 : ∀ᵐ x ∂μ, ∀ i, 0 < L i x)
    (hLInt : ∀ i, Integrable (fun x => g x * L i x) μ)
    (hLog : ∀ i, Integrable (fun x => g x * Real.log (L i x)) μ)
    (hRecip : Integrable (fun x => g x / ∏ i, L i x) μ)
    (q : ι → ℝ) (hq : ∀ i, q i < 1)
    (hRange : ∀ i, ∀ᵐ x ∂μ, scaledDeviation (top i : ℝ) (L i) x ∈ Icc (0 : ℝ) (q i))
    (hPow : ∀ i, ∀ k : ℕ, 1 ≤ k → k ≤ 6 →
      Integrable (fun x => scaledDeviation (top i : ℝ) (L i) x ^ k) (weightedProbability μ g))
    (hMom : ∀ i, ∀ k : ℕ, 1 ≤ k → k ≤ 6 →
      (moments i k : ℝ) = ∫ x, scaledDeviation (top i : ℝ) (L i) x ^ k ∂weightedProbability μ g) :
    (simplexLowerQ96 m means moments : ℝ) ≤ ∫ x, 4 * g x / ∏ i, L i x ∂μ := by
  let ν := weightedProbability μ g
  letI : IsProbabilityMeasure ν := weightedProbability_isProbability μ g hgInt hg0 hm
  have hFactor (i : ι) : 0 ≤ factorLowerQ80 (moments i) ∧
      (∫ x, Real.log (L i x) ∂ν) ≤
        Real.log (∫ x, L i x ∂ν) - (factorLowerQ80 (moments i) : ℝ) := by
    apply factor_Q80_sound ν (L i) (top i : ℝ) (by exact_mod_cast hTop i)
      (moments i) (hq i)
    · exact (withDensity_absolutelyContinuous _ _).ae_le (hRange i)
    · exact (withDensity_absolutelyContinuous _ _).ae_le (hL0.mono fun x hx => hx i)
    · exact integrable_weightedProbability μ g hgMeas hg0 hm (hLInt i)
    · exact integrable_weightedProbability μ g hgMeas hg0 hm (hLog i)
    · exact hPow i
    · exact hMom i
  have hBound (i : ι) : (∫ x, g x * Real.log (L i x) ∂μ) / mass μ g ≤
      Real.log (means i : ℝ) - (factorLowerQ80 (moments i) : ℝ) := by
    have h := (hFactor i).2
    simp only [ν, integral_weightedProbability μ g hgMeas hg0 hm] at h
    rw [← hMeans i] at h
    exact h
  have hJ := weighted_log_gap_cubic_lower_four μ g L
    (fun i => (means i : ℝ)) (fun i => (factorLowerQ80 (moments i) : ℝ))
    hgMeas hgInt hg0 hm hL0 hLog hRecip
    (fun i => by exact_mod_cast hMeansPos i)
    (fun i => by exact_mod_cast (hFactor i).1) hBound
  have hNew : (newEvaluator m means moments : ℝ) ≤ ∫ x, 4 * g x / ∏ i, L i x ∂μ := by
    rw [newEvaluator_cast, hMass]
    exact hJ
  exact (roundDownQ_le 96 (newEvaluator m means moments)).trans hNew

/-- Any later dyadic consumer may round a proved intermediate rational lower
bound downward again. This is not a fabricated Q112 stage of the producer. -/
theorem refloor_intermediate_sound (bits : ℕ) (r : ℚ) {I : ℝ} (h : (r : ℝ) ≤ I) :
    (roundDownQ bits r : ℝ) ≤ I := (roundDownQ_le bits r).trans h

end

end ImbalancedChen.P2OriginalLogMomentQ96CheckerSourceOnly
