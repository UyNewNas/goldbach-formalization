import ImbalancedChen.P2HistoricLogCallerGuards
import ImbalancedChen.P2SimultaneousTableIteration

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual Buchstab weights in certify_finite_step_table.py are
`log(I(b) / a).lo`, where a=1+j/50 and b=1+(j+1)/50.  Both endpoints
are first rounded to I80, their quotient is rounded again, and only then
is the historical atanh32 logarithm called.  In particular this is not
`logI (b/a)` and is not an exact-real logarithm rounded once.

This file removes the 200 local coefficient guards from the existing
analytic Buchstab engine.  Separation of consecutive rational knots pays
the TWO point-rounding errors before division.  The literal integer
atanh loop proves nonnegativity of every weight, without evaluating the
200 outputs.  Its existing real logarithm theorem supplies the enclosure.

The original positive seed, W1/W2 baselines and feedback, immutable
184+64 history and the copied h248 integers remain separate obligations.
No BankEndpointLicences or final table soundness is assumed or asserted.
-/

namespace ImbalancedChen.P2HistoricalBankLogWeights

noncomputable section

open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2HistoricLogPointInterpreter
open Certificates.P2HistoricLogCallerGuards
open Certificates.P2DirectedLogRounding
open P2TableActionSourceOnly P2SimultaneousTableSourceOnly
open scoped BigOperators

/-- The producer's rational grid, before any fixed-point conversion. -/
def gridQ (j : ℕ) : ℚ := 1 + (j : ℚ) / 50

theorem gridQ_cast (j : ℕ) : (gridQ j : ℝ) = tableGrid j := by
  simp [gridQ, tableGrid]

theorem gridQ_one_le (j : ℕ) : 1 ≤ gridQ j := by
  exact le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg j) (by norm_num))

theorem gridQ_step (j : ℕ) : gridQ (j+1) = gridQ j + 1/50 := by
  simp only [gridQ, Nat.cast_add, Nat.cast_one]
  ring

/-- The producer tests the left knot, not the query's right endpoint. -/
theorem gridQ_left_admitted_iff (j : ℕ) : 2 ≤ gridQ j ↔ 50 ≤ j := by
  constructor
  · intro hj
    have hr : (50 : ℚ) ≤ j := by dsimp [gridQ] at hj; linarith
    exact_mod_cast hr
  · intro hj
    have hr : (50 : ℚ) ≤ j := by exact_mod_cast hj
    dsimp [gridQ]
    linarith

/-- Exact rational index before Python's `int`, with no truncation of a
nonintegral endpoint.  This is the original lower tail start. -/
theorem gridQ_lower_index {j : ℕ} (hj : 50 ≤ j) :
    (gridQ (j+1)-2)*50 = ((j-49 : ℕ) : ℚ) := by
  rw [Nat.cast_sub (by omega : 49 ≤ j)]
  simp only [gridQ, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

theorem gridQ_lower_floor_index {j : ℕ} (hj : 50 ≤ j) :
    ⌊(gridQ (j+1)-2)*50⌋ = ((j-49 : ℕ) : ℤ) := by
  rw [gridQ_lower_index hj]
  simp

theorem point_order (q : ℚ) : (I80.point q).lo ≤ (I80.point q).hi := by
  exact Int.floor_le_ceil (q * (Q : ℚ))

private theorem floor_int_div_positive (m n : ℤ) (hn : 0 < n) :
    ⌊(m : ℚ)/(n : ℚ)⌋ = m/n := by
  have hnZ : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
  have hnQ : (n.toNat : ℚ) = (n : ℚ) := by exact_mod_cast hnZ
  have hfloor := Rat.floor_intCast_div_natCast m n.toNat
  rw [hnQ, hnZ] at hfloor
  exact hfloor

/-- Operational binding of the division lower endpoint to the four
literal Python `n*Q//d` corners.  The denominator order is reversed by
reciprocalBounds; taking the minimum preserves the same four values. -/
theorem quotient_lo_integer {x y : I80} (hypos : 0 < y.lo) (hy : y.lo ≤ y.hi) :
    (x.div y).lo =
      min (min (x.lo*(Q : ℤ)/y.hi) (x.lo*(Q : ℤ)/y.lo))
        (min (x.hi*(Q : ℤ)/y.hi) (x.hi*(Q : ℤ)/y.lo)) := by
  have hcorner (m n : ℤ) (hn : 0 < n) :
      ⌊((m : ℚ)/Q * (1/((n : ℚ)/Q)))*(Q : ℚ)⌋ = m*(Q : ℤ)/n := by
    have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have he : ((m : ℚ)/Q * (1/((n : ℚ)/Q)))*(Q : ℚ) =
        ((m*(Q : ℤ) : ℤ) : ℚ)/(n : ℚ) := by
      push_cast
      field_simp [Q_ne_zero, hnQ] <;> ring
    rw [he]
    exact floor_int_div_positive _ _ hn
  simp only [I80.div, I80.ofEnclosure, Enclosure.divisionBounds,
    Enclosure.mul, Enclosure.reciprocalBounds, I80.enclosure, I80.decodeLo,
    I80.decodeHi, min_mul_of_nonneg _ _ Q_pos.le, floor_min_rat]
  rw [hcorner x.lo y.hi (hypos.trans_le hy), hcorner x.lo y.lo hypos,
    hcorner x.hi y.hi (hypos.trans_le hy), hcorner x.hi y.lo hypos]

/-- The real grid spacing dominates the outward point errors.  This is
a proof for all indices, not a 200-case endpoint calculation. -/
theorem consecutive_rounded_knots (j : ℕ) :
    (I80.point (gridQ j)).hi ≤ (I80.point (gridQ (j+1))).lo := by
  change ⌈gridQ j * (Q : ℚ)⌉ ≤ ⌊gridQ (j+1) * (Q : ℚ)⌋
  apply Int.le_floor.mpr
  have hceil := Int.ceil_lt_add_one (gridQ j * (Q : ℚ))
  have hscale : (50 : ℚ) ≤ Q := by norm_num [Q]
  rw [gridQ_step]
  nlinarith

private theorem normalized_corner_one_le {m n : ℤ}
    (hn : 0 < n) (hnm : n ≤ m) :
    1 ≤ ((m : ℚ) / Q) * (1 / ((n : ℚ) / Q)) := by
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have he : ((m : ℚ) / Q) * (1 / ((n : ℚ) / Q)) = (m : ℚ) / n := by
    field_simp [Q_ne_zero, hnQ.ne'] <;> ring
  rw [he]
  apply (le_div_iff₀ hnQ).mpr
  simpa only [one_mul] using (show (n : ℚ) ≤ m by exact_mod_cast hnm)

/-- Every one of the four quotient corners is at least one.  The outer
Q80 floor therefore stays at least Q; this proves the subsequent log
guard on the rounded interval itself. -/
theorem quotient_lo_ge_Q {x y : I80}
    (hx : x.lo ≤ x.hi) (hy : y.lo ≤ y.hi)
    (hypos : 0 < y.lo) (hyx : y.hi ≤ x.lo) :
    (Q : ℤ) ≤ (x.div y).lo := by
  have hlow : (1 : ℚ) ≤ (x.enclosure.divisionBounds y.enclosure).lower := by
    change 1 ≤ min
      (min (((x.lo : ℚ)/Q) * (1/((y.hi : ℚ)/Q)))
        (((x.lo : ℚ)/Q) * (1/((y.lo : ℚ)/Q))))
      (min (((x.hi : ℚ)/Q) * (1/((y.hi : ℚ)/Q)))
        (((x.hi : ℚ)/Q) * (1/((y.lo : ℚ)/Q))))
    exact le_min
      (le_min (normalized_corner_one_le (hypos.trans_le hy) hyx)
        (normalized_corner_one_le hypos (hy.trans hyx)))
      (le_min (normalized_corner_one_le (hypos.trans_le hy) (hyx.trans hx))
        (normalized_corner_one_le hypos (hy.trans (hyx.trans hx))))
  change (Q : ℤ) ≤ ⌊(x.enclosure.divisionBounds y.enclosure).lower * (Q : ℚ)⌋
  apply Int.le_floor.mpr
  simpa only [Int.cast_natCast, one_mul] using
    mul_le_mul_of_nonneg_right hlow Q_pos.le

/-- Literal `I(b)/a`: Python coerces its rational denominator to I(a). -/
def quotientBox (j : ℕ) : I80 :=
  (I80.point (gridQ (j+1))).div (I80.point (gridQ j))

theorem quotientBox_lo_ge_Q (j : ℕ) : (Q : ℤ) ≤ (quotientBox j).lo := by
  exact quotient_lo_ge_Q (point_order _) (point_order _)
    (point_lo_pos_of_one_le _ (gridQ_one_le j)) (consecutive_rounded_knots j)

theorem quotientBox_contains (j : ℕ) :
    (quotientBox j).Contains (tableGrid (j+1) / tableGrid j) := by
  have hc := I80.div_contains (I80.point_contains (gridQ (j+1)))
    (I80.point_contains (gridQ j))
    (point_lo_pos_of_one_le _ (gridQ_one_le j))
  simpa only [quotientBox, gridQ_cast] using hc

/-- Nonnegativity belongs to the literal lower integer loop.  Soundness
alone would not imply it: a lower endpoint for log(x)>0 can be negative. -/
theorem oddLoop_lower_nonnegative {ul uh : ℤ} (hul : 0 ≤ ul) (n : ℕ) :
    0 ≤ (oddLoop (oddSquare ul uh) ul uh n).power.lo ∧
      0 ≤ (oddLoop (oddSquare ul uh) ul uh n).total.lo := by
  have hsquare : 0 ≤ (oddSquare ul uh).lo :=
    Int.ediv_nonneg (mul_self_nonneg ul) Q_int_pos.le
  induction n with
  | zero => exact ⟨hul, le_rfl⟩
  | succ n ih =>
      constructor
      · exact positiveMul_lo_nonnegative ih.1 hsquare
      · change 0 ≤ (oddLoop (oddSquare ul uh) ul uh n).total.lo +
          (oddLoop (oddSquare ul uh) ul uh n).power.lo / ((2*n+1 : ℕ) : ℤ)
        exact add_nonneg ih.2 (Int.ediv_nonneg ih.1 (by positivity))

theorem atanhBounds_lo_nonnegative {ul uh : ℤ} (hul : 0 ≤ ul) :
    0 ≤ (atanhBounds ul uh).lo := by
  exact mul_nonneg (by norm_num) (oddLoop_lower_nonnegative (uh := uh) hul 32).2

theorem logTwoBounds_lo_nonnegative : 0 ≤ logTwoBounds.lo := by
  exact atanhBounds_lo_nonnegative (Int.ediv_nonneg Q_int_pos.le (by norm_num))

theorem sourceShift_nonnegative_of_Q_le {q : ℤ} (hq : (Q : ℤ) ≤ q) :
    0 ≤ Certificates.P2HistoricLogRangeReduction.sourceShift q := by
  have hnat : Q ≤ q.toNat := by omega
  have hsize : 80 < q.toNat.size := Nat.lt_size.mpr hnat
  unfold Certificates.P2HistoricLogRangeReduction.sourceShift
    Certificates.P2HistoricLogRangeReduction.binaryExponent
  omega

/-- The source's signed LOG2 branch is determined by the integer input.
At q>=Q it is the nonnegative branch, and both its summands are >=0. -/
theorem logPoint_lo_nonnegative_of_Q_le {q : ℤ} (hq : (Q : ℤ) ≤ q) :
    0 ≤ (logPoint q).lo := by
  by_cases he : q = (Q : ℤ)
  · simp only [logPoint, if_pos he, I80.raw, le_refl]
  · have hqpos : 0 < q := Q_int_pos.trans_le hq
    have hends := Certificates.P2HistoricLogRangeReduction.source_endpoint_guards hqpos
    have hcheck := reducedCheck_of_endpoints hends.1 hends.2.1 hends.2.2
    have hred : ReducedChecks
        (Certificates.P2HistoricLogRangeReduction.sourceRL q)
        (Certificates.P2HistoricLogRangeReduction.sourceRH q) := of_decide_eq_true hcheck
    have hshift := sourceShift_nonnegative_of_Q_le hq
    have hbase := atanhBounds_lo_nonnegative hred.2.1
    simp only [logPoint, if_neg he, logPointFromReduction, I80.add,
      integerScale, if_pos hshift]
    exact add_nonneg hbase (mul_nonneg hshift logTwoBounds_lo_nonnegative)

/-- The actual saved scalar algorithm, without a literal array replay. -/
def logWeight (j : ℕ) : ℤ := (logInterval (quotientBox j)).lo

theorem logWeight_nonnegative (j : ℕ) : 0 ≤ logWeight j := by
  exact logPoint_lo_nonnegative_of_Q_le (quotientBox_lo_ge_Q j)

/-- Analytic enclosure for every actual producer coefficient.  Both the
division assertion and the logarithm assertion have been discharged. -/
theorem logWeight_le_log (j : ℕ) :
    (logWeight j : ℝ) / tableQ ≤ Real.log (tableGrid (j+1) / tableGrid j) := by
  have hlog := logInterval_contains (quotientBox_contains j)
    (Q_int_pos.trans_le (quotientBox_lo_ge_Q j))
  have hl := ((contains_iff _ _).mp hlog).1
  simpa only [logWeight, decode, tableQ, Q] using hl

/-- No coefficient certificate fields are supplied by a caller. -/
def historicalLogWeights : LogWeights where
  numerator := logWeight
  nonnegative := fun j _ => logWeight_nonnegative j
  log_lower := fun j _ => logWeight_le_log j

/-- Concrete ordinary action engine with its original Q80 scalar backend.
The assumptions are only the preceding generation's invariant, not local
log enclosures or an endpoint bound for the newly produced candidate. -/
theorem historical_buchstab_action_sound {δ : ℝ} {old : Table}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10)
    (hn : Nonnegative old) (hsound : Sound δ old) (a : Action) :
    (evaluate historicalLogWeights old a : ℝ) / tableQ ≤
      Wu2008DoubleSieve.wuImprovementLimit a.target.1 δ
        (tableGrid (a.target.2.val+1)) := by
  exact evaluate_sound historicalLogWeights hδ hδhi hn hsound a

end
end ImbalancedChen.P2HistoricalBankLogWeights
