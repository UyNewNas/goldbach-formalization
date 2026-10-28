import ImbalancedChen.P2Original248LiteralData
import ImbalancedChen.P2HistoricLogPointInterpreter
import ImbalancedChen.P2Author512EnhancedHQueryDomain

/-!
SOURCE ONLY; UNCOMPILED; ZERO FORMAL CREDIT.
The original55 h248 entries are reduced to the exact immutable-old64-round
integer program on the actual frozen184 record. Closed arithmetic proof
proposals below have NOT been evaluated or compiled. The log coefficient
soundness and lower Buchstab step are derived from existing real theorems,
not assumed as original h-bank endpoint claims.

This is not a proof of the copied h248 analytic licences. In particular the
preceding184 construction, positive seed and actual enhanced W1/W2 analytic
constructors remain OPEN. No upper-state soundness is supplied by its hash.
-/
namespace ImbalancedChen.P2Original248LowerArithmetic

noncomputable section
open Set MeasureTheory
open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2HistoricI80DivisionSoundness
open Certificates.P2HistoricLogPointInterpreter
open P2SimultaneousTableSourceOnly
open P2TableActionSourceOnly
open P2Original248RawRound
open P2Original248LiteralData
open P2HistoricSavedOrdinaryDefectAssembly

/-- The source first calls log on the rounded quotient I(right)/I(left).
It does not first turn the exact rational ratio into a single I80.point. -/
def intervalLog (x : I80) : I80 :=
  ⟨(logPoint x.lo).lo,(logPoint x.hi).hi⟩

theorem intervalLog_contains {x : I80} {v : ℝ}
    (hx : x.Contains v) (hpos : 0 < x.lo) :
    (intervalLog x).Contains (Real.log v) := by
  have hc := (contains_iff x v).mp hx
  have hlow : (0:ℝ) < decode x.lo :=
    div_pos (by exact_mod_cast hpos) Q_real_pos
  have hv : 0 < v := hlow.trans_le hc.1
  have hhiR : (0:ℝ)<decode x.hi := hv.trans_le hc.2
  have hhi : 0 < x.hi := by
    have hn := (lt_div_iff₀ Q_real_pos).mp hhiR
    exact_mod_cast (show (0:ℝ)<(x.hi:ℝ) by simpa using hn)
  have hl := (contains_iff _ _).mp (logPoint_contains hpos)
  have hu := (contains_iff _ _).mp (logPoint_contains hhi)
  apply (contains_iff _ _).mpr
  exact ⟨hl.1.trans (Real.log_le_log hlow hc.1),
    (Real.log_le_log hv hc.2).trans hu.2⟩

def rationalGrid (j : ℕ) : ℚ := 1+(j:ℚ)/50

def logInput (j : ℕ) : I80 :=
  (I80.point (rationalGrid (j+1))).div (I80.point (rationalGrid j))

/-- Pure finite original-program consistency obligations. These compare
integer values only; they are not true-log or endpoint-licence premises. -/
def WeightArithmeticChecks : Prop := ∀ j : Fin 200,
  0 ≤ rawWeight j.val ∧
  0 < (I80.point (rationalGrid j.val)).lo ∧
  0 < (logInput j.val).lo ∧
  rawWeight j.val = (intervalLog (logInput j.val)).lo

/-- Unexecuted closed kernel-decision proposal for the200 copied log
weights and their exact original interval-log computation. -/
theorem proposed_weightArithmeticChecks : WeightArithmeticChecks := by
  decide +kernel

/-- The actual copied coefficient is below the logarithmic measure of
its exact original closed cell. No log bound is an external hypothesis. -/
theorem actual_weight_log_lower (j : Fin 200) :
    (rawWeight j.val:ℝ)/tableQ ≤
      Real.log (tableGrid (j.val+1)/tableGrid j.val) := by
  have hc := proposed_weightArithmeticChecks j
  have hdiv : (logInput j.val).Contains
      ((rationalGrid (j.val+1):ℝ)/(rationalGrid j.val:ℝ)) := by
    exact I80.div_contains (I80.point_contains _) (I80.point_contains _) hc.2.1
  have hlog := intervalLog_contains hdiv hc.2.2.1
  have hl := (contains_iff _ _).mp hlog
  rw [←hc.2.2.2] at hl
  simpa only [decode,tableQ,Q,rationalGrid,tableGrid,Rat.cast_add,
    Rat.cast_one,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] using hl.1

/-- Concrete original log weights for the existing Buchstab soundness
constructor; no zero or substitute logarithm coefficient bank is used. -/
def actualLogWeights : LogWeights where
  numerator := rawWeight
  nonnegative := by
    intro j hj
    exact (proposed_weightArithmeticChecks ⟨j,hj⟩).1
  log_lower := by
    intro j hj
    exact actual_weight_log_lower ⟨j,hj⟩

/-- Genuine analytic induction STEP for the lower side of the original
one_round, after all upper W1/W2 updates. The previous-table invariants
are induction hypotheses, not a new primitive licence for the final bank.
No analytic soundness of an upper W1/W2 action is claimed by this step. -/
theorem original_lower_step_sound {δ : ℝ} {old : Table}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10)
    (hn : Nonnegative old) (hs : Sound δ old) (i : Fin 200) (hi : 50 ≤ i.val) :
    (oneRound rawWeight w1Bank w2Bank old false i:ℝ)/tableQ ≤
      Wu2008DoubleSieve.wuImprovementLimit false δ (tableGrid (i.val+1)) := by
  have ha := evaluate_sound actualLogWeights hδ hδhi hn hs
    (.buchstabLower i hi)
  change (suffix rawWeight old true (i.val-49):ℝ)/tableQ ≤ _ at ha
  rw [oneRound_lower rawWeight w1Bank w2Bank old i hi]
  rcases le_total (old false i) (suffix rawWeight old true (i.val-49)) with h | h
  · rw [max_eq_right h]
    exact ha
  · rw [max_eq_left h]
    exact hs false i

/-- The55 actual copied endpoints are indices100..154, not an unrelated
smaller seed or a newly generated replacement h bank. -/
def actualIndex (r : Fin 55) : Fin 200 := ⟨r.val+100,by omega⟩

def Terminal55Agreement : Prop := ∀ r : Fin 55,
  terminal248 false (actualIndex r) = bankLowerTable ((r.val:ℤ)+100)

/-- Source-only closed arithmetic proof proposal for the exact55 values.
Its kernel reduction is left to the user's dedicated compilation/checker
work. This declaration has no receipt and zero formal credit. -/
theorem proposed_terminal55Agreement : Terminal55Agreement := by
  decide +kernel

/-- Exact original integer origin of each copied h248 entry: retained
h184 or one of64 tails of an immutable preceding H table. This removes
any need to posit the copied h endpoint itself as a primitive input. It
does not make the seed/W1/W2 semantic induction disappear. -/
theorem copied55_as_original_lower_history (r : Fin 55) :
    bankLowerTable ((r.val:ℤ)+100) =
      (List.range 64).foldl (fun cur n => max cur
        (suffix rawWeight (state n) true ((actualIndex r).val-49)))
        (seed184 false (actualIndex r)) := by
  rw [←proposed_terminal55Agreement r]
  exact lower_history_max rawWeight w1Bank w2Bank seed184 (actualIndex r)
    (by dsimp [actualIndex]; omega) 64

/-- Unchanged row indexing between the original table action convention
and the actual endpoint supplier sought in batch30c. -/
theorem original_grid_eq_bank_endpoint (r : Fin 55) :
    tableGrid ((actualIndex r).val+1) =
      (bankCellRight ((r.val:ℤ)+100):ℝ) := by
  simp only [tableGrid,bankCellRight,actualIndex]
  push_cast
  ring

end ImbalancedChen.P2Original248LowerArithmetic
