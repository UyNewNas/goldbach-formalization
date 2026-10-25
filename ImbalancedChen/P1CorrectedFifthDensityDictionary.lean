import ImbalancedChen.P1VariableFifthOriginalBaseQ3Bridge
import ImbalancedChen.P1HistoricalFifthJointIntegralSign
import ImbalancedChen.P1OriginalCoarseFifthJointGeometry

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The original variable fifth maximum has an exact finite causal density
identity on the original T3 first-exit carrier. The corrected selected
stored-cap construction has the same carrier and an exact finite gated
charge, but the stored fifth cap has not been proved to dominate the
original variable fourth level on every next candidate. Consequently its
charge is not identified here with a retained-polynomial difference.

The continuous dictionary below keeps both strict own-cube indicators.
It does not assert an asymptotic passage from the finite prime sum to the
integral, nor identify this original-parent integral with the generic D
integral (whose base, Q3, and old fourth cap can differ).
-/

namespace ImbalancedChen.P1CorrectedFifthDensityDictionary

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators

abbrev Point5 := Fin 5 → ℝ
abbrev Label5 (m : ℕ) := Fin 5 → Fin (m + 1)

def originalBase (e : ℚ) (m : ℕ) (N : ℕ) : Bool → List ℕ → Bool :=
  HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ)

def originalQ3 (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (N : ℕ) : List ℕ → ℝ :=
  HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ)

def originalQ4 (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (N : ℕ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop) :
    List ℕ → ℝ :=
  P1OriginalVariableFourthContinuation.producerLevel4
    (e : ℝ) chi m omega (N : ℝ) rows4 licensed4

def originalT3 (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (N : ℕ) :
    Bool → List ℕ → Bool :=
  thirdCappedUpperPolicy (originalBase e m N) (originalQ3 e chi m omega N)

theorem originalT3_eq_historical (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (N : ℕ) :
    originalT3 e chi m omega N =
      HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ) := rfl

def originalFourthRetained (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (z : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop) : ℝ :=
  firstExitRetainedPolynomial
    (fourthCappedUpperPolicy (originalBase e m N) (originalQ3 e chi m omega N)
      (originalQ4 e chi m omega N rows4 licensed4))
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
    (roughPrimeUniverse N cap 0 z)

def variableFifthRetained (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (z : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (J5 : Finset (Label5 m))
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m)) : ℝ :=
  firstExitRetainedPolynomial
    (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
      rows4 licensed4 J5 rows5)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
    (roughPrimeUniverse N cap 0 z)

/-- Finite causal density identity on the actual original T3 tree. The
fifth maximum inherits the fourth cap even for a losing fifth candidate;
the fourth producer inherits the rough-activated original Q3. -/
theorem variable_fifth_finite_density_identity
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (J5 : Finset (Label5 m))
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m)) :
    originalFourthRetained e chi m omega N cap z rows4 licensed4 -
      variableFifthRetained e chi m omega N cap z rows4 licensed4 J5 rows5 =
      P1OriginalVariableFifthContinuation.actualFifthSaving e chi m omega
        rows4 licensed4 J5 rows5 N cap z := by
  unfold originalFourthRetained variableFifthRetained
    P1OriginalVariableFifthContinuation.actualFifthSaving
    P1OriginalVariableFifthContinuation.policy5
  apply actualHistoricalFifthSaving_eq
  · intro state hstate
    exact P1OriginalVariableFourthContinuation.producer_actual_h34
      (e : ℝ) chi m omega N cap hN.le z rows4 licensed4 state
      (by simpa only [originalBase, originalQ3, HistoricalThirdCoarse.policy]
        using hstate)
  · intro frontier hf candidate hc
    exact P1OriginalVariableFifthContinuation.actual_h45
      e chi m omega (N : ℝ) rows4 licensed4 J5 rows5
      N cap hN z rfl frontier candidate
      (by simpa only [originalBase, originalQ3, HistoricalThirdCoarse.policy]
        using hf) hc

/-- The corrected construction's finite fifth charge is exact on the same
original carrier; its old and new strict own-cube gates remain separate. -/
def correctedStoredCharge
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega : ℝ) (N cap : ℕ) (z : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop) : ℝ :=
  actualHistoricalFifthSaving
    (originalBase e D.m N) (originalQ3 e chi D.m omega N)
    (originalQ4 e chi D.m omega N rows4 licensed4)
    (P1VariableFifthOriginalBaseQ3Bridge.correctedStoredLevel5
      D J e chi omega (N : ℝ) rows4 licensed4)
    N cap z

theorem corrected_charge_uses_original_T3
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega : ℝ) (N cap : ℕ) (z : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop) :
    correctedStoredCharge D J e chi omega N cap z rows4 licensed4 =
      actualHistoricalFifthSaving
        (HistoricalThirdCoarse.initialPolicy (e : ℝ) D.m (N : ℝ))
        (HistoricalThirdCoarse.rawLevel (e : ℝ) chi D.m omega (N : ℝ))
        (P1OriginalVariableFourthContinuation.producerLevel4
          (e : ℝ) chi D.m omega (N : ℝ) rows4 licensed4)
        (P1VariableFifthOriginalBaseQ3Bridge.correctedStoredLevel5
          D J e chi omega (N : ℝ) rows4 licensed4)
        N cap z := rfl

/-- On a selected cell the *new* finite gated term uses the literal stored
cap; its old term remains the original variable fourth ancestor level. -/
theorem corrected_selected_new_gated_density
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega : ℝ) (N cap : ℕ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (pre : List ℕ) (hlen : pre.length = 5)
    (j : Label5 D.m) (hj : j ∈ D.cells5 ∩ J)
    (ht : primeHistoryLogCoordinates (N : ℝ) 5 pre ∈
      logPrimeMeshCell 0 (19 / 96) D.m j) :
    actualOwnCubeGatedMinusDensity N cap
      (P1VariableFifthOriginalBaseQ3Bridge.correctedStoredLevel5
        D J e chi omega (N : ℝ) rows4 licensed4) pre =
    actualOwnCubeGatedMinusDensity N cap
      (fun _ => (N : ℝ) ^ (D.cap5 j : ℝ)) pre := by
  have hcap := P1VariableFifthOriginalBaseQ3Bridge.corrected_stored_level_on_selected_cell
    D J e chi omega (N : ℝ) rows4 licensed4 pre hlen j hj ht
  have hlevel :
      P1VariableFifthOriginalBaseQ3Bridge.correctedStoredLevel5
        D J e chi omega (N : ℝ) rows4 licensed4 pre =
        (N : ℝ) ^ (D.cap5 j : ℝ) := by
    exact congrArg (fun x : ℝ => (N : ℝ) ^ x) hcap
  simp only [actualOwnCubeGatedMinusDensity, hlevel]

/-- Continuous local dictionary. Both own-cube indicators are evaluated at
their own levels, and the old fourth profile is supplied independently of
the generic stored table's `old5`. -/
def correctedCellKernel (old4 : Point5 → ℝ) (new5 : ℝ) (t : Point5) : ℝ :=
  (primeOwnCubeGatedProfile new5 t - primeOwnCubeGatedProfile (old4 t) t) *
    ∏ i, 1 / t i

theorem correctedCellKernel_two_strict_gates
    (old4 : Point5 → ℝ) (new5 : ℝ) (t : Point5) :
    correctedCellKernel old4 new5 t =
      ((if primeTupleOwnCubeForm t < new5
        then primeTupleMinusProfile new5 t else 0) -
        (if primeTupleOwnCubeForm t < old4 t
        then primeTupleMinusProfile (old4 t) t else 0)) *
      ∏ i, 1 / t i := by rfl

/-- A local sign follows from an actual fourth-to-fifth level comparison,
not from an assumed integral sign. This hypothesis is deliberately local;
the selected stored table has no proved global comparison yet. -/
theorem correctedCellKernel_nonneg
    (old4 : Point5 → ℝ) (new5 : ℝ) (t : Point5)
    (ht : ∀ i, 0 < t i) (hlevel : old4 t ≤ new5) :
    0 ≤ correctedCellKernel old4 new5 t := by
  unfold correctedCellKernel
  apply mul_nonneg
  · exact sub_nonneg.mpr
      (p1PrimeOwnCubeGatedProfile_mono t (ht (Fin.last 4)) hlevel)
  · exact Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (ht i).le)

/-- This geometric carrier includes the original first-label stop and
rough-activated raw third gate. A positive lower cut removes the singular
coordinate boundary without changing those historical gates. -/
def correctedOriginalCell
    (e : ℚ) (chi omega a : ℝ) (m : ℕ) (j : Label5 m) : Set Point5 :=
  logPrimeBox (fun _ => a) (fun _ => (19 / 96 : ℝ)) ∩
    (logPrimeMeshCell 0 (19 / 96) m j ∩
      HistoricalThirdCoarse.P1OriginalCoarseFifth.jointRegion
        (e : ℝ) chi m omega j)

/-- Pointwise continuous version of the original variable fourth producer.
Its seed is the original rough-activated Q3 exponent on this fifth owner;
all eligible fourth rows participate in the finite maximum. -/
def originalVariableFourthProfile
    (e : ℚ) (chi omega : ℝ) (m : ℕ) (j : Label5 m)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (t : Point5) : ℝ :=
  P1OriginalVariableFourthContinuation.profile4
    (HistoricalThirdCoarse.P1OriginalCoarseFifth.currentExponent
      (e : ℝ) chi m omega j t)
    rows4 (P1OriginalVariableFourthContinuation.producerEligible licensed4)
    (fun r => r.bufferedCandidate (e : ℝ))
    (historicalPrefixProject (by omega : 4 ≤ 5) t)

theorem originalVariableFourthProfile_inherits_rawQ3
    (e : ℚ) (chi omega : ℝ) (m : ℕ) (j : Label5 m)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (t : Point5) :
    HistoricalThirdCoarse.P1OriginalCoarseFifth.currentExponent
      (e : ℝ) chi m omega j t ≤
        originalVariableFourthProfile e chi omega m j rows4 licensed4 t := by
  exact P1OriginalVariableFourthContinuation.profile4_seed_le
    _ rows4 (P1OriginalVariableFourthContinuation.producerEligible licensed4)
    (fun r => r.bufferedCandidate (e : ℝ))
    (historicalPrefixProject (by omega : 4 ≤ 5) t)

/-- The exact continuous integral dictated by an actual fourth profile on
one original fifth cell. No generic-D fourth profile is substituted. -/
def correctedOriginalCellIntegral
    (e : ℚ) (chi omega a : ℝ) (m : ℕ) (j : Label5 m)
    (old4 : Point5 → ℝ) (new5 : ℝ) : ℝ :=
  ∫ t in correctedOriginalCell e chi omega a m j,
    correctedCellKernel old4 new5 t

def correctedSelectedStoredIntegral
    (D : HistoricalPrefixCapData) (e : ℚ) (chi omega a : ℝ)
    (j : Label5 D.m)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop) : ℝ :=
  correctedOriginalCellIntegral e chi omega a D.m j
    (originalVariableFourthProfile e chi omega D.m j rows4 licensed4)
    (D.cap5 j : ℝ)

theorem correctedSelectedStoredIntegral_exact
    (D : HistoricalPrefixCapData) (e : ℚ) (chi omega a : ℝ)
    (j : Label5 D.m)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop) :
    correctedSelectedStoredIntegral D e chi omega a j rows4 licensed4 =
      ∫ t in correctedOriginalCell e chi omega a D.m j,
        correctedCellKernel
          (originalVariableFourthProfile e chi omega D.m j rows4 licensed4)
          (D.cap5 j : ℝ) t := rfl

theorem correctedOriginalCellIntegral_two_strict_gates
    (e : ℚ) (chi omega a : ℝ) (m : ℕ) (j : Label5 m)
    (old4 : Point5 → ℝ) (new5 : ℝ) :
    correctedOriginalCellIntegral e chi omega a m j old4 new5 =
      ∫ t in correctedOriginalCell e chi omega a m j,
        ((if primeTupleOwnCubeForm t < new5
          then primeTupleMinusProfile new5 t else 0) -
          (if primeTupleOwnCubeForm t < old4 t
          then primeTupleMinusProfile (old4 t) t else 0)) *
        ∏ i, 1 / t i := by rfl

end
end ImbalancedChen.P1CorrectedFifthDensityDictionary
