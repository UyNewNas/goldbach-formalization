import ImbalancedChen.P2N48AllPatternDirectedMassPorts
import ImbalancedChen.OriginalPairedN48SmallLogSoundness

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original independent J112 block_mass/weights program, specialized to
the four high-band equal-bin patterns.  The distinguished z coordinate
keeps its extra inverse.  Each signed moment retains the source multiply,
power, subtract, zero-started sum and left-associated block product.

The only closed arithmetic proposal below is the positive logarithm
division gate on the 96 original scalar bin ratios. It has NOT been run.
No desired real mass enclosure or row check is a premise.
-/
namespace ImbalancedChen.P2N48OriginalHighBlockWeights
noncomputable section
open Certificates.P2DirectedLogRounding
open OriginalN48Q112LocalProduct OriginalPairedN48OmegaProducerAdapter
open OriginalPairedN48OmegaStepArithmetic OriginalPairedN48SmallLogSoundness
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48TiedParentMassReduction P2N48AllHighBandTiePatterns
open P2N48OriginalStrictLogMassAndOmegaPorts P2N48AllPatternDirectedMassPorts
open P2N48TiedMomentPrimitives P2N48AllHighBandWeightedMass
open P2N48ActualGeometricKeyDecoder

def positiveLogDivisor (q : ℚ) : Prop :=
  0 < (sourceSub (rational 1)
    (sourceMul (rational (logX q)) (rational (logX q)))).lo

instance (q : ℚ) : Decidable (positiveLogDivisor q) := by
  unfold positiveLogDivisor
  infer_instance

def originalBinRatio (t : Fin 2) (i : Fin 48) : ℚ :=
  if t.val=0 then ((lowLo i+343 : ℕ) : ℚ)/(lowLo i : ℚ)
  else ((highLo i+420 : ℕ) : ℚ)/(highLo i : ℚ)

/-- Closed 2*48 scalar integer-arithmetic proposal, never executed. -/
theorem all_bin_log_divisors_proposal :
    ∀ t : Fin 2, ∀ i : Fin 48, positiveLogDivisor (originalBinRatio t i) := by
  decide +kernel

theorem logArgument_integer_ratio (r : SourceRow) (j : Fin 4) :
    logArgument r j=(rightEnd r j : ℚ)/(leftEnd r j : ℚ) := by
  unfold logArgument upperQ lowerQ
  field_simp <;> ring

theorem original_row_log_divisor (r : SourceRow) (j : Fin 4) :
    positiveLogDivisor (logArgument r j) := by
  rw [logArgument_integer_ratio]
  fin_cases j
  · by_cases ht : r.term.val=0
    · simpa [originalBinRatio,leftEnd,rightEnd,width,ht] using
        all_bin_log_divisors_proposal r.term r.ix
    · have hone : r.term.val=1 := by have h := r.term.isLt; omega
      simpa [originalBinRatio,leftEnd,rightEnd,width,ht,hone] using
        all_bin_log_divisors_proposal r.term r.ix
  · simpa [originalBinRatio,leftEnd,rightEnd,width] using
      all_bin_log_divisors_proposal 0 r.iy
  · simpa [originalBinRatio,leftEnd,rightEnd,width] using
      all_bin_log_divisors_proposal 0 r.iz
  · simpa [originalBinRatio,leftEnd,rightEnd,width] using
      all_bin_log_divisors_proposal 0 r.iw

def originalRowLogToken (r : SourceRow) (j : Fin 4) : Token :=
  sourceSmallLog (logArgument r j)

/-- The original ln range-reduction loop takes zero steps, since every
bin ratio is in [1,3/2]. Its final 0*LOG2 correction is exactly inert. -/
theorem original_zero_log_correction (L logTwo : Token) :
    sourceAdd L (sourceMul (rational 0) logTwo)=L := by
  cases L
  cases logTwo
  simp [sourceAdd,sourceMul,lowerProduct,upperProduct,rational,encode,Enclosure.point]

theorem originalRowLogToken_contains (r : SourceRow) (j : Fin 4) :
    (decode (originalRowLogToken r j)).Contains (rowLog r j) := by
  have h := sourceSmallLog_contains (row_log_argument_range r j).1
    (original_row_log_divisor r j)
  simpa only [originalRowLogToken,rowLog,logArgument,Rat.cast_div,
    upperQ_cast,lowerQ_cast] using h

/-- Untied non-z blocks keep the original L^1/J(1!) operations. -/
def originalSingleton (r : SourceRow) (j : Fin 4) : Token :=
  sourceDiv (sourcePow (originalRowLogToken r j) 1) (rational 1)

theorem originalSingleton_contains (r : SourceRow) (j : Fin 4) :
    (decode (originalSingleton r j)).Contains (rowLog r j) := by
  have h := sourceDiv_contains _ (rational 1)
    (rational_lower_pos (by norm_num : (1 : ℚ)≤1))
    (sourcePow_contains _ (originalRowLogToken_contains r j) 1) (rational_contains 1)
  simpa only [originalSingleton,pow_one,Rat.cast_one,div_one] using h

def originalEx (r : SourceRow) (j : Fin 4) : Token :=
  rational (lowerQ r j/upperQ r j)

/-- mom[j+1]=(j+1)*mom[j]-ex*L^(j+1), exactly as the source loop. -/
def originalMoment (r : SourceRow) (j : Fin 4) : ℕ→Token
  | 0 => sourceSub (rational 1) (originalEx r j)
  | n+1 => sourceSub (sourceMul (rational (n+1)) (originalMoment r j n))
      (sourceMul (originalEx r j) (sourcePow (originalRowLogToken r j) (n+1)))

/-- The (-1)^k * choose(r,k) factor is rounded before both products.
For the high band r is 0 or 1, so all factorial denominators are 1. -/
def originalTerm (r : SourceRow) (j : Fin 4) (p s k : ℕ) : Token :=
  sourceMul
    (sourceMul (rational (((-1 : ℚ)^k)*(Nat.choose p k : ℚ)))
      (sourcePow (originalRowLogToken r j) (p-k)))
    (originalMoment r j (s+k))

def originalMomentValue (r : SourceRow) (j : Fin 4) (p s : ℕ) : Token :=
  ((List.range (p+1)).map (originalTerm r j p s)).foldl sourceAdd (rational 0)

def originalZBlock (r : SourceRow) (j : Fin 4) (p s : ℕ) : Token :=
  sourceMul (rational (1/(lowerQ r j*(Nat.factorial p : ℚ)*(Nat.factorial s : ℚ))))
    (originalMomentValue r j p s)

/-- Exact finite source-loop expansions; no endpoint arithmetic runs. -/
theorem originalMomentValue_zero (r : SourceRow) (j : Fin 4) (s : ℕ) :
    originalMomentValue r j 0 s=
      sourceAdd (rational 0) (originalTerm r j 0 s 0) := by rfl

theorem originalMomentValue_one (r : SourceRow) (j : Fin 4) (s : ℕ) :
    originalMomentValue r j 1 s=
      sourceAdd (sourceAdd (rational 0) (originalTerm r j 1 s 0))
        (originalTerm r j 1 s 1) := by rfl

private theorem moment0_contains (r : SourceRow) (j : Fin 4) :
    (decode (originalMoment r j 0)).Contains (J0 (rowLower r j) (rowUpper r j)) := by
  have h := sourceSub_contains (rational 1) (originalEx r j)
    (rational_contains 1) (rational_contains (lowerQ r j/upperQ r j))
  simpa only [originalMoment,originalEx,J0,Rat.cast_one,Rat.cast_div,
    lowerQ_cast,upperQ_cast] using h

private theorem moment1_contains (r : SourceRow) (j : Fin 4) :
    (decode (originalMoment r j 1)).Contains (J1 (rowLower r j) (rowUpper r j)) := by
  have h := sourceSub_contains _ _
    (sourceMul_contains _ _ (rational_contains 1) (moment0_contains r j))
    (sourceMul_contains _ _ (rational_contains (lowerQ r j/upperQ r j))
      (sourcePow_contains _ (originalRowLogToken_contains r j) 1))
  convert h using 1 <;>
    simp only [originalMoment,originalEx,J0,J1,rowLog,Rat.cast_one,
      Rat.cast_div,lowerQ_cast,upperQ_cast,pow_one] <;> ring

private theorem moment2_contains (r : SourceRow) (j : Fin 4) :
    (decode (originalMoment r j 2)).Contains (J2 (rowLower r j) (rowUpper r j)) := by
  have h := sourceSub_contains _ _
    (sourceMul_contains _ _ (rational_contains 2) (moment1_contains r j))
    (sourceMul_contains _ _ (rational_contains (lowerQ r j/upperQ r j))
      (sourcePow_contains _ (originalRowLogToken_contains r j) 2))
  convert h using 1 <;>
    simp only [originalMoment,originalEx,J1,J2,rowLog,Rat.cast_ofNat,
      Rat.cast_div,lowerQ_cast,upperQ_cast] <;> ring

private theorem term_contains (r : SourceRow) (j : Fin 4) (p s k : ℕ)
    {M : ℝ} (hM : (decode (originalMoment r j (s+k))).Contains M) :
    (decode (originalTerm r j p s k)).Contains
      (((-1 : ℝ)^k)*(Nat.choose p k : ℝ)*(rowLog r j)^(p-k)*M) := by
  have h := sourceMul_contains _ _
    (sourceMul_contains _ _
      (rational_contains (((-1 : ℚ)^k)*(Nat.choose p k : ℚ)))
      (sourcePow_contains _ (originalRowLogToken_contains r j) (p-k))) hM
  simpa only [originalTerm,Rat.cast_mul,Rat.cast_pow,Rat.cast_neg,
    Rat.cast_one,Rat.cast_natCast] using h

private theorem momentValue00_contains (r : SourceRow) (j : Fin 4) :
    (decode (originalMomentValue r j 0 0)).Contains (J0 (rowLower r j) (rowUpper r j)) := by
  rw [originalMomentValue_zero]
  have h := sourceAdd_contains _ _ (rational_contains 0)
    (term_contains r j 0 0 0 (moment0_contains r j))
  simpa only [Rat.cast_zero,pow_zero,Nat.choose_zero_right,Nat.cast_one,
    one_mul,zero_add,Nat.sub_self] using h

private theorem momentValue01_contains (r : SourceRow) (j : Fin 4) :
    (decode (originalMomentValue r j 0 1)).Contains (J1 (rowLower r j) (rowUpper r j)) := by
  rw [originalMomentValue_zero]
  have h := sourceAdd_contains _ _ (rational_contains 0)
    (term_contains r j 0 1 0 (moment1_contains r j))
  simpa only [Rat.cast_zero,pow_zero,Nat.choose_zero_right,Nat.cast_one,
    one_mul,zero_add,Nat.sub_self] using h

private theorem momentValue10_contains (r : SourceRow) (j : Fin 4) :
    (decode (originalMomentValue r j 1 0)).Contains
      (rowLog r j*J0 (rowLower r j) (rowUpper r j)-J1 (rowLower r j) (rowUpper r j)) := by
  rw [originalMomentValue_one]
  have h := sourceAdd_contains _ _
    (sourceAdd_contains _ _ (rational_contains 0)
      (term_contains r j 1 0 0 (moment0_contains r j)))
    (term_contains r j 1 0 1 (moment1_contains r j))
  convert h using 1 <;>
    norm_num only [Rat.cast_zero,pow_zero,pow_one,Nat.choose_zero_right,
      Nat.choose_self,Nat.cast_one,one_mul,zero_add,Nat.sub_self,Nat.sub_zero] <;> ring

private theorem momentValue11_contains (r : SourceRow) (j : Fin 4) :
    (decode (originalMomentValue r j 1 1)).Contains
      (rowLog r j*J1 (rowLower r j) (rowUpper r j)-J2 (rowLower r j) (rowUpper r j)) := by
  rw [originalMomentValue_one]
  have h := sourceAdd_contains _ _
    (sourceAdd_contains _ _ (rational_contains 0)
      (term_contains r j 1 1 0 (moment1_contains r j)))
    (term_contains r j 1 1 1 (moment2_contains r j))
  convert h using 1 <;>
    norm_num only [Rat.cast_zero,pow_zero,pow_one,Nat.choose_zero_right,
      Nat.choose_self,Nat.cast_one,one_mul,zero_add,Nat.sub_self,Nat.sub_zero] <;> ring

theorem originalZBlock00_contains (r : SourceRow) (j : Fin 4) :
    (decode (originalZBlock r j 0 0)).Contains (1/rowLower r j-1/rowUpper r j) := by
  have h := sourceMul_contains _ _ (rational_contains (1/lowerQ r j))
    (momentValue00_contains r j)
  convert h using 1
  · simp only [originalZBlock,Nat.factorial_zero,Nat.cast_one,mul_one]
  · simp only [J0,Rat.cast_div,Rat.cast_one,lowerQ_cast]
    field_simp [(rowLower_pos r j).ne',(rowUpper_pos r j).ne'] <;> ring

theorem originalZBlock01_contains (r : SourceRow) (j : Fin 4) :
    (decode (originalZBlock r j 0 1)).Contains (moment01 (rowLower r j) (rowUpper r j)) := by
  have h := sourceMul_contains _ _ (rational_contains (1/lowerQ r j))
    (momentValue01_contains r j)
  simpa only [originalZBlock,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,mul_one,
    Rat.cast_div,Rat.cast_one,lowerQ_cast,
    original_rs01_formula (rowLower_pos r j).ne' (rowUpper_pos r j).ne'] using h

theorem originalZBlock10_contains (r : SourceRow) (j : Fin 4) :
    (decode (originalZBlock r j 1 0)).Contains (moment10 (rowLower r j) (rowUpper r j)) := by
  have h := sourceMul_contains _ _ (rational_contains (1/lowerQ r j))
    (momentValue10_contains r j)
  simpa only [originalZBlock,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,mul_one,
    Rat.cast_div,Rat.cast_one,lowerQ_cast,rowLog,
    original_rs10_formula (rowLower_pos r j).ne' (rowUpper_pos r j).ne'] using h

theorem originalZBlock11_contains (r : SourceRow) (j : Fin 4) :
    (decode (originalZBlock r j 1 1)).Contains (moment11 (rowLower r j) (rowUpper r j)) := by
  have h := sourceMul_contains _ _ (rational_contains (1/lowerQ r j))
    (momentValue11_contains r j)
  simpa only [originalZBlock,Nat.factorial_one,Nat.cast_one,mul_one,
    Rat.cast_div,Rat.cast_one,lowerQ_cast,rowLog,
    original_rs11_formula (rowLower_pos r j).ne' (rowUpper_pos r j).ne'] using h

private theorem lowLo_injective : Function.Injective lowLo := by
  intro i j h
  apply Fin.ext
  dsimp [lowLo] at h
  omega

/-- The source equality test on neighboring endpoint pairs yields these
exact blocks. In particular a high first coordinate cannot join a low
block. This is symbolic geometry, not an executed row classifier. -/
theorem original_high_block_equalities (r : SourceRow) (ht : r.term.val=1) :
    ¬adjacentTie r 0 ∧ (adjacentTie r 1 ↔ r.iy=r.iz) ∧
      (adjacentTie r 2 ↔ r.iz=r.iw) := by
  refine ⟨?_,?_,?_⟩
  · intro h
    have hleft := h.1
    have hy := r.iy.isLt
    simp [leftEnd,highLo,lowLo,ht] at hleft
    omega
  · constructor
    · intro h
      apply lowLo_injective
      simpa [adjacentTie,leftEnd] using h.1
    · intro h
      simp [adjacentTie,leftEnd,rightEnd,width,h]
  · constructor
    · intro h
      apply lowLo_injective
      simpa [adjacentTie,leftEnd] using h.1
    · intro h
      simp [adjacentTie,leftEnd,rightEnd,width,h]

/-- This is the original source z=J(1); z=z*zpart left fold.
The high coordinate is always a separate block; the low ordered indices
give precisely the following four original contiguous equal-bin blocks. -/
def originalRowZToken (r : SourceRow) : Token :=
  if r.iy=r.iz then
    if r.iz=r.iw then
      sourceMul (sourceMul (rational 1) (originalSingleton r 0)) (originalZBlock r 1 1 1)
    else sourceMul
      (sourceMul (sourceMul (rational 1) (originalSingleton r 0)) (originalZBlock r 1 1 0))
      (originalSingleton r 3)
  else if r.iz=r.iw then
    sourceMul
      (sourceMul (sourceMul (rational 1) (originalSingleton r 0)) (originalSingleton r 1))
      (originalZBlock r 2 0 1)
  else sourceMul
    (sourceMul
      (sourceMul (sourceMul (rational 1) (originalSingleton r 0)) (originalSingleton r 1))
      (originalZBlock r 2 0 0)) (originalSingleton r 3)

theorem originalRowZToken_contains_formula (r : SourceRow) :
    (decode (originalRowZToken r)).Contains (rowZFormula r) := by
  have h0 := sourceMul_contains _ _ (rational_contains 1) (originalSingleton_contains r 0)
  have h1 := originalSingleton_contains r 1
  have h3 := originalSingleton_contains r 3
  by_cases h12 : r.iy=r.iz
  · by_cases h23 : r.iz=r.iw
    · simpa only [originalRowZToken,rowZFormula,if_pos h12,if_pos h23,Rat.cast_one,one_mul] using
        sourceMul_contains _ _ h0 (originalZBlock11_contains r 1)
    · simpa only [originalRowZToken,rowZFormula,if_pos h12,if_neg h23,Rat.cast_one,one_mul] using
        sourceMul_contains _ _ (sourceMul_contains _ _ h0 (originalZBlock10_contains r 1)) h3
  · by_cases h23 : r.iz=r.iw
    · simpa only [originalRowZToken,rowZFormula,if_neg h12,if_pos h23,Rat.cast_one,one_mul] using
        sourceMul_contains _ _ (sourceMul_contains _ _ h0 h1) (originalZBlock01_contains r 2)
    · simpa only [originalRowZToken,rowZFormula,if_neg h12,if_neg h23,Rat.cast_one,one_mul,strictZ,rowLog] using
        sourceMul_contains _ _
          (sourceMul_contains _ _ (sourceMul_contains _ _ h0 h1) (originalZBlock00_contains r 2)) h3

/-- Actual full physical parent; all tie Fubini/FTC identities are supplied
by the independent frozen E source, not by a desired enclosure premise. -/
theorem original_high_row_token_contains_trueMass (r : SourceRow)
    (ht : r.term.val=1) (hchron : r.iw≤r.iz ∧ r.iz≤r.iy) :
    (decode (originalRowZToken r)).Contains (parentUnweightedMass (fullParent r)) := by
  rw [highBand_true_mass_formula r ht hchron]
  exact originalRowZToken_contains_formula r

theorem original_retained_row_token_contains_trueMass (r : SourceRow)
    (hr : r∈actualRetainedRows) :
    (decode (originalRowZToken r)).Contains (parentUnweightedMass (fullParent r)) := by
  rw [actual_retained_true_mass_formula r hr]
  exact originalRowZToken_contains_formula r

end
end ImbalancedChen.P2N48OriginalHighBlockWeights
