import ImbalancedChen.P4AOriginalCompleteSixthAffinePrograms
import ImbalancedChen.P4AFull87HistoricalChangedSupport

/-! Evaluate the actual complete sixth on every length-six history, including
both corrected fallback seeds. A finite code chooses its true native third
read. The variable third input remains an affine decision program through
all later maxima and guards. No rational-value assumption on lambda3. -/
namespace ImbalancedChen.P4AFull87VariableSeedHistory
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram
open P4AOriginalFourthFifthAffinePrograms
open P4AOriginalCompleteSixthAffinePrograms
open P1OriginalVariableFourthContinuation
open P2OriginalFourthCapProducerInterface
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalCompleteSixthChronology
open P4AOriginalFull87FiniteParentCaps (thirdAlphabet originalSeed_mem)
open P5OriginalAboveMuThirdLowerPhysicalCoefficient

abbrev SeedCode (d : OriginalData) :=
  (thirdAlphabet d.e d.chi d.m : Type) × Bool × Bool

private def originalIndex (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    (thirdAlphabet d.e d.chi d.m : Type) :=
  let h := Finset.mem_image.mp (originalSeed_mem d N pre)
  ⟨Classical.choose h,(Classical.choose_spec h).1⟩

private theorem originalIndex_eq (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    ((originalIndex d N pre).val : ℝ) = originalSeed d N pre :=
  (Classical.choose_spec (Finset.mem_image.mp (originalSeed_mem d N pre))).2

def seedCode (d : OriginalData) (N : ℝ) (pre : List ℕ) : SeedCode d :=
  (originalIndex d N pre,decide (thirdGuard N pre),decide (secondGuard N pre))

def third (d : OriginalData) (code : SeedCode d) : Program 3 :=
  let base := atom (K (code.1.val : ℝ))
  let arg := if code.2.1 then (X 1).add (X 2) else X 1
  let tent := Program.inf (atom (ascending arg)) (atom (descending arg))
  .sup base (if code.2.1 || code.2.2 then tent else base)

def baseValue (b : Program 3) (N : ℝ) (pre : List ℕ) :=
  b.eval (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre))

theorem seed_exact (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (hl : pre.length = 6) :
    lambda3 d N pre = baseValue (third d (seedCode d N pre)) N pre := by
  let a := rosserAncestor 3 pre
  have hlen : a.length = 3 := by simp [a,hl]
  have hy : primeHistoryLogCoordinates N 3 a 1 =
      primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 1 := by
    have h := primeHistoryLogCoordinates_ancestor N hlen (by decide : 2 ≤ 3) (1 : Fin 2)
    simpa only [a, rosserAncestor_nested 2 3 (by decide)] using h.symm
  have hy' : primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 1 =
      primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 1 := hy.symm
  by_cases ht : thirdGuard N pre <;> by_cases hs : secondGuard N pre <;>
    simp [lambda3,fallbackSeed,baseValue,third,seedCode,ht,hs,Program.eval,
      eval_ascending, eval_descending,VariableEnvelope.v_eq_min,originalIndex_eq,hy']

private theorem base_anc (b : Program 3) (N : ℝ) (pre : List ℕ) (r : ℕ) (hr : 3 ≤ r) :
    baseValue b N (rosserAncestor r pre) = baseValue b N pre := by
  simp only [baseValue,rosserAncestor_nested 3 r hr]

def liftSeed (k : ℕ) (hk : 3 ≤ k) (b : Program 3) : Program k :=
  b.pull (fun i => i.castLE hk)

theorem liftSeed_exact (k : ℕ) (hk : 3 ≤ k) (b : Program 3) (N : ℝ)
    (pre : List ℕ) (hl : pre.length = k) :
    (liftSeed k hk b).eval (primeHistoryLogCoordinates N k pre) = baseValue b N pre := by
  rw [liftSeed,Program.eval_pull,baseValue]
  congr 1
  funext i
  exact (primeHistoryLogCoordinates_ancestor N hl hk i).symm

def variableFourthProgram (d : OriginalData) (b : Program 3) : Program 4 :=
  maxRows (fourthTests d) (fourthCandidate d) (liftSeed 4 (by decide) b) d.rows4.toList

theorem variableFourthProgram_exact (d : OriginalData) (b : Program 3) (t : Fin 4 → ℝ) :
    (variableFourthProgram d b).eval t =
      finiteMax d.rows4 (fun r => producerEligible d.licensed4 r t)
        (fun r => r.bufferedCandidate (d.e : ℝ) t) ((liftSeed 4 (by decide) b).eval t) := by
  simp only [variableFourthProgram, eval_maxRows, Finset.toList_toFinset]
  congr 1
  · funext r
    exact propext (fourthTests_exact d r t)
  · funext r
    exact fourthCandidate_exact d r t

def variableFifthProgram (d : OriginalData) (b : Program 3) : Program 5 :=
  maxRows (fifthTests d) (fifthCandidate d)
    ((variableFourthProgram d b).pull Fin.castSucc) d.rows5.toList

theorem variableFifthProgram_exact (d : OriginalData) (b : Program 3) (t : Fin 5 → ℝ) :
    (variableFifthProgram d b).eval t =
      finiteMax d.rows5
        (fun r => P1OriginalVariableFifthContinuation.eligible d.e d.chi d.m d.omega d.J5 r t)
        (fun r => P1OriginalVariableFifthContinuation.candidate (d.e : ℝ) r.selected t)
        ((variableFourthProgram d b).eval (fun i => t i.castSucc)) := by
  simp only [variableFifthProgram, eval_maxRows, Finset.toList_toFinset]
  congr 1
  · funext r
    exact propext (fifthTests_exact d r t)
  · funext r
    exact fifthCandidate_exact d r t
  · exact Program.eval_pull _ _ _

theorem variableFourth_at_history (d : OriginalData) (b : Program 3) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 4) (hb : lambda3 d N pre = baseValue b N pre) :
    (variableFourthProgram d b).eval (primeHistoryLogCoordinates N 4 pre) = exponent4 d N pre := by
  rw [variableFourthProgram_exact, exponent4, if_pos hlen, liftSeed_exact _ _ b N pre hlen,hb]

theorem variableFifth_at_history (d : OriginalData) (b : Program 3) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 5) (hb : lambda3 d N pre = baseValue b N pre) :
    (variableFifthProgram d b).eval (primeHistoryLogCoordinates N 5 pre) = exponent5 d N pre := by
  have h4len : (rosserAncestor 4 pre).length = 4 := by simp [hlen]
  have h4b : lambda3 d N (rosserAncestor 4 pre) = baseValue b N (rosserAncestor 4 pre) := by
    rw [P5OriginalCommonRefinedPreservation.lambda3_ancestor d N 4 (by decide), base_anc _ _ _ 4 (by decide), hb]
  have hc : (fun i : Fin 4 => primeHistoryLogCoordinates N 5 pre i.castSucc) =
      primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre) := by
    funext i
    exact (primeHistoryLogCoordinates_ancestor N hlen (by decide : 4 ≤ 5) i).symm
  rw [variableFifthProgram_exact, hc, variableFourth_at_history d b N _ h4len h4b,
    exponent5, if_pos hlen]

def variableFifthAtSix (d : OriginalData) (b : Program 3) : Program 6 :=
  (variableFifthProgram d b).pull Fin.castSucc

def variableSavedTests (d : OriginalData) (b : Program 3) (i : P4AOriginalSavedSixthArchive.Row) : List (Gate 6) :=
  savedSourceTests i ++
  [LT (atom h3A) (liftSeed 6 (by decide) b), LT (atom h5A) (liftSeed 6 (by decide) b),
   LE (variableFifthAtSix d b) (savedOldUpper i)]

def variableSavedProgram (d : OriginalData) (b : Program 3) : Program 6 :=
  maxRows (variableSavedTests d b) savedEndpoint (variableFifthAtSix d b)
    (Finset.univ : Finset P4AOriginalSavedSixthArchive.Row).toList

theorem variableSavedTests_exact (d : OriginalData) (b : Program 3) (i : P4AOriginalSavedSixthArchive.Row) (t : SixPoint) :
    Passed t (variableSavedTests d b i) ↔ P4AOriginalSavedSixthArchive.Source i t ∧
      Certificates.P2OriginalSixthElevenLogSemantics.H3 t < ((liftSeed 6 (by decide) b).eval t) ∧ Certificates.P2OriginalSixthElevenLogSemantics.H5 t < ((liftSeed 6 (by decide) b).eval t) ∧
      (variableFifthAtSix d b).eval t ≤ P4AOriginalSavedSixthArchive.oldUpper i t := by
  simp only [variableSavedTests, passed_append, savedSourceTests_exact, passed_cons, passed_nil,
    holds_LT, holds_LE, Program.eval, eval_h3A, eval_h5A, Affine.eval_const,
    savedOldUpper_exact, and_true]

def variableElevenTests (d : OriginalData) (b : Program 3) (c : ElevenCell) : List (Gate 6) :=
  elevenSourceTests c ++
  [LT (atom h5A) (variableFifthAtSix d b), LE (variableFifthAtSix d b) (atom (elevenOldA c))]

def variableElevenProgram (d : OriginalData) (b : Program 3) : Program 6 :=
  maxRows (variableElevenTests d b) (fun c => atom (elevenNewA c)) (variableSavedProgram d b) Certificates.P2OriginalSixthElevenLogSemantics.allCells

theorem variableElevenTests_exact (d : OriginalData) (b : Program 3) (c : ElevenCell) (t : SixPoint) :
    Passed t (variableElevenTests d b c) ↔ Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t ∧
      Certificates.P2OriginalSixthElevenLogSemantics.H5 t < (variableFifthAtSix d b).eval t ∧ (variableFifthAtSix d b).eval t ≤ Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t := by
  simp only [variableElevenTests, passed_append, elevenSourceTests_exact, passed_cons, passed_nil,
    holds_LT, holds_LE, Program.eval, eval_h5A, elevenOldA_exact, and_true]

def variableAfterProgram (d : OriginalData) (b : Program 3) : ℕ → Program 6
  | 0 => variableElevenProgram d b
  | j + 1 => laterStep j (variableAfterProgram d b j)

def variableCompleteProgram (d : OriginalData) (b : Program 3) : Program 6 := variableAfterProgram d b 8

theorem variableFifthAtSix_at_history (d : OriginalData) (b : Program 3) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 6) (hb : lambda3 d N pre = baseValue b N pre) :
    (variableFifthAtSix d b).eval (primeHistoryLogCoordinates N 6 pre) = actualParent5 d N pre := by
  have h5len : (rosserAncestor 5 pre).length = 5 := by simp [hlen]
  have h5b : lambda3 d N (rosserAncestor 5 pre) = baseValue b N (rosserAncestor 5 pre) := by
    rw [lambda3_ancestor d N 5 (by decide), base_anc _ _ _ 5 (by decide), hb]
  have hc : (fun i : Fin 5 => primeHistoryLogCoordinates N 6 pre i.castSucc) =
      primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre) := by
    funext i
    exact (primeHistoryLogCoordinates_ancestor N hlen (by decide : 5 ≤ 6) i).symm
  rw [variableFifthAtSix, Program.eval_pull, hc, variableFifth_at_history d b N _ h5len h5b]
  rfl

theorem variableSavedProgram_at_history (e : ℚ) (q : ℕ) (om N : ℝ) (b : Program 3)
    (pre : List ℕ) (hlen : pre.length = 6) (hb : lambda3 (data e q om) N pre = baseValue b N pre) :
    (variableSavedProgram (data e q om) b).eval (primeHistoryLogCoordinates N 6 pre) =
      savedExponent e q om N pre := by
  have hf := variableFifthAtSix_at_history (data e q om) b N pre hlen hb
  simp only [variableSavedProgram, eval_maxRows, Finset.toList_toFinset,
    savedExponent, savedEligible, hlen, true_and, hb]
  congr 1
  · funext i
    apply propext
    simpa only [hf, fifth,liftSeed_exact _ _ b N pre hlen] using variableSavedTests_exact (data e q om) b i
      (primeHistoryLogCoordinates N 6 pre)
  · funext i
    exact savedEndpoint_exact i _
  · exact hf

theorem variableElevenProgram_at_history (e : ℚ) (q : ℕ) (om N : ℝ) (b : Program 3)
    (pre : List ℕ) (hlen : pre.length = 6) (hb : lambda3 (data e q om) N pre = baseValue b N pre) :
    (variableElevenProgram (data e q om) b).eval (primeHistoryLogCoordinates N 6 pre) =
      elevenExponent e q om N pre := by
  have hf := variableFifthAtSix_at_history (data e q om) b N pre hlen hb
  simp only [variableElevenProgram, eval_maxRows, elevenExponent, eligibleSixth,
    hlen, true_and]
  congr 1
  · funext c
    apply propext
    simpa only [hf] using variableElevenTests_exact (data e q om) b c
      (primeHistoryLogCoordinates N 6 pre)
  · funext c
    exact elevenNewA_exact c _
  · exact variableSavedProgram_at_history e q om N b pre hlen hb

theorem variableAfterProgram_at_history (e : ℚ) (q : ℕ) (om N : ℝ) (b : Program 3)
    (pre : List ℕ) (hlen : pre.length = 6) (hb : lambda3 (data e q om) N pre = baseValue b N pre)
    (j : ℕ) :
    (variableAfterProgram (data e q om) b j).eval (primeHistoryLogCoordinates N 6 pre) =
      afterLater e q om N pre j := by
  induction j with
  | zero => exact variableElevenProgram_at_history e q om N b pre hlen hb
  | succ j ih =>
      simp only [variableAfterProgram, laterStep, eval_maxRows, Finset.toList_toFinset,
        afterLater, applyLater, laterEligible, hlen, true_and]
      congr 1
      · funext c
        apply propext
        simpa only [ih] using laterTests_exact j (variableAfterProgram (data e q om) b j) c
          (primeHistoryLogCoordinates N 6 pre)
      · funext c
        exact laterEndpointA_exact c _
      · exact ih

theorem variableCompleteProgram_at_history (e : ℚ) (q : ℕ) (om N : ℝ) (b : Program 3)
    (pre : List ℕ) (hlen : pre.length = 6) (hb : lambda3 (data e q om) N pre = baseValue b N pre) :
    (variableCompleteProgram (data e q om) b).eval (primeHistoryLogCoordinates N 6 pre) =
      currentSixthExponent e q om N pre :=
  variableAfterProgram_at_history e q om N b pre hlen hb 8

theorem complete_at_own_six (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ)
    (hl : pre.length = 6) :
    let d := data e q om
    let b := third d (seedCode d N pre)
    (variableCompleteProgram d b).eval (primeHistoryLogCoordinates N 6 pre) =
      currentSixthExponent e q om N pre :=
  variableCompleteProgram_at_history e q om N _ pre hl (seed_exact _ N pre hl)

end
end ImbalancedChen.P4AFull87VariableSeedHistory
