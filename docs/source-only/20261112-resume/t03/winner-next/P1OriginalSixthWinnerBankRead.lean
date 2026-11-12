import ImbalancedChen.P4AOriginalLicensedSixthBoxedWitness
import ImbalancedChen.P4AFull87DataSeedHistory

/-! Read the original, fixed sixth winner trace on either fifth bank.
The later tests read their own chronological raw predecessor. The winning
tests compare already rounded eligible values with the inherited fifth. -/
namespace ImbalancedChen.P1OriginalSixthWinnerBankRead
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram P1FiniteAffineQuantizerTable P1AffineTaggedDecision
open P4AOriginalFourthFifthAffinePrograms P4AOriginalCompleteSixthAffinePrograms
open P4AFull87VariableSeedHistory P5OriginalCommonRefinedConstructor
open P4AOriginalSixthActionBank (Action Entry endpoint selected)
open P4AOriginalSixthTaggedWinner (actionTests finiteFifth)
open P4AOriginalLicensedSixthAffineProgram
open P4AOriginalLicensedSixthBoxedWitness (decision decision_some_sound decision_none_iff)
open P4AOriginalFull87DataPolicy
open P1GuardFrozenFiniteCapAlgebra (rounded)
open P4AOriginalFull87HistoryCore (width)
open P1QuantizedActionLicense (LowerLicense)

private theorem lift_constant (k : ℕ) (hk : 3 ≤ k) (b : ℚ) :
    liftSeed k hk (atom (K (b:ℝ))) = atom (K (b:ℝ)) := by
  simp [liftSeed,Program.pull,Affine.pull,Affine.const]

private theorem constant_after (d : OriginalData) (b : ℚ) (k : ℕ) :
    variableAfterProgram d (atom (K (b:ℝ))) k = afterProgram d b k := by
  induction k with
  | zero =>
    simp only [variableAfterProgram,afterProgram,variableElevenProgram,elevenProgram,
      variableElevenTests,elevenTests,variableSavedProgram,savedProgram,variableSavedTests,
      savedTests,variableFifthAtSix,fifthAtSix,variableFifthProgram,fifthProgram,
      variableFourthProgram,fourthProgram,lift_constant]
  | succ k ih => rw [variableAfterProgram,afterProgram,ih]

theorem action_at_history (d : OriginalData) (b : ℚ) (N : ℝ) (h : List ℕ)
    (hl : h.length = 6) (hb : lambda3 d N h = (b:ℝ)) (a : Action) :
    Passed (primeHistoryLogCoordinates N 6 h) (actionTests d b a) ↔
      ActualEligible d N h a := by
  have hf := fifthAtSix_at_history d b N h hl hb
  cases a with
  | saved i =>
    simpa only [actionTests,ActualEligible,savedEligible,hl,true_and,hb,hf] using
      savedTests_exact d b i (primeHistoryLogCoordinates N 6 h)
  | eleven c =>
    simpa only [actionTests,ActualEligible,eligibleSixth,hl,true_and,hf] using
      elevenTests_exact d b c (primeHistoryLogCoordinates N 6 h)
  | later c =>
    let k := P4AOriginalSixthLaterLiteral.stage c
    have hbase : lambda3 d N h = baseValue (atom (K (b:ℝ))) N h := by
      simpa only [baseValue,Program.eval,Affine.eval_const] using hb
    have hprev := P4AFull87DataSeedHistory.data_variableAfterProgram_at_history
      d N (atom (K (b:ℝ))) h hl hbase k
    rw [constant_after] at hprev
    simpa only [actionTests,ActualEligible,P4AOriginalCompleteSixthChronology.laterEligible,
      hl,true_and,hprev,k] using
      laterTests_exact k (afterProgram d b k) c (primeHistoryLogCoordinates N 6 h)

theorem accepted_at_history (n : ℕ) (d : OriginalData) (b : ℚ) (N : ℝ)
    (h : List ℕ) (hl : h.length = 6) (hb : lambda3 d N h = (b:ℝ)) (a : Action) :
    PointAccepted n d b (primeHistoryLogCoordinates N 6 h) a ↔ Accepted n d N h a := by
  unfold PointAccepted Accepted
  rw [action_at_history d b N h hl hb a]

theorem fifth_at_history (n : ℕ) (d : OriginalData) (b : ℚ) (N : ℝ)
    (h : List ℕ) (hl : h.length = 6) (hb : lambda3 d N h = (b:ℝ))
    (hs : originalSeed d N h = (b:ℝ)) :
    (finiteFifth n d b).eval (primeHistoryLogCoordinates N 6 h) =
      cap5 n d N (rosserAncestor 5 h) := by
  rw [finiteFifth,protectedProgram_exact,fifthAtSix_at_history d b N h hl hb,
    cap5_eq_protect,P4AOriginalFull87FiniteParentCaps.originalSeed_ancestor _ _ 5 (by decide),hs]
  rfl

theorem value_at_history (n : ℕ) (d : OriginalData) (b : ℚ) (N : ℝ)
    (h : List ℕ) (hl : h.length = 6) (hb : lambda3 d N h = (b:ℝ))
    (hs : originalSeed d N h = (b:ℝ)) :
    (program n d b).eval (primeHistoryLogCoordinates N 6 h) = licensedCap n d N h := by
  rw [program_eval,fifth_at_history n d b N h hl hb hs,licensedCap]
  congr 1
  funext a
  exact propext (accepted_at_history n d b N h hl hb a)

/-- Exact on every arithmetic point, including ties and rejected boxes. -/
theorem read_at_history (n m : ℕ) (d : OriginalData) (b : ℚ) (N : ℝ)
    (h : List ℕ) (hl : h.length = 6) (hb : lambda3 d N h = (b:ℝ))
    (hs : originalSeed d N h = (b:ℝ)) :
    let t := primeHistoryLogCoordinates N 6 h
    let tag := (decision n d b).lookup m t
    valueLookup n d b m t = licensedCap n d N h ∧
    (tag = none ↔ licensedCap n d N h = cap5 n d N (rosserAncestor 5 h)) ∧
    (∀ a : Entry, tag = some a →
      cap5 n d N (rosserAncestor 5 h) < licensedCap n d N h ∧
      Accepted n d N h a.val ∧
      licensedCap n d N h = (rounded n (endpoint a.val t):ℝ) ∧
      LowerLicense (selected a.val) t (licensedCap n d N h) ∧
      licensedCap n d N h + width n ≤ VariableEnvelope.v (∑ j ∈ selected a.val,t j)) := by
  dsimp only
  have hcap := value_at_history n d b N h hl hb hs
  have hprev := fifth_at_history n d b N h hl hb hs
  refine ⟨(valueLookup_exact _ _ _ _ _).trans hcap,?_,?_⟩
  · rw [Trace.lookup_exact,decision_none_iff,hcap,hprev]
  · intro a htag
    rw [Trace.lookup_exact] at htag
    obtain ⟨hlt,ha,hv⟩ := decision_some_sound n d b _ a htag
    have hactual := (accepted_at_history n d b N h hl hb a.val).mp ha
    rw [hprev,hcap] at hlt
    rw [hcap] at hv
    exact ⟨hlt,hactual,hv,hv.symm ▸ hactual.2.1,hv.symm ▸ hactual.2.2⟩

end
end ImbalancedChen.P1OriginalSixthWinnerBankRead
