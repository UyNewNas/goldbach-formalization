import ImbalancedChen.P4AOriginalFiniteFallbackSectorTransport
import ImbalancedChen.P4AOriginalElevenUpperDispatch
import ImbalancedChen.P4AOriginalFiniteFallbackTerminal

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The final ACTUAL finite fallback policy has a common upper dispatcher.
Its two upper fallback slots are literal gains4 and5. The remaining
three early lower slots are literal gains0,1,2. This exact telescope
keeps those groups disjoint and retains every genuine later source.
-/
namespace ImbalancedChen.P4AOriginalFiniteAll22RawLedger
noncomputable section
open scoped Classical BigOperators
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87RawChronology (rawRoot)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFiniteFallbackPolicy (dispatch)
open P4AOrderedThirdArithmeticOccurrence (fresh)
open P4AFallbackCanonicalBanks (bank)

def lowStage (k n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :=
  dispatch N (fresh (data e q a) omega N)
    (P4AOriginalOrderedSixthStages.policy k n (data e q a) omega N)
def lowEighth (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :=
  dispatch N (fresh (data e q a) omega N)
    (P4AOriginalOrderedThirdFullPolicy.policy (width r) n (data e q a) omega N)
def finalPolicy (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :=
  P4AOriginalFiniteFallbackPolicy.policy (bank m) (width r) n (data e q a) omega N

theorem lowStage_zero (n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :
    lowStage 0 n e q a omega N=dispatch N (fresh (data e q a) omega N)
      (P4AOriginalOrderedSixthStages.orderedFifth n (data e q a) omega N) := by
  rw [lowStage,P4AOriginalOrderedSixthStages.policy_zero]

def lowerEarly (n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) : ℝ :=
  normalize N (rawRoot (fresh (data e q a) omega N) N-rawRoot (lowStage 0 n e q a omega N) N)
def lowerSaved (n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) : ℝ :=
  normalize N (rawRoot (lowStage 0 n e q a omega N) N-rawRoot (lowStage 1 n e q a omega N) N)
def lowerEleven (n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) : ℝ :=
  normalize N (rawRoot (lowStage 1 n e q a omega N) N-rawRoot (lowStage 2 n e q a omega N) N)
def lowerLater (n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) : ℝ :=
  normalize N (rawRoot (lowStage 2 n e q a omega N) N-rawRoot (lowStage 10 n e q a omega N) N)
def lowerEighth (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) : ℝ :=
  normalize N (rawRoot (lowStage 10 n e q a omega N) N-rawRoot (lowEighth r n e q a omega N) N)
def upperFallback (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) : ℝ :=
  normalize N (rawRoot (P4AOriginalFiniteFallbackJointGain.before m (width r) n e q a omega N) N-
    rawRoot (finalPolicy m r n e q a omega N) N)

theorem lowerEleven_eq_paid_source (n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :
    lowerEleven n e q a omega N=P4AOriginalElevenOrderedSum.gain n (data e q a) omega N := by
  have hU : ∀ h,fresh (data e q a) omega N true h=true := by
    intro h
    rw [←P4AOriginalFiniteFallbackOccurrence.empty_eq (bank 0) (data e q a) omega N]
    exact P4AOriginalFiniteFallbackOccurrence.positive _ _ _ _ _
  exact P4AOriginalElevenUpperDispatch.actual_dispatch_gain n (data e q a) omega N _ hU

theorem before_eq_lowEighth (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :
    P4AOriginalFiniteFallbackJointGain.before m (width r) n e q a omega N=lowEighth r n e q a omega N := by
  rw [P4AOriginalFiniteFallbackJointGain.before,P4AOriginalFiniteFallbackFullTree.withLower,
    P4AOriginalFiniteFallbackOccurrence.empty_eq]
  rfl

/-- Exact same-target identity before ANY numerical floor or estimate.
No early scalar is assumed paid,and no nominal slot is imported twice. -/
theorem exact_all22_telescope (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :
    normalize N (rawRoot (finalPolicy m r n e q a omega N) N)=
      normalize N (rawRoot (fresh (data e q a) omega N) N)-lowerEarly n e q a omega N-
        lowerSaved n e q a omega N-lowerEleven n e q a omega N-lowerLater n e q a omega N-
        lowerEighth r n e q a omega N-upperFallback m r n e q a omega N := by
  unfold lowerEarly lowerSaved lowerEleven lowerLater lowerEighth upperFallback
  rw [before_eq_lowEighth]
  unfold normalize
  ring

def lowerEarlySlots : ℝ := currentUpperEighteenGains 0+currentUpperEighteenGains 1+currentUpperEighteenGains 2
def upperFallbackSlots : ℝ := currentUpperEighteenGains 4+currentUpperEighteenGains 5
def lowerEarlyDefect (n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) : ℝ :=
  lowerEarlySlots-lowerEarly n e q a omega N

end
end ImbalancedChen.P4AOriginalFiniteAll22RawLedger
