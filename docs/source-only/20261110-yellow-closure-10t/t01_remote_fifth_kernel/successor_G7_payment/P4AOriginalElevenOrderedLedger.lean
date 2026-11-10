import ImbalancedChen.P4AOriginalElevenOrderedPayment

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The G7 replacement floor enters the actual same-tree sixth remainder
ONCE, after G4 and before the eight later stages. This exact normalized
identity uses T05's stage10, which is the original updated sixth parent.
The remaining later-stage and final count reserves are not assumed paid.
-/
namespace ImbalancedChen.P4AOriginalElevenOrderedLedger
noncomputable section
open P5OriginalCommonRefinedConstructor (OriginalData)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalFull87RawChronology (rawRoot)
open P4AOriginalElevenOrderedSum (gain)
open P4AOriginalElevenActualCommonHistory (bank)
open P4AOriginalElevenOrderedPayment (originalFloor)

def afterG4 (n : ℕ) (d : OriginalData) (omega : ℝ) (N : ℕ) : ℝ :=
  normalize N (rawRoot (P4AOriginalOrderedSixthStages.policy 10 n d omega (N:ℝ)) N-
    rawRoot (P4AOriginalOrderedSixthStages.policy 1 n d omega (N:ℝ)) N)
def afterG7 (n : ℕ) (d : OriginalData) (omega : ℝ) (N : ℕ) : ℝ :=
  normalize N (rawRoot (P4AOriginalOrderedSixthStages.policy 10 n d omega (N:ℝ)) N-
    rawRoot (P4AOriginalOrderedSixthStages.policy 2 n d omega (N:ℝ)) N)

theorem exact_original_G7_charge (n : ℕ) (d : OriginalData) (omega : ℝ) (N : ℕ) :
    afterG4 n d omega N=afterG7 n d omega N-gain n d omega N := by
  unfold afterG4 afterG7 gain normalize
  ring

theorem paid_original_G7_charge {n : ℕ} {d : OriginalData} {omega epsilon : ℝ} {N : ℕ}
    (h : originalFloor-epsilon<gain n d omega N) :
    afterG4 n d omega N<afterG7 n d omega N-originalFloor+epsilon := by
  rw [exact_original_G7_charge]
  linarith

/-- Direct actual-ledger form of the original G7 terminal. No old G7 floor
is added, and neither G4 nor a later sixth action is counted twice. -/
theorem exists_original_G7_actual_ledger_charge (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ n0 : ℕ,∀ n≥n0,∃ e0 : ℝ,0<e0 ∧
    ∀ e : ℚ,0<e → (e:ℝ)<e0 → ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,
    ∀ a omega : ℝ,a≤1/100 → omega≤a →
    ∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N →
      afterG4 n (bank e q a) omega N<afterG7 n (bank e q a) omega N-originalFloor+epsilon := by
  obtain ⟨n0,h⟩ := P4AOriginalElevenOrderedPayment.exists_original_G7_ordered_payment epsilon hepsilon
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨e0,he0,hE⟩ := h n hn
  refine ⟨e0,he0,?_⟩
  intro e he hee
  obtain ⟨q0,hq0,hQ⟩ := hE e he hee
  refine ⟨q0,hq0,?_⟩
  intro q hq a omega ha hwa
  obtain ⟨N0,hN0,hN⟩ := hQ q hq a omega ha hwa
  exact ⟨N0,hN0,fun N hNN hev => paid_original_G7_charge (hN N hNN hev)⟩

end
end ImbalancedChen.P4AOriginalElevenOrderedLedger
