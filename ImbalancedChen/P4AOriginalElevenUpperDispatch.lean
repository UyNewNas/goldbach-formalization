import ImbalancedChen.P4AOriginalFiniteFallbackSectorTransport
import ImbalancedChen.P4AOriginalElevenOrderedChangedSupport
import ImbalancedChen.P4AOriginalElevenOrderedPayment

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The actual G7 stage is IDENTICAL on every high first-prime word. This is
proved from the original PhysicalCell winner and its largest-coordinate
gate,then followed through the real six-ancestor frozen policy. Therefore
the true G7 payment survives the final common finite upper dispatcher.
-/
namespace ImbalancedChen.P4AOriginalElevenUpperDispatch
noncomputable section
open VariableEnvelope
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFiniteFallbackPolicy (Rule high dispatch)
open P4AOriginalOrderedSixthStages (level orderedLevel policy)
open P4AOriginalFull87RawChronology (rawRoot)
open P5OriginalCommonPositivePresieve (normalize)

theorem high_ancestor_six (N : ℝ) (h : List ℕ) : high N (rosserAncestor 6 h) ↔ high N h := by
  simp only [high,P4AOriginalFiniteFallbackPolicy.point,rosserAncestor_nested 1 6 (by decide)]

theorem g7_caps_equal_on_high (n : ℕ) (d : OriginalData) (omega N : ℝ) (h : List ℕ)
    (hlen : h.length=6) (hh : high N h) : orderedLevel 1 n d omega N h=orderedLevel 2 n d omega N h := by
  let R := P4AOriginalOrderedThirdFullPolicy.current d omega N h
  have hPM : orderedLevel 1 n d omega N h≤orderedLevel 2 n d omega N h :=
    P4AOriginalOrderedSixthStages.level_mono n R d N h (by decide : 1≤2)
  by_contra hne
  obtain ⟨c,hc,_⟩ := P4AOriginalElevenOrderedChangedSupport.changed_owner n R d N h
    (lt_of_le_of_ne hPM hne)
  have hcoord := primeHistoryLogCoordinates_ancestor N hlen (by decide : 1≤6) (0:Fin 1)
  have hlarge : mu<primeHistoryLogCoordinates N 6 h 0 := by
    change mu<primeHistoryLogCoordinates N 1 (rosserAncestor 1 h) 0 at hh
    simpa only [hcoord] using hh
  exact (not_lt_of_ge hc.largest.le) hlarge

/-- All high first-exit histories agree,including the initial words and
each genuine frozen sixth ancestor. No global raw-policy equality is used. -/
theorem g7_policy_equal_on_high (n : ℕ) (d : OriginalData) (omega N : ℝ) (b : Bool)
    (h : List ℕ) (hh : high N h) : policy 1 n d omega N b h=policy 2 n d omega N b h := by
  by_cases hl : h.length≤6
  · simp only [policy,firstExitDepthSplicePolicy,if_pos hl]
  · have hlen : (rosserAncestor 6 h).length=6 := by simp only [rosserAncestor,List.length_drop]; omega
    have hc := g7_caps_equal_on_high n d omega N (rosserAncestor 6 h) hlen
      ((high_ancestor_six N h).mpr hh)
    simp only [policy,firstExitDepthSplicePolicy,if_neg hl,frozenParityRosserPolicy,ancestorFrozenPolicy]
    rw [hc]

theorem actual_dispatch_gain (n : ℕ) (d : OriginalData) (omega : ℝ) (N : ℕ) (U : Rule)
    (hU : ∀ h,U true h=true) :
    normalize N (rawRoot (dispatch N U (policy 1 n d omega (N:ℝ))) N-
      rawRoot (dispatch N U (policy 2 n d omega (N:ℝ))) N)=
      P4AOriginalElevenOrderedSum.gain n d omega N := by
  exact congrArg (normalize N) (P4AOriginalFiniteFallbackSectorTransport.local_increment N U _ _ hU
    (P4AOriginalOrderedSixthSigned.even 1 n d omega N)
    (P4AOriginalOrderedSixthSigned.even 2 n d omega N)
    (g7_policy_equal_on_high n d omega (N:ℝ)))

/-- The common upper rule may be the actual finite bank selected later,
and may vary with N. The original G7 floor and its tolerance are paid once. -/
theorem exists_original_G7_dispatched_payment (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ n0 : ℕ,∀ n≥n0,∃ e0 : ℝ,0<e0 ∧
    ∀ e : ℚ,0<e → (e:ℝ)<e0 → ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,
    ∀ a omega : ℝ,a≤1/100 → omega≤a →
    ∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N → ∀ U : Rule,(∀ h,U true h=true) →
      P4AOriginalElevenOrderedPayment.originalFloor-epsilon<
        normalize N (rawRoot (dispatch N U (policy 1 n (P4AOriginalNewFifthUnion.data e q a) omega N)) N-
          rawRoot (dispatch N U (policy 2 n (P4AOriginalNewFifthUnion.data e q a) omega N)) N) := by
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
  refine ⟨N0,hN0,?_⟩
  intro N hNN hev U hU
  rw [actual_dispatch_gain n (P4AOriginalNewFifthUnion.data e q a) omega N U hU]
  exact hN N hNN hev

end
end ImbalancedChen.P4AOriginalElevenUpperDispatch
