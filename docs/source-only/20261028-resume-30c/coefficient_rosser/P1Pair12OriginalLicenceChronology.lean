import ImbalancedChen.P1Pair12ActualWireSourceSupport
import ImbalancedChen.OriginalFourthBankStreamingScan
import ImbalancedChen.P1OriginalVariableFourthActiveOnly

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original licence is retained as an input. No new licence is defined.
The second-batch wire flag is compared with that original licence on the
same complete ordered raw record bank. The unsupported/Theta branch has
an exact chronological equality: every raw record is seen, seed slot zero
wins, and all subsequent retained frontiers and signed terminal arithmetic
sources agree. No all-pass or original-licence equality premise is used.

The remaining difference of the TWO ACTUAL physical coefficients is then
identified with one signed remainder on the common original rank-four
frontier, restricted to genuinely supported third ancestors. This is a
localization, not a claim that the remainder vanishes. It does not assert
archive parse, adopted compact partition coverage, H5, K or a PP estimate.
-/

namespace ImbalancedChen.P1Pair12OriginalLicenceChronology

noncomputable section
open Classical
open scoped BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFifthContinuation
open P1Pair12ActualWireSourceSupport
open P1Pair12RetainedSignedSource
open OriginalFullFourthPriorityOwnership20261026a
open OriginalFourthBankStreamingScan20261026b

/-- Full original scan, including every repeated raw occurrence. The seed
beats every buffered fourth candidate, independently of the licence. -/
theorem actual_raw_scan_initial (records : List FourthWireRow) (e : ℝ)
    (licensedOriginal : ProducerRow → Prop) (t : Point) :
    scan records e (HistoricalThirdCoarse.initial e) licensedOriginal t =
      ⟨records.length, HistoricalThirdCoarse.initial e, 0⟩ := by
  have hp := P1OriginalVariableFourthActiveOnly.producerProfile_initial
    e (fourthFamily records) licensedOriginal t
  have ho := (owner_zero_iff records e (HistoricalThirdCoarse.initial e)
    licensedOriginal t).mpr hp
  rw [scan_eq_actual_maximum_and_owner, hp, ho]
  rfl

/-- A true original unsupported history gives exact seen/value/first
chronology equality with the existing raw-check flag, on the SAME bank.
The original licence is neither replaced nor assumed equal to the flag. -/
theorem actual_original_checked_scan_chronology
    (records : List FourthWireRow) (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (licensedOriginal : ProducerRow → Prop) (history : List ℕ)
    (hs : ¬ P1ThirdFallbackSupport.supported e chi m omega N
      (rosserAncestor 3 history)) :
    scan records e (seedExponent e chi m omega N history) licensedOriginal
        (primeHistoryLogCoordinates N 4 history) =
      scan records e (seedExponent e chi m omega N history)
        (fun r => sourceGeometryFlag r = true) (primeHistoryLogCoordinates N 4 history) := by
  have hseed : seedExponent e chi m omega N history = HistoricalThirdCoarse.initial e := by
    unfold seedExponent P1CoarseFirstCubeFallbackMargin.effectiveExponent
    exact if_neg hs
  rw [hseed, actual_raw_scan_initial, actual_raw_scan_initial]

/-- The original actual fifth policy is literally the first-stop initial
policy on both inactive and active-unselected third histories. This applies
to ANY original row licence and preserves the actual original row maxima. -/
theorem original_policy5_fallback
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows4 : Finset ProducerRow) (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (positive : Bool) (history : List ℕ)
    (hs : ¬ P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N
      (rosserAncestor 3 history)) :
    policy5 e chi m omega N rows4 licensedOriginal J5 rows5 positive history =
      HistoricalThirdCoarse.initialPolicy (e : ℝ) m N positive history := by
  by_cases hsmall : history.length ≤ 4
  · rw [policy5_through_four e chi m omega N rows4 licensedOriginal J5 rows5
      positive history hsmall]
    exact P1ThirdFallbackSupport.policy_fallback (e : ℝ) chi m omega N
      positive history hs
  · have hne : history.length ≠ 1 := by omega
    have hs5 : ¬ P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N
        (rosserAncestor 3 (rosserAncestor 5 history)) := by
      rw [rosserAncestor_nested 3 5 (by omega)]
      exact hs
    have hcap := fifth_eq_initial_of_unsupported e chi m omega N rows4
      licensedOriginal J5 rows5 (rosserAncestor 5 history) hs5
    simp [policy5, fifthCappedUpperPolicy, firstExitDepthSplicePolicy, hsmall,
      frozenParityRosserPolicy, ancestorFrozenPolicy, level5, hcap,
      ordinaryParityRosserPolicy, HistoricalThirdCoarse.initialPolicy,
      oddFirstExitPolicy, hne]

/-- Exact arithmetic continuation, for a nonmultiplicative terminal test.
The support hypothesis is inherited by every subsequent selected prefix. -/
theorem original_signed_source_fallback
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows4 : Finset ProducerRow) (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (pre remaining : List ℕ) (positive : Bool) (mass : ℝ)
    (hlen : 3 ≤ pre.length)
    (hs : ¬ P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N
      (rosserAncestor 3 pre)) :
    signedTest (policy5 e chi m omega N rows4 licensedOriginal J5 rows5)
        h T pre positive mass remaining =
      signedTest (HistoricalThirdCoarse.initialPolicy (e : ℝ) m N)
        h T pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
      have hn : 3 ≤ (p :: pre).length := by simpa only [List.length_cons] using hlen.trans (Nat.le_succ _)
      have hsnext : ¬ P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N
          (rosserAncestor 3 (p :: pre)) := by
        rw [rosserAncestor_cons 3 p pre hlen]
        exact hs
      simp only [signedTest]
      rw [original_policy5_fallback e chi m omega N rows4 licensedOriginal
          J5 rows5 (!positive) (p :: pre) hsnext,
        ih pre positive mass hlen hs,
        ih (p :: pre) (!positive) (mass * h p) hn hsnext]

/-- This equality concerns the full later frontier, including remaining
carrier, mass, sign and prefix order. It is not merely a cap comparison. -/
theorem original_frontier_chronology_fallback
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows4 : Finset ProducerRow) (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (rank : ℕ) (h : ℕ → ℝ) (pre remaining : List ℕ)
    (positive : Bool) (mass : ℝ) (hlen : 3 ≤ pre.length)
    (hs : ¬ P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N
      (rosserAncestor 3 pre)) :
    firstExitDepthFrontier rank
        (policy5 e chi m omega N rows4 licensedOriginal J5 rows5)
        h pre positive mass remaining =
      firstExitDepthFrontier rank (HistoricalThirdCoarse.initialPolicy (e : ℝ) m N)
        h pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
      by_cases hk : rank ≤ pre.length
      · simp only [firstExitDepthFrontier, if_pos hk]
      · have hn : 3 ≤ (p :: pre).length := by
          simpa only [List.length_cons] using hlen.trans (Nat.le_succ _)
        have hsnext : ¬ P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N
            (rosserAncestor 3 (p :: pre)) := by
          rw [rosserAncestor_cons 3 p pre hlen]
          exact hs
        simp only [firstExitDepthFrontier, if_neg hk]
        rw [original_policy5_fallback e chi m omega N rows4 licensedOriginal
            J5 rows5 (!positive) (p :: pre) hsnext,
          ih pre positive mass hlen hs,
          ih (p :: pre) (!positive) (mass * h p) hn hsnext]

/-- No original/check licence equality is assumed. At every actual retained
unsupported sixth state their later chronology is equal because both are
proved equal to the same original first-stop initial continuation. -/
theorem actual_original_checked_later_chronology
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (records : List FourthWireRow) (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (N cap : ℕ) (w z : ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 6
      (policy5 e chi m omega (N : ℝ) (fourthFamily records) licensedOriginal J5 rows5)
      (fun _ : ℕ => 1) [] true 1 (roughPrimeUniverse N cap w z))
    (hs : ¬ P1ThirdFallbackSupport.supported (e : ℝ) chi m omega (N : ℝ)
      (rosserAncestor 3 state.selectedPrefix)) (rank : ℕ) :
    firstExitDepthFrontier rank
        (policy5 e chi m omega (N : ℝ) (fourthFamily records) licensedOriginal J5 rows5)
        (fun _ : ℕ => 1) state.selectedPrefix state.positive state.mass state.remaining =
      firstExitDepthFrontier rank (wirePolicy5 e chi m omega records J5 rows5 N)
        (fun _ : ℕ => 1) state.selectedPrefix state.positive state.mass state.remaining := by
  have hlen := firstExitDepthFrontier_selected_length 6
    (policy5 e chi m omega (N : ℝ) (fourthFamily records) licensedOriginal J5 rows5)
    (fun _ : ℕ => 1) [] (roughPrimeUniverse N cap w z) true 1 (by simp) state hstate
  rw [original_frontier_chronology_fallback e chi m omega (N : ℝ)
    (fourthFamily records) licensedOriginal J5 rows5 rank (fun _ => 1)
    state.selectedPrefix state.remaining state.positive state.mass (by omega) hs]
  exact (original_frontier_chronology_fallback e chi m omega (N : ℝ)
    (fourthFamily records) (fun r => sourceGeometryFlag r = true) J5 rows5 rank
    (fun _ => 1) state.selectedPrefix state.remaining state.positive state.mass
    (by omega) hs).symm

private theorem sum_maps_sub {α : Type*} (states : List α) (F G : α → ℝ) :
    (states.map F).sum - (states.map G).sum =
      (states.map (fun s => F s - G s)).sum := by
  induction states with
  | nil => simp
  | cons s states ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      ring

private theorem sum_filter_of_zero {α : Type*} (states : List α)
    (P : α → Prop) [DecidablePred P] (F : α → ℝ)
    (hz : ∀ s ∈ states, ¬ P s → F s = 0) :
    (states.map F).sum = ((states.filter (fun s => decide (P s))).map F).sum := by
  revert hz
  induction states with
  | nil => intro _hz; simp
  | cons s states ih =>
      intro hz
      have htail : ∀ x ∈ states, ¬ P x → F x = 0 := by
        intro x hx
        exact hz x (List.mem_cons_of_mem s hx)
      by_cases hs : P s
      · simp [hs, ih htail]
      · simp [hs, hz s (by simp) hs, ih htail]

/-- The literal policy5 has the SAME original firstStop/rawQ3 prefix through
rank four, for the original licence as well as for the existing wire flag. -/
theorem original_policy5_as_same_parent_splice
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows4 : Finset ProducerRow) (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m)) :
    firstExitDepthSplicePolicy 4 (HistoricalThirdCoarse.policy (e : ℝ) chi m omega N)
        (policy5 e chi m omega N rows4 licensedOriginal J5 rows5) =
      policy5 e chi m omega N rows4 licensedOriginal J5 rows5 := by
  funext positive pre
  by_cases hlen : pre.length ≤ 4
  · simp only [firstExitDepthSplicePolicy, if_pos hlen]
    exact (policy5_through_four e chi m omega N rows4 licensedOriginal J5 rows5
      positive pre hlen).symm
  · simp only [firstExitDepthSplicePolicy, if_neg hlen]

/-- Both arithmetic sources stop at the literal common original rank-four
frontier. All early terminal branches cancel, for arbitrary signed tests. -/
theorem original_licence_root_difference
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows4 : Finset ProducerRow) (licensedOriginal licensedChecked : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    signedTest (policy5 e chi m omega N rows4 licensedOriginal J5 rows5)
        h T [] true 1 carrier -
      signedTest (policy5 e chi m omega N rows4 licensedChecked J5 rows5)
        h T [] true 1 carrier =
      ((firstExitDepthFrontier 4 (HistoricalThirdCoarse.policy (e : ℝ) chi m omega N)
          h [] true 1 carrier).map
        (fun s => signedTest (policy5 e chi m omega N rows4 licensedOriginal J5 rows5)
            h T s.selectedPrefix s.positive s.mass s.remaining -
          signedTest (policy5 e chi m omega N rows4 licensedChecked J5 rows5)
            h T s.selectedPrefix s.positive s.mass s.remaining)).sum := by
  have horiginal := signedTest_splice_eq_stopped_add_frontier 4
    (HistoricalThirdCoarse.policy (e : ℝ) chi m omega N)
    (policy5 e chi m omega N rows4 licensedOriginal J5 rows5) h T [] carrier true 1
  have hchecked := signedTest_splice_eq_stopped_add_frontier 4
    (HistoricalThirdCoarse.policy (e : ℝ) chi m omega N)
    (policy5 e chi m omega N rows4 licensedChecked J5 rows5) h T [] carrier true 1
  rw [original_policy5_as_same_parent_splice] at horiginal hchecked
  rw [horiginal, hchecked, add_sub_add_left_eq_sub]
  exact sum_maps_sub _ _ _

/-- Exact original-versus-existing-check physical-rho remainder. Only the
supported part of their common original fourth frontier can contribute.
The expression is SIGNED and includes the same count/exact-mean test G;
no small/rough coefficient or licence is silently exchanged. -/
theorem actual_original_checked_physical_remainder
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (records : List FourthWireRow) (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (N cap mark : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    let Roriginal := policy5 e chi m omega (N : ℝ) (fourthFamily records)
      licensedOriginal J5 rows5
    let Rchecked := wirePolicy5 e chi m omega records J5 rows5 N
    let states := firstExitDepthFrontier 4
      (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
      (fun _ : ℕ => 1) [] true 1 (roughPrimeUniverse N cap w z)
    (∑ q ∈ actualSmallRoughModuli (Roriginal false) N cap w z,
      actualSmallRoughRho (Roriginal false) N cap w z L q * G (mark * q)) -
      (∑ q ∈ actualSmallRoughModuli (Rchecked false) N cap w z,
        actualSmallRoughRho (Rchecked false) N cap w z L q * G (mark * q)) =
      ((states.filter (fun s => decide (P1ThirdFallbackSupport.supported
          (e : ℝ) chi m omega (N : ℝ) (rosserAncestor 3 s.selectedPrefix)))).map
        (fun s => signedTest Roriginal (fun _ => 1) (attachedLeafTest N cap mark w L G)
            s.selectedPrefix s.positive s.mass s.remaining -
          signedTest Rchecked (fun _ => 1) (attachedLeafTest N cap mark w L G)
            s.selectedPrefix s.positive s.mass s.remaining)).sum := by
  dsimp only
  have hevenOriginal := P4AOriginalVariableFifthPhysicalLedger.fifth_even e chi m omega
    (fourthFamily records) licensedOriginal J5 rows5 (N : ℝ)
  have hevenChecked := P4AOriginalVariableFifthPhysicalLedger.fifth_even e chi m omega
    (fourthFamily records) (fun r => sourceGeometryFlag r = true) J5 rows5 (N : ℝ)
  rw [show wirePolicy5 e chi m omega records J5 rows5 N =
      policy5 e chi m omega (N : ℝ) (fourthFamily records)
        (fun r => sourceGeometryFlag r = true) J5 rows5 from rfl]
  rw [physical_test_eq_signedTest _ hevenOriginal,
    physical_test_eq_signedTest _ hevenChecked,
    original_licence_root_difference]
  apply sum_filter_of_zero
  intro s hs hunsupported
  have hlen := firstExitDepthFrontier_selected_length 4
    (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ)) (fun _ : ℕ => 1)
    [] (roughPrimeUniverse N cap w z) true 1 (by simp) s hs
  rw [original_signed_source_fallback e chi m omega (N : ℝ)
      (fourthFamily records) licensedOriginal J5 rows5 (fun _ => 1)
      (attachedLeafTest N cap mark w L G) s.selectedPrefix s.remaining s.positive s.mass
      (by omega) hunsupported,
    original_signed_source_fallback e chi m omega (N : ℝ)
      (fourthFamily records) (fun r => sourceGeometryFlag r = true) J5 rows5
      (fun _ => 1) (attachedLeafTest N cap mark w L G)
      s.selectedPrefix s.remaining s.positive s.mass (by omega) hunsupported,
    sub_self]

end
end ImbalancedChen.P1Pair12OriginalLicenceChronology
