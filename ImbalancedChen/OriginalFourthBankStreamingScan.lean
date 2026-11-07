import ImbalancedChen.OriginalFourthBankFirstSuffixOwner

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal one-pass raw fourth-row scan. Every record increments the position,
including repetitions and ineligible records. The inherited seed owns slot
zero. A row changes the state only when its original licence and closed-box
test hold and its exact buffered tent STRICTLY exceeds the current value.
Thus equality retains the earliest actual occurrence without deduplication.

The finite scan is proved equal to the existing actual producer maximum
AND its least positional owner. This specifies a procedure; no evaluation
of arbitrary real predicates, archived row pass or chronological22 mapping
is asserted. The original e/chi/m/omega history seed is retained explicitly.
-/

namespace ImbalancedChen.OriginalFourthBankStreamingScan20261026b

noncomputable section
open scoped Classical
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open OriginalFullFourthPriorityOwnership20261026a
open OriginalFourthBankAppendMaximum20261026b
open OriginalFourthBankAppendOwnership20261026b
open OriginalFourthBankFirstSuffixOwner20261026b

private theorem singleton_row (raw : FourthWireRow) (r : ProducerRow)
    (hr : r ∈ fourthFamily [raw]) : r = raw.toProducerRow := by
  obtain ⟨wire, hw, hd⟩ := (mem_fourthFamily_iff [raw] r).mp hr
  have hw' : wire = raw := by simpa only [List.mem_singleton] using hw
  simpa only [hw'] using hd.symm

/-- The scalar one-row stage is derived from the actual finite maximum,
not assumed as the desired scan update. -/
theorem singleton_profile (raw : FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point) :
    producerProfile4 e (fourthFamily [raw]) licensed seed t =
      if producerEligible licensed raw.toProducerRow t then
        max seed (raw.toProducerRow.bufferedCandidate e t) else seed := by
  by_cases he : producerEligible licensed raw.toProducerRow t
  · rw [if_pos he]
    apply le_antisymm
    · apply finiteMax_le
      · exact le_max_left _ _
      · intro r hr _her
        rw [singleton_row raw r hr]
        exact le_max_right _ _
    · exact max_le (producerProfile4_seed_le e (fourthFamily [raw]) licensed seed t)
        (finiteMax_row_le (fourthFamily [raw]) _ _ seed raw.toProducerRow
          ((mem_fourthFamily_iff [raw] _).mpr ⟨raw, by simp, rfl⟩) he)
  · rw [if_neg he]
    apply finiteMax_eq_seed_of_outside
    intro r hr her
    apply he
    simpa only [singleton_row raw r hr] using her

/-- Exact one-record append transition, carrying BOTH scalar and first
position. The update condition contains the original licence/box tests. -/
theorem one_row_transition (front : List FourthWireRow) (raw : FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point) :
    (producerProfile4 e (fourthFamily (front ++ [raw])) licensed seed t,
      (owner (front ++ [raw]) e seed licensed t).val) =
      if producerEligible licensed raw.toProducerRow t ∧
          producerProfile4 e (fourthFamily front) licensed seed t <
            raw.toProducerRow.bufferedCandidate e t then
        (raw.toProducerRow.bufferedCandidate e t, front.length + 1)
      else (producerProfile4 e (fourthFamily front) licensed seed t,
        (owner front e seed licensed t).val) := by
  by_cases hu : producerEligible licensed raw.toProducerRow t ∧
      producerProfile4 e (fourthFamily front) licensed seed t <
        raw.toProducerRow.bufferedCandidate e t
  · rw [if_pos hu]
    have hs : producerProfile4 e (fourthFamily [raw]) licensed seed t =
        raw.toProducerRow.bufferedCandidate e t := by
      rw [singleton_profile, if_pos hu.1,
        max_eq_right ((producerProfile4_seed_le e (fourthFamily front) licensed seed t).trans hu.2.le)]
    have hstrict : producerProfile4 e (fourthFamily front) licensed seed t <
        producerProfile4 e (fourthFamily [raw]) licensed seed t := by
      rw [hs]
      exact hu.2
    obtain ⟨i, hi⟩ := strict_suffix_owner_is_row front [raw] e seed licensed t hstrict
    have howner := owner_append_strict_suffix front [raw] e seed licensed t hstrict i hi
    have hi0 : i.val = 0 := by have h := i.isLt; simp only [List.length_singleton] at h; omega
    apply Prod.ext
    · rw [producerProfile_append, hs, max_eq_right hu.2.le]
    · rw [howner]
      dsimp [suffixPosition, suffixRowPosition]
      omega
  · rw [if_neg hu]
    have hrows : ∀ r ∈ fourthFamily [raw], producerEligible licensed r t →
        r.bufferedCandidate e t ≤ producerProfile4 e (fourthFamily front) licensed seed t := by
      intro r hr her
      have hr' := singleton_row raw r hr
      rw [hr'] at her ⊢
      exact le_of_not_gt (fun hg => hu ⟨her, hg⟩)
    have ht := (suffix_nonimproving_iff front [raw] e seed licensed t).mpr hrows
    have howner := owner_append_of_nonimproving front [raw] e seed licensed t ht
    apply Prod.ext
    · exact producerProfile_append_eq_front front [raw] e seed licensed t ht
    · rw [howner]
      rfl

@[ext] structure ScanState where
  seen : ℕ
  value : ℝ
  first : ℕ

/-- The scan never changes an old winner on equality, a failed licence,
or a failed original closed-box membership test. Every occurrence counts. -/
def scanStep (e : ℝ) (licensed : ProducerRow → Prop) (t : Point)
    (state : ScanState) (raw : FourthWireRow) : ScanState :=
  if producerEligible licensed raw.toProducerRow t ∧
      state.value < raw.toProducerRow.bufferedCandidate e t then
    ⟨state.seen + 1, raw.toProducerRow.bufferedCandidate e t, state.seen + 1⟩
  else ⟨state.seen + 1, state.value, state.first⟩

def scan (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point) : ScanState :=
  records.foldl (scanStep e licensed t) ⟨0, seed, 0⟩

theorem scan_append_one (front : List FourthWireRow) (raw : FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point) :
    scan (front ++ [raw]) e seed licensed t =
      scanStep e licensed t (scan front e seed licensed t) raw := by
  simp only [scan, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The one-pass procedure returns the ACTUAL finite producer maximum
and its first positional owner simultaneously, including seed fallback. -/
theorem scan_eq_actual_maximum_and_owner (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point) :
    scan records e seed licensed t =
      ⟨records.length, producerProfile4 e (fourthFamily records) licensed seed t,
        (owner records e seed licensed t).val⟩ := by
  induction records using List.reverseRecOn with
  | nil =>
      have hp : producerProfile4 e (fourthFamily []) licensed seed t = seed := by
        apply finiteMax_eq_seed_of_outside
        intro r hr _he
        simpa [fourthFamily] using hr
      have ho : (owner [] e seed licensed t).val = 0 := by
        have hi := (owner [] e seed licensed t).isLt
        simp only [List.length_nil] at hi
        omega
      simp only [scan, List.foldl_nil, List.length_nil, hp, ho]
  | append_singleton front raw ih =>
      rw [scan_append_one, ih]
      have ht := one_row_transition front raw e seed licensed t
      by_cases hu : producerEligible licensed raw.toProducerRow t ∧
          producerProfile4 e (fourthFamily front) licensed seed t <
            raw.toProducerRow.bufferedCandidate e t
      · rw [if_pos hu] at ht
        have hv := congrArg Prod.fst ht
        have ho := congrArg Prod.snd ht
        simp only [scanStep, if_pos hu]
        apply ScanState.ext
        · simp
        · exact hv.symm
        · exact ho.symm
      · rw [if_neg hu] at ht
        have hv := congrArg Prod.fst ht
        have ho := congrArg Prod.snd ht
        simp only [scanStep, if_neg hu]
        apply ScanState.ext
        · simp
        · exact hv.symm
        · exact ho.symm

/-- The computed natural position is a real bank slot, rather than a
separate unbound winner statistic. -/
def scannedOwner (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point) : BankPosition records :=
  ⟨(scan records e seed licensed t).first, by
    rw [scan_eq_actual_maximum_and_owner]
    exact (owner records e seed licensed t).isLt⟩

theorem scannedOwner_eq_actual_owner (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point) :
    scannedOwner records e seed licensed t = owner records e seed licensed t := by
  apply Fin.ext
  exact congrArg ScanState.first (scan_eq_actual_maximum_and_owner records e seed licensed t)

/-- The same scan gives the literal original rank-four physical level,
with the inherited parameter-dependent seed and actual logarithmic tuple. -/
theorem scan_original_history_level (records : List FourthWireRow) (e chi : ℝ) (m : ℕ)
    (omega N : ℝ) (licensed : ProducerRow → Prop) (history : List ℕ)
    (hlen : history.length = 4) :
    N ^ (scan records e (seedExponent e chi m omega N history) licensed
      (primeHistoryLogCoordinates N 4 history)).value =
      producerLevel4 e chi m omega N (fourthFamily records) licensed history := by
  rw [scan_eq_actual_maximum_and_owner, producerLevel4_rank_four _ _ _ _ _ _ _ _ hlen]

end
end ImbalancedChen.OriginalFourthBankStreamingScan20261026b
