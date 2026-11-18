import ImbalancedChen.Part5OriginalH430InitialFixedSourceObstruction
import ImbalancedChen.Part5OriginalH430ActualSecondRosserRetention

/-!
P5.6 / h34: canonically group the ACTUAL original U3/U4 q/tag
receipts that pass the true rank-two ordinary Rosser policy.

A receipt z retains its U3/U4 tag, its original prime p and quotient q.
If some genuine second prime ell survives the ORIGINAL arithmetic
enumerator and the ACTUAL two-prime Rosser test, Nat.find selects one
such ell. The finite owner key is (tag,p,ell), never just a scalar
feedback label or a quotient q. This proves an exact, disjoint
arithmetic-fibre partition with all original q multiplicities and
arbitrary signed weights preserved.

No q-to-feedback-history injection, source-to-Theta payment,
count normalization, selected/inherited compatibility, CLOSED-CELL
induction or complete h34 closure is asserted.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualRetainedPrefixFibres

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430ActualRootStageReceipts
open Part5OriginalH430ActualSecondRosserRetention
open Part5OriginalH430InitialFixedSourceObstruction
open Part5OriginalH430ActualWinnerFixedRead

/-- TRUE original tagged q receipts for which both the original root
stage and at least one actual rank-two Rosser factor survive. -/
def stageRetainedOriginal (N cap precision : ℕ)
    (tau z0 : ℝ) (lower : Bool) : Finset TaggedReceiver := by
  classical
  exact (originalTagged N).filter (fun z =>
    selectedOriginalRootStage N cap precision tau z0 lower z ∧
    hasRetainedOriginalSecond N cap precision tau z0 lower z)

theorem mem_stage_retained_original
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver) :
    z ∈ stageRetainedOriginal N cap precision tau z0 lower ↔
      z ∈ originalTagged N ∧
      selectedOriginalRootStage N cap precision tau z0 lower z ∧
      hasRetainedOriginalSecond N cap precision tau z0 lower z := by
  simp [stageRetainedOriginal]

/-- A genuine rank-two historical prefix records BOTH root tag and
original p in addition to the actual accepted prime factor ell.
It deliberately does not identify two distinct quotient receipts. -/
abbrev SecondPrefixKey := Root × ℕ × ℕ

/-- Minimum actual retained second prime, rather than an arbitrary
new source licence. Nat.find is used ONLY on the already established
existential predicate of the real ordinary Rosser selector. -/
noncomputable def actualSecondPrefixKey
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver) : Option SecondPrefixKey := by
  classical
  exact if h : hasRetainedOriginalSecond
      N cap precision tau z0 lower z then
    some (arithmeticBand z, arithmeticPrime z, Nat.find h)
  else none

/-- An assigned receipt has a TRUE prime divisor of its original q
and a TRUE accepted [ell,p] Rosser prefix. Its tag and p are literal. -/
theorem actual_second_prefix_witness
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver)
    (hz : z ∈ stageRetainedOriginal N cap precision tau z0 lower) :
    ∃ ell : ℕ,
      actualSecondPrefixKey N cap precision tau z0 lower z =
        some (arithmeticBand z, arithmeticPrime z, ell) ∧
      ell.Prime ∧ ell ∣ arithmeticQuotientPrime z ∧
      retainedOriginalSecond N cap precision tau z0 lower z ell := by
  classical
  have hret : hasRetainedOriginalSecond
      N cap precision tau z0 lower z :=
    (mem_stage_retained_original N cap precision tau z0 lower z).mp hz |>.2.2
  refine ⟨Nat.find hret, ?_, ?_⟩
  · simp [actualSecondPrefixKey, hret]
  · exact Nat.find_spec hret

theorem actual_second_prefix_none_of_no_retention
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver)
    (hno : ¬ hasRetainedOriginalSecond
      N cap precision tau z0 lower z) :
    actualSecondPrefixKey N cap precision tau z0 lower z = none := by
  simp [actualSecondPrefixKey, hno]

/-- All keys actually hit by the ORIGINAL retained tagged q receipts.
The key may not be a valid feedback history occurrence; that remains
a distinct manuscript-internal proof obligation. -/
def stagePrefixKeys (N cap precision : ℕ)
    (tau z0 : ℝ) (lower : Bool) : Finset (Option SecondPrefixKey) := by
  classical
  exact (stageRetainedOriginal N cap precision tau z0 lower).image
    (actualSecondPrefixKey N cap precision tau z0 lower)

/-- A key is a genuine (U3/U4,p,ell) accepted factor, not a
fabricated or empty owner. The q witness remains in the source. -/
theorem stage_prefix_key_witness
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    {key : Option SecondPrefixKey}
    (hk : key ∈ stagePrefixKeys N cap precision tau z0 lower) :
    ∃ z ∈ stageRetainedOriginal N cap precision tau z0 lower,
      ∃ ell : ℕ,
        key = some (arithmeticBand z, arithmeticPrime z, ell) ∧
        ell.Prime ∧ ell ∣ arithmeticQuotientPrime z ∧
        retainedOriginalSecond N cap precision tau z0 lower z ell := by
  classical
  obtain ⟨z, hz, hkey⟩ := Finset.mem_image.mp hk
  obtain ⟨ell, hw, hp, hd, hr⟩ :=
    actual_second_prefix_witness N cap precision tau z0 lower z hz
  exact ⟨z, hz, ell, hkey.symm.trans hw, hp, hd, hr⟩

theorem no_none_stage_prefix_key
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    (none : Option SecondPrefixKey) ∉
      stagePrefixKeys N cap precision tau z0 lower := by
  intro h
  obtain ⟨z, hz, ell, heq, _, _, _⟩ :=
    stage_prefix_key_witness N cap precision tau z0 lower h
  cases heq

/-- Original arithmetic fibre for a TRUE tag/p/second-prime prefix.
All distinct original q receipts remain separate members. -/
def actualRetainedPrefixFibre
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (key : Option SecondPrefixKey) : Finset TaggedReceiver := by
  classical
  exact (stageRetainedOriginal N cap precision tau z0 lower).filter
    (fun z => actualSecondPrefixKey N cap precision tau z0 lower z = key)

theorem prefix_fibres_disjoint
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    {key₁ key₂ : Option SecondPrefixKey} (hne : key₁ ≠ key₂) :
    Disjoint
      (actualRetainedPrefixFibre N cap precision tau z0 lower key₁)
      (actualRetainedPrefixFibre N cap precision tau z0 lower key₂) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hz₁ hz₂
  have h₁ := (Finset.mem_filter.mp hz₁).2
  have h₂ := (Finset.mem_filter.mp hz₂).2
  exact hne (h₁.symm.trans h₂)

/-- Each original tagged q occurs in precisely its actual second
prefix fibre; multiple accepted ell's do not duplicate that receipt. -/
theorem exact_retained_source_by_prefix
    {α : Type*} [AddCommMonoid α]
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → α) :
    (∑ z ∈ stageRetainedOriginal N cap precision tau z0 lower, w z) =
      ∑ key ∈ stagePrefixKeys N cap precision tau z0 lower,
        ∑ z ∈ actualRetainedPrefixFibre
          N cap precision tau z0 lower key, w z := by
  classical
  let R := stageRetainedOriginal N cap precision tau z0 lower
  let S := stagePrefixKeys N cap precision tau z0 lower
  let owner := actualSecondPrefixKey N cap precision tau z0 lower
  have hsum :
      (∑ z ∈ R, w z) =
        ∑ key ∈ S, ∑ z ∈ R,
          if owner z = key then w z else 0 := by
    calc
      (∑ z ∈ R, w z) =
          ∑ z ∈ R, ∑ key ∈ S,
            if owner z = key then w z else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        have hmem : owner z ∈ S :=
          Finset.mem_image.mpr ⟨z, hz, rfl⟩
        have hsingle :
            (∑ key ∈ S, if owner z = key then w z else 0) = w z := by
          calc
            _ = (if owner z = owner z then w z else 0) := by
              apply Finset.sum_eq_single (owner z)
              · intro key _ hneq
                have hne : owner z ≠ key := Ne.symm hneq
                simp [hne]
              · intro hnot
                exact (hnot hmem).elim
            _ = w z := by simp
        exact hsingle.symm
      _ = ∑ key ∈ S, ∑ z ∈ R,
            if owner z = key then w z else 0 := Finset.sum_comm
  rw [hsum]
  apply Finset.sum_congr rfl
  intro key _
  simp only [actualRetainedPrefixFibre, Finset.sum_filter]

/-- A genuine retained original q/tag receipt gives positive
original arithmetic mass even at the first stage, whose bank-fixed
Q80 source was proved zero. No claim of already-paid history mass. -/
theorem positive_retained_count_not_paid_by_first_fixed
    (N n cap precision : ℕ) (root : Root)
    (tau z0 : ℝ) (p : ℕ) (lower : Bool)
    {z : TaggedReceiver}
    (hz : z ∈ stageRetainedOriginal N cap precision tau z0 lower)
    (C : ℝ) :
    ¬ (((stageRetainedOriginal N cap precision tau z0 lower).card : ℝ) ≤
      C * resolvedWinnerFixedMass N n root tau p firstOriginalGeneration) := by
  have hpositive : (0 : ℝ) <
      ((stageRetainedOriginal N cap precision tau z0 lower).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨z, hz⟩)
  intro h
  rw [first_resolved_winner_fixed_mass_zero, mul_zero] at h
  exact (not_le_of_gt hpositive) h

end
end ImbalancedChen.Part5OriginalH430ActualRetainedPrefixFibres
