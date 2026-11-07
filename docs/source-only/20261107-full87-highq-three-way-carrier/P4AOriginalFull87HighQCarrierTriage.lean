import ImbalancedChen.P4AOriginalFull87HighQFrontierDominance
import ImbalancedChen.FirstExitFrontierInvariants
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A second, independent arithmetical gate for the SAME full87 owned eighth
occurrences: if every actual small Rosser factor times the selected eighth
product AND the product of the literal unprocessed rough carrier is <= X,
every possible terminal modulus of both ordinary continuations is <= X.
Consequently the high-q old-minus-new ordinary saving vanishes EXACTLY.

Combined with strict prefix dominance from the predecessor, this makes
an occurrence-preserving three-way high-q ledger: forced-full, proved-zero,
and unresolved mixed. The upper carrier envelope is deliberately coarse;
we do not assert that its zero class is nonempty in saved87, or that the
mixed term is small in H_N units. No policy, beta, PP input or reserve is
changed.
-/

namespace ImbalancedChen.P4AOriginalFull87HighQCarrierTriage
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest full87_high_q_gain_eq_owned_sources)
open P4AOriginalFull87HighQFrontierDominance
  (owned_highQ_saving_eq_full_of_large_prefix)
open P4AOriginalFull87OwnedEighthSource
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthPolicy
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalLicensedSixthSignedLedger (physical)

/-- Explicit, checkable upper bound on every possible full physical q
below the ACTUAL occurrence. This uses the whole literal remaining carrier,
not an abstract new sieve support or a numerical PP level. -/
def carrierEnvelope (N cap X : ℕ) (w : ℝ)
    (s : FirstExitDepthState ℕ) : Prop :=
  ∀ a ∈ actualSmallRosserSupport N cap w,
    a * (s.selectedPrefix.prod * s.remaining.prod) ≤ X

/-- With the complete physical modulus below the strict cutoff, the
sign-dependent original small Rosser terminal contributes exactly zero. -/
private theorem attached_highQ_zero_of_bounded_product
    (N cap X : ℕ) (w L : ℝ) (F : ℕ → ℝ)
    (pre : List ℕ) (positive : Bool)
    (hsmall : ∀ a ∈ actualSmallRosserSupport N cap w,
      a * pre.prod ≤ X) :
    attachedLeafTest N cap 1 w L (highQTest X F) positive pre = 0 := by
  unfold attachedLeafTest
  apply Finset.sum_eq_zero
  intro a ha
  have hnot : ¬ X < a * pre.prod := Nat.not_lt.mpr (hsmall a ha)
  simp [highQTest, hnot]

/-- Unlike a cap monotonicity assertion, this is a structural
induction on the actual signed first-exit recursion. Every skipped
branch has a smaller product envelope; every selected branch has
the same total prefix-times-remaining product. There is no signed
saving monotonicity premise. -/
theorem signedTest_highQ_zero_of_carrier_envelope
    (R : Bool → List ℕ → Bool) (N cap X : ℕ) (w L : ℝ)
    (F : ℕ → ℝ) (pre remaining : List ℕ)
    (positive : Bool) (mass : ℝ) :
    (∀ p ∈ remaining, 0 < p) →
    (∀ a ∈ actualSmallRosserSupport N cap w,
      a * (pre.prod * remaining.prod) ≤ X) →
    signedTest R (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L (highQTest X F))
      pre positive mass remaining = 0 := by
  induction remaining generalizing pre positive mass with
  | nil =>
      intro _ hbound
      have hsmall : ∀ a ∈ actualSmallRosserSupport N cap w,
          a * pre.prod ≤ X := by
        intro a ha
        simpa using hbound a ha
      simp only [signedTest]
      rw [attached_highQ_zero_of_bounded_product
        N cap X w L F pre positive hsmall]
      ring
  | cons p ps ih =>
      intro hpositive hbound
      have hp : 1 ≤ p := hpositive p (by simp)
      have htail : ∀ r ∈ ps, 0 < r := by
        intro r hr
        exact hpositive r (by simp [hr])
      have hskip : ∀ a ∈ actualSmallRosserSupport N cap w,
          a * (pre.prod * ps.prod) ≤ X := by
        intro a ha
        have hb : a * (pre.prod * (p * ps.prod)) ≤ X := by
          simpa only [List.prod_cons] using hbound a ha
        have hm : (a * pre.prod * ps.prod) * 1 ≤
            (a * pre.prod * ps.prod) * p :=
          Nat.mul_le_mul_left _ hp
        have hle : a * (pre.prod * ps.prod) ≤
            a * (pre.prod * (p * ps.prod)) := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hm
        exact hle.trans hb
      have htake : ∀ a ∈ actualSmallRosserSupport N cap w,
          a * ((p :: pre).prod * ps.prod) ≤ X := by
        intro a ha
        simpa [List.prod_cons, mul_assoc, mul_comm, mul_left_comm]
          using hbound a ha
      by_cases hr : R (!positive) (p :: pre) = true
      · simp only [signedTest, if_pos hr]
        rw [ih pre positive mass htail hskip,
          ih (p :: pre) (!positive) (mass * (1 : ℝ)) htail htake]
        ring
      · simp only [signedTest, if_neg hr, add_zero]
        exact ih pre positive mass htail hskip

/-- Recover the actual unprocessed positive primes from the original
sixth-policy eighth frontier, not from any invented carrier assumption. -/
private theorem owned_remaining_positive
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c) :
    ∀ p ∈ s.remaining, 0 < p := by
  have hfront : s ∈ frontier n e q om N cap w z := by
    rw [states_eq_owner_filter] at hs
    exact (List.mem_filter.mp hs).1
  obtain ⟨r, tail, _hselected, _hr, hremaining⟩ :=
    mem_firstExitDepthFrontier_roughPrime_remaining 8 (by decide)
      (sixthPolicy n e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ)) N cap w z s hfront
  intro p hp
  rw [hremaining] at hp
  exact (mem_roughPrimeUniverse_prime hp).pos

/-- The low-envelope occurrence is arithmetically zero for BOTH
original ordinary continuations. An empty geometric set is not used
to discard an arithmetic contribution. -/
theorem owned_highQ_saving_zero_of_carrier_envelope
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (hbounded : carrierEnvelope N cap X w s) :
    ordinarySaving n e q om N cap w L (highQTest X F) c s = 0 := by
  have hpositive :=
    owned_remaining_positive delta n e q om N cap w z c s hs
  have hsmall : ∀ a ∈ actualSmallRosserSupport N cap w,
      a * (s.selectedPrefix.prod * s.remaining.prod) ≤ X := hbounded
  have hold := signedTest_highQ_zero_of_carrier_envelope
    (ordinaryParityRosserPolicy false
      ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
    N cap X w L F s.selectedPrefix s.remaining s.positive s.mass
    hpositive hsmall
  have hnew := signedTest_highQ_zero_of_carrier_envelope
    (ordinaryParityRosserPolicy false
      ((N : ℝ) ^ (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
    N cap X w L F s.selectedPrefix s.remaining s.positive s.mass
    hpositive hsmall
  unfold ordinarySaving
  rw [hold, hnew, sub_self]

/-- Unchanged occurrence LIST, strict prefix gate first. -/
def forcedHighSource
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (c : Cell) : ℝ :=
  ((((states delta n e q om N cap w z
    (fun _ : ℕ => (1 : ℝ)) c).filter
      (fun s => decide (X < s.selectedPrefix.prod))).map
      (ordinarySaving n e q om N cap w L F c)).sum)

/-- Remaining high-q arithmetic only where neither the forced-full
gate nor the proved-zero carrier gate applies. The entire test is the
original full-q highQTest on the SAME signed ordinary saving. -/
def mixedHighSource
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (c : Cell) : ℝ :=
  (((((states delta n e q om N cap w z
    (fun _ : ℕ => (1 : ℝ)) c).filter
      (fun s => !decide (X < s.selectedPrefix.prod))).filter
      (fun s => !decide (carrierEnvelope N cap X w s))).map
      (ordinarySaving n e q om N cap w L (highQTest X F) c)).sum)

private theorem list_sum_split_bool {α : Type*}
    (xs : List α) (select : α → Bool) (f : α → ℝ) :
    (xs.map f).sum =
      ((xs.filter select).map f).sum +
      ((xs.filter (fun s => !select s)).map f).sum := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
      cases h : select a <;>
        simp [h, ih, add_assoc, add_left_comm, add_comm]

private theorem list_map_sum_zero_of_mem {α : Type*}
    (xs : List α) (f : α → ℝ) :
    (∀ a ∈ xs, f a = 0) → (xs.map f).sum = 0 := by
  induction xs with
  | nil => intro _; simp
  | cons a rest ih =>
      intro h
      have ha : f a = 0 := h a (by simp)
      have hrest : ∀ b ∈ rest, f b = 0 := by
        intro b hb
        exact h b (by simp [hb])
      simp [ha, ih hrest]

/-- Original owned eighth source, with a genuine third arithmetical
class removed because its complete high-q contribution is ZERO.
The two remaining sums preserve all signs and duplicate occurrences. -/
theorem owned_highQ_source_eq_forced_add_mixed
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (c : Cell) :
    ownedSource delta n e q om N cap w z L (highQTest X F) c =
      forcedHighSource delta n e q om N cap w z L X F c +
      mixedHighSource delta n e q om N cap w z L X F c := by
  let xs := states delta n e q om N cap w z
    (fun _ : ℕ => (1 : ℝ)) c
  let big : FirstExitDepthState ℕ → Bool :=
    fun s => decide (X < s.selectedPrefix.prod)
  let low : FirstExitDepthState ℕ → Bool :=
    fun s => decide (carrierEnvelope N cap X w s)
  let f := ordinarySaving n e q om N cap w L (highQTest X F) c
  let g := ordinarySaving n e q om N cap w L F c
  have hfirst := list_sum_split_bool xs big f
  have hsecond := list_sum_split_bool
    (xs.filter (fun s => !big s)) low f
  have hbig : ((xs.filter big).map f).sum =
      ((xs.filter big).map g).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro s hs
    obtain ⟨hxs, hbig⟩ := List.mem_filter.mp hs
    have hstrict : X < s.selectedPrefix.prod :=
      of_decide_eq_true hbig
    exact owned_highQ_saving_eq_full_of_large_prefix
      delta n e q om N cap w z L X F c s hxs hstrict
  have hzero :
      ((((xs.filter (fun s => !big s)).filter low).map f).sum) = 0 := by
    apply list_map_sum_zero_of_mem
    intro s hs
    obtain ⟨hnobig, hlow⟩ := List.mem_filter.mp hs
    have hxs : s ∈ xs := (List.mem_filter.mp hnobig).1
    have henvelope : carrierEnvelope N cap X w s :=
      of_decide_eq_true hlow
    exact owned_highQ_saving_zero_of_carrier_envelope
      delta n e q om N cap w z L X F c s hxs henvelope
  change (xs.map f).sum =
    ((xs.filter big).map g).sum +
    ((((xs.filter (fun s => !big s)).filter
      (fun s => !low s)).map f).sum)
  calc
    (xs.map f).sum =
      ((xs.filter big).map f).sum +
      ((xs.filter (fun s => !big s)).map f).sum := hfirst
    _ = ((xs.filter big).map g).sum +
        ((((xs.filter (fun s => !big s)).filter
          (fun s => !low s)).map f).sum) := by
      rw [hsecond, hbig, hzero]
      ring

/-- The complete original sixth-to-eighth high-q physical difference
now has only forced-full occurrences and genuinely undecided occurrences.
This is a finite equality, NOT an asymptotic bound and NOT a PP licence. -/
theorem full87_highQ_gain_forced_plus_mixed
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    physical (sixthPolicy n e q om (N : ℝ)) N cap w z L
        (highQTest X F) -
      physical (policy delta n e q om (N : ℝ)) N cap w z L
        (highQTest X F) =
      (∑ c : Cell, forcedHighSource delta n e q om N cap w z L X F c) +
      (∑ c : Cell, mixedHighSource delta n e q om N cap w z L X F c) := by
  rw [full87_high_q_gain_eq_owned_sources]
  calc
    (∑ c : Cell, ownedSource delta n e q om N cap w z L
        (highQTest X F) c) =
      ∑ c : Cell,
        (forcedHighSource delta n e q om N cap w z L X F c +
         mixedHighSource delta n e q om N cap w z L X F c) := by
      apply Finset.sum_congr rfl
      intro c _
      exact owned_highQ_source_eq_forced_add_mixed
        delta n e q om N cap w z L X F c
    _ = _ := Finset.sum_add_distrib

end
end ImbalancedChen.P4AOriginalFull87HighQCarrierTriage
