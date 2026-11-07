import ImbalancedChen.Part3OriginalS2ReceiverLambdaBinding
import ImbalancedChen.Part3OriginalS2SameGevreyPacket
import Mathlib.Tactic

/-!
Actual individual-window key coefficients BEFORE and AFTER the original
smooth trim. The existing independently built lambdaTrim is recovered on
its actual d window. Full/kept/tail and two-key products are exact; a sum
of independently keyed products is never called a common-key square.
SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
-/

namespace ImbalancedChen.Part3OriginalS2ActualKeyCoefficients

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalS2SmoothYRankinStart
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalS2LambdaDivisorPacket
open ImbalancedChen.Part3OriginalS2ActualBlockPacketBound
open ImbalancedChen.Part3OriginalS2SameGevreyPacket
open ImbalancedChen.Part3OriginalS2ReceiverLambdaBinding
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumOwnedCanonicalReindex20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open Classical Finset
open scoped BigOperators

noncomputable section

def keyPredicate (z : ℝ) (k : Key) (q : ℕ × ℕ) : Prop :=
  owner (strictReceiverCutoff z) q = k

def keyFull (d : MediumAtom) (z : ℝ) (k : Key) (small rough : ℕ) : ℂ :=
  ∑ q ∈ labelSubset d z small rough (keyPredicate z k), d.gamma2 q.1 * d.gamma3 q.2

def keyKept (d : MediumAtom) (x z : ℝ) (k : Key) (small rough : ℕ) : ℂ :=
  ∑ q ∈ labelSubset d z small rough
    (fun q => keyPredicate z k q ∧ individualSmoothWithinY x z q),
      d.gamma2 q.1 * d.gamma3 q.2

def keyTail (d : MediumAtom) (x z : ℝ) (k : Key) (small rough : ℕ) : ℂ :=
  ∑ q ∈ labelSubset d z small rough
    (fun q => keyPredicate z k q ∧ ¬individualSmoothWithinY x z q),
      d.gamma2 q.1 * d.gamma3 q.2

theorem keyFull_eq_kept_add_tail (d : MediumAtom) (x z : ℝ) (k : Key)
    (small rough : ℕ) :
    keyFull d z k small rough = keyKept d x z k small rough + keyTail d x z k small rough := by
  let S := labelSubset d z small rough (keyPredicate z k)
  have h := Finset.sum_filter_add_sum_filter_not S
    (individualSmoothWithinY x z) (fun q => d.gamma2 q.1 * d.gamma3 q.2)
  simpa only [keyFull, keyKept, keyTail, labelSubset, S,
    Finset.filter_filter, and_assoc] using h.symm

theorem keyKeptCarrier_eq_ownedSlice
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (x z : ℝ) (hz : 0 ≤ z) (k : Key) (small rough : ℕ) :
    labelSubset d z small rough
      (fun q => keyPredicate z k q ∧ individualSmoothWithinY x z q) =
      ownedSlice d (strictReceiverCutoff z) (roughY x) k small rough := by
  have hS : labelSubset d z small rough
      (fun q => keyPredicate z k q ∧ individualSmoothWithinY x z q) =
      (receiverKeptSlice d x z small rough).filter (keyPredicate z k) := by
    rw [receiverKeptSlice_eq_original hd x z hz small rough]
    ext q
    simp only [labelSubset, Finset.mem_filter, and_assoc, and_left_comm, and_comm]
  rw [hS]
  ext q
  simp only [receiverKeptSlice, ownedSlice, ownedModuli, keyPredicate,
    Finset.mem_filter, and_assoc, and_left_comm, and_comm]

/-- The actual canonical lambdaTrim keeps every individual s,t,u,v
window through owner=k; it is not a whole-Lambda surrogate. -/
theorem keyKept_eq_actual_lambdaTrim
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (x z : ℝ) (hz : 0 ≤ z) (k : Key) (small rough : ℕ)
    (hsmall : small ∈ dyadicWindow k.d) :
    keyKept d x z k small rough =
      lambdaTrim d (strictReceiverCutoff z) (roughY x) k small rough := by
  unfold keyKept
  rw [keyKeptCarrier_eq_ownedSlice hd x z hz k small rough]
  exact (lambdaTrim_eq_ownedSlice d (strictReceiverCutoff z) (roughY x)
    k small rough hsmall).symm

theorem keyFull_norm_le_tau
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (z : ℝ) (k : Key) (small rough : ℕ) (hp : 0 < small * rough) :
    ‖keyFull d z k small rough‖ ≤ ((small * rough).divisors.card : ℝ) :=
  labelSubset_gamma_norm_le_tau hd z small rough (keyPredicate z k) hp

theorem keyKept_norm_le_tau
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (x z : ℝ) (k : Key) (small rough : ℕ) (hp : 0 < small * rough) :
    ‖keyKept d x z k small rough‖ ≤ ((small * rough).divisors.card : ℝ) :=
  labelSubset_gamma_norm_le_tau hd z small rough
    (fun q => keyPredicate z k q ∧ individualSmoothWithinY x z q) hp

theorem keyTail_norm_le_tau
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (x z : ℝ) (k : Key) (small rough : ℕ) (hp : 0 < small * rough) :
    ‖keyTail d x z k small rough‖ ≤ ((small * rough).divisors.card : ℝ) :=
  labelSubset_gamma_norm_le_tau hd z small rough
    (fun q => keyPredicate z k q ∧ ¬individualSmoothWithinY x z q) hp

/-- Complex cancellation is not used to infer support of a different
coefficient: the witness comes from this very keyTail finite sum. -/
theorem keyTail_nonzero_witness (d : MediumAtom) (x z : ℝ) (k : Key)
    (small rough : ℕ) (hne : keyTail d x z k small rough ≠ 0) :
    ∃ q ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
      labelDW z q = (small, rough) ∧ keyPredicate z k q ∧
      ¬individualSmoothWithinY x z q ∧ d.gamma2 q.1 * d.gamma3 q.2 ≠ 0 := by
  have hw : ∃ q ∈ labelSubset d z small rough
      (fun q => keyPredicate z k q ∧ ¬individualSmoothWithinY x z q),
      d.gamma2 q.1 * d.gamma3 q.2 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Finset.sum_eq_zero (fun q hq => h q hq))
  obtain ⟨q, hq, hγ⟩ := hw
  obtain ⟨hp, hl, hk, ht⟩ := Finset.mem_filter.mp hq
  exact ⟨q, hp, hl, hk, ht, hγ⟩

theorem keyFull_nonzero_coprime
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (z : ℝ) (k : Key) (small rough : ℕ)
    (hne : keyFull d z k small rough ≠ 0) :
    Nat.Coprime (small * rough) d.residue.natAbs :=
  nonzero_labelSubset_coprime hd z small rough (keyPredicate z k) hne

/-- Both sides may have independent key labels. The common-key case is
obtained by kL=kR, without deleting any off-diagonal ownership terms. -/
theorem key_pair_four_way (d : MediumAtom) (x z : ℝ)
    (kL kR : Key) (small r s : ℕ) :
    keyFull d z kL small r * star (keyFull d z kR small s) =
      keyKept d x z kL small r * star (keyKept d x z kR small s) +
      keyTail d x z kL small r * star (keyKept d x z kR small s) +
      keyKept d x z kL small r * star (keyTail d x z kR small s) +
      keyTail d x z kL small r * star (keyTail d x z kR small s) := by
  rw [keyFull_eq_kept_add_tail, keyFull_eq_kept_add_tail, star_add]
  ring

theorem key_samePsiTerm_four_way (d : MediumAtom) (x z : ℝ)
    (kL kR : Key) (t : S2Index) :
    samePsiTerm d (keyFull d z kL) (keyFull d z kR) t =
      samePsiTerm d (keyKept d x z kL) (keyKept d x z kR) t +
      samePsiTerm d (keyTail d x z kL) (keyKept d x z kR) t +
      samePsiTerm d (keyKept d x z kL) (keyTail d x z kR) t +
      samePsiTerm d (keyTail d x z kL) (keyTail d x z kR) t := by
  unfold samePsiTerm s2TermWithM
  by_cases hg : Nat.Coprime t.2.2.1.1 (t.1.1 * t.1.2 * t.2.1.1) ∧
      Nat.Coprime t.2.2.1.2 (t.1.1 * t.1.2 * t.2.1.2) ∧
      Int.ModEq (t.1.1 * t.1.2 * t.2.1.1)
        (((t.2.2.2 * t.2.2.1.1 : ℕ) : ℤ)) d.residue
  · simp only [if_pos hg]
    rw [keyFull_eq_kept_add_tail, keyFull_eq_kept_add_tail, star_add]
    ring
  · simp [hg]

end
end ImbalancedChen.Part3OriginalS2ActualKeyCoefficients
