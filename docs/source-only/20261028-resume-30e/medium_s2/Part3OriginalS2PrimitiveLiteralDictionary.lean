import ImbalancedChen.Part3OriginalS2ActualKeyCoefficients
import ImbalancedChen.Part3MediumLiteralS3Stages
import Mathlib.Tactic

/-!
Consume the independently defined actual primitive paired S2. The exact
mean's m gate is reduced only after the deleted progression is known
primitive. Single-zero and other-rough-gate corrections are separate
finite sums. All common-key windows, actual paperPsi weights and both
physical moduli are retained. SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
-/

namespace ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalS2SameGevreyPacket
open ImbalancedChen.Part3OriginalS2ActualKeyCoefficients
open ImbalancedChen.Part3.MediumPrimitivePsiSource20261028
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumLiteralS3Deleted20261028
open ImbalancedChen.Part3.MediumDeletedIndicatorShift20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.OriginalGevreySharedRowDictionary20261028
open ImbalancedChen.Part3OriginalS2ActualPsiWeightAdapter
open Classical Finset
open scoped BigOperators

noncomputable section

def canonicalIndex (t : PairIndex) : S2Index :=
  ⟨(t.1.1, t.1.2.1), ((t.2.1.1, t.2.2.1), ((t.2.1.2, t.2.2.2), t.1.2.2))⟩

def exactFirstProduct (d : MediumAtom) (t : PairIndex) : Prop :=
  (((t.2.1.2 * t.1.2.2 : ℕ) : ℤ)) = d.residue

def otherRoughGate (t : PairIndex) : Prop := Nat.Coprime t.1.2.2 t.2.2.1

def restoredTerm (d : MediumAtom) (z y : ℝ) (k : Key) (t : PairIndex) : ℂ :=
  samePsiTerm d (lambdaTrim d z y k) (lambdaTrim d z y k) (canonicalIndex t)

private theorem coprime_of_product_congruent {a : ℤ} {l n m : ℕ}
    (ha : Nat.Coprime l a.natAbs) (h : Int.ModEq l (((n * m : ℕ) : ℤ)) a) :
    Nat.Coprime n l ∧ Nat.Coprime m l := by
  have hag : Int.gcd a l = 1 := by simpa [Int.gcd, Nat.gcd_comm] using ha
  have hrem : (((n * m : ℕ) : ℤ)) % (l : ℤ) = a % (l : ℤ) := h
  have hprod : Int.gcd (((n * m : ℕ) : ℤ)) l = 1 := by
    rw [← Int.gcd_emod (((n * m : ℕ) : ℤ)) l, hrem, Int.gcd_emod, hag]
  have hnm : Nat.Coprime (n * m) l := by simpa [Int.gcd] using hprod
  exact Nat.coprime_mul_iff_left.mp hnm

/-- This is an equality with the actual independently defined S2Term.
It does not replace the original exact coprime mean by an unrelated gate. -/
theorem actualS2Term_eq_deleted_rough_gate
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key)
    (q small r s n₁ n₂ m : ℕ) (hq : Nat.Coprime q d.residue.natAbs) :
    S2Term d z y k ((q, small, m), (r, n₁), (s, n₂)) =
      if ¬exactFirstProduct d ((q, small, m), (r, n₁), (s, n₂)) ∧
          otherRoughGate ((q, small, m), (r, n₁), (s, n₂)) then
        restoredTerm d z y k ((q, small, m), (r, n₁), (s, n₂)) else 0 := by
  by_cases hλ : lambdaTrim d z y k small r = 0
  · simp [S2Term, pairCoefficient, hλ, restoredTerm, canonicalIndex,
      samePsiTerm, s2TermWithM]
  · have hpair := lambdaTrim_support_residue_product hd z y k small r hλ
    have hprimitive : Nat.Coprime (q * small * r) d.residue.natAbs := by
      simpa only [Nat.mul_assoc] using Nat.coprime_mul_iff_left.mpr ⟨hq, hpair⟩
    by_cases hz : (((n₁ * m : ℕ) : ℤ)) = d.residue
    · simp [S2Term, pairCoefficient, firstDeleted, oldIndex, deletedIndicator,
        exactFirstProduct, hz]
    · by_cases hc : Int.ModEq (q * small * r) (((n₁ * m : ℕ) : ℤ)) d.residue
      · obtain ⟨hn₁, hm⟩ := coprime_of_product_congruent hprimitive hc
        have hmbase : Nat.Coprime m (q * small) := (Nat.coprime_mul_iff_right.mp hm).1
        have hmean : Nat.Coprime (n₂ * m) (q * small * s) ↔
            Nat.Coprime n₂ (q * small * s) ∧ Nat.Coprime m s := by
          constructor
          · intro h
            obtain ⟨hn, hmright⟩ := Nat.coprime_mul_iff_left.mp h
            exact ⟨hn, (Nat.coprime_mul_iff_right.mp hmright).2⟩
          · rintro ⟨hn, hms⟩
            exact Nat.coprime_mul_iff_left.mpr
              ⟨hn, Nat.coprime_mul_iff_right.mpr ⟨hmbase, hms⟩⟩
        have hcong : (((n₁ * m : ℕ) : ℤ)) % ((q * small * r : ℕ) : ℤ) =
            d.residue % ((q * small * r : ℕ) : ℤ) := hc
        have hcomm : m * n₁ = n₁ * m := Nat.mul_comm _ _
        by_cases hn₂ : Nat.Coprime n₂ (q * small * s) <;>
          by_cases hms : Nat.Coprime m s <;>
          simp [S2Term, pairCoefficient, firstDeleted, oldIndex, deletedIndicator,
            literalMeanKernel, restoredTerm, canonicalIndex, samePsiTerm, s2TermWithM,
            exactFirstProduct, otherRoughGate, jointPsi, paperQWeight, paperMWeight,
            actualPsiQWeight, actualPsiMWeight, hz, hcong, hc, hcomm,
            hn₁, hmean, hn₂, hms] <;> ring
      · have hcong : ¬((((n₁ * m : ℕ) : ℤ)) % ((q * small * r : ℕ) : ℤ) =
            d.residue % ((q * small * r : ℕ) : ℤ)) := hc
        have hcomm : m * n₁ = n₁ * m := Nat.mul_comm _ _
        simp [S2Term, pairCoefficient, firstDeleted, oldIndex, deletedIndicator,
          restoredTerm, canonicalIndex, samePsiTerm, s2TermWithM,
          exactFirstProduct, hz, hcong, hc, hcomm]

theorem actualS2Term_eq_deleted_rough_gate_on_carrier
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key)
    (t : PairIndex) (ht : t ∈ pairedCarrier d k) :
    S2Term d z y k t =
      if ¬exactFirstProduct d t ∧ otherRoughGate t then restoredTerm d z y k t else 0 := by
  have hq := (Finset.mem_filter.mp (Finset.mem_product.mp ht).1).2
  rcases t with ⟨⟨q, small, m⟩, ⟨r, n₁⟩, ⟨s, n₂⟩⟩
  exact actualS2Term_eq_deleted_rough_gate hd z y k q small r s n₁ n₂ m hq

def restoredSum (d : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ t ∈ pairedCarrier d k, restoredTerm d z y k t

def singleZeroCorrection (d : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ t ∈ pairedCarrier d k,
    if exactFirstProduct d t then restoredTerm d z y k t else 0

def otherRoughCorrection (d : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ t ∈ pairedCarrier d k,
    if ¬exactFirstProduct d t ∧ ¬otherRoughGate t then restoredTerm d z y k t else 0

/-- Exact order: keep the deletion during rough-gate removal, then restore
the single zero. Neither correction is an unnamed whole-S2 residual. -/
theorem restoredSum_eq_actualS2_add_named_corrections
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key) :
    restoredSum d z y k =
      (∑ t ∈ pairedCarrier d k, S2Term d z y k t) +
        otherRoughCorrection d z y k + singleZeroCorrection d z y k := by
  unfold restoredSum otherRoughCorrection singleZeroCorrection
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [actualS2Term_eq_deleted_rough_gate_on_carrier hd z y k t ht]
  by_cases hz : exactFirstProduct d t <;>
    by_cases hs : otherRoughGate t <;> simp [hz, hs]

theorem actual_preliminary_S2_real_identity
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key) :
    (restoredSum d z y k).re = primitiveS2 d z y k +
      (otherRoughCorrection d z y k).re + (singleZeroCorrection d z y k).re := by
  rw [restoredSum_eq_actualS2_add_named_corrections hd z y k,
    Complex.add_re, Complex.add_re, ← primitiveS2_eq_paired_re]

theorem paired_small_in_key (d : MediumAtom) (k : Key) (t : PairIndex)
    (ht : t ∈ pairedCarrier d k) : t.1.2.1 ∈ dyadicWindow k.d := by
  have ho := (Finset.mem_product.mp ht).1
  have hs := (Finset.mem_filter.mp ho).1
  exact (Finset.mem_product.mp (Finset.mem_product.mp hs).2).1

/-- Consume the independent per-key receiver/trim binder on the actual
preliminary carrier. No sum of different keys is silently squared. -/
theorem restoredTerm_receiver_eq_actual_keyKept
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (x z : ℝ) (hz : 0 ≤ z)
    (k : Key) (t : PairIndex) (ht : t ∈ pairedCarrier d k) :
    restoredTerm d (strictReceiverCutoff z) (roughY x) k t =
      samePsiTerm d (keyKept d x z k) (keyKept d x z k) (canonicalIndex t) := by
  have hsmall := paired_small_in_key d k t ht
  unfold restoredTerm samePsiTerm s2TermWithM canonicalIndex
  rw [← keyKept_eq_actual_lambdaTrim hd x z hz k t.1.2.1 t.2.1.1 hsmall,
    ← keyKept_eq_actual_lambdaTrim hd x z hz k t.1.2.1 t.2.2.1 hsmall]

def keyFullRestoredSum (d : MediumAtom) (x z : ℝ) (k : Key) : ℂ :=
  ∑ t ∈ pairedCarrier d k,
    samePsiTerm d (keyFull d z k) (keyFull d z k) (canonicalIndex t)

def keyMixedTailSum (d : MediumAtom) (x z : ℝ) (k : Key) : ℂ :=
  ∑ t ∈ pairedCarrier d k,
    (samePsiTerm d (keyTail d x z k) (keyKept d x z k) (canonicalIndex t) +
      samePsiTerm d (keyKept d x z k) (keyTail d x z k) (canonicalIndex t) +
      samePsiTerm d (keyTail d x z k) (keyTail d x z k) (canonicalIndex t))

/-- Full/kept comparison on the ACTUAL primitive smooth-q carrier.
The common individual-window key remains the same on both coefficient copies. -/
theorem keyFullRestoredSum_eq_actual_kept_add_tail
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (x z : ℝ) (hz : 0 ≤ z) (k : Key) :
    keyFullRestoredSum d x z k =
      restoredSum d (strictReceiverCutoff z) (roughY x) k + keyMixedTailSum d x z k := by
  unfold keyFullRestoredSum restoredSum keyMixedTailSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [restoredTerm_receiver_eq_actual_keyKept hd x z hz k t ht]
  simpa only [add_assoc] using key_samePsiTerm_four_way d x z k k (canonicalIndex t)

/-- The genuine preliminary S2 remains accompanied by BOTH named
corrections and all three smooth-tail ownership terms. No zero is discarded. -/
theorem actual_preliminary_S2_receiver_full_identity
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (x z : ℝ) (hz : 0 ≤ z) (k : Key) :
    (keyFullRestoredSum d x z k).re =
      primitiveS2 d (strictReceiverCutoff z) (roughY x) k +
        (otherRoughCorrection d (strictReceiverCutoff z) (roughY x) k).re +
        (singleZeroCorrection d (strictReceiverCutoff z) (roughY x) k).re +
        (keyMixedTailSum d x z k).re := by
  rw [keyFullRestoredSum_eq_actual_kept_add_tail hd x z hz k, Complex.add_re,
    actual_preliminary_S2_real_identity hd]

end
end ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
