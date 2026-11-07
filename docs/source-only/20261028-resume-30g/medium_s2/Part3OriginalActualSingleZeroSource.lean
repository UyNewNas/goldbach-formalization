import ImbalancedChen.Part3OriginalS2ActualCenteringLedger
import ImbalancedChen.Part3MediumSingleZeroFiberCost
import ImbalancedChen.Part3MediumLiteralS3DeletedCarrier
import ImbalancedChen.Part3PolynomialResidueDivisorBound
import Mathlib.Tactic

/-! The genuine E single-zero terms on the actual primitive paired
carrier. Active terms enter the original NONZERO-shift divisor fibre.
No replacement FactorData coefficient or assumed final restoration bound
is introduced. SOURCE ONLY / UNCOMPILED / ZERO CREDIT. -/

namespace ImbalancedChen.Part3OriginalActualSingleZeroSource

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalS2ActualTailTransfer
open ImbalancedChen.Part3OriginalS2ActualKeyCoefficients
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open ImbalancedChen.Part3OriginalS2NativePsiGeometry
open ImbalancedChen.Part3.MediumPrimitivePsiSource20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumLiteralS3Deleted20261028
open ImbalancedChen.Part3.MediumDeletedIndicatorShift20261028
open ImbalancedChen.Part3.MediumSingleZeroFiber20261028
open ImbalancedChen.Part3.MediumNativePrincipalSource20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.OriginalGevreyFinalPsi20261028
open ImbalancedChen.Part3.OriginalGevreySharedRowDictionary20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3.OriginalMediumS1SeparatedDivisorMean
open Classical Finset
open scoped BigOperators

noncomputable section

def actualFirstZero (d : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ t ∈ offDiagonalCarrier d k, firstZeroTerm d z y k t

def actualSecondZero (d : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ t ∈ offDiagonalCarrier d k, secondZeroTerm d z y k t

def firstActive (d : MediumAtom) (z y : ℝ) (k : Key) : Finset PairIndex :=
  (offDiagonalCarrier d k).filter (fun t => firstZeroTerm d z y k t ≠ 0)

theorem actualFirstZero_eq_active (d : MediumAtom) (z y : ℝ) (k : Key) :
    actualFirstZero d z y k = ∑ t ∈ firstActive d z y k, firstZeroTerm d z y k t := by
  unfold actualFirstZero firstActive
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro t ht hn
  by_contra hne
  exact hn (Finset.mem_filter.mpr ⟨ht, hne⟩)

theorem firstActive_data
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key)
    (t : PairIndex) (ht : t ∈ firstActive d z y k) :
    t ∈ pairedCarrier d k ∧ (oldIndex t).n1 ≠ (oldIndex t).n2 ∧
      0 < (oldIndex t).m ∧
      ((oldIndex t).n1 * (oldIndex t).m : ℕ) = d.residue.natAbs ∧
      d.residue = (d.residue.natAbs : ℤ) ∧
      (oldIndex t).m.Coprime ((oldIndex t).q * (oldIndex t).d) ∧
      zeroIndicator d.residue (oldIndex t).n1 (oldIndex t).m ≠ 0 ∧
      secondDeleted d.residue (oldIndex t) ≠ 0 := by
  obtain ⟨ht, hne⟩ := Finset.mem_filter.mp ht
  obtain ⟨ht, h12⟩ := Finset.mem_filter.mp ht
  have hzero : zeroIndicator d.residue (oldIndex t).n1 (oldIndex t).m ≠ 0 := by
    intro hz
    exact hne (by simp [firstZeroTerm, hz])
  have hdel : secondDeleted d.residue (oldIndex t) ≠ 0 := by
    intro hz
    exact hne (by simp [firstZeroTerm, hz])
  have hλ : lambdaTrim d z y k (oldIndex t).d (oldIndex t).s ≠ 0 := by
    intro hz
    change lambdaTrim d z y k t.1.2.1 t.2.2.1 = 0 at hz
    exact hne (by simp [firstZeroTerm, pairCoefficient, hz])
  have heq : (((oldIndex t).n1 * (oldIndex t).m : ℕ) : ℤ) = d.residue := by
    by_contra hz
    exact hzero (by simp [zeroIndicator, hz])
  have ha : d.residue = (d.residue.natAbs : ℤ) := by
    rw [← heq]
    simp
  have hprod : (oldIndex t).n1 * (oldIndex t).m = d.residue.natAbs := by
    exact_mod_cast heq.trans ha
  have hq := (Finset.mem_filter.mp (Finset.mem_product.mp ht).1).2
  have hds := (lambdaTrim_support_residue hd z y k (oldIndex t).d (oldIndex t).s hλ).1
  have hbase : ((oldIndex t).q * (oldIndex t).d).Coprime d.residue.natAbs :=
    Nat.coprime_mul_iff_left.mpr ⟨hq, hds⟩
  have hmdiv : (oldIndex t).m ∣ d.residue.natAbs :=
    ⟨(oldIndex t).n1, by rw [← hprod]; ring⟩
  have hmCop := (Nat.Coprime.of_dvd_right hmdiv hbase).symm
  exact ⟨ht, h12, paired_m_positive (zero_lt_one.trans_le hd.2.1) ht,
    hprod, ha, hmCop, hzero, hdel⟩

theorem firstActive_qd_mem_nativeQD
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key)
    (t : PairIndex) (ht : t ∈ firstActive d z y k) :
    ((oldIndex t).q, (oldIndex t).d) ∈ nativeQD d k := by
  have hne := (Finset.mem_filter.mp ht).2
  have hpaired := (firstActive_data hd z y k t ht).1
  have houter := (Finset.mem_product.mp hpaired).1
  have hraw := (Finset.mem_filter.mp houter).1
  have hq := (Finset.mem_product.mp hraw).1
  have hdwin := (Finset.mem_product.mp (Finset.mem_product.mp hraw).2).1
  have hqc := (Finset.mem_filter.mp houter).2
  have hλ : lambdaTrim d z y k (oldIndex t).d (oldIndex t).s ≠ 0 := by
    intro hz
    change lambdaTrim d z y k t.1.2.1 t.2.2.1 = 0 at hz
    exact hne (by simp [firstZeroTerm, pairCoefficient, hz])
  have hdc := (lambdaTrim_support_residue hd z y k (oldIndex t).d (oldIndex t).s hλ).1
  exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hq, hqc⟩,
    Finset.mem_filter.mpr ⟨hdwin, hdc⟩⟩

/-- Directly consume the existing nonzero-shift counting fibre, now at
the independently defined actual firstZeroTerm source. -/
theorem firstActive_mem_existing_fibre
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key)
    (t : PairIndex) (ht : t ∈ firstActive d z y k) :
    ((oldIndex t).n2, (oldIndex t).s) ∈
      firstZeroFiber (Nat.ceil d.U) (Nat.floor (2 * d.U) + 1)
        (oldIndex t).m (oldIndex t).n1 (oldIndex t).q (oldIndex t).d
        d.residue.natAbs (dyadicWindow k.w) := by
  obtain ⟨hpaired, h12, hm, hprod, ha, hcop, hzero, hdel⟩ := firstActive_data hd z y k t ht
  have hij := Finset.mem_product.mp (Finset.mem_product.mp hpaired).2
  have hs := (Finset.mem_product.mp hij.2).1
  have hn₂ := (Finset.mem_product.mp hij.2).2
  have hn₂raw := (Finset.mem_filter.mp hn₂).1
  have hn₂I : (oldIndex t).n2 ∈ Finset.Ico (Nat.ceil d.U) (Nat.floor (2 * d.U) + 1) := by
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp hn₂raw).1, by
      have hh := (Finset.mem_Icc.mp hn₂raw).2
      omega⟩
  exact firstSingleZero_to_existing_fiber ha
    (Finset.mem_filter.mpr ⟨Finset.mem_singleton_self _, hzero, hdel⟩)
    hn₂I hs (Ne.symm h12)

def swapPair (t : PairIndex) : PairIndex := (t.1, (t.2.2, t.2.1))

theorem swapPair_involutive : Function.Involutive swapPair := fun _ => rfl

theorem swapPair_mem_offDiagonal (d : MediumAtom) (k : Key) (t : PairIndex) :
    swapPair t ∈ offDiagonalCarrier d k ↔ t ∈ offDiagonalCarrier d k := by
  simp only [offDiagonalCarrier, pairedCarrier, swapPair, oldIndex,
    Finset.mem_filter, Finset.mem_product, ne_eq]
  tauto

theorem firstZeroTerm_swap (d : MediumAtom) (z y : ℝ) (k : Key) (t : PairIndex) :
    firstZeroTerm d z y k (swapPair t) = star (secondZeroTerm d z y k t) := by
  unfold firstZeroTerm secondZeroTerm pairCoefficient swapPair oldIndex
    firstDeleted secondDeleted zeroIndicator deletedIndicator jointPsi
  split_ifs <;> simp [star_mul, star_star, mul_comm, mul_left_comm, mul_assoc]

/-- The symmetric source has precisely the same norm, on the same
actual off-diagonal carrier. No independently counted second square is used. -/
theorem actualSecondZero_norm_eq_first (d : MediumAtom) (z y : ℝ) (k : Key) :
    ‖actualSecondZero d z y k‖ = ‖actualFirstZero d z y k‖ := by
  have he : actualFirstZero d z y k = star (actualSecondZero d z y k) := by
    unfold actualFirstZero actualSecondZero
    rw [star_sum]
    apply Finset.sum_bij (fun t _ => swapPair t)
    · intro t ht
      exact (swapPair_mem_offDiagonal d k t).mpr ht
    · intro t ht t' ht' heq
      exact swapPair_involutive.injective heq
    · intro t ht
      exact ⟨swapPair t, (swapPair_mem_offDiagonal d k t).mpr ht, rfl⟩
    · intro t ht
      simpa only [swapPair_involutive t] using (firstZeroTerm_swap d z y k (swapPair t))
  rw [he, norm_star]

end
end ImbalancedChen.Part3OriginalActualSingleZeroSource
