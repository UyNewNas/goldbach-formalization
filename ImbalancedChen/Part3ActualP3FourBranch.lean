import ImbalancedChen.Part3ActualP3LabelledReindex

/-!
SOURCE ONLY / UNCOMPILED / HOLD.
The future import maps exactly to source a998dedd, not an admitted module.
Every original physical label carries all four signed branches. Both original
row gates and the signed resonance mask are kept. In particular, a zero real
projection product is NOT a licence to remove each of its complex branches.
No activity, phase identity, norm estimate or row energy is a premise.
-/

noncomputable section

namespace ImbalancedChen.Part3.ActualP3FourBranchSourceOnly

open Classical Finset ActualP3LabelledReindexSourceOnly
open scoped BigOperators

/-- Each Bool says whether its original signed frequency is negated. -/
abbrev Branch := Bool × Bool

def branches : Finset Branch := {false, true} ×ˢ {false, true}

def signedFrequency (negate : Bool) (h : ℤ) : ℤ :=
  if negate then -h else h

/-- BOTH literal original row gates; no original-product activity condition. -/
def pairedGate (o : Outer) (u v : ℕ × ℤ) : Prop :=
  ((o.2.1.1 * u.1).gcd (o.2.1.2.1 * o.2.1.2.2) = o.2.2 ∧
    ComplexCRT.Compatible (o.1.1 * (o.2.1.1 * u.1))
      (o.1.1 * (o.2.1.2.1 * o.2.1.2.2)) o.1.2.1 o.1.2.2) ∧
  ((o.2.1.1 * v.1).gcd (o.2.1.2.1 * o.2.1.2.2) = o.2.2 ∧
    ComplexCRT.Compatible (o.1.1 * (o.2.1.1 * v.1))
      (o.1.1 * (o.2.1.2.1 * o.2.1.2.2)) o.1.2.1 o.1.2.2)

/-- The exact signed complex branch, with the two original gates retained.
The conjugation pattern is intentionally different in its second factor. -/
def branchRowTerm (d : MediumAtom) (Z : ℝ) (o : Outer)
    (u v : ℕ × ℤ) (e : Branch) : ℂ :=
  let p := o.1.1
  let N1 := o.1.2.1
  let N2 := o.1.2.2
  let r := o.2.1.1
  let w := o.2.1.2.1 * o.2.1.2.2
  let alpha := SharedGeneralDRowAdapter.amplitude d Z p r u.1 w u.2
  let beta := SharedGeneralDRowAdapter.amplitude d Z p r v.1 w v.2
  if pairedGate o u v then
    (d.gamma2 u.1 * star (d.gamma2 v.1)) / 4 *
      ((if e.1 then star alpha else alpha) *
        (if e.2 then beta else star beta) *
        SharedGeneralDRowAdapter.packet p r u.1 v.1 w N1 N2 d.residue
          (signedFrequency e.1 u.2) (signedFrequency e.2 v.2))
  else 0

/-- Full physical summand: unchanged outer weights and ORIGINAL resonance. -/
def guardedBranchTerm (d : MediumAtom) (Z Ybeta Ysupport : ℝ)
    (resonant : Bool) (l : Label) (e : Branch) : ℂ :=
  d.smallCoreSquaredOuterCoefficient Ybeta Ysupport l.1 *
    (if decide (l.2.1.2 * (l.2.2.1 : ℤ) = l.2.2.2 * (l.2.1.1 : ℤ) ∨
        l.2.1.2 * (l.2.2.1 : ℤ) = -(l.2.2.2 * (l.2.1.1 : ℤ))) = resonant then
      branchRowTerm d Z l.1 l.2.1 l.2.2 e
    else 0)

/-- Exact original real-projection product equals the sum of its four signed
complex branches. There is no nonzero-product or individual-branch premise. -/
theorem row_pair_eq_four_branches (d : MediumAtom) (Z : ℝ)
    (o : Outer) (u v : ℕ × ℤ)
    (hp : 0 < o.1.1) (hr : 0 < o.2.1.1)
    (hs : 0 < u.1) (hs' : 0 < v.1)
    (hw : 0 < o.2.1.2.1 * o.2.1.2.2)
    (hN1 : 0 < o.1.2.1) (hN2 : 0 < o.1.2.2) :
    d.smallCoreSquaredRowTerm Z o u * star (d.smallCoreSquaredRowTerm Z o v) =
      ∑ e ∈ branches, branchRowTerm d Z o u v e := by
  rw [d.smallCoreSquaredRowTerm_pair_packet Z o u v hp hr hs hs' hw hN1 hN2]
  unfold MediumAtom.smallCoreSquaredPairedPacketTerm
  dsimp only
  split_ifs with hraw
  · have hg : pairedGate o u v := hraw
    simp [branches, Finset.sum_product, branchRowTerm, signedFrequency, hg]
    ring
  · have hg : ¬ pairedGate o u v := hraw
    simp [branches, branchRowTerm, hg]

/-- Exact full original outer/block sum, with all four branches attached to
EACH original label. This is not an image quotient or a new Cartesian union. -/
theorem actual_block_sum_eq_labelled_four_branches (d : MediumAtom)
    (Z Ybeta Ysupport : ℝ) (resonant : Bool)
    (hU : 1 ≤ d.U) (hQ1 : 1 ≤ d.Q1) (hQ2 : 1 ≤ d.Q2) (hQ3 : 1 ≤ d.Q3) :
    (∑ o ∈ d.smallCoreSquaredOuterCarrier,
      d.smallCoreSquaredOuterCoefficient Ybeta Ysupport o *
        d.smallCoreSquaredBlock Z resonant o) =
      ∑ l ∈ carrier d Z, ∑ e ∈ branches,
        guardedBranchTerm d Z Ybeta Ysupport resonant l e := by
  have hflat :
      (∑ o ∈ d.smallCoreSquaredOuterCarrier,
        d.smallCoreSquaredOuterCoefficient Ybeta Ysupport o *
          d.smallCoreSquaredBlock Z resonant o) =
        ∑ l ∈ carrier d Z, term d Z Ybeta Ysupport resonant l := by
    unfold carrier
    rw [Finset.sum_sigma]
    simp only [term, MediumAtom.smallCoreSquaredBlock,
      Finset.sum_product, Finset.mul_sum]
  rw [hflat]
  apply Finset.sum_congr rfl
  intro l hl
  rcases l with ⟨o, u, v⟩
  unfold carrier at hl
  obtain ⟨ho, huv⟩ := Finset.mem_sigma.mp hl
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
  have factor_pos {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
      (hn : n ∈ factorCarrier Q) : 0 < n := by
    have hlo := (Finset.mem_Icc.mp hn).1
    have hceil : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
    omega
  unfold MediumAtom.smallCoreSquaredOuterCarrier at ho
  dsimp only at ho
  obtain ⟨hpN, hTail⟩ := Finset.mem_product.mp ho
  have hpMem := (Finset.mem_product.mp (Finset.mem_filter.mp hpN).1).1
  have hNs := (Finset.mem_product.mp (Finset.mem_filter.mp hpN).1).2
  have hN1Mem := (Finset.mem_product.mp hNs).1
  have hN2Mem := (Finset.mem_product.mp hNs).2
  change o.1.2.1 ∈ factorCarrier d.U at hN1Mem
  change o.1.2.2 ∈ factorCarrier d.U at hN2Mem
  have hp : 0 < o.1.1 := factor_pos hQ1 (Finset.mem_filter.mp hpMem).1
  have hN1 : 0 < o.1.2.1 := factor_pos hU hN1Mem
  have hN2 : 0 < o.1.2.2 := factor_pos hU hN2Mem
  obtain ⟨t, ht, hImage⟩ := Finset.mem_biUnion.mp hTail
  obtain ⟨D, _hD, he⟩ := Finset.mem_image.mp hImage
  have heTail : t = o.2.1 := congrArg Prod.fst he
  rw [heTail] at ht
  have hr : 0 < o.2.1.1 := factor_pos hQ3 (Finset.mem_product.mp ht).1
  have hr' := factor_pos hQ3 (Finset.mem_product.mp (Finset.mem_product.mp ht).2).1
  have hs0 := factor_pos hQ2 (Finset.mem_product.mp (Finset.mem_product.mp ht).2).2
  have hw : 0 < o.2.1.2.1 * o.2.1.2.2 := Nat.mul_pos hr' hs0
  have hs : 0 < u.1 := factor_pos hQ2 (Finset.mem_product.mp hu).1
  have hs' : 0 < v.1 := factor_pos hQ2 (Finset.mem_product.mp hv).1
  have hrow := row_pair_eq_four_branches d Z o u v hp hr hs hs' hw hN1 hN2
  unfold term guardedBranchTerm
  dsimp only
  by_cases hres : decide (u.2 * (v.1 : ℤ) = v.2 * (u.1 : ℤ) ∨
      u.2 * (v.1 : ℤ) = -(v.2 * (u.1 : ℤ))) = resonant
  · simp only [if_pos hres]
    rw [hrow, Finset.mul_sum]
  · simp only [if_neg hres, mul_zero, Finset.sum_const_zero]

end ImbalancedChen.Part3.ActualP3FourBranchSourceOnly
