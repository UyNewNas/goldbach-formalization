import ImbalancedChen.Part3SharedFirstFactorGeneralDRowAdapter
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
SOURCE ONLY / UNCOMPILED / HOLD. Concrete original P3 labels, not a free weight.
The sum below keeps the original signed resonance decision, both row gates,
outer coefficient and real projection. The imported actual adapter retains
all four root/slow/CRT branches and complex Poisson amplitudes. No image of b
is substituted for the original labels, and no independent b window is claimed.
This is finite c/residue regrouping and active-pair unit licensing only.
-/

noncomputable section

namespace ImbalancedChen.Part3.ActualP3LabelledReindexSourceOnly

open Classical Finset
open scoped BigOperators

abbrev Outer := (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ)
abbrev Label := (_o : Outer) × ((ℕ × ℤ) × (ℕ × ℤ))

/-- Every original outer label carries its OWN original ordered inner pair. -/
def carrier (d : MediumAtom) (Z : ℝ) : Finset Label :=
  d.smallCoreSquaredOuterCarrier.sigma (fun o =>
    d.smallCoreSquaredInnerCarrier Z o ×ˢ d.smallCoreSquaredInnerCarrier Z o)

/-- The actual packet c=n1*w0, using the first row's constructed gcd. -/
def packetC (l : Label) : ℕ :=
  let o := l.1
  let w := o.2.1.2.1 * o.2.1.2.2
  let D := (o.2.1.1 * l.2.1.1).gcd w
  let g := o.1.2.1.gcd o.1.2.2
  CanonicalReciprocalData.coprimePart (o.1.2.1 / g) g * (w / D)

def packetB (l : Label) : ℕ :=
  let o := l.1
  let w := o.2.1.2.1 * o.2.1.2.2
  let D := (o.2.1.1 * l.2.1.1).gcd w
  let g := o.1.2.1.gcd o.1.2.2
  (g * CanonicalReciprocalData.supportedPart (o.1.2.1 / g) g) *
    (o.1.2.2 / g) * (o.2.1.1 / o.2.1.1.gcd D)

def packetZ (l : Label) : ℕ :=
  let o := l.1
  let D := (o.2.1.1 * l.2.1.1).gcd (o.2.1.2.1 * o.2.1.2.2)
  let q := D / o.2.1.1.gcd D
  (l.2.1.1 / q) * (l.2.2.1 / q)

/-- Nat modulo avoids identifying residues from different moduli. Inactive
zero-modulus labels are not deleted; the unit theorem applies to active pairs. -/
def key (l : Label) : ℕ × ℕ := (packetC l, packetB l % packetC l)

/-- Literal original summand; no freely supplied coefficient or phase. -/
def term (d : MediumAtom) (Z Ybeta Ysupport : ℝ) (resonant : Bool)
    (l : Label) : ℂ :=
  d.smallCoreSquaredOuterCoefficient Ybeta Ysupport l.1 *
    (if decide (l.2.1.2 * (l.2.2.1 : ℤ) = l.2.2.2 * (l.2.1.1 : ℤ) ∨
        l.2.1.2 * (l.2.2.1 : ℤ) = -(l.2.2.2 * (l.2.1.1 : ℤ))) = resonant then
      d.smallCoreSquaredRowTerm Z l.1 l.2.1 *
        star (d.smallCoreSquaredRowTerm Z l.1 l.2.2)
    else 0)

/-- Exact original outer/block sum regrouped by its constructed c and b mod c.
All repeated physical rows and every decomposition label remain in the fibre. -/
theorem actual_block_sum_eq_c_residue_fibres (d : MediumAtom)
    (Z Ybeta Ysupport : ℝ) (resonant : Bool) :
    (∑ o ∈ d.smallCoreSquaredOuterCarrier,
      d.smallCoreSquaredOuterCoefficient Ybeta Ysupport o *
        d.smallCoreSquaredBlock Z resonant o) =
      ∑ k ∈ (carrier d Z).image key,
        ∑ l ∈ (carrier d Z).filter (fun l => key l = k),
          term d Z Ybeta Ysupport resonant l := by
  have hflat :
      (∑ o ∈ d.smallCoreSquaredOuterCarrier,
        d.smallCoreSquaredOuterCoefficient Ybeta Ysupport o *
          d.smallCoreSquaredBlock Z resonant o) =
        ∑ l ∈ carrier d Z, term d Z Ybeta Ysupport resonant l := by
    unfold carrier
    rw [Finset.sum_sigma]
    simp only [term, MediumAtom.smallCoreSquaredBlock,
      Finset.sum_product, Finset.mul_sum]
  exact hflat.trans
    (Finset.sum_fiberwise_of_maps_to
      (s := carrier d Z) (t := (carrier d Z).image key) (g := key)
      (fun l hl => Finset.mem_image_of_mem key hl)
      (term d Z Ybeta Ysupport resonant)).symm

/-- Existing arithmetic units on every active ORIGINAL labelled pair.
Activity is the original guarded row product, not a caller unit assumption.
The four branch signs change frequencies, never b,c,z or these licences. -/
theorem actual_active_pair_units (d : MediumAtom) (Z : ℝ)
    (hU : 1 ≤ d.U) (hQ1 : 1 ≤ d.Q1) (hQ2 : 1 ≤ d.Q2) (hQ3 : 1 ≤ d.Q3)
    (l : Label) (hl : l ∈ carrier d Z)
    (hactive : d.smallCoreSquaredRowTerm Z l.1 l.2.1 *
      star (d.smallCoreSquaredRowTerm Z l.1 l.2.2) ≠ 0) :
    0 < packetC l ∧ (packetB l).Coprime (packetC l) ∧
      (packetZ l).Coprime (packetC l) := by
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
  let gate (x : ℕ × ℤ) : Prop :=
    (o.2.1.1 * x.1).gcd (o.2.1.2.1 * o.2.1.2.2) = o.2.2 ∧
      ComplexCRT.Compatible (o.1.1 * (o.2.1.1 * x.1))
        (o.1.1 * (o.2.1.2.1 * o.2.1.2.2)) o.1.2.1 o.1.2.2
  have hgu : gate u := by
    by_contra hnot
    have hz : d.smallCoreSquaredRowTerm Z o u = 0 := by
      unfold MediumAtom.smallCoreSquaredRowTerm
      dsimp only
      rw [if_neg hnot]
    exact hactive (by rw [hz, zero_mul])
  have hgv : gate v := by
    by_contra hnot
    have hz : d.smallCoreSquaredRowTerm Z o v = 0 := by
      unfold MediumAtom.smallCoreSquaredRowTerm
      dsimp only
      rw [if_neg hnot]
    exact hactive (by rw [hz, star_zero, mul_zero])
  have hdata := sharedGeneralD_paired_fourier hp hr hs hs' hw hN1 hN2
    hgu.2 hgv.2 (hgv.1.trans hgu.1.symm) d.residue u.2 v.2
  rcases hdata with ⟨_hK, _hA, hc, _hst, _hst', hb, _hroot,
    htA, htA', _hL, _hL', _hphase⟩
  dsimp only [packetC, packetB, packetZ]
  refine ⟨hc, hb, ?_⟩
  exact (htA.of_dvd_right (dvd_mul_left _ _)).mul_left
    (htA'.of_dvd_right (dvd_mul_left _ _))

end ImbalancedChen.Part3.ActualP3LabelledReindexSourceOnly
