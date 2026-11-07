import ImbalancedChen.Part3SharedFirstFactorGeneralDRowAdapter
import ImbalancedChen.Part3SharedFirstFactorSupportedCoreCauchy

/-!
# Actual cleaned supported-carrier consumer of the general-D row adapter

Original admissibility and literal outer-carrier membership supply every
positivity premise of the finite block adapter. The atom is the actual
cleaned original atom, and both outer cutoffs are the original scale^(sigma/4).
The inner carrier, signed resonance mask, guarded rows and complete four-branch
packets are unchanged. This is an exact finite identity, with no spectral
bound or positivity assertion for the complementary block.

The imported row adapter and its paired Fourier identity are source candidates
pending separate kernel acceptance. This consumer is likewise source-only.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators

namespace SharedGeneralDSupportedRowConsumer

private theorem factor_pos {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
    (hn : n ∈ factorCarrier Q) : 0 < n := by
  obtain ⟨hlo, _⟩ := Finset.mem_Icc.mp hn
  have hc : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
  omega

end SharedGeneralDSupportedRowConsumer

/-- On the actual nonzero coefficient support, original admissibility
automatically discharges every positivity premise of the packet adapter. -/
theorem MediumAtom.cleaned_smallCoreSquaredSupportedBlock_eq_pairedPacket
    (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom)
    (hd : MediumAdmissible B sigma kappa c0 d) (Z : ℝ) (resonant : Bool)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ))
    (ho : o ∈ d.cleanedAlphaAtom.smallCoreSquaredSupportedOuterCarrier
      (d.scale ^ (sigma / 4)) (d.scale ^ (sigma / 4))) :
    d.cleanedAlphaAtom.smallCoreSquaredBlock Z resonant o =
      ∑ u ∈ d.cleanedAlphaAtom.smallCoreSquaredInnerCarrier Z o,
        ∑ v ∈ d.cleanedAlphaAtom.smallCoreSquaredInnerCarrier Z o,
          if decide (u.2 * (v.1 : ℤ) = v.2 * (u.1 : ℤ) ∨
              u.2 * (v.1 : ℤ) = -(v.2 * (u.1 : ℤ))) = resonant then
            d.cleanedAlphaAtom.smallCoreSquaredPairedPacketTerm Z o u v
          else 0 := by
  let e := d.cleanedAlphaAtom
  have he : MediumAdmissible B sigma kappa c0 e :=
    mediumAdmissible_cleanedAlphaAtom hd
  have hoOuter : o ∈ e.smallCoreSquaredOuterCarrier :=
    ((e.mem_smallCoreSquaredSupportedOuterCarrier
      (d.scale ^ (sigma / 4)) (d.scale ^ (sigma / 4)) o).mp ho).1
  change o ∈ ((e.primitiveFirstFactorCarrier ×ˢ
    (e.transposedAtom.betaCarrier ×ˢ e.transposedAtom.betaCarrier)).filter
      (fun t => t.2.1 ≠ t.2.2 ∧ Nat.ModEq t.1 t.2.1 t.2.2)) ×ˢ
    ((factorCarrier e.Q3) ×ˢ ((factorCarrier e.Q3) ×ˢ factorCarrier e.Q2)).biUnion
      (fun t => (t.2.1 * t.2.2).divisors.image (fun D => (t, D))) at hoOuter
  have hPairs := (Finset.mem_filter.mp (Finset.mem_product.mp hoOuter).1).1
  have hpCarrier : o.1.1 ∈ factorCarrier e.Q1 :=
    (Finset.mem_filter.mp (Finset.mem_product.mp hPairs).1).1
  have hN1Carrier : o.1.2.1 ∈ factorCarrier e.U :=
    (Finset.mem_product.mp (Finset.mem_product.mp hPairs).2).1
  have hN2Carrier : o.1.2.2 ∈ factorCarrier e.U :=
    (Finset.mem_product.mp (Finset.mem_product.mp hPairs).2).2
  obtain ⟨t, ht, hImage⟩ := Finset.mem_biUnion.mp (Finset.mem_product.mp hoOuter).2
  obtain ⟨D, _hD, hImageEq⟩ := Finset.mem_image.mp hImage
  have htEq : t = o.2.1 := congrArg Prod.fst hImageEq
  rw [htEq] at ht
  have hrCarrier : o.2.1.1 ∈ factorCarrier e.Q3 := (Finset.mem_product.mp ht).1
  have hr'Carrier : o.2.1.2.1 ∈ factorCarrier e.Q3 :=
    (Finset.mem_product.mp (Finset.mem_product.mp ht).2).1
  have hs'Carrier : o.2.1.2.2 ∈ factorCarrier e.Q2 :=
    (Finset.mem_product.mp (Finset.mem_product.mp ht).2).2
  have hp : 0 < o.1.1 :=
    SharedGeneralDSupportedRowConsumer.factor_pos he.2.2.1 hpCarrier
  have hr : 0 < o.2.1.1 :=
    SharedGeneralDSupportedRowConsumer.factor_pos he.2.2.2.2.1 hrCarrier
  have hr' : 0 < o.2.1.2.1 :=
    SharedGeneralDSupportedRowConsumer.factor_pos he.2.2.2.2.1 hr'Carrier
  have hs' : 0 < o.2.1.2.2 :=
    SharedGeneralDSupportedRowConsumer.factor_pos he.2.2.2.1 hs'Carrier
  have hw : 0 < o.2.1.2.1 * o.2.1.2.2 := Nat.mul_pos hr' hs'
  have hN1 : 0 < o.1.2.1 :=
    SharedGeneralDSupportedRowConsumer.factor_pos he.1 hN1Carrier
  have hN2 : 0 < o.1.2.2 :=
    SharedGeneralDSupportedRowConsumer.factor_pos he.1 hN2Carrier
  exact e.smallCoreSquaredBlock_eq_pairedPacket Z resonant o he.2.2.2.1
    hp hr hw hN1 hN2

end

end ImbalancedChen.Part3
