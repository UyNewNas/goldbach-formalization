import ImbalancedChen.Part3DistributionTargets
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Nat.Totient

/-!
# Exact additive Fourier expansion with the primitive centre retained

The finite character sum is reused from Mathlib's primitive-character
orthogonality theorem at the full modulus, including composite moduli.
The primitive mean is expanded through the actual units of `ZMod q`.
Its zero frequency cancels exactly against the congruence indicator.
Modulus one is included. No primality or squarefreeness of q is assumed.

The actual medium-atom and labelled-prime consumers retain their finite
carriers and all weights. In particular a prime-product source is not
replaced by a sum over arbitrary integers, nor is a Fourier character of
a product factored as though its argument were a sum.

These are finite identities. Auxiliary SW, the common completion, the
dispersion-to-reciprocal-phase identity and the aggregate gcd estimates
needed for `RestrictedMediumObligation` remain separate obligations.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped BigOperators
open Classical

/-- The literal congruence indicator minus its primitive-coprime mean. -/
def centeredResidueIndicator (q : ℕ) [NeZero q] (a z : ZMod q) : ℂ :=
  (if z = a then 1 else 0) -
    (if IsUnit z then 1 else 0) / (Nat.totient q : ℂ)

/-- The additive transform of the actual unit indicator, with the sign
used by Fourier inversion. -/
def primitiveAdditiveCoefficient (q : ℕ) [NeZero q] (h : ZMod q) : ℂ :=
  ∑ u : (ZMod q)ˣ, ZMod.stdAddChar (-h * (u : ZMod q))

/-- The complete Fourier coefficient of the centered residue indicator.
The residue and the coprime centre retain their own exact transforms. -/
def centeredAdditiveCoefficient (q : ℕ) [NeZero q] (a h : ZMod q) : ℂ :=
  ZMod.stdAddChar (-h * a) -
    primitiveAdditiveCoefficient q h / (Nat.totient q : ℂ)

/-- Primitive additive orthogonality is valid at every positive modulus. -/
theorem sum_stdAddChar_mul_eq (q : ℕ) [NeZero q] (z : ZMod q) :
    (∑ h : ZMod q, ZMod.stdAddChar (h * z)) =
      if z = 0 then (q : ℂ) else 0 := by
  have h := AddChar.sum_mulShift z (ZMod.isPrimitive_stdAddChar q)
  by_cases hz : z = 0
  · simp [hz]
  · simpa [hz] using h

/-- The Fourier sum of an actual residue indicator, before centering. -/
theorem sum_residueAdditiveCoefficient_mul (q : ℕ) [NeZero q]
    (a z : ZMod q) :
    (∑ h : ZMod q,
      ZMod.stdAddChar (-h * a) * ZMod.stdAddChar (h * z)) =
        (q : ℂ) * (if z = a then 1 else 0) := by
  have hterm (h : ZMod q) :
      ZMod.stdAddChar (-h * a) * ZMod.stdAddChar (h * z) =
        ZMod.stdAddChar (h * (z - a)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hterm]
  rw [sum_stdAddChar_mul_eq]
  by_cases h : z = a <;> simp [h, sub_eq_zero]

/-- Summing the literal indicators of unit residues gives precisely the
unit predicate, with no multiple representatives. -/
theorem sum_unitResidueIndicator (q : ℕ) [NeZero q] (z : ZMod q) :
    (∑ u : (ZMod q)ˣ, if z = (u : ZMod q) then (1 : ℂ) else 0) =
      if IsUnit z then 1 else 0 := by
  by_cases hz : IsUnit z
  · obtain ⟨u, rfl⟩ := hz
    have heq (v : (ZMod q)ˣ) :
        (u : ZMod q) = (v : ZMod q) ↔ v = u := by
      constructor
      · intro h
        exact Units.ext h.symm
      · intro h
        rw [h]
    simp [heq]
  · have heq (u : (ZMod q)ˣ) : z ≠ (u : ZMod q) := by
      intro h
      exact hz (h.symm ▸ u.isUnit)
    simp [hz, heq]

/-- The Fourier transform of the primitive centre uses the full actual
unit group, including its cardinality phi(q). -/
theorem sum_primitiveAdditiveCoefficient_mul (q : ℕ) [NeZero q]
    (z : ZMod q) :
    (∑ h : ZMod q,
      primitiveAdditiveCoefficient q h * ZMod.stdAddChar (h * z)) =
        (q : ℂ) * (if IsUnit z then 1 else 0) := by
  simp only [primitiveAdditiveCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [sum_residueAdditiveCoefficient_mul]
  rw [← Finset.mul_sum, sum_unitResidueIndicator]

theorem primitiveAdditiveCoefficient_zero (q : ℕ) [NeZero q] :
    primitiveAdditiveCoefficient q 0 = (Nat.totient q : ℂ) := by
  simp [primitiveAdditiveCoefficient, ZMod.card_units_eq_totient]

/-- The zero frequency cancels exactly; there is no hidden total-mass
term left after replacing the primitive centre by a total-mass surrogate. -/
theorem centeredAdditiveCoefficient_zero (q : ℕ) [NeZero q]
    (a : ZMod q) : centeredAdditiveCoefficient q a 0 = 0 := by
  have hphi : (Nat.totient q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  simp [centeredAdditiveCoefficient, primitiveAdditiveCoefficient_zero, hphi]

/-- Modulus one is included and every coefficient is zero there. -/
theorem centeredAdditiveCoefficient_modulus_one (a h : ZMod 1) :
    centeredAdditiveCoefficient 1 a h = 0 := by
  have hh : h = 0 := Subsingleton.elim _ _
  rw [hh, centeredAdditiveCoefficient_zero]

theorem sum_centeredAdditiveCoefficient_mul (q : ℕ) [NeZero q]
    (a z : ZMod q) :
    (∑ h : ZMod q,
      centeredAdditiveCoefficient q a h * ZMod.stdAddChar (h * z)) =
        (q : ℂ) * centeredResidueIndicator q a z := by
  simp_rw [centeredAdditiveCoefficient, sub_mul, div_mul_eq_mul_div]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div,
    sum_residueAdditiveCoefficient_mul, sum_primitiveAdditiveCoefficient_mul]
  unfold centeredResidueIndicator
  ring

/-- The full sum equals its nonzero-frequency sum by the proved zero
coefficient, rather than by dropping a principal term informally. -/
theorem centeredFourierSum_eq_erase_zero (q : ℕ) [NeZero q]
    (a z : ZMod q) :
    (∑ h : ZMod q,
      centeredAdditiveCoefficient q a h * ZMod.stdAddChar (h * z)) =
      ∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0,
        centeredAdditiveCoefficient q a h * ZMod.stdAddChar (h * z) := by
  have h := Finset.sum_erase_add (Finset.univ : Finset (ZMod q))
    (fun h => centeredAdditiveCoefficient q a h * ZMod.stdAddChar (h * z))
    (Finset.mem_univ 0)
  simpa only [centeredAdditiveCoefficient_zero, zero_mul, add_zero] using h.symm

/-- Exact coprime-centered Fourier inversion. A positive composite
modulus and modulus one use exactly this same identity. -/
theorem centeredResidueIndicator_eq_fourier (q : ℕ) [NeZero q]
    (a z : ZMod q) :
    centeredResidueIndicator q a z =
      (q : ℂ)⁻¹ *
        ∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          centeredAdditiveCoefficient q a h * ZMod.stdAddChar (h * z) := by
  rw [← centeredFourierSum_eq_erase_zero, sum_centeredAdditiveCoefficient_mul]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rw [← mul_assoc, inv_mul_cancel₀ hq, one_mul]

/-- Fourier inversion commutes with every literal finite weighted source.
This algebraic identity does not assert a distribution estimate for
arbitrary weights or replace the displayed source carrier. -/
theorem sum_weighted_centeredResidueIndicator_eq_fourier
    {alpha : Type*} (S : Finset alpha) (q : ℕ) [NeZero q]
    (a : ZMod q) (z : alpha → ZMod q) (weight : alpha → ℂ) :
    (∑ t ∈ S, weight t * centeredResidueIndicator q a (z t)) =
      (q : ℂ)⁻¹ *
        ∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          centeredAdditiveCoefficient q a h *
            ∑ t ∈ S, weight t * ZMod.stdAddChar (h * z t) := by
  calc
    _ = ∑ t ∈ S, ∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0,
        (q : ℂ)⁻¹ * centeredAdditiveCoefficient q a h *
          (weight t * ZMod.stdAddChar (h * z t)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [centeredResidueIndicator_eq_fourier]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = ∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0, ∑ t ∈ S,
        (q : ℂ)⁻¹ * centeredAdditiveCoefficient q a h *
          (weight t * ZMod.stdAddChar (h * z t)) := Finset.sum_comm
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro t _
      ring

/-- Exact conversion of the original integer remainder equality and
natural coprimality predicate, before the medium source is transformed. -/
theorem centeredResidueIndicator_nat_int (q : ℕ) [NeZero q]
    (a : ℤ) (m : ℕ) :
    ((if ((m : ℤ) % (q : ℤ) = a % (q : ℤ)) then (1 : ℂ) else 0) -
      (if m.Coprime q then 1 else 0) / (Nat.totient q : ℂ)) =
        centeredResidueIndicator q (a : ZMod q) (m : ZMod q) := by
  have heq : ((m : ℤ) % (q : ℤ) = a % (q : ℤ)) ↔
      (m : ZMod q) = (a : ZMod q) := by
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff' (m : ℤ) a q).symm
  simp only [centeredResidueIndicator, heq, ZMod.isUnit_iff_coprime]

/-- The actual medium atom, with its fixed alpha interval, beta carrier,
complex coefficients and original moving residue, has this exact finite
nonzero-additive-frequency expansion at its full physical modulus q. -/
theorem MediumAtom.discrepancy_eq_centeredFourier
    (d : MediumAtom) (q : ℕ) [NeZero q] :
    d.discrepancy q =
      (q : ℂ)⁻¹ *
        ∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          centeredAdditiveCoefficient q (d.residue : ZMod q) h *
            ∑ n ∈ d.alphaCarrier, ∑ m ∈ d.betaCarrier,
              d.alpha n * d.beta m *
                ZMod.stdAddChar (h * ((n * m : ℕ) : ZMod q)) := by
  unfold MediumAtom.discrepancy
  simp_rw [centeredResidueIndicator_nat_int]
  simpa only [Finset.sum_product] using
    sum_weighted_centeredResidueIndicator_eq_fourier
      (d.alphaCarrier ×ˢ d.betaCarrier) q (d.residue : ZMod q)
      (fun t : ℕ × ℕ => ((t.1 * t.2 : ℕ) : ZMod q))
      (fun t : ℕ × ℕ => d.alpha t.1 * d.beta t.2)

/-- The natural congruence predicate in the literal labelled-prime source
is the same finite-ring indicator; no prime condition is changed. -/
theorem centeredResidueIndicator_nat_nat (q : ℕ) [NeZero q]
    (N m : ℕ) :
    ((if Nat.ModEq q m N then (1 : ℂ) else 0) -
      (if m.Coprime q then 1 else 0) / (Nat.totient q : ℂ)) =
        centeredResidueIndicator q (N : ZMod q) (m : ZMod q) := by
  simp only [centeredResidueIndicator, ZMod.natCast_eq_natCast_iff,
    ZMod.isUnit_iff_coprime]

/-- Exact single-modulus consumer for the real prime-product source.
All original prime labels, repeated primes, slot order and W remain in
the finite sum. This is the literal per-q summand of its signed error. -/
theorem labelledPrimeSource_centeredFourier
    (k P N q : ℕ) [NeZero q]
    (W : (Fin k → Fin (P + 1)) → ℝ) :
    (∑ t ∈ labelledPrimeTuples k P, (W t : ℂ) *
      ((if Nat.ModEq q (labelledProduct t) N then (1 : ℂ) else 0) -
        (if Nat.Coprime (labelledProduct t) q then 1 else 0) /
          (Nat.totient q : ℂ))) =
      (q : ℂ)⁻¹ *
        ∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          centeredAdditiveCoefficient q (N : ZMod q) h *
            ∑ t ∈ labelledPrimeTuples k P,
              (W t : ℂ) * ZMod.stdAddChar (h * (labelledProduct t : ZMod q)) := by
  simp_rw [centeredResidueIndicator_nat_nat]
  exact sum_weighted_centeredResidueIndicator_eq_fourier
    (labelledPrimeTuples k P) q (N : ZMod q)
    (fun t => (labelledProduct t : ZMod q)) (fun t => (W t : ℂ))

end

end ImbalancedChen.Part3
