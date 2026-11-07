import ImbalancedChen.P6LiteralWitnessUniqueness
import ImbalancedChen.P6LiteralCountEquiv

/-!
# Exact count of canonical literal triples

The bounded literal triples project onto precisely the accepted additive
primes. Below exponent one the literal factor pair is unique, including its
`r = 1` branch, so the projection is injective and the triple count is `RealDb`.

Source-only draft. The two P6 imports refer to sibling draft sources that must
be staged under these module names before authorized compilation.
-/

namespace ImbalancedChen.P6

noncomputable section

/-- Literal representations have all three coordinates strictly below `N`.
The additive prime is positive, and each receiver factor is positive. -/
theorem P6_literal_coordinates_lt {N p r q : ℕ}
    (hp : Nat.Prime p) (hr : r = 1 ∨ Nat.Prime r)
    (hq : Nat.Prime q) (hN : N = p + r * q) :
    p < N ∧ r < N ∧ q < N := by
  have hrpos : 0 < r := by
    rcases hr with hrOne | hrPrime
    · omega
    · exact hrPrime.pos
  have hprodpos : 0 < r * q := Nat.mul_pos hrpos hq.pos
  have hrle : r ≤ r * q := Nat.le_mul_of_pos_right r hq.pos
  have hqle : q ≤ r * q := Nat.le_mul_of_pos_left q hrpos
  have hppos : 0 < p := hp.pos
  omega

/-- Bounded literal triples. The first coordinate is the additive prime;
the inner pair is the literal factor witness, including `r = 1`. -/
def P6CanonicalLiteralTriples (b : ℝ) (N : ℕ) : Finset (ℕ × (ℕ × ℕ)) := by
  classical
  exact ((Finset.range N).product
    ((Finset.range N).product (Finset.range N))).filter fun z =>
      Nat.Prime z.1 ∧ (z.2.1 = 1 ∨ Nat.Prime z.2.1) ∧ Nat.Prime z.2.2 ∧
        N = z.1 + z.2.1 * z.2.2 ∧ (z.2.1 : ℝ) ≤ (z.2.2 : ℝ) ^ b

/-- The range bounds in the definition lose no literal representation. -/
@[simp] theorem P6_mem_canonicalLiteralTriples {b : ℝ} {N p r q : ℕ} :
    (p, (r, q)) ∈ P6CanonicalLiteralTriples b N ↔
      Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ b := by
  classical
  constructor
  · intro hz
    exact (Finset.mem_filter.mp hz).2
  · rintro ⟨hp, hr, hq, hN, hpow⟩
    have hbounds := P6_literal_coordinates_lt hp hr hq hN
    apply Finset.mem_filter.mpr
    refine ⟨?_, hp, hr, hq, hN, hpow⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hbounds.1,
        Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr hbounds.2.1, Finset.mem_range.mpr hbounds.2.2⟩⟩

/-- Projection to the additive prime has exactly the accepted finite set as
its image. Only the lower exponent bound is needed for surjectivity. -/
theorem P6_canonicalLiteralTriples_fst_image {b : ℝ} {N : ℕ}
    (hb : 0 ≤ b) :
    (P6CanonicalLiteralTriples b N).image
      (fun z : ℕ × (ℕ × ℕ) => z.1) = realImbalancedPrimes b N := by
  classical
  ext p
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨⟨p', ⟨r, q⟩⟩, hz, heq⟩
    change p' = p at heq
    subst p'
    obtain ⟨hpPrime, hr, hq, hN, hpow⟩ := P6_mem_canonicalLiteralTriples.mp hz
    exact P6_mem_realImbalancedPrimes_of_literal hpPrime hr hq hN hpow
  · intro hp
    obtain ⟨r, q, hpPrime, hr, hq, hN, hpow⟩ :=
      (P6_mem_realImbalancedPrimes_iff_literal hb).mp hp
    exact Finset.mem_image.mpr
      ⟨(p, (r, q)),
        P6_mem_canonicalLiteralTriples.mpr ⟨hpPrime, hr, hq, hN, hpow⟩, rfl⟩

/-- The projection is injective on the literal triples below exponent one.
This is the required uniqueness input for an exact cardinality identity. -/
theorem P6_canonicalLiteralTriples_fst_injOn {b : ℝ} {N : ℕ}
    (hb : b < 1) :
    Set.InjOn (fun z : ℕ × (ℕ × ℕ) => z.1)
      (↑(P6CanonicalLiteralTriples b N) : Set (ℕ × (ℕ × ℕ))) := by
  intro x hx y hy hxy
  rcases x with ⟨p, ⟨r, q⟩⟩
  rcases y with ⟨p', ⟨s, t⟩⟩
  change p = p' at hxy
  subst p'
  obtain ⟨_, hr, hq, hNrq, hrpow⟩ := P6_mem_canonicalLiteralTriples.mp hx
  obtain ⟨_, hs, ht, hNst, hspow⟩ := P6_mem_canonicalLiteralTriples.mp hy
  obtain ⟨hrs, hqt⟩ :=
    P6_literal_factors_unique hb hr hq hs ht hNrq hNst hrpow hspow
  subst s
  subst t
  rfl

/-- For `0 ≤ b < 1`, the number of bounded literal triples equals the count
of distinct accepted additive primes. Injectivity is proved before applying
the image-cardinality theorem. -/
theorem P6_canonicalLiteralTriples_card_eq_RealDb {b : ℝ} {N : ℕ}
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    (P6CanonicalLiteralTriples b N).card = RealDb b N := by
  classical
  calc
    (P6CanonicalLiteralTriples b N).card =
        ((P6CanonicalLiteralTriples b N).image
          (fun z : ℕ × (ℕ × ℕ) => z.1)).card :=
      (Finset.card_image_iff.mpr (P6_canonicalLiteralTriples_fst_injOn hb1)).symm
    _ = (realImbalancedPrimes b N).card := by
      rw [P6_canonicalLiteralTriples_fst_image hb0]
    _ = RealDb b N := rfl

end

end ImbalancedChen.P6
