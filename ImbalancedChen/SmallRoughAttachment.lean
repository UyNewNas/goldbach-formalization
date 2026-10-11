import ImbalancedChen.PhysicalUpperWeightBridge
import Mathlib.Data.Nat.PrimeFin

/-!
# Unique small/rough attachment to one physical coefficient

The physical coefficient in the manuscript is indexed by a product of two
moduli.  The first modulus only contains primes strictly below `w`; the
second only contains primes at least `w` (and, in the concrete construction,
strictly below the upper sieve cutoff).  The strict/inclusive convention at
`w` makes these prime supports disjoint.

This file proves the resulting finite facts without assuming any density or
distribution estimate: cross-coprimality, uniqueness of the product
decomposition, exact reindexing to one function `rho`, and preservation of
the coefficient bound.  Thus later estimates can refer to the same literal
`rho` used by `PhysicalUpperWeightBridge`.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Every prime factor of `d` lies strictly below the attachment cutoff. -/
def SmallPrimeSupportedAt (w : ℝ) (d : ℕ) : Prop :=
  d ≠ 0 ∧ ∀ p ∈ d.primeFactors, (p : ℝ) < w

/-- Every prime factor of `d` lies on or above the attachment cutoff. -/
def RoughPrimeSupportedAt (w : ℝ) (d : ℕ) : Prop :=
  d ≠ 0 ∧ ∀ p ∈ d.primeFactors, w ≤ (p : ℝ)

/-- Strictly-small and inclusively-rough supports are coprime.  In
particular a prime exactly at `w` belongs only to the rough side. -/
theorem smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
    {w : ℝ} {a b : ℕ}
    (ha : SmallPrimeSupportedAt w a)
    (hb : RoughPrimeSupportedAt w b) :
    a.Coprime b := by
  apply (Nat.disjoint_primeFactors ha.1 hb.1).mp
  rw [Finset.disjoint_left]
  intro p hpa hpb
  exact (not_lt_of_ge (hb.2 p hpb)) (ha.2 p hpa)

/-- The product determines its small and rough factors uniquely.  This does
not require squarefreeness: repeated prime powers remain on their respective
side of the strict cutoff. -/
theorem smallRough_factorization_unique
    {w : ℝ} {d e : ℕ × ℕ}
    (hdSmall : SmallPrimeSupportedAt w d.1)
    (hdRough : RoughPrimeSupportedAt w d.2)
    (heSmall : SmallPrimeSupportedAt w e.1)
    (heRough : RoughPrimeSupportedAt w e.2)
    (hprod : d.1 * d.2 = e.1 * e.2) :
    d = e := by
  have hde : d.1.Coprime e.2 :=
    smallPrimeSupportedAt_coprime_roughPrimeSupportedAt hdSmall heRough
  have hed : e.1.Coprime d.2 :=
    smallPrimeSupportedAt_coprime_roughPrimeSupportedAt heSmall hdRough
  have hfirst : d.1 = e.1 := by
    apply Nat.dvd_antisymm
    · apply hde.dvd_of_dvd_mul_right
      rw [← hprod]
      exact dvd_mul_right _ _
    · apply hed.dvd_of_dvd_mul_right
      rw [hprod]
      exact dvd_mul_right _ _
  apply Prod.ext hfirst
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hdSmall.1)
  simpa only [hfirst] using hprod

/-- All displayed small/rough pairs. -/
def smallRoughPairs (small rough : Finset ℕ) : Finset (ℕ × ℕ) :=
  small ×ˢ rough

/-- Their multiplicity-free physical modulus support. -/
def smallRoughModuli (small rough : Finset ℕ) : Finset ℕ :=
  (smallRoughPairs small rough).image fun x => x.1 * x.2

/-- On cutoff-separated supports, multiplication is injective on the entire
displayed pair support. -/
theorem smallRough_mul_injOn
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d) :
    Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2) (smallRoughPairs small rough) := by
  intro d hd e he hprod
  change d ∈ small ×ˢ rough at hd
  change e ∈ small ×ˢ rough at he
  rw [Finset.mem_product] at hd he
  exact smallRough_factorization_unique
    (hsmall d.1 hd.1) (hrough d.2 hd.2)
    (hsmall e.1 he.1) (hrough e.2 he.2) hprod

/-- The sign-sensitive coefficient attached to one small/rough pair. -/
def smallRoughPairCoefficient
    (roughCoeff betaMinus betaPlus : ℕ → ℝ) (x : ℕ × ℕ) : ℝ :=
  signAttachedCoefficient (roughCoeff x.2)
    (betaMinus x.1) (betaPlus x.1)

/-- One physical coefficient function.  It is defined as the finite fibre
sum so it is total off the displayed support; uniqueness below proves that
every occupied fibre has exactly one term. -/
def smallRoughRho
    (small rough : Finset ℕ)
    (roughCoeff betaMinus betaPlus : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ x ∈ smallRoughPairs small rough with x.1 * x.2 = q,
    smallRoughPairCoefficient roughCoeff betaMinus betaPlus x

/-- At an occupied product, the physical coefficient is exactly the one
pair coefficient, with no multiplicity factor. -/
theorem smallRoughRho_mul
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (roughCoeff betaMinus betaPlus : ℕ → ℝ)
    {a b : ℕ} (ha : a ∈ small) (hb : b ∈ rough) :
    smallRoughRho small rough roughCoeff betaMinus betaPlus (a * b) =
      smallRoughPairCoefficient roughCoeff betaMinus betaPlus (a, b) := by
  classical
  have hab : (a, b) ∈ smallRoughPairs small rough := by
    simp [smallRoughPairs, ha, hb]
  unfold smallRoughRho
  rw [Finset.sum_eq_single (a, b)]
  · intro x hx hne
    rw [Finset.mem_filter] at hx
    exact (hne ((smallRough_mul_injOn hsmall hrough) hx.1 hab hx.2)).elim
  · intro hnot
    exact (hnot (Finset.mem_filter.mpr ⟨hab, rfl⟩)).elim

/-- The physical coefficient vanishes away from the product support. -/
theorem smallRoughRho_eq_zero_of_not_mem
    (small rough : Finset ℕ)
    (roughCoeff betaMinus betaPlus : ℕ → ℝ)
    {q : ℕ} (hq : q ∉ smallRoughModuli small rough) :
    smallRoughRho small rough roughCoeff betaMinus betaPlus q = 0 := by
  classical
  unfold smallRoughRho
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mem_filter] at hx
  exfalso
  exact hq (Finset.mem_image.mpr ⟨x, hx.1, hx.2⟩)

/-- The literal pair-indexed attached divisor expression. -/
def smallRoughPairDivisorSum
    (small rough : Finset ℕ)
    (roughCoeff betaMinus betaPlus : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ x ∈ smallRoughPairs small rough,
    if x.1 * x.2 ∣ n then
      smallRoughPairCoefficient roughCoeff betaMinus betaPlus x
    else 0

/-- Exact reindexing of the pair expression as the divisor sum of one
physical coefficient `smallRoughRho`.  The same function can therefore be
fed to the pointwise, density and signed-distribution interfaces. -/
theorem smallRoughPairDivisorSum_eq_physicalDivisorSum
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (roughCoeff betaMinus betaPlus : ℕ → ℝ) (n : ℕ) :
    smallRoughPairDivisorSum small rough roughCoeff betaMinus betaPlus n =
      physicalDivisorSum (smallRoughModuli small rough)
        (smallRoughRho small rough roughCoeff betaMinus betaPlus) n := by
  classical
  unfold smallRoughPairDivisorSum physicalDivisorSum smallRoughModuli
  rw [Finset.sum_image (smallRough_mul_injOn hsmall hrough)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [smallRoughRho_mul hsmall hrough roughCoeff betaMinus betaPlus]
  · exact (Finset.mem_product.mp hx).1
  · exact (Finset.mem_product.mp hx).2

/-- Any scalar sum over the multiplicity-free physical modulus support can
be pulled back to the displayed small/rough pairs without a fibre factor. -/
theorem sum_smallRoughModuli
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (F : ℕ → ℝ) :
    (∑ q ∈ smallRoughModuli small rough, F q) =
      ∑ x ∈ smallRoughPairs small rough, F (x.1 * x.2) := by
  classical
  unfold smallRoughModuli
  rw [Finset.sum_image (smallRough_mul_injOn hsmall hrough)]

/-- In particular, a physical sum weighted by `smallRoughRho` is exactly
the original pair-coefficient sum.  This is the finite reindexing needed by
the later density and signed-distribution estimates. -/
theorem sum_smallRoughRho_mul
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (roughCoeff betaMinus betaPlus : ℕ → ℝ) (F : ℕ → ℝ) :
    (∑ q ∈ smallRoughModuli small rough,
        smallRoughRho small rough roughCoeff betaMinus betaPlus q * F q) =
      ∑ x ∈ smallRoughPairs small rough,
        smallRoughPairCoefficient roughCoeff betaMinus betaPlus x *
          F (x.1 * x.2) := by
  rw [sum_smallRoughModuli hsmall hrough]
  apply Finset.sum_congr rfl
  intro x hx
  rw [smallRoughRho_mul hsmall hrough roughCoeff betaMinus betaPlus]
  · exact (Finset.mem_product.mp hx).1
  · exact (Finset.mem_product.mp hx).2

/-- Divisibility by a physical product is equivalent to divisibility by
both factors.  The reverse implication uses the cutoff-forced coprimality. -/
theorem smallRough_mul_dvd_iff
    {w : ℝ} {a b n : ℕ}
    (ha : SmallPrimeSupportedAt w a)
    (hb : RoughPrimeSupportedAt w b) :
    a * b ∣ n ↔ a ∣ n ∧ b ∣ n := by
  constructor
  · intro h
    exact ⟨(dvd_mul_right a b).trans h, (dvd_mul_left b a).trans h⟩
  · rintro ⟨han, hbn⟩
    exact (smallPrimeSupportedAt_coprime_roughPrimeSupportedAt ha hb).mul_dvd_of_dvd_of_dvd
      han hbn

/-- Expanding the upper or lower small-prime divisor sum selected by the
sign of each rough coefficient gives exactly the pair-indexed attachment.
The divisibility equivalence is where the strict small/rough cutoff is used. -/
theorem smallRoughPairDivisorSum_eq_signSensitiveAttachment
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (roughCoeff betaMinus betaPlus : ℕ → ℝ) (n : ℕ) :
    smallRoughPairDivisorSum small rough roughCoeff betaMinus betaPlus n =
      signSensitiveAttachment rough roughCoeff
        (supportedDivisorSum small betaMinus n)
        (supportedDivisorSum small betaPlus n) n := by
  classical
  unfold smallRoughPairDivisorSum smallRoughPairs
  rw [Finset.sum_product, Finset.sum_comm]
  unfold signSensitiveAttachment
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hbn : b ∣ n
  · rw [if_pos hbn]
    unfold signAttachedValue
    by_cases hc : 0 ≤ roughCoeff b
    · rw [if_pos hc]
      unfold supportedDivisorSum
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases han : a ∣ n
      · rw [if_pos ((smallRough_mul_dvd_iff
          (hsmall a ha) (hrough b hb)).2 ⟨han, hbn⟩), if_pos han]
        simp [hc, smallRoughPairCoefficient, signAttachedCoefficient]
      · rw [if_neg (fun hab => han ((smallRough_mul_dvd_iff
          (hsmall a ha) (hrough b hb)).1 hab).1), if_neg han]
        simp
    · rw [if_neg hc]
      unfold supportedDivisorSum
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases han : a ∣ n
      · rw [if_pos ((smallRough_mul_dvd_iff
          (hsmall a ha) (hrough b hb)).2 ⟨han, hbn⟩), if_pos han]
        simp [hc, smallRoughPairCoefficient, signAttachedCoefficient]
      · rw [if_neg (fun hab => han ((smallRough_mul_dvd_iff
          (hsmall a ha) (hrough b hb)).1 hab).1), if_neg han]
        simp
  · rw [if_neg hbn]
    apply Finset.sum_eq_zero
    intro a ha
    rw [if_neg]
    intro hab
    exact hbn ((dvd_mul_left b a).trans hab)

/-- The sign-sensitive expression from the pointwise majorant is literally
the divisor sum of the same physical coefficient used by the density and
signed-distribution decomposition. -/
theorem signSensitiveAttachment_eq_smallRough_physicalDivisorSum
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (roughCoeff betaMinus betaPlus : ℕ → ℝ) (n : ℕ) :
    signSensitiveAttachment rough roughCoeff
        (supportedDivisorSum small betaMinus n)
        (supportedDivisorSum small betaPlus n) n =
      physicalDivisorSum (smallRoughModuli small rough)
        (smallRoughRho small rough roughCoeff betaMinus betaPlus) n := by
  rw [← smallRoughPairDivisorSum_eq_signSensitiveAttachment
    hsmall hrough roughCoeff betaMinus betaPlus n]
  exact smallRoughPairDivisorSum_eq_physicalDivisorSum
    hsmall hrough roughCoeff betaMinus betaPlus n

/-- Separate one-bounds transport to the single occupied physical
coefficient, again without any cardinality or multiplicity loss. -/
theorem abs_smallRoughRho_mul_le_one
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (roughCoeff betaMinus betaPlus : ℕ → ℝ)
    (hc : ∀ d ∈ rough, |roughCoeff d| ≤ 1)
    (hminus : ∀ d ∈ small, |betaMinus d| ≤ 1)
    (hplus : ∀ d ∈ small, |betaPlus d| ≤ 1)
    {a b : ℕ} (ha : a ∈ small) (hb : b ∈ rough) :
    |smallRoughRho small rough roughCoeff betaMinus betaPlus (a * b)| ≤ 1 := by
  rw [smallRoughRho_mul hsmall hrough roughCoeff betaMinus betaPlus ha hb]
  exact abs_signAttachedCoefficient_le_one (hc b hb) (hminus a ha) (hplus a ha)

end

end ImbalancedChen
