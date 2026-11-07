import ImbalancedChen.Part3OriginalS2LambdaDivisorPacket
import ImbalancedChen.Part3OriginalS2RoughScalePayment
import Mathlib.Tactic

/-!
# The actual same-d S2 smooth-tail packet: the finite inequality (F)

The coefficient carrier is the exact same-d image carrier, filtered by
the original D,R dyadic block and the literal left modulus q*d*r=l.
No Cartesian completion of the two rough fibers is made. The free n2
variable is summed only with its actual primitive gate, and the factor
1/phi(q*d*s) is retained in the nonnegative coefficient cost.

The progression sum T(l,a) is obtained from the actual alpha/common-m
product fiber, using the previously proved divisor-fiber bound. In
particular T keeps the moving residue a, and the zero product fiber
vanishes by the original smooth cutoff. The result below is the finite
inequality (F), not its later Shiu or dyadic-geometry estimate.

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
-/

namespace ImbalancedChen.Part3OriginalS2ActualBlockPacketBound

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalS2ExactSmoothTailExpansion
open ImbalancedChen.Part3OriginalS2SmoothYRankinStart
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalS2ZeroGramCompiler
open ImbalancedChen.Part3OriginalS2ActualPsiWeightAdapter
open ImbalancedChen.Part3OriginalS2ActualPsiTailPackets
open ImbalancedChen.Part3OriginalS2ShiuPrimitiveFiber
open ImbalancedChen.Part3OriginalS2LambdaDivisorPacket
open ImbalancedChen.Part3OriginalS2RoughScalePayment
open Classical Finset
open scoped BigOperators

noncomputable section

abbrev CoefficientIndex := Σ _ : ℕ × ℕ, ℕ × ℕ

def coefficientCarrier (d : MediumAtom) (z : ℝ) : Finset CoefficientIndex :=
  (d.primitiveFirstFactorCarrier ×ˢ dCarrier d z).sigma
    (fun qd => roughFiber d z qd.2 ×ˢ roughFiber d z qd.2)

def inPaperBlock (D R : ℝ) (c : CoefficientIndex) : Prop :=
  D ≤ (c.1.2 : ℝ) ∧ (c.1.2 : ℝ) < 2 * D ∧
    R ≤ (c.2.1 : ℝ) ∧ (c.2.1 : ℝ) < 2 * R ∧
    R ≤ (c.2.2 : ℝ) ∧ (c.2.2 : ℝ) < 2 * R

def blockCoefficientCarrier (d : MediumAtom) (z D R : ℝ) (l : ℕ) :
    Finset CoefficientIndex :=
  (coefficientCarrier d z).filter
    (fun c => inPaperBlock D R c ∧ c.1.1 * c.1.2 * c.2.1 = l)

/-- The exact finite progression envelope T(l,a), with the actual product image. -/
def divisorProgression (d : MediumAtom) (l : ℕ) (a : ℤ) : ℝ :=
  ∑ v ∈ mnImage d,
    if Int.ModEq l (v : ℤ) a then (v.divisors.card : ℝ) else 0

def actualProgression (d : MediumAtom) (l : ℕ) : ℂ :=
  ∑ nm ∈ mnCarrier d,
    if Int.ModEq l (((nm.1 * nm.2 : ℕ) : ℤ)) d.residue then
      primitivePairWeight d l nm else 0

/-- The actual free n2 coefficient; its cardinality is not discarded. -/
def freeAlphaMass (d : MediumAtom) (k : ℕ) : ℂ :=
  ∑ n ∈ d.alphaCarrier, if Nat.Coprime n k then star (d.alpha n) else 0

def freeAlphaCount (d : MediumAtom) (k : ℕ) : ℝ :=
  ((d.alphaCarrier.filter (fun n => Nat.Coprime n k)).card : ℝ)

def coefficientInnerSum (d : MediumAtom) (c : CoefficientIndex)
    (left right : ℕ → ℕ → ℂ) : ℂ :=
  ∑ n₁ ∈ d.alphaCarrier, ∑ n₂ ∈ d.alphaCarrier,
    ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
      s2TermWithCoefficients d (actualPsiQWeight d) left right
        ⟨c.1, (c.2, ((n₁, n₂), m))⟩

def coefficientThreeTailSum (d : MediumAtom) (x z : ℝ)
    (c : CoefficientIndex) : ℂ :=
  ∑ n₁ ∈ d.alphaCarrier, ∑ n₂ ∈ d.alphaCarrier,
    ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
      actualThreeTailTerm d x z ⟨c.1, (c.2, ((n₁, n₂), m))⟩

def blockCoefficientPacket (d : MediumAtom) (x z D R : ℝ) (l : ℕ) : ℂ :=
  ∑ c ∈ blockCoefficientCarrier d z D R l,
    coefficientThreeTailSum d x z c

/-- This is A_(l,D,R) on the existing literal paperBlockOuterCarrier. -/
def actualPaperBlockPacket (d : MediumAtom) (x z D R : ℝ) (l : ℕ) : ℂ :=
  ∑ o ∈ (paperBlockOuterCarrier d z D R).filter
      (fun o => o.1.1 * o.1.2 * o.2.1.1 = l),
    ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
      actualThreeTailTerm d x z ⟨o.1, (o.2.1, (o.2.2, m))⟩

def coefficientCost (d : MediumAtom) (c : CoefficientIndex) : ℝ :=
  3 * ((c.1.2 * c.2.1).divisors.card : ℝ) *
    ((c.1.2 * c.2.2).divisors.card : ℝ) *
    freeAlphaCount d (c.1.1 * c.1.2 * c.2.2) /
      (Nat.totient (c.1.1 * c.1.2 * c.2.2) : ℝ)

/-- The exact H_(l,D,R), retaining phi(q*d*s) and same-d multiplicities. -/
def blockGeometryCost (d : MediumAtom) (z D R : ℝ) (l : ℕ) : ℝ :=
  ∑ c ∈ blockCoefficientCarrier d z D R l, coefficientCost d c

theorem divisorProgression_nonneg (d : MediumAtom) (l : ℕ) (a : ℤ) :
    0 ≤ divisorProgression d l a := by
  unfold divisorProgression
  apply Finset.sum_nonneg
  intro v hv
  split_ifs <;> positivity

theorem freeAlphaCount_nonneg (d : MediumAtom) (k : ℕ) :
    0 ≤ freeAlphaCount d k := by
  unfold freeAlphaCount
  positivity

theorem actualProgression_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (l : ℕ) :
    ‖actualProgression d l‖ ≤ divisorProgression d l d.residue := by
  exact shifted_inner_norm_le_divisor_progression hd l d.residue

theorem freeAlphaMass_norm_le_count
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (k : ℕ) :
    ‖freeAlphaMass d k‖ ≤ freeAlphaCount d k := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha,
    _, _, _, _, _⟩ := hd
  rw [freeAlphaMass, ← Finset.sum_filter]
  calc
    ‖∑ n ∈ d.alphaCarrier.filter (fun n => Nat.Coprime n k),
        star (d.alpha n)‖ ≤
      ∑ n ∈ d.alphaCarrier.filter (fun n => Nat.Coprime n k),
        ‖star (d.alpha n)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ d.alphaCarrier.filter (fun n => Nat.Coprime n k),
        (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          simpa only [norm_star] using hAlpha n (Finset.mem_filter.mp hn).1
    _ = freeAlphaCount d k := by simp [freeAlphaCount]

private theorem separated_three_sums
    (A B C : Finset ℕ) (K : ℂ) (F : ℕ → ℂ) (G : ℕ → ℕ → ℂ) :
    (∑ n₁ ∈ A, ∑ n₂ ∈ B, ∑ m ∈ C, K * F n₂ * G n₁ m) =
      K * (∑ n₂ ∈ B, F n₂) * (∑ n₁ ∈ A, ∑ m ∈ C, G n₁ m) := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- Exact finite Fubini. The primitive n1 gate remains inside its progression;
the separate n2 gate is precisely the free mass at the right modulus. -/
theorem coefficientInnerSum_factor (d : MediumAtom) (c : CoefficientIndex)
    (left right : ℕ → ℕ → ℂ) :
    coefficientInnerSum d c left right =
      (actualPsiQWeight d c.1.1 * left c.1.2 c.2.1 *
        star (right c.1.2 c.2.2) /
          (Nat.totient (c.1.1 * c.1.2 * c.2.2) : ℂ)) *
        freeAlphaMass d (c.1.1 * c.1.2 * c.2.2) *
        actualProgression d (c.1.1 * c.1.2 * c.2.1) := by
  let K := actualPsiQWeight d c.1.1 * left c.1.2 c.2.1 *
    star (right c.1.2 c.2.2) /
      (Nat.totient (c.1.1 * c.1.2 * c.2.2) : ℂ)
  let F : ℕ → ℂ := fun n₂ =>
    if Nat.Coprime n₂ (c.1.1 * c.1.2 * c.2.2) then star (d.alpha n₂) else 0
  let G : ℕ → ℕ → ℂ := fun n₁ m =>
    if Int.ModEq (c.1.1 * c.1.2 * c.2.1)
        (((n₁ * m : ℕ) : ℤ)) d.residue then
      primitivePairWeight d (c.1.1 * c.1.2 * c.2.1) (n₁, m) else 0
  have hterm (n₁ n₂ m : ℕ) :
      s2TermWithCoefficients d (actualPsiQWeight d) left right
        ⟨c.1, (c.2, ((n₁, n₂), m))⟩ = K * F n₂ * G n₁ m := by
    by_cases h₁ : Nat.Coprime n₁ (c.1.1 * c.1.2 * c.2.1) <;>
      by_cases h₂ : Nat.Coprime n₂ (c.1.1 * c.1.2 * c.2.2) <;>
      by_cases ha : Int.ModEq (c.1.1 * c.1.2 * c.2.1)
          (((n₁ * m : ℕ) : ℤ)) d.residue <;>
      simp [s2TermWithCoefficients, K, F, G, primitivePairWeight,
        h₁, h₂, Nat.mul_comm m n₁, ha] <;> ring
  unfold coefficientInnerSum
  simp_rw [hterm]
  rw [separated_three_sums]
  change K * freeAlphaMass d (c.1.1 * c.1.2 * c.2.2) *
      (∑ n₁ ∈ d.alphaCarrier,
        ∑ m ∈ d.transposedAtom.commonSmoothCarrier, G n₁ m) = _
  simp only [actualProgression, mnCarrier, Finset.sum_product, K, G]

theorem coefficientInnerSum_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (c : CoefficientIndex) (left right : ℕ → ℕ → ℂ)
    (hleft : ‖left c.1.2 c.2.1‖ ≤ ((c.1.2 * c.2.1).divisors.card : ℝ))
    (hright : ‖right c.1.2 c.2.2‖ ≤ ((c.1.2 * c.2.2).divisors.card : ℝ)) :
    ‖coefficientInnerSum d c left right‖ ≤
      (((c.1.2 * c.2.1).divisors.card : ℝ) *
        ((c.1.2 * c.2.2).divisors.card : ℝ) *
          freeAlphaCount d (c.1.1 * c.1.2 * c.2.2) /
            (Nat.totient (c.1.1 * c.1.2 * c.2.2) : ℝ)) *
        divisorProgression d (c.1.1 * c.1.2 * c.2.1) d.residue := by
  have hq := actualPsiQWeight_norm_le_one d c.1.1
  have hfree := freeAlphaMass_norm_le_count hd (c.1.1 * c.1.2 * c.2.2)
  have hprog := actualProgression_norm_le hd (c.1.1 * c.1.2 * c.2.1)
  have hfn := freeAlphaCount_nonneg d (c.1.1 * c.1.2 * c.2.2)
  have hpn := divisorProgression_nonneg d (c.1.1 * c.1.2 * c.2.1) d.residue
  rw [coefficientInnerSum_factor]
  simp only [norm_mul, norm_div, norm_star, Complex.norm_natCast]
  calc
    (‖actualPsiQWeight d c.1.1‖ * ‖left c.1.2 c.2.1‖ *
        ‖right c.1.2 c.2.2‖ / (Nat.totient (c.1.1 * c.1.2 * c.2.2) : ℝ)) *
        ‖freeAlphaMass d (c.1.1 * c.1.2 * c.2.2)‖ *
        ‖actualProgression d (c.1.1 * c.1.2 * c.2.1)‖ ≤
      (1 * ((c.1.2 * c.2.1).divisors.card : ℝ) *
        ((c.1.2 * c.2.2).divisors.card : ℝ) /
          (Nat.totient (c.1.1 * c.1.2 * c.2.2) : ℝ)) *
        freeAlphaCount d (c.1.1 * c.1.2 * c.2.2) *
        divisorProgression d (c.1.1 * c.1.2 * c.2.1) d.residue := by
          gcongr <;> first | assumption | positivity
    _ = _ := by ring

theorem coefficientThreeTailSum_eq (d : MediumAtom) (x z : ℝ)
    (c : CoefficientIndex) :
    coefficientThreeTailSum d x z c =
      coefficientInnerSum d c (lambdaSmoothTail d x z) (lambdaSmoothKept d x z) +
      coefficientInnerSum d c (lambdaSmoothKept d x z) (lambdaSmoothTail d x z) +
      coefficientInnerSum d c (lambdaSmoothTail d x z) (lambdaSmoothTail d x z) := by
  simp only [coefficientThreeTailSum, actualThreeTailTerm,
    coefficientInnerSum, Finset.sum_add_distrib]

theorem coefficientThreeTailSum_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (x z : ℝ) (c : CoefficientIndex) (hc : c ∈ coefficientCarrier d z) :
    ‖coefficientThreeTailSum d x z c‖ ≤
      coefficientCost d c *
        divisorProgression d (c.1.1 * c.1.2 * c.2.1) d.residue := by
  obtain ⟨hqd, hrs⟩ := Finset.mem_sigma.mp hc
  have hsmall := dCarrier_pos d z c.1.2 (Finset.mem_product.mp hqd).2
  have hr := roughFiber_pos d z c.1.2 c.2.1 (Finset.mem_product.mp hrs).1
  have hs := roughFiber_pos d z c.1.2 c.2.2 (Finset.mem_product.mp hrs).2
  have hpr := Nat.mul_pos hsmall hr
  have hps := Nat.mul_pos hsmall hs
  have htl := lambdaSmoothTail_norm_le_tau hd x z c.1.2 c.2.1 hpr
  have hkl := lambdaSmoothKept_norm_le_tau hd x z c.1.2 c.2.1 hpr
  have htr := lambdaSmoothTail_norm_le_tau hd x z c.1.2 c.2.2 hps
  have hkr := lambdaSmoothKept_norm_le_tau hd x z c.1.2 c.2.2 hps
  have h₁ := coefficientInnerSum_norm_le hd c
    (lambdaSmoothTail d x z) (lambdaSmoothKept d x z) htl hkr
  have h₂ := coefficientInnerSum_norm_le hd c
    (lambdaSmoothKept d x z) (lambdaSmoothTail d x z) hkl htr
  have h₃ := coefficientInnerSum_norm_le hd c
    (lambdaSmoothTail d x z) (lambdaSmoothTail d x z) htl htr
  rw [coefficientThreeTailSum_eq]
  calc
    ‖coefficientInnerSum d c (lambdaSmoothTail d x z) (lambdaSmoothKept d x z) +
        coefficientInnerSum d c (lambdaSmoothKept d x z) (lambdaSmoothTail d x z) +
        coefficientInnerSum d c (lambdaSmoothTail d x z) (lambdaSmoothTail d x z)‖ ≤
      ‖coefficientInnerSum d c (lambdaSmoothTail d x z) (lambdaSmoothKept d x z)‖ +
      ‖coefficientInnerSum d c (lambdaSmoothKept d x z) (lambdaSmoothTail d x z)‖ +
      ‖coefficientInnerSum d c (lambdaSmoothTail d x z) (lambdaSmoothTail d x z)‖ :=
        (norm_add_le _ _).trans
          (add_le_add_right (norm_add_le _ _) _)
    _ ≤ _ := by
      dsimp [coefficientCost]
      nlinarith [h₁, h₂, h₃]

/-- The finite coefficient packet bound (F), with no Shiu or H-bound premise. -/
theorem blockCoefficientPacket_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (x z D R : ℝ) (l : ℕ) :
    ‖blockCoefficientPacket d x z D R l‖ ≤
      divisorProgression d l d.residue * blockGeometryCost d z D R l := by
  unfold blockCoefficientPacket
  calc
    ‖∑ c ∈ blockCoefficientCarrier d z D R l,
        coefficientThreeTailSum d x z c‖ ≤
      ∑ c ∈ blockCoefficientCarrier d z D R l,
        ‖coefficientThreeTailSum d x z c‖ := norm_sum_le _ _
    _ ≤ ∑ c ∈ blockCoefficientCarrier d z D R l,
        coefficientCost d c * divisorProgression d l d.residue := by
          apply Finset.sum_le_sum
          intro c hc
          have hsource := (Finset.mem_filter.mp hc).1
          have hl := (Finset.mem_filter.mp hc).2.2
          simpa only [hl] using coefficientThreeTailSum_norm_le hd x z c hsource
    _ = divisorProgression d l d.residue * blockGeometryCost d z D R l := by
          rw [← Finset.sum_mul]
          exact mul_comm _ _

/-- Exact interface to the already defined physical paper-block carrier.
The block predicate is independent of n1,n2,m, so finite Fubini does not
introduce any unsupported coefficient or modify either primitive gate. -/
theorem actualPaperBlockPacket_eq_coefficientPacket
    (d : MediumAtom) (x z D R : ℝ) (l : ℕ) :
    actualPaperBlockPacket d x z D R l =
      blockCoefficientPacket d x z D R l := by
  unfold actualPaperBlockPacket blockCoefficientPacket
    paperBlockOuterCarrier s2OuterCarrier blockCoefficientCarrier coefficientCarrier
  simp only [Finset.filter_filter, Finset.sum_filter, Finset.sum_sigma,
    Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro small hsmall
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hblock : D ≤ (small : ℝ) ∧ (small : ℝ) < 2 * D ∧
      R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R ∧
      R ≤ (s : ℝ) ∧ (s : ℝ) < 2 * R
  · by_cases hl : q * small * r = l
    · simp [inPaperBlock, hblock, hl, coefficientThreeTailSum]
    · simp [inPaperBlock, hblock, hl]
  · simp [inPaperBlock, hblock]

/-- Inequality (F) for the literal actual-psi paperBlockOuterCarrier sum. -/
theorem actualPaperBlockPacket_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (x z D R : ℝ) (l : ℕ) :
    ‖actualPaperBlockPacket d x z D R l‖ ≤
      divisorProgression d l d.residue * blockGeometryCost d z D R l := by
  rw [actualPaperBlockPacket_eq_coefficientPacket]
  exact blockCoefficientPacket_norm_le hd x z D R l

/-- Nonzero literal auxiliary coefficients retain their original reduced
residue support. This uses gamma2,gamma3 themselves, not merely the image
carrier, which also contains pairs with zero coefficient. -/
theorem nonzero_labelSubset_coprime
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (z : ℝ) (small rough : ℕ) (P : ℕ × ℕ → Prop)
    (hne : (∑ v ∈ labelSubset d z small rough P,
      d.gamma2 v.1 * d.gamma3 v.2) ≠ 0) :
    Nat.Coprime (small * rough) d.residue.natAbs := by
  obtain ⟨_, _, _, hQ2, hQ3, _, _, _, _, _, _, _, _, _, _, _,
    hgamma2, hgamma3⟩ := hd
  have hwitness : ∃ v ∈ labelSubset d z small rough P,
      d.gamma2 v.1 * d.gamma3 v.2 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Finset.sum_eq_zero (fun v hv => h v hv))
  obtain ⟨v, hv, hterm⟩ := hwitness
  have hsource := (Finset.mem_filter.mp hv).1
  have hlabel := (Finset.mem_filter.mp hv).2.1
  obtain ⟨hv2, hv3⟩ := Finset.mem_product.mp hsource
  have h2ne : d.gamma2 v.1 ≠ 0 := by
    intro hz
    exact hterm (by simp [hz])
  have h3ne : d.gamma3 v.2 ≠ 0 := by
    intro hz
    exact hterm (by simp [hz])
  have hc2 := (hgamma2 v.1 hv2).2 h2ne
  have hc3 := (hgamma3 v.2 hv3).2 h3ne
  have hp : v.1 * v.2 = small * rough := by
    simpa only [hlabel] using labelDW_product d z hsource hQ2 hQ3
  rw [← hp]
  exact Nat.coprime_mul_iff_left.mpr ⟨hc2, hc3⟩

theorem nonzero_smoothKept_coprime
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (x z : ℝ) (small rough : ℕ)
    (hne : lambdaSmoothKept d x z small rough ≠ 0) :
    Nat.Coprime (small * rough) d.residue.natAbs := by
  apply nonzero_labelSubset_coprime hd z small rough
    (individualSmoothWithinY x z)
  simpa only [labelSubset, lambdaSmoothKept] using hne

theorem nonzero_smoothTail_coprime
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (x z : ℝ) (small rough : ℕ)
    (hne : lambdaSmoothTail d x z small rough ≠ 0) :
    Nat.Coprime (small * rough) d.residue.natAbs := by
  apply nonzero_labelSubset_coprime hd z small rough
    (fun v => ¬individualSmoothWithinY x z v)
  simpa only [labelSubset, lambdaSmoothTail] using hne

/-- Every genuinely contributing coefficient has the moving residue
reduced at the LEFT modulus q*d*r. No coprimality between q,d,r is needed. -/
theorem nonzero_coefficientThreeTailSum_coprime
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (x z : ℝ) (c : CoefficientIndex)
    (hc : c ∈ coefficientCarrier d z)
    (hne : coefficientThreeTailSum d x z c ≠ 0) :
    Nat.Coprime (c.1.1 * c.1.2 * c.2.1) d.residue.natAbs := by
  have hqd := (Finset.mem_sigma.mp hc).1
  have hq := (Finset.mem_product.mp hqd).1
  have hqc : Nat.Coprime c.1.1 d.residue.natAbs :=
    (Finset.mem_filter.mp hq).2
  have hleft : lambdaSmoothTail d x z c.1.2 c.2.1 ≠ 0 ∨
      lambdaSmoothKept d x z c.1.2 c.2.1 ≠ 0 := by
    by_contra h
    simp only [not_or, not_ne_iff] at h
    exact hne (by simp [coefficientThreeTailSum, actualThreeTailTerm,
      s2TermWithCoefficients, h.1, h.2])
  have hlc : Nat.Coprime (c.1.2 * c.2.1) d.residue.natAbs := by
    rcases hleft with ht | hk
    · exact nonzero_smoothTail_coprime hd x z c.1.2 c.2.1 ht
    · exact nonzero_smoothKept_coprime hd x z c.1.2 c.2.1 hk
  simpa only [Nat.mul_assoc] using
    (Nat.coprime_mul_iff_left.mpr ⟨hqc, hlc⟩)

/-- This is the reduced-residue licence needed by the later primitive
Shiu step. Zero packets require no progression estimate. -/
theorem nonzero_actualPaperBlockPacket_coprime
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (x z D R : ℝ) (l : ℕ)
    (hne : actualPaperBlockPacket d x z D R l ≠ 0) :
    Nat.Coprime l d.residue.natAbs := by
  rw [actualPaperBlockPacket_eq_coefficientPacket] at hne
  have hwitness : ∃ c ∈ blockCoefficientCarrier d z D R l,
      coefficientThreeTailSum d x z c ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    exact Finset.sum_eq_zero (fun c hc => h c hc)
  obtain ⟨c, hc, hterm⟩ := hwitness
  have hsource := (Finset.mem_filter.mp hc).1
  have hl := (Finset.mem_filter.mp hc).2.2
  simpa only [hl] using nonzero_coefficientThreeTailSum_coprime hd x z c hsource hterm

end
end ImbalancedChen.Part3OriginalS2ActualBlockPacketBound
