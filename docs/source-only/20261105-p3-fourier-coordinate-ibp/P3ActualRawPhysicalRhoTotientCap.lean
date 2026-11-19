import ImbalancedChen.ActualSmallRoughAttachment
import ImbalancedChen.P3ActualSignedPairTotientCap
import Mathlib.Tactic

/-!
P3.6 — ACTUAL raw small/rough physical coefficient, not a hypothetical
pair-convolution coefficient. Manuscript fixed at
chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product-completion §3 (T) and §4 (F).

The earlier two-log mass bound assumed an arbitrary finite pair source
and one-bounded coefficients. Here the SAME concrete
`actualSmallRoughRho` defined by `FiniteUpperCarrierCore` is used:
- actual lower/upper Rosser branch selection is kept;
- actual first-exit retained rough Möbius coefficients are kept;
- small primes < w, rough primes >= w (including the equality case);
- the product is the original integer physical modulus;
- all actual source pairs are recovered, without a new coefficient.

The cap inequalities on the actual small/rough divisor supports are
EXPLICIT hypotheses. This does not prove that those caps are fixed powers
of N, nor identify the final causally compiled INTEGER rho_N with the raw
REAL attachment. No PP discrepancy, density bound or external result is
an assumption. SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualRawPhysicalRhoTotientCap
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualPhysicalTotientConvolution
open ImbalancedChen.P3ActualSignedPairTotientCap

/-- Exact concrete source identity, including the sign-sensitive
Rosser choice made according to the actual retained rough coefficient.
Cutoff disjointness, not a synthetic fibre-uniqueness premise, is used. -/
theorem actual_raw_rho_at_pair
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (a b : ℕ)
    (ha : a ∈ actualSmallRosserSupport N cap w)
    (hb : b ∈ fixedRoughSupport retainOdd N cap w z) :
    actualSmallRoughRho retainOdd N cap w z L (a * b) =
      signAttachedCoefficient
        (fixedRoughCoefficient retainOdd N cap w z b)
        (actualSmallRosserMinus N cap w L a)
        (actualSmallRosserPlus N cap w L a) := by
  simpa only [actualSmallRoughRho, smallRoughPairCoefficient] using
    (smallRoughRho_mul
      (fun d hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
      (fun d hd => fixedRoughSupport_roughPrimeSupportedAt
        retainOdd N cap w z hd)
      (fixedRoughCoefficient retainOdd N cap w z)
      (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L) ha hb)

/-- The actual raw pair coefficient is genuinely one-bounded, including
a branch selected by the SIGN of the rough Möbius coefficient. -/
theorem actual_raw_pair_coefficient_abs_le_one
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (a b : ℕ)
    (ha : a ∈ actualSmallRosserSupport N cap w)
    (hb : b ∈ fixedRoughSupport retainOdd N cap w z) :
    |signAttachedCoefficient
        (fixedRoughCoefficient retainOdd N cap w z b)
        (actualSmallRosserMinus N cap w L a)
        (actualSmallRosserPlus N cap w L a)| ≤ 1 := by
  rw [← actual_raw_rho_at_pair retainOdd N cap w z L a b ha hb]
  exact actualSmallRoughRho_abs_le_one retainOdd N cap w z L (a * b)

/-- The positive PHYSICAL reciprocal-totient mass of the exact raw
attachment. In particular the denominator is phi(q) for the FULL
integer modulus q, not a density or auxiliary level. -/
def actualRawPhysicalTotientMass
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) : ℝ :=
  ∑ q ∈ actualSmallRoughModuli retainOdd N cap w z,
    |actualSmallRoughRho retainOdd N cap w z L q| *
      (Nat.totient q : ℝ)⁻¹

/-- Concrete source admission of the TWO-LOG physical mean budget.

The only additional numerical premises concern the true finite factor
supports: every actual small divisor <= A, every actual retained rough
divisor <= B. Their polynomial size in N is NOT proved here. The
actual rho, global original product carrier, exact phi, and sign-dependent
Rosser/rough coefficients are unchanged. -/
theorem actual_raw_physical_mass_le_log_caps
    (retainOdd : List ℕ → Bool) (N cap A B : ℕ) (w z L : ℝ)
    (hA : ∀ a ∈ actualSmallRosserSupport N cap w, a ≤ A)
    (hB : ∀ b ∈ fixedRoughSupport retainOdd N cap w z, b ≤ B) :
    actualRawPhysicalTotientMass retainOdd N cap w z L ≤
      logTotientCap A * logTotientCap B := by
  classical
  let s := actualSmallRosserSupport N cap w
  let r := fixedRoughSupport retainOdd N cap w z
  let c := fixedRoughCoefficient retainOdd N cap w z
  let lo := actualSmallRosserMinus N cap w L
  let hi := actualSmallRosserPlus N cap w L
  have hs : ∀ a ∈ s, SmallPrimeSupportedAt w a := by
    intro a ha
    exact actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha
  have hr : ∀ b ∈ r, RoughPrimeSupportedAt w b := by
    intro b hb
    exact fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hb
  have hscap : s ⊆ Finset.Icc 1 A := by
    intro a ha
    have hp : 0 < a := Nat.pos_of_ne_zero (hs a ha).1
    exact Finset.mem_Icc.mpr ⟨by omega, hA a ha⟩
  have hrcap : r ⊆ Finset.Icc 1 B := by
    intro b hb
    have hp : 0 < b := Nat.pos_of_ne_zero (hr b hb).1
    exact Finset.mem_Icc.mpr ⟨by omega, hB b hb⟩
  have hAsum :
      (∑ a ∈ Finset.Icc 1 A, (Nat.totient a : ℝ)⁻¹) ≤
        logTotientCap A := sum_reciprocal_totient_le_log A
  have hBsum :
      (∑ b ∈ Finset.Icc 1 B, (Nat.totient b : ℝ)⁻¹) ≤
        logTotientCap B := sum_reciprocal_totient_le_log B
  unfold actualRawPhysicalTotientMass
  change (∑ q ∈ smallRoughModuli s r,
      |smallRoughRho s r c lo hi q| * (Nat.totient q : ℝ)⁻¹) ≤ _
  rw [sum_smallRoughModuli hs hr
    (fun q => |smallRoughRho s r c lo hi q| * (Nat.totient q : ℝ)⁻¹)]
  calc
    (∑ x ∈ smallRoughPairs s r,
        |smallRoughRho s r c lo hi (x.1 * x.2)| *
          (Nat.totient (x.1 * x.2) : ℝ)⁻¹) ≤
      ∑ x ∈ smallRoughPairs s r,
        (Nat.totient x.1 : ℝ)⁻¹ *
          (Nat.totient x.2 : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro x hx
        have hcoeff :
            |smallRoughRho s r c lo hi (x.1 * x.2)| ≤ 1 := by
          exact actualSmallRoughRho_abs_le_one
            retainOdd N cap w z L (x.1 * x.2)
        have hpos : 0 < x.1 ∧ 0 < x.2 := by
          obtain ⟨ha, hb⟩ := Finset.mem_product.mp hx
          exact ⟨Nat.pos_of_ne_zero (hs x.1 ha).1,
            Nat.pos_of_ne_zero (hr x.2 hb).1⟩
        calc
          _ ≤ (Nat.totient (x.1 * x.2) : ℝ)⁻¹ := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hcoeff (by positivity)
          _ ≤ (Nat.totient x.1 : ℝ)⁻¹ *
                (Nat.totient x.2 : ℝ)⁻¹ :=
            reciprocal_totient_product_le x.1 x.2 hpos.1 hpos.2
    _ ≤ ∑ x ∈ (Finset.Icc 1 A).product (Finset.Icc 1 B),
          (Nat.totient x.1 : ℝ)⁻¹ *
            (Nat.totient x.2 : ℝ)⁻¹ := by
        change (∑ x ∈ s.product r,
          (Nat.totient x.1 : ℝ)⁻¹ * (Nat.totient x.2 : ℝ)⁻¹) ≤ _
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.product_mono hscap hrcap)
          (fun x hx hxnot => by positivity)
    _ = (∑ a ∈ Finset.Icc 1 A, (Nat.totient a : ℝ)⁻¹) *
          (∑ b ∈ Finset.Icc 1 B, (Nat.totient b : ℝ)⁻¹) := by
        rw [Finset.sum_product, Finset.sum_mul_sum]
    _ ≤ logTotientCap A *
          (∑ b ∈ Finset.Icc 1 B, (Nat.totient b : ℝ)⁻¹) := by
        exact mul_le_mul_of_nonneg_right hAsum
          (Finset.sum_nonneg (fun b hb => by positivity))
    _ ≤ logTotientCap A * logTotientCap B := by
        exact mul_le_mul_of_nonneg_left hBsum
          (logTotientCap_nonneg A)

end
end ImbalancedChen.P3ActualRawPhysicalRhoTotientCap
