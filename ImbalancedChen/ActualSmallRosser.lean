import ImbalancedChen.RoughPrimeUniverse
import ImbalancedChen.SmallRoughAttachment
import MathlibNt.SieveTheory.LiLiuPrereqWFSmallRosser
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Int.Basic

/-!
# Actual small-prime Rosser weights, including the zero argument

The two coefficients are the fixed dependency's literal lower and upper
Rosser weights on the product of primes `p < w`, `p ∤ N`. Their level is the
real number `L`, with strict endpoint `d < L`. No pointwise sieve inequality
is supplied as a premise.

The divisor sum is taken over the fixed nonzero sieve product's divisors,
not over `n.divisors`. Reindexing through `gcd(M, |n|)` therefore handles
every integer, including zero and negative arguments, exactly.
The density and the attachment to the current causal rough policy remain
separate obligations.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

namespace ActualSmallRosserProvider

open MathlibNt.SieveTheory.LiLiuPrereqWF

abbrev lowerWeight := SmallRosser.lowerWeight
abbrev upperWeight := SmallRosser.upperWeight

end ActualSmallRosserProvider

/-- The real, strictly bounded small-prime carrier. The natural `cap` only
enumerates the primes; a theorem below removes it from the predicate. -/
def actualSmallPrimeFinset (N cap : ℕ) (w : ℝ) : Finset ℕ :=
  roughPrimeFinset N cap 0 w

@[simp] theorem mem_actualSmallPrimeFinset {N cap p : ℕ} {w : ℝ} :
    p ∈ actualSmallPrimeFinset N cap w ↔
      p < cap ∧ Nat.Prime p ∧ ¬p ∣ N ∧ (p : ℝ) < w := by
  simp [actualSmallPrimeFinset, Nat.cast_nonneg]

theorem mem_actualSmallPrimeFinset_iff_of_cutoff_le_cap
    {N cap p : ℕ} {w : ℝ} (hwcap : w ≤ (cap : ℝ)) :
    p ∈ actualSmallPrimeFinset N cap w ↔
      Nat.Prime p ∧ ¬p ∣ N ∧ (p : ℝ) < w := by
  simpa only [actualSmallPrimeFinset, Nat.cast_nonneg, true_and] using
    (mem_roughPrimeFinset_iff_of_cutoff_le_cap
      (N := N) (cap := cap) (p := p) (w := (0 : ℝ)) hwcap)

theorem actualSmallPrimeFinset_prime (N cap : ℕ) (w : ℝ) :
    ∀ p ∈ actualSmallPrimeFinset N cap w, Nat.Prime p :=
  fun _ hp => (mem_actualSmallPrimeFinset.mp hp).2.1

/-- The actual finite presieving product. -/
def actualSmallPrimeProduct (N cap : ℕ) (w : ℝ) : ℕ :=
  (actualSmallPrimeFinset N cap w).prod id

theorem actualSmallPrimeProduct_squarefree (N cap : ℕ) (w : ℝ) :
    Squarefree (actualSmallPrimeProduct N cap w) :=
  MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.primeProduct_squarefree
    _ (actualSmallPrimeFinset_prime N cap w)

theorem actualSmallPrimeProduct_ne_zero (N cap : ℕ) (w : ℝ) :
    actualSmallPrimeProduct N cap w ≠ 0 :=
  (actualSmallPrimeProduct_squarefree N cap w).ne_zero

theorem actualSmallPrimeProduct_coprime_target (N cap : ℕ) (w : ℝ) :
    (actualSmallPrimeProduct N cap w).Coprime N := by
  rw [actualSmallPrimeProduct, Nat.coprime_prod_left_iff]
  intro p hp
  have hpS := mem_actualSmallPrimeFinset.mp hp
  exact hpS.2.1.coprime_iff_not_dvd.mpr hpS.2.2.1

@[simp] theorem actualSmallPrimeProduct_primeFactors (N cap : ℕ) (w : ℝ) :
    (actualSmallPrimeProduct N cap w).primeFactors = actualSmallPrimeFinset N cap w := by
  simpa only [actualSmallPrimeProduct, id_eq] using
    Nat.primeFactors_prod (actualSmallPrimeFinset_prime N cap w)

/-- A common displayed support for both signs. Coefficients outside the
strict level vanish even when their divisor belongs to this display. -/
def actualSmallRosserSupport (N cap : ℕ) (w : ℝ) : Finset ℕ :=
  (actualSmallPrimeProduct N cap w).divisors

theorem actualSmallRosserSupport_squarefree (N cap : ℕ) (w : ℝ) {d : ℕ}
    (hd : d ∈ actualSmallRosserSupport N cap w) : Squarefree d :=
  Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd).1
    (actualSmallPrimeProduct_squarefree N cap w)

theorem actualSmallRosserSupport_coprime_target (N cap : ℕ) (w : ℝ) {d : ℕ}
    (hd : d ∈ actualSmallRosserSupport N cap w) : d.Coprime N :=
  (actualSmallPrimeProduct_coprime_target N cap w).of_dvd_left
    (Nat.mem_divisors.mp hd).1

theorem actualSmallRosserSupport_smallPrimeSupportedAt
    (N cap : ℕ) (w : ℝ) {d : ℕ}
    (hd : d ∈ actualSmallRosserSupport N cap w) : SmallPrimeSupportedAt w d := by
  have hdM : d ∣ actualSmallPrimeProduct N cap w := (Nat.mem_divisors.mp hd).1
  have hsf : Squarefree d := Squarefree.squarefree_of_dvd hdM
    (actualSmallPrimeProduct_squarefree N cap w)
  refine ⟨hsf.ne_zero, ?_⟩
  intro p hp
  have hpM := Nat.primeFactors_mono hdM (actualSmallPrimeProduct_ne_zero N cap w) hp
  rw [actualSmallPrimeProduct_primeFactors] at hpM
  exact (mem_actualSmallPrimeFinset.mp hpM).2.2.2

/-- The actual lower coefficient, with the provider's even-prefix tests. -/
def actualSmallRosserMinus (N cap : ℕ) (w L : ℝ) : ℕ → ℝ :=
  ActualSmallRosserProvider.lowerWeight (actualSmallPrimeProduct N cap w) L

/-- The actual upper coefficient, with the provider's odd-prefix tests. -/
def actualSmallRosserPlus (N cap : ℕ) (w L : ℝ) : ℕ → ℝ :=
  ActualSmallRosserProvider.upperWeight (actualSmallPrimeProduct N cap w) L

theorem actualSmallRosserMinus_abs_le_one (N cap : ℕ) (w L : ℝ) (d : ℕ) :
    |actualSmallRosserMinus N cap w L d| ≤ 1 :=
  MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.lowerWeight_boundedOne _ _ d

theorem actualSmallRosserPlus_abs_le_one (N cap : ℕ) (w L : ℝ) (d : ℕ) :
    |actualSmallRosserPlus N cap w L d| ≤ 1 :=
  MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_boundedOne _ _ d

theorem actualSmallRosserMinus_active {N cap d : ℕ} {w L : ℝ}
    (hd : actualSmallRosserMinus N cap w L d ≠ 0) :
    d ∈ actualSmallRosserSupport N cap w ∧ (d : ℝ) < L ∧ SmallPrimeSupportedAt w d := by
  have h := MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.lowerWeight_active hd
  exact ⟨h.1, h.2.1, actualSmallRosserSupport_smallPrimeSupportedAt N cap w h.1⟩

theorem actualSmallRosserPlus_active {N cap d : ℕ} {w L : ℝ}
    (hd : actualSmallRosserPlus N cap w L d ≠ 0) :
    d ∈ actualSmallRosserSupport N cap w ∧ (d : ℝ) < L ∧ SmallPrimeSupportedAt w d := by
  have h := MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_active hd
  exact ⟨h.1, h.2.1, actualSmallRosserSupport_smallPrimeSupportedAt N cap w h.1⟩

/-- This finite reindexing works even when `n = 0`, because the support is
the divisor set of the nonzero product `M`. -/
theorem supportedDivisorSum_divisors_eq_gcd_sum
    {M : ℕ} (hM : M ≠ 0) (beta : ℕ → ℝ) (n : ℕ) :
    supportedDivisorSum M.divisors beta n = ∑ d ∈ (M.gcd n).divisors, beta d := by
  have hg : M.gcd n ≠ 0 := Nat.gcd_ne_zero_left hM
  have hs : M.divisors.filter (fun d => d ∣ n) = (M.gcd n).divisors := by
    ext d
    constructor
    · intro hd
      obtain ⟨hdM, hdn⟩ := Finset.mem_filter.mp hd
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd (Nat.mem_divisors.mp hdM).1 hdn, hg⟩
    · intro hd
      obtain ⟨hdM, hdn⟩ := Nat.dvd_gcd_iff.mp (Nat.mem_divisors.mp hd).1
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdM, hM⟩, hdn⟩
  unfold supportedDivisorSum
  rw [hs]

/-- Concrete lower and upper divisor sums on all natural arguments, with
the exact support expected by `SignSensitiveAttachment`. No analytic or
pointwise sieve conclusion is among the hypotheses. -/
theorem actualSmallRosser_sandwich_nat
    (N cap : ℕ) (w L : ℝ) (hL : 1 < L) (hwL : w ≤ L) (n : ℕ) :
    supportedDivisorSum (actualSmallRosserSupport N cap w)
        (actualSmallRosserMinus N cap w L) n ≤
        (if (actualSmallPrimeProduct N cap w).Coprime n then (1 : ℝ) else 0) ∧
    (if (actualSmallPrimeProduct N cap w).Coprime n then (1 : ℝ) else 0) ≤
      supportedDivisorSum (actualSmallRosserSupport N cap w)
        (actualSmallRosserPlus N cap w L) n := by
  classical
  have hM := actualSmallPrimeProduct_squarefree N cap w
  have hcut : ∀ p ∈ (actualSmallPrimeProduct N cap w).primeFactors, (p : ℝ) < L := by
    intro p hp
    rw [actualSmallPrimeProduct_primeFactors] at hp
    exact ((mem_actualSmallPrimeFinset.mp hp).2.2.2).trans_le hwL
  unfold actualSmallRosserSupport
  rw [supportedDivisorSum_divisors_eq_gcd_sum hM.ne_zero,
    supportedDivisorSum_divisors_eq_gcd_sum hM.ne_zero]
  constructor
  · exact MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.lowerWeight_divisor_sum
      hM hcut (Nat.gcd_dvd_left _ _)
  · exact MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_divisor_sum
      hM hL (Nat.gcd_dvd_left _ _)

/-- The literal small-prime roughness indicator, independent of enumeration
and defined on every integer, including zero. -/
def actualSmallRoughIndicator (N : ℕ) (w : ℝ) (n : ℤ) : ℝ := by
  classical
  exact if (∀ p : ℕ, Nat.Prime p ∧ ¬p ∣ N ∧ (p : ℝ) < w → ¬(p : ℤ) ∣ n)
    then 1 else 0

theorem actualSmallPrimeProduct_coprime_natAbs_iff
    (N cap : ℕ) (w : ℝ) (hwcap : w ≤ (cap : ℝ)) (n : ℤ) :
    (actualSmallPrimeProduct N cap w).Coprime n.natAbs ↔
      ∀ p : ℕ, Nat.Prime p ∧ ¬p ∣ N ∧ (p : ℝ) < w → ¬(p : ℤ) ∣ n := by
  rw [actualSmallPrimeProduct, Nat.coprime_prod_left_iff]
  constructor
  · intro h p hp hd
    have hpS := (mem_actualSmallPrimeFinset_iff_of_cutoff_le_cap hwcap).mpr hp
    exact (hp.1.coprime_iff_not_dvd.mp (h p hpS)) (Int.natCast_dvd.mp hd)
  · intro h p hp
    have hpS := (mem_actualSmallPrimeFinset_iff_of_cutoff_le_cap hwcap).mp hp
    exact hpS.1.coprime_iff_not_dvd.mpr (fun hd => h p hpS (Int.natCast_dvd.mpr hd))

/-- The fixed-support sum has exactly the intended integer divisibility
semantics. No sign or zero case is dropped by passing to `natAbs`. -/
theorem supportedDivisorSum_natAbs_eq_integer_sum
    (S : Finset ℕ) (beta : ℕ → ℝ) (n : ℤ) :
    supportedDivisorSum S beta n.natAbs =
      ∑ d ∈ S, if (d : ℤ) ∣ n then beta d else 0 := by
  classical
  simp only [supportedDivisorSum, Finset.sum_filter, Int.natCast_dvd]

/-- The actual lower small-prime polynomial on an integer argument. -/
def actualSmallRosserMinusSum (N cap : ℕ) (w L : ℝ) (n : ℤ) : ℝ :=
  supportedDivisorSum (actualSmallRosserSupport N cap w)
    (actualSmallRosserMinus N cap w L) n.natAbs

/-- The actual upper small-prime polynomial on an integer argument. -/
def actualSmallRosserPlusSum (N cap : ℕ) (w L : ℝ) (n : ℤ) : ℝ :=
  supportedDivisorSum (actualSmallRosserSupport N cap w)
    (actualSmallRosserPlus N cap w L) n.natAbs

/-- The manuscript's pointwise small-prime sandwich, now for the actual
Rosser coefficients on every integer. The only assumptions are explicit
level and enumeration inequalities. -/
theorem actualSmallRosser_sandwich
    (N cap : ℕ) (w L : ℝ) (hL : 1 < L) (hwL : w ≤ L)
    (hwcap : w ≤ (cap : ℝ)) (n : ℤ) :
    actualSmallRosserMinusSum N cap w L n ≤ actualSmallRoughIndicator N w n ∧
      actualSmallRoughIndicator N w n ≤ actualSmallRosserPlusSum N cap w L n := by
  classical
  have h := actualSmallRosser_sandwich_nat N cap w L hL hwL n.natAbs
  simpa only [actualSmallRosserMinusSum, actualSmallRosserPlusSum,
    actualSmallRoughIndicator, actualSmallPrimeProduct_coprime_natAbs_iff N cap w hwcap n]
    using h

end

end ImbalancedChen
