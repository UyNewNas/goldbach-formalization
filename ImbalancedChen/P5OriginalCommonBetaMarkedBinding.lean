import ImbalancedChen.P5OriginalCommonBetaTargetTransport
import ImbalancedChen.P5ZU1011OriginalSixteenArithmeticProducts
import ImbalancedChen.P5ZU1011OriginalW16SmallBetaMonomials

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The ORIGINAL common pair at w=N^(nu0*eta^2), L=N^(nu0*eta) is chosen using
N alone. Every actual joint U10/U11 four-prime prefix has all marked primes
>=N^(417/5000). Thus one exponent choice before all rows yields exactly
the same beta pair at target fullPrefix(t)*N and any covering enumeration.
The full physical N level is retained, not changed to (fullPrefix*N)^ell.

The resulting actual nonzero factor feeds the existing SmallBetaActive
interface used by all three original W/ordinary monomial budgets. Those
already-proved monomial theorems are deliberately not copied here.
-/

namespace ImbalancedChen.P5Z.OriginalCommonBetaMarkedBinding

noncomputable section
open P5U1011JointOverlap
open U1011OriginalSixteenArithmeticProducts
open OriginalCommonBetaTargetTransport
open U1011OriginalW16SmallBetaMonomials

/-- The genuine original JOINT carrier, including both bands and their
actual mask, makes the full marked prefix coprime to the common product.
No desired coprimality or beta equality is supplied as a premise. -/
theorem original_prefix_coprime_common_small {N enumeration : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ jointSelector N E)
    (nu0 eta : ℝ) (homega : nu0 * eta ^ 2 ≤ (417 / 5000 : ℝ))
    (hcap : (N : ℝ) ^ (nu0 * eta ^ 2) ≤ (enumeration : ℝ)) :
    (fullPrefix t).Coprime
      (actualSmallPrimeProduct N enumeration ((N : ℝ) ^ (nu0 * eta ^ 2))) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hmarked : (N : ℝ) ^ (417 / 5000 : ℝ) ≤ (slots t 3 : ℝ) := by
    simpa [slots] using (joint_band_and_mask ht).1
  have hsmall : (N : ℝ) ^ (nu0 * eta ^ 2) ≤ (slots t 3 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hNreal homega).trans hmarked
  rw [currentChen_actualSmallPrimeProduct_eq_sieveProduct N enumeration _ hcap]
  exact fullPrefix_coprime_lowered_sieve ht hsmall

/-- ONE original physical beta pair, before policy/box/tuple enumeration.
Every row-target pair equals it as complete functions, including inactive
coefficients, with exactly the same physical w and L. -/
theorem original_common_pair_on_actual_mark {N enumeration : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ jointSelector N E)
    (nu0 eta : ℝ) (homega : nu0 * eta ^ 2 ≤ (417 / 5000 : ℝ))
    (hcap : (N : ℝ) ^ (nu0 * eta ^ 2) ≤ (enumeration : ℝ)) :
    let w := (N : ℝ) ^ (nu0 * eta ^ 2)
    let L := (N : ℝ) ^ (nu0 * eta)
    actualSmallRosserPlus (fullPrefix t * N) enumeration w L =
      actualSmallRosserPlus N (Nat.ceil w) w L ∧
    actualSmallRosserMinus (fullPrefix t * N) enumeration w L =
      actualSmallRosserMinus N (Nat.ceil w) w L := by
  dsimp only
  have hcommon := Nat.le_ceil ((N : ℝ) ^ (nu0 * eta ^ 2))
  exact actual_small_pair_target_mul_cover
    (original_prefix_coprime_common_small hN ht nu0 eta homega hcommon)
    hcommon hcap _

/-- The same rough sign branch is preserved at every actual marked row.
The common beta level remains N^(nu0*eta), independent of the mark. -/
theorem original_common_signed_pair_on_actual_mark {N enumeration : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ jointSelector N E)
    (nu0 eta c : ℝ) (homega : nu0 * eta ^ 2 ≤ (417 / 5000 : ℝ))
    (hcap : (N : ℝ) ^ (nu0 * eta ^ 2) ≤ (enumeration : ℝ)) :
    let w := (N : ℝ) ^ (nu0 * eta ^ 2)
    let L := (N : ℝ) ^ (nu0 * eta)
    (if 0 ≤ c then actualSmallRosserPlus (fullPrefix t * N) enumeration w L
      else actualSmallRosserMinus (fullPrefix t * N) enumeration w L) =
    (if 0 ≤ c then actualSmallRosserPlus N (Nat.ceil w) w L
      else actualSmallRosserMinus N (Nat.ceil w) w L) := by
  dsimp only
  have hp := original_common_pair_on_actual_mark hN ht nu0 eta homega hcap
  dsimp only at hp
  rw [hp.1, hp.2]

/-- Exact entry into the existing actual-factor/all-three-budget API.
A nonzero coefficient at the marked target and COMMON physical level is
precisely SmallBetaActive for the one common pair based on N. -/
theorem original_mark_active_iff_common {N enumeration e : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ jointSelector N E)
    (nu0 eta : ℝ) (homega : nu0 * eta ^ 2 ≤ (417 / 5000 : ℝ))
    (hcap : (N : ℝ) ^ (nu0 * eta ^ 2) ≤ (enumeration : ℝ)) :
    let w := (N : ℝ) ^ (nu0 * eta ^ 2)
    let ell := nu0 * eta
    (actualSmallRosserPlus (fullPrefix t * N) enumeration w ((N : ℝ) ^ ell) e ≠ 0 ∨
      actualSmallRosserMinus (fullPrefix t * N) enumeration w ((N : ℝ) ^ ell) e ≠ 0) ↔
      SmallBetaActive N (Nat.ceil w) e w ell := by
  dsimp only
  have hp := original_common_pair_on_actual_mark hN ht nu0 eta homega hcap
  dsimp only at hp
  rw [hp.1, hp.2]
  rfl

end
end ImbalancedChen.P5Z.OriginalCommonBetaMarkedBinding
