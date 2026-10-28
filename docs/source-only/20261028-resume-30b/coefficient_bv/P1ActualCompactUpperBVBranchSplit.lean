import ImbalancedChen.P1ActualCompactUpperLowRankFixedLevelBV
import ImbalancedChen.P1ActualCompactUpperLowRankIntegerBinding

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The manuscript's upper low-rank branch is a rank bound on the actual
rough factor of the full small-times-rough physical modulus.  Its actual
compact attached coefficient already has a below-half BV theorem.

This file retains that SAME coefficient on both sides of an exact branch
split.  The complementary nonzero terms have an actual integer witness
with rough rank at least three.  No joint four-mark coefficient is
identified with this compact upper coefficient, and the high-rank analytic
estimate remains a separate internal obligation.
-/

namespace ImbalancedChen.P1ActualCompactUpperBVBranchSplit

noncomputable section
open Classical Filter
open scoped BigOperators
open P1ActualCompactUpperLowRankPhysicalBV
open P1ActualCompactUpperLowRankFixedLevelBV
open P1ActualCompactUpperLowRankIntegerBinding

/-- The original counting-interface coefficient; no branch changes it. -/
def rho (e h epsilon : ℝ) (m N : ℕ) : ℕ → ℝ :=
  attachedUpperCoefficient 1 thirdPrefixRho epsilon
    (P4ASameRhoCompact.retain e h m) (fun M => M) N

def support (e h epsilon : ℝ) (m N : ℕ) : Finset ℕ :=
  attachedUpperModuli 1 thirdPrefixRho epsilon
    (P4ASameRhoCompact.retain e h m) (fun M => M) N

/-- The high branch keeps zero terms in the displayed support, just as the
physical support does. Every NONZERO term is classified below. -/
def high (e h epsilon : ℝ) (m N : ℕ) : Finset ℕ :=
  (support e h epsilon m N).filter
    (fun q => q ∉ actualAttachedCompactLowRankActive e h m N epsilon)

theorem low_subset_support (e h epsilon : ℝ) (m N : ℕ) :
    actualAttachedCompactLowRankActive e h m N epsilon ⊆ support e h epsilon m N := by
  rw [support, actualAttachedCompact_moduli_eq]
  exact Finset.filter_subset _ _

/-- Exact full-support split for EVERY arithmetic test.  The same rho is
used for AP counts, coprime means, centre terms, and signed discrepancies. -/
theorem signed_branch_split (e h epsilon : ℝ) (m N : ℕ) (F : ℕ → ℝ) :
    (∑ q ∈ support e h epsilon m N, rho e h epsilon m N q * F q) =
      (∑ q ∈ actualAttachedCompactLowRankActive e h m N epsilon,
        rho e h epsilon m N q * F q) +
      ∑ q ∈ high e h epsilon m N, rho e h epsilon m N q * F q := by
  have hf : (support e h epsilon m N).filter
      (fun q => q ∈ actualAttachedCompactLowRankActive e h m N epsilon) =
      actualAttachedCompactLowRankActive e h m N epsilon := by
    ext q
    constructor
    · exact fun hq => (Finset.mem_filter.mp hq).2
    · intro hq
      exact Finset.mem_filter.mpr ⟨low_subset_support e h epsilon m N hq, hq⟩
  have hs := Finset.sum_filter_add_sum_filter_not (support e h epsilon m N)
    (fun q => q ∈ actualAttachedCompactLowRankActive e h m N epsilon)
    (fun q => rho e h epsilon m N q * F q)
  rw [hf] at hs
  exact hs.symm

/-- On a genuinely active high-branch term, the actual small/rough
factorization has rough rank >=3. Uniqueness makes the universal rank
predicate in the existing low branch equivalent to the rank of this
actual nonzero row; an unrelated low-rank factorization cannot intervene. -/
theorem high_active_integer_witness {e h epsilon : ℝ} {m N q : ℕ}
    (hq : q ∈ high e h epsilon m N)
    (hactive : rho e h epsilon m N q ≠ 0) :
    ∃ a ∈ actualSmallRosserSupport N N ((N : ℝ) ^ (epsilon ^ 2)),
      ∃ b ∈ fixedRoughSupport
          (actualExtendedThirdCompactUpperPolicy e h m N false) N N
          ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ (19 / 96 : ℝ)),
        q = a * b ∧ (a : ℝ) < (N : ℝ) ^ epsilon ∧
        fixedRoughCoefficient
          (actualExtendedThirdCompactUpperPolicy e h m N false) N N
          ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ (19 / 96 : ℝ)) b ≠ 0 ∧
        3 ≤ b.primeFactors.card ∧ Nat.Coprime q N := by
  have hnot := (Finset.mem_filter.mp hq).2
  have hnative : actualExtendedThirdCompactRho e h m N N
      ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ (19 / 96 : ℝ))
      ((N : ℝ) ^ epsilon) q ≠ 0 := by
    simpa only [rho, actualAttachedCompact_rho_eq] using hactive
  obtain ⟨a, ha, b, hb, hab, haL, hbactive, hmem, hcop, _, _⟩ :=
    compact_upper_active_integer_lowrank_binding e h m N N
      ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ (19 / 96 : ℝ))
      ((N : ℝ) ^ epsilon) q hnative
  have hrank : 3 ≤ b.primeFactors.card := by
    by_contra hsmall
    have hbcard : b.primeFactors.card ≤ 2 := by omega
    apply hnot
    change q ∈ (actualExtendedThirdCompactModuli e h m N N
      ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ (19 / 96 : ℝ))).filter _
    refine Finset.mem_filter.mpr ⟨hmem, hnative, ?_⟩
    intro a' ha' b' hb' hab'
    have hpair : (a', b') = (a, b) := smallRough_factorization_unique
      (actualSmallRosserSupport_smallPrimeSupportedAt N N _ ha')
      (fixedRoughSupport_roughPrimeSupportedAt
        (actualExtendedThirdCompactUpperPolicy e h m N false) N N _ _ hb')
      (actualSmallRosserSupport_smallPrimeSupportedAt N N _ ha)
      (fixedRoughSupport_roughPrimeSupportedAt
        (actualExtendedThirdCompactUpperPolicy e h m N false) N N _ _ hb)
      (hab'.symm.trans hab)
    have hbEq : b' = b := congrArg Prod.snd hpair
    simpa only [hbEq] using hbcard
  exact ⟨a, ha, b, hb, hab, haL, hbactive, hrank, hcop⟩

/-- The actual low branch still reads the original initial policy at the
SAME complete q. This follows from the actual shallow-tree identity. -/
theorem low_initial_coefficient_identity {e h epsilon : ℝ} {m N q : ℕ}
    (hq : q ∈ actualAttachedCompactLowRankActive e h m N epsilon) :
    rho e h epsilon m N q = actualSmallRoughRho
      (actualExtendedThirdCompactInitialPolicy e m N false) N N
      ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ (19 / 96 : ℝ))
      ((N : ℝ) ^ epsilon) q := by
  obtain ⟨_, hactive, hrank⟩ := Finset.mem_filter.mp hq
  obtain ⟨a, ha, b, hb, hab, _, _, _, _, _, hsame⟩ :=
    compact_upper_active_integer_lowrank_binding e h m N N
      ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ (19 / 96 : ℝ))
      ((N : ℝ) ^ epsilon) q hactive
  have h := hsame (hrank a ha b hb hab)
  simpa only [rho, actualAttachedCompact_rho_eq] using h

/-- A concrete caller for the genuine compact upper low branch.  The
ordinary BV primitive is used through the exact frozen Phase6 supplier;
its threshold precedes every compact policy, mesh and attachment choice.
The formula isolates only the still-open high-rank discrepancy. -/
theorem actual_upper_discrepancy_minus_high_BV (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ e h : ℝ, ∀ m : ℕ, ∀ epsilon : ℝ,
        e ≤ 1 / 384 → epsilon ≤ 2 * e →
        |(∑ q ∈ support e h epsilon m N,
            rho e h epsilon m N q * part3PrimeAPError N N q) -
          ∑ q ∈ high e h epsilon m N,
            rho e h epsilon m N q * part3PrimeAPError N N q| ≤
          C * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  obtain ⟨B, hB, C, hC, hBV⟩ := actualAttachedCompact_BV_and_reciprocal_mass A hA
  refine ⟨B, hB, C, hC, ?_⟩
  filter_upwards [hBV] with N hBV
  intro e h m epsilon he hepsilon
  have hlow := (hBV e h m epsilon he hepsilon).1
  have hsplit := signed_branch_split e h epsilon m N (part3PrimeAPError N N)
  have hid : (∑ q ∈ support e h epsilon m N,
      rho e h epsilon m N q * part3PrimeAPError N N q) -
      (∑ q ∈ high e h epsilon m N,
        rho e h epsilon m N q * part3PrimeAPError N N q) =
      ∑ q ∈ actualAttachedCompactLowRankActive e h m N epsilon,
        rho e h epsilon m N q * part3PrimeAPError N N q := by
    linarith only [hsplit]
  rw [hid]
  simpa only [rho] using hlow

end
end ImbalancedChen.P1ActualCompactUpperBVBranchSplit
