import ImbalancedChen.P4AOriginalFull87WeightedSharpSmooth
import ImbalancedChen.CoprimeRecentering
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4, original-prime smoothing: exact finite primitive-recentering of the
SAME physical full-beta coefficient. The smooth original-prime source is
first converted to its real weighted prime AP sum, not a different sieve.
For each modulus the exact-coprime average differs from the full prime
weighted average by precisely its weighted modulus-prime divisors.
No PP theorem, Gevrey profile, q-level asymptotic, or reserve is assumed.
For a nonprime centre the p=N zero gap never enters the literal source.
-/

namespace ImbalancedChen.P4AOriginalFull87WeightedPrimitiveRecentering
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87WeightedSharpSmooth
open P4AOriginalFull87LicensedSixthPolicy

/-- Prime divisors of the physical modulus, with the original smoothing
weight (not a unit-mass replacement). -/
def weightedModulusPrimeMass (N D d : ℕ) (W : ℕ → ℝ) : ℝ :=
  ∑ p ∈ chenPrimePrefix (N + D), if p ∣ d then W p else 0

/-- The full smooth weighted mass, with the same enlarged prime universe. -/
def weightedPrimeMass (N D : ℕ) (W : ℕ → ℝ) : ℝ :=
  ∑ p ∈ chenPrimePrefix (N + D), W p

/-- Exactly which prime mass the reduced-residue mean removes. This
identity holds for signed W and for d=0 (no inverse φ is used here). -/
theorem weighted_coprime_mass_eq_full_sub_modulus_primes
    (N D d : ℕ) (W : ℕ → ℝ) :
    finiteCoprimeMass (chenPrimePrefix (N + D)) W d =
      weightedPrimeMass N D W - weightedModulusPrimeMass N D d W := by
  classical
  have hpartition :
      finiteCoprimeMass (chenPrimePrefix (N + D)) W d +
        weightedModulusPrimeMass N D d W = weightedPrimeMass N D W := by
    simp only [finiteCoprimeMass, weightedModulusPrimeMass,
      weightedPrimeMass, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hpprime := (mem_chenPrimePrefix.mp hp).2
    by_cases hd : p ∣ d
    · have hnot : ¬ Nat.Coprime p d := by
        intro hc
        exact (hpprime.coprime_iff_not_dvd.mp hc) hd
      simp [hd, hnot]
    · have hcop : Nat.Coprime p d :=
        hpprime.coprime_iff_not_dvd.mpr hd
      simp [hd, hcop]
  linarith

/-- The actual smooth original-prime fibre, at a nonprime centre, is
literally the weighted AP fibre of the same FULL physical q. In particular,
modulus 0 is not silently discarded and all prime occurrences remain in
the same Finset prefix. -/
theorem original_smooth_eq_actual_weighted_AP
    (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ)
    (hN : ¬ Nat.Prime N) :
    originalSmoothLiteral P N D cap w z L W =
      ∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
        actualSmallRoughRho (P false) N cap w z L d *
          finiteCongruenceMass (chenPrimePrefix (N + D)) W N d := by
  classical
  let Q := actualSmallRoughModuli (P false) N cap w z
  let ρ := actualSmallRoughRho (P false) N cap w z L
  let S := chenPrimePrefix (N + D)
  have hpoint (p : ℕ) (hp : p ∈ S) :
      (if p < N then W p * originalGapFibre P N cap w z L (N - p)
       else if N < p then W p * originalGapFibre P N cap w z L (p - N)
       else 0) =
      ∑ d ∈ Q, ρ d * (if Nat.ModEq d p N then W p else 0) := by
    have hprime : Nat.Prime p := (mem_chenPrimePrefix.mp hp).2
    by_cases hlt : p < N
    · have hgap (d : ℕ) : d ∣ N - p ↔ Nat.ModEq d p N :=
        dvd_sub_iff_modEq_of_le (Nat.le_of_lt hlt)
      simp only [if_pos hlt]
      change W p * (∑ d ∈ Q.filter (fun d => d ∣ N - p), ρ d) = _
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdiv : d ∣ N - p
      · have hmod := (hgap d).mp hdiv
        simp [hdiv, hmod, mul_comm]
      · have hmod : ¬Nat.ModEq d p N := fun hm => hdiv ((hgap d).mpr hm)
        simp [hdiv, hmod]
    · by_cases hgt : N < p
      · have hgap (d : ℕ) : d ∣ p - N ↔ Nat.ModEq d p N := by
          constructor
          · intro hd
            exact ((dvd_sub_iff_modEq_of_le (Nat.le_of_lt hgt)).mp hd).symm
          · intro hd
            exact (dvd_sub_iff_modEq_of_le (Nat.le_of_lt hgt)).mpr hd.symm
        simp only [if_neg hlt, if_pos hgt]
        change W p * (∑ d ∈ Q.filter (fun d => d ∣ p - N), ρ d) = _
        rw [Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hdiv : d ∣ p - N
        · have hmod := (hgap d).mp hdiv
          simp [hdiv, hmod, mul_comm]
        · have hmod : ¬Nat.ModEq d p N := fun hm => hdiv ((hgap d).mpr hm)
          simp [hdiv, hmod]
      · have heq : p = N := by omega
        exact (hN (heq ▸ hprime)).elim
  unfold originalSmoothLiteral
  change (∑ p ∈ S,
      if p < N then W p * originalGapFibre P N cap w z L (N - p)
      else if N < p then W p * originalGapFibre P N cap w z L (p - N)
      else 0) = _
  calc
    _ = ∑ p ∈ S, ∑ d ∈ Q,
          ρ d * (if Nat.ModEq d p N then W p else 0) := by
            apply Finset.sum_congr rfl
            intro p hp
            exact hpoint p hp
    _ = ∑ d ∈ Q, ∑ p ∈ S,
          ρ d * (if Nat.ModEq d p N then W p else 0) :=
            Finset.sum_comm
    _ = ∑ d ∈ Q, ρ d * finiteCongruenceMass S W N d := by
          apply Finset.sum_congr rfl
          intro d hd
          simp only [finiteCongruenceMass, Finset.sum_filter,
            Finset.mul_sum]

/-- Exact primitive recentering for a smooth ORIGINAL prime and its frozen
physical coefficient: no independent post-smoothing rho. The explicit
modulus-prime correction has a MINUS sign. -/
theorem original_smooth_primitive_recentered_same_rho
    (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ)
    (hN : ¬ Nat.Prime N) :
    originalSmoothLiteral P N D cap w z L W -
        weightedPrimeMass N D W *
          (∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
            actualSmallRoughRho (P false) N cap w z L d /
              (Nat.totient d : ℝ)) =
      (∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
        actualSmallRoughRho (P false) N cap w z L d *
          finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d) -
      (∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
        actualSmallRoughRho (P false) N cap w z L d *
          (weightedModulusPrimeMass N D d W / (Nat.totient d : ℝ))) := by
  classical
  let Q := actualSmallRoughModuli (P false) N cap w z
  let ρ := actualSmallRoughRho (P false) N cap w z L
  let S := chenPrimePrefix (N + D)
  let T := weightedPrimeMass N D W
  have hpoint (d : ℕ) :
      finiteCongruenceMass S W N d - T / (Nat.totient d : ℝ) =
        finitePrimitiveDiscrepancy S W N d -
          weightedModulusPrimeMass N D d W / (Nat.totient d : ℝ) := by
    have hc := weighted_coprime_mass_eq_full_sub_modulus_primes N D d W
    change finiteCoprimeMass S W d = T - weightedModulusPrimeMass N D d W at hc
    unfold finitePrimitiveDiscrepancy
    rw [hc]
    ring
  rw [original_smooth_eq_actual_weighted_AP P N D cap w z L W hN]
  change (∑ d ∈ Q, ρ d * finiteCongruenceMass S W N d) -
    T * (∑ d ∈ Q, ρ d / (Nat.totient d : ℝ)) = _
  calc
    _ = ∑ d ∈ Q, ρ d *
          (finiteCongruenceMass S W N d - T / (Nat.totient d : ℝ)) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro d _
          ring
    _ = ∑ d ∈ Q, ρ d *
          (finitePrimitiveDiscrepancy S W N d -
            weightedModulusPrimeMass N D d W / (Nat.totient d : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d _
          rw [hpoint d]
    _ = (∑ d ∈ Q, ρ d * finitePrimitiveDiscrepancy S W N d) -
          (∑ d ∈ Q,
             ρ d * (weightedModulusPrimeMass N D d W /
               (Nat.totient d : ℝ))) := by
          simp only [mul_sub, Finset.sum_sub_distrib]

end
end ImbalancedChen.P4AOriginalFull87WeightedPrimitiveRecentering
