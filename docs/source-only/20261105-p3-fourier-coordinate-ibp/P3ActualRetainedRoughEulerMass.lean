import ImbalancedChen.P3ActualRawActiveLevelTotientCap
import ImbalancedChen.FixedRoughCoefficients
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic

/-!
P3.6 — retained first-exit rough Euler-factor mass, without a rank cap.
Frozen paper: UyNewNas/chen-imbalanced-semiprimes@
9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §3(T), §4(F).

The earlier rough modulus budget used a cap^K on every retained product.
For arbitrary retainOdd, this K is not uniformly bounded. Instead this
packet uses the genuine squarefree prime-factor support of every actual
first-exit modulus. Its reciprocal-totient mass is no larger than the
FULL finite Euler product over the original roughPrimeUniverse.
No bound for that Euler product by a fixed log N power is asserted here.
The actual coefficient is still the raw real rho, not final causal rho_N.
No classical analytic input is implemented or assumed.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualRetainedRoughEulerMass
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualRawActiveLevelTotientCap
open ImbalancedChen.P3ActualRawPhysicalRhoTotientCap
open ImbalancedChen.P3ActualSignedPairTotientCap
open ImbalancedChen.P3ActualPhysicalTotientConvolution

/-- Exact weight of one prime, including the prime 2. -/
private def invPhiPrime (p : ℕ) : ℝ := ((p - 1 : ℕ) : ℝ)⁻¹

/-- Purely finite squarefree Euler expansion; does not use any analytic
prime-counting or Mertens estimate. -/
private theorem sum_powerset_prime_weights (P : Finset ℕ) :
    (∑ T ∈ P.powerset, ∏ p ∈ T, invPhiPrime p) =
      ∏ p ∈ P, (1 + invPhiPrime p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [invPhiPrime]
  | @insert p P hp ih =>
    rw [Finset.sum_powerset_insert hp, Finset.prod_insert hp]
    have hsecond :
        (∑ T ∈ P.powerset, ∏ q ∈ insert p T, invPhiPrime q) =
          invPhiPrime p * (∑ T ∈ P.powerset, ∏ q ∈ T, invPhiPrime q) := by
      calc
        _ = ∑ T ∈ P.powerset,
              invPhiPrime p * (∏ q ∈ T, invPhiPrime q) := by
          apply Finset.sum_congr rfl
          intro T hT
          have hpT : p ∉ T := fun h => hp ((Finset.mem_powerset.mp hT) h)
          rw [Finset.prod_insert hpT]
        _ = _ := (Finset.mul_sum).symm
    rw [hsecond, ih]
    ring

/-- For squarefree n the reciprocal totient is exactly the product of
prime reciprocal (p-1) factors, with no assumption about the ordering. -/
private theorem inv_totient_of_squarefree (n : ℕ) (hn : Squarefree n) :
    (Nat.totient n : ℝ)⁻¹ =
      ∏ p ∈ n.primeFactors, invPhiPrime p := by
  have hphi : Nat.totient n =
      ∏ p ∈ n.primeFactors, (p - 1) := by
    calc
      Nat.totient n =
          (n / ∏ p ∈ n.primeFactors, p) *
            ∏ p ∈ n.primeFactors, (p - 1) :=
        Nat.totient_eq_div_primeFactors_mul n
      _ = ∏ p ∈ n.primeFactors, (p - 1) := by
        rw [Nat.prod_primeFactors_of_squarefree hn]
        simp [hn.ne_zero]
  simp [hphi, invPhiPrime, Nat.cast_prod, Finset.prod_inv_distrib]

/-- General finite support estimate. The only content requirements are
squarefreeness and membership of ALL prime factors in P. In particular
there is no bound on |S|, the rank, or the size of the product modulus. -/
private theorem squarefree_support_mass_le_euler
    (S P : Finset ℕ)
    (hsq : ∀ b ∈ S, Squarefree b)
    (hprime : ∀ b ∈ S, b.primeFactors ⊆ P) :
    (∑ b ∈ S, (Nat.totient b : ℝ)⁻¹) ≤
      ∏ p ∈ P, (1 + invPhiPrime p) := by
  classical
  have hinj : Set.InjOn Nat.primeFactors S := by
    intro b hb c hc hbc
    calc
      b = ∏ p ∈ b.primeFactors, p :=
        (Nat.prod_primeFactors_of_squarefree (hsq b hb)).symm
      _ = ∏ p ∈ c.primeFactors, p := by rw [hbc]
      _ = c := Nat.prod_primeFactors_of_squarefree (hsq c hc)
  have hsub : S.image Nat.primeFactors ⊆ P.powerset := by
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨b, hb, rfl⟩
    exact Finset.mem_powerset.mpr (hprime b hb)
  calc
    (∑ b ∈ S, (Nat.totient b : ℝ)⁻¹) =
        ∑ b ∈ S, ∏ p ∈ b.primeFactors, invPhiPrime p := by
      apply Finset.sum_congr rfl
      intro b hb
      exact inv_totient_of_squarefree b (hsq b hb)
    _ = ∑ T ∈ S.image Nat.primeFactors, ∏ p ∈ T, invPhiPrime p := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑ T ∈ P.powerset, ∏ p ∈ T, invPhiPrime p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro T hT hnot
      simp only [invPhiPrime]
      positivity
    _ = _ := sum_powerset_prime_weights P

/-- Finite Euler factor bound on the ACTUAL retained rough first-exit
source. It is valid for every retention policy, including policies with
unbounded retained rank. The prime interval and N-coprimality are exact. -/
def roughEulerMass (N cap : ℕ) (w z : ℝ) : ℝ :=
  ∏ p ∈ roughPrimeFinset N cap w z,
    (1 + ((p - 1 : ℕ) : ℝ)⁻¹)

theorem actual_retained_rough_totient_mass_le_euler
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    (∑ b ∈ fixedRoughSupport retainOdd N cap w z,
      (Nat.totient b : ℝ)⁻¹) ≤ roughEulerMass N cap w z := by
  classical
  let S := fixedRoughSupport retainOdd N cap w z
  let P := (roughPrimeUniverse N cap w z).toFinset
  have hsq : ∀ b ∈ S, Squarefree b := by
    intro b hb
    exact fixedRoughSupport_squarefree retainOdd N cap w z hb
  have hprime : ∀ b ∈ S, b.primeFactors ⊆ P := by
    intro b hb p hp
    change p ∈ (roughPrimeUniverse N cap w z).toFinset
    simpa using fixedRoughSupport_primeFactors_mem retainOdd N cap w z hb hp
  have h := squarefree_support_mass_le_euler S P hsq hprime
  simpa only [S, P, roughPrimeUniverse_toFinset, roughEulerMass,
    invPhiPrime] using h

/-- Source-level physical rough mean budget with NO retained-rank or
rough-factor size premise. The remaining factor is an explicit, finite,
original-carrier Euler product, not a claimed log^E uniform estimate. -/
theorem actual_raw_physical_mass_le_active_level_euler
    (retainOdd : List ℕ → Bool) (N cap A : ℕ) (w z L : ℝ)
    (hLA : L ≤ (A : ℝ)) :
    actualRawPhysicalTotientMass retainOdd N cap w z L ≤
      logTotientCap A * roughEulerMass N cap w z := by
  classical
  let s := actualSmallRosserSupport N cap w
  let r := fixedRoughSupport retainOdd N cap w z
  let t := activeSmallRosserByLevel N cap w L
  let Q := actualSmallRoughModuli retainOdd N cap w z
  let Q' := smallRoughModuli t r
  let rho := actualSmallRoughRho retainOdd N cap w z L
  let F : ℕ → ℝ := fun q => |rho q| * (Nat.totient q : ℝ)⁻¹
  have hs : ∀ a ∈ t, SmallPrimeSupportedAt w a := by
    intro a ha
    exact actualSmallRosserSupport_smallPrimeSupportedAt N cap w
      (Finset.mem_filter.mp ha).1
  have hr : ∀ b ∈ r, RoughPrimeSupportedAt w b := by
    intro b hb
    exact fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hb
  have htcap : t ⊆ Finset.Icc 1 A := by
    intro a ha
    have ha0 : 0 < a := Nat.pos_of_ne_zero (hs a ha).1
    have haReal : (a : ℝ) ≤ (A : ℝ) :=
      (le_of_lt (Finset.mem_filter.mp ha).2).trans hLA
    exact Finset.mem_Icc.mpr ⟨ha0, by exact_mod_cast haReal⟩
  have hqsub : Q' ⊆ Q := by
    change (smallRoughPairs t r).image (fun x => x.1 * x.2) ⊆
      (smallRoughPairs s r).image (fun x => x.1 * x.2)
    apply Finset.image_mono
    change t.product r ⊆ s.product r
    exact Finset.product_mono (Finset.filter_subset _ _) (Finset.Subset.rfl)
  have hzero : ∀ q ∈ Q, q ∉ Q' → F q = 0 := by
    intro q hq hnot
    have hrho : rho q = 0 := by
      by_contra hnz
      have hactive : q ∈ activeRawPhysicalModuli retainOdd N cap w z L :=
        Finset.mem_filter.mpr ⟨hq, hnz⟩
      exact hnot (active_raw_physical_moduli_subset
        retainOdd N cap w z L hactive)
    simp [F, hrho]
  have hdrop : (∑ q ∈ Q, F q) = ∑ q ∈ Q', F q :=
    (Finset.sum_subset hqsub hzero).symm
  change (∑ q ∈ Q, F q) ≤ _
  rw [hdrop, sum_smallRoughModuli hs hr F]
  calc
    (∑ x ∈ smallRoughPairs t r, F (x.1 * x.2)) ≤
      ∑ x ∈ smallRoughPairs t r,
        (Nat.totient x.1 : ℝ)⁻¹ * (Nat.totient x.2 : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hx
      have hpos : 0 < x.1 ∧ 0 < x.2 :=
        ⟨Nat.pos_of_ne_zero (hs x.1 ha).1,
          Nat.pos_of_ne_zero (hr x.2 hb).1⟩
      have hcoeff : |rho (x.1 * x.2)| ≤ 1 :=
        actualSmallRoughRho_abs_le_one retainOdd N cap w z L _
      calc
        F (x.1 * x.2) ≤
            (Nat.totient (x.1 * x.2) : ℝ)⁻¹ := by
          simpa only [F, one_mul] using
            mul_le_mul_of_nonneg_right hcoeff (by positivity)
        _ ≤ (Nat.totient x.1 : ℝ)⁻¹ *
            (Nat.totient x.2 : ℝ)⁻¹ :=
          reciprocal_totient_product_le x.1 x.2 hpos.1 hpos.2
    _ ≤ ∑ x ∈ (Finset.Icc 1 A).product r,
          (Nat.totient x.1 : ℝ)⁻¹ *
          (Nat.totient x.2 : ℝ)⁻¹ := by
      change (∑ x ∈ t.product r,
        (Nat.totient x.1 : ℝ)⁻¹ * (Nat.totient x.2 : ℝ)⁻¹) ≤ _
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.product_mono htcap (Finset.Subset.rfl))
        (fun x hx hnot => by positivity)
    _ = (∑ a ∈ Finset.Icc 1 A, (Nat.totient a : ℝ)⁻¹) *
        (∑ b ∈ r, (Nat.totient b : ℝ)⁻¹) := by
      rw [Finset.sum_product, Finset.sum_mul_sum]
    _ ≤ logTotientCap A * (∑ b ∈ r, (Nat.totient b : ℝ)⁻¹) := by
      exact mul_le_mul_of_nonneg_right
        (sum_reciprocal_totient_le_log A)
        (Finset.sum_nonneg (fun b hb => by positivity))
    _ ≤ logTotientCap A * roughEulerMass N cap w z := by
      exact mul_le_mul_of_nonneg_left
        (actual_retained_rough_totient_mass_le_euler retainOdd N cap w z)
        (logTotientCap_nonneg A)

end
end ImbalancedChen.P3ActualRetainedRoughEulerMass
