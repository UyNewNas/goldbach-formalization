import ImbalancedChen.P3ActualEvenLowerEulerMass
import ImbalancedChen.ChenInitialPrimeSource
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic

/-!
P3.6: a finite first prime-divisor moment for the ACTUAL even first-exit
LOWER rough support. Frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product-completion §§1,3(T),4(F), manuscript-body eq:current-PP.

The preceding pair-moment factorization left the rough factor
  sum_{r in fixedEvenRoughSupport} C_N(r)/phi(r)
unpaid. We now charge that entire actual support to the first moment of
the same ORIGINAL rough prime universe's finite Euler product. There is
no retained-rank assumption, nor a replacement for the literal even-exit
retention policy. This is a finite combinatorial upper bound; it does NOT
assert a uniform power of log N for the Euler product or its prime sum,
and it does NOT pay a signed arithmetic discrepancy or final global rho_N.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualEvenLowerRoughPrimeMoment
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualRetainedRoughEulerMass
open ImbalancedChen.P3ActualEvenLowerEulerMass

def roughPrimeInvPhi (p : ℕ) : ℝ := (((p - 1 : ℕ) : ℝ))⁻¹

/-- Pure finite Euler identity, valid for any real-valued prime weight. -/
private theorem powerset_euler (P : Finset ℕ) (f : ℕ → ℝ) :
    (∑ T ∈ P.powerset, ∏ p ∈ T, f p) =
      ∏ p ∈ P, (1 + f p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    rw [Finset.sum_powerset_insert hp, Finset.prod_insert hp]
    have hsecond :
        (∑ T ∈ P.powerset, ∏ q ∈ insert p T, f q) =
        f p * (∑ T ∈ P.powerset, ∏ q ∈ T, f q) := by
      calc
        _ = ∑ T ∈ P.powerset, f p * (∏ q ∈ T, f q) := by
          apply Finset.sum_congr rfl
          intro T hT
          have hpT : p ∉ T := fun h => hp ((Finset.mem_powerset.mp hT) h)
          rw [Finset.prod_insert hpT]
        _ = _ := (Finset.mul_sum).symm
    rw [hsecond, ih]
    ring

/-- Nonnegativity of finite products, using only the locally supplied weights. -/
private theorem prod_nonneg_local (P : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ p ∈ P, 0 ≤ f p) : 0 ≤ ∏ p ∈ P, f p := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    rw [Finset.prod_insert hp]
    exact mul_nonneg (hf p (Finset.mem_insert_self p P))
      (ih (fun q hq => hf q (Finset.mem_insert_of_mem hq)))

/-- The first moment of all squarefree subproducts is at most their
Euler mass times the sum of single-prime reciprocal totients.
This is a non-analytic, no-rank combinatorial estimate. -/
private theorem powerset_card_first_moment_le
    (P : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ p ∈ P, 0 ≤ f p) :
    (∑ T ∈ P.powerset, (T.card : ℝ) * (∏ p ∈ T, f p)) ≤
      (∏ p ∈ P, (1 + f p)) * (∑ p ∈ P, f p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have hfP : ∀ q ∈ P, 0 ≤ f q := by
      intro q hq
      exact hf q (Finset.mem_insert_of_mem hq)
    have hfp : 0 ≤ f p := hf p (Finset.mem_insert_self p P)
    have hih := ih hfP
    have hrec :
        (∑ T ∈ (insert p P).powerset,
          (T.card : ℝ) * (∏ q ∈ T, f q)) =
        (1 + f p) *
          (∑ T ∈ P.powerset, (T.card : ℝ) * (∏ q ∈ T, f q)) +
        f p * (∑ T ∈ P.powerset, ∏ q ∈ T, f q) := by
      rw [Finset.sum_powerset_insert hp]
      have hins :
          (∑ T ∈ P.powerset,
            ((insert p T).card : ℝ) * (∏ q ∈ insert p T, f q)) =
          f p * (∑ T ∈ P.powerset,
            (T.card : ℝ) * (∏ q ∈ T, f q)) +
          f p * (∑ T ∈ P.powerset, ∏ q ∈ T, f q) := by
        calc
          _ = ∑ T ∈ P.powerset,
              f p * ((T.card : ℝ) * (∏ q ∈ T, f q)) +
                f p * (∏ q ∈ T, f q) := by
              apply Finset.sum_congr rfl
              intro T hT
              have hpT : p ∉ T := fun h => hp ((Finset.mem_powerset.mp hT) h)
              rw [Finset.prod_insert hpT, Finset.card_insert_of_not_mem hpT]
              push_cast
              ring
          _ = _ := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [hins]
      ring
    have he : 0 ≤ ∏ q ∈ P, (1 + f q) := by
      exact prod_nonneg_local P (fun q => 1 + f q)
        (fun q hq => by linarith [hfP q hq])
    have hsum : 0 ≤ ∑ q ∈ P, f q :=
      Finset.sum_nonneg (fun q hq => hfP q hq)
    rw [hrec, powerset_euler P f, Finset.prod_insert hp,
      Finset.sum_insert hp]
    calc
      (1 + f p) *
          (∑ T ∈ P.powerset, (T.card : ℝ) * (∏ q ∈ T, f q)) +
        f p * (∏ q ∈ P, (1 + f q)) ≤
        (1 + f p) *
          ((∏ q ∈ P, (1 + f q)) * (∑ q ∈ P, f q)) +
        f p * (∏ q ∈ P, (1 + f q)) := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_left hih (by linarith)) _
      _ ≤ ((1 + f p) * (∏ q ∈ P, (1 + f q))) *
            (f p + ∑ q ∈ P, f q) := by
          have hdelta : 0 ≤ f p * f p * (∏ q ∈ P, (1 + f q)) :=
            mul_nonneg (mul_nonneg hfp hfp) he
          nlinarith

/-- In a nonzero modulus every prime counted by the actual inclusive
prime-source correction is indeed a distinct prime factor. -/
theorem chen_prime_divisor_count_le_primeFactors_card
    (N r : ℕ) (hr : r ≠ 0) :
    chenPrimeDivisorCount N r ≤ (r.primeFactors.card : ℝ) := by
  classical
  have hsub : (chenPrimePrefix N).filter (fun p => p ∣ r) ⊆
      r.primeFactors := by
    intro p hp
    obtain ⟨hpref, hpdiv⟩ := Finset.mem_filter.mp hp
    exact (mem_chenPrimePrefix.mp hpref).2.mem_primeFactors hpdiv hr
  unfold chenPrimeDivisorCount
  exact_mod_cast Finset.card_le_card hsub

/-- Finite explicit rough prime first moment, with no uniform asymptotic
claim. The prime-factor bound uses only nonzero, squarefree, and literal
prime-universe support; no retained-rank K is imposed. -/
theorem squarefree_prime_divisor_moment_le_euler
    (N : ℕ) (S P : Finset ℕ)
    (hsq : ∀ r ∈ S, Squarefree r)
    (hfactor : ∀ r ∈ S, r.primeFactors ⊆ P) :
    (∑ r ∈ S, chenPrimeDivisorCount N r *
      (Nat.totient r : ℝ)⁻¹) ≤
      (∏ p ∈ P, (1 + roughPrimeInvPhi p)) * (∑ p ∈ P, roughPrimeInvPhi p) := by
  classical
  have hinj : Set.InjOn Nat.primeFactors S := by
    intro a ha b hb hab
    calc
      a = ∏ p ∈ a.primeFactors, p :=
        (Nat.prod_primeFactors_of_squarefree (hsq a ha)).symm
      _ = ∏ p ∈ b.primeFactors, p := by rw [hab]
      _ = b := Nat.prod_primeFactors_of_squarefree (hsq b hb)
  have himage : S.image Nat.primeFactors ⊆ P.powerset := by
    intro T hT
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_powerset.mpr (hfactor r hr)
  have hphi (r : ℕ) (hr : r ∈ S) :
      (Nat.totient r : ℝ)⁻¹ = ∏ p ∈ r.primeFactors, roughPrimeInvPhi p := by
    have hphi : Nat.totient r =
        ∏ p ∈ r.primeFactors, (p - 1) := by
      calc
        Nat.totient r =
            (r / ∏ p ∈ r.primeFactors, p) *
              ∏ p ∈ r.primeFactors, (p - 1) :=
          Nat.totient_eq_div_primeFactors_mul r
        _ = ∏ p ∈ r.primeFactors, (p - 1) := by
          rw [Nat.prod_primeFactors_of_squarefree (hsq r hr)]
          simp [(hsq r hr).ne_zero]
    simp [hphi, roughPrimeInvPhi, Nat.cast_prod, Finset.prod_inv_distrib]
  calc
    (∑ r ∈ S, chenPrimeDivisorCount N r *
      (Nat.totient r : ℝ)⁻¹) ≤
      ∑ r ∈ S, (r.primeFactors.card : ℝ) *
        (Nat.totient r : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro r hr
          exact mul_le_mul_of_nonneg_right
            (chen_prime_divisor_count_le_primeFactors_card N r
              (hsq r hr).ne_zero) (by positivity)
    _ = ∑ T ∈ S.image Nat.primeFactors,
          (T.card : ℝ) * (∏ p ∈ T, roughPrimeInvPhi p) := by
          rw [Finset.sum_image hinj]
          apply Finset.sum_congr rfl
          intro r hr
          rw [hphi r hr]
    _ ≤ ∑ T ∈ P.powerset, (T.card : ℝ) * (∏ p ∈ T, roughPrimeInvPhi p) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg himage
          intro T hT hnot
          have hp : ∀ p ∈ T, 0 ≤ roughPrimeInvPhi p := by
            intro p hpt
            simp [roughPrimeInvPhi]
            positivity
          have hprod : 0 ≤ ∏ p ∈ T, roughPrimeInvPhi p :=
            prod_nonneg_local T roughPrimeInvPhi hp
          exact mul_nonneg (by positivity) hprod
    _ ≤ _ := powerset_card_first_moment_le P roughPrimeInvPhi
      (fun p hp => by simp [u]; positivity)

/-- Instantiation to the *actual* even-first-exit LOWER rough leaves,
not an arbitrary replacement coefficient. All original strict prime
windows are encapsulated in the unchanged roughPrimeUniverse. -/
theorem actual_even_retained_rough_prime_divisor_moment_le_euler
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    (∑ r ∈ fixedEvenRoughSupport retainEven N cap w z,
      chenPrimeDivisorCount N r * (Nat.totient r : ℝ)⁻¹) ≤
      roughEulerMass N cap w z *
        (∑ p ∈ roughPrimeFinset N cap w z, roughPrimeInvPhi p) := by
  classical
  let S := fixedEvenRoughSupport retainEven N cap w z
  let P := (roughPrimeUniverse N cap w z).toFinset
  have hsq : ∀ r ∈ S, Squarefree r := by
    intro r hr
    exact fixedEvenRoughSupport_squarefree retainEven N cap w z hr
  have hfactor : ∀ r ∈ S, r.primeFactors ⊆ P := by
    intro r hr p hp
    change p ∈ (roughPrimeUniverse N cap w z).toFinset
    simpa using fixedEvenRoughSupport_primeFactors_mem
      retainEven N cap w z hr hp
  have h := squarefree_prime_divisor_moment_le_euler N S P hsq hfactor
  simpa only [S, P, roughPrimeUniverse_toFinset, roughEulerMass] using h

end
end ImbalancedChen.P3ActualEvenLowerRoughPrimeMoment
