import ImbalancedChen.P5ProperPowerSignedMeanHBTransport
import ImbalancedChen.P5OriginalPrimeEndpointDivisors
import Mathlib.Data.Fintype.BigOperators

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Absolute modulus payment for the SAME signed proper-power chart before and
AFTER its exact HB atlas transform.  Nonzero complete-product differences
pay only their literal divisors.  The exact-product collision is separated
and pays the finite physical modulus count, not divisors(0).  The exact
coprime mean keeps the same rho and phi(q).  This is not yet an asymptotic
proper-power tuple-mass estimate, and is not the unweighted prime-square
restoration in the ordered bad-receiver count.
-/

namespace ImbalancedChen.P5Z.ProperPowerSignedModulusPayment

noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.P5OriginalPrimeEndpoint
open ImbalancedChen.P5Z.LicensedOriginalIntegerProfile
open ImbalancedChen.P5Z.PerGroupIntegerHBAtlasPushforward
open ImbalancedChen.Part3.OriginalProperPowerActualChart
open ImbalancedChen.P5Z.ProperPowerSignedMeanHBTransport

/-- Exact reciprocal-totient cost of the original signed physical rho. -/
def meanBudget (Q : Finset ℕ) (rho : ℕ → ℂ) : ℝ :=
  ∑ q ∈ Q, ‖rho q‖ / (Nat.totient q : ℝ)

def countRow (Q : Finset ℕ) (rho : ℕ → ℂ) (t b : ℕ) : ℂ :=
  ∑ q ∈ Q with Nat.ModEq q b t, rho q

def meanRow (Q : Finset ℕ) (rho : ℕ → ℂ) (b : ℕ) : ℂ :=
  ∑ q ∈ Q with Nat.Coprime b q, rho q / (Nat.totient q : ℂ)

theorem signedRow_eq_count_sub_mean (Q : Finset ℕ) (rho : ℕ → ℂ)
    (t b : ℕ) : signedRow Q rho t b = countRow Q rho t b - meanRow Q rho b := by
  unfold signedRow signedKernel countRow meanRow
  simp only [Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hc : Nat.ModEq q b t <;> by_cases hp : Nat.Coprime b q <;>
    simp [hc, hp, mul_sub, mul_div_assoc]

theorem norm_meanRow_le (Q : Finset ℕ) (rho : ℕ → ℂ) (b : ℕ) :
    ‖meanRow Q rho b‖ ≤ meanBudget Q rho := by
  unfold meanRow meanBudget
  calc
    _ ≤ ∑ q ∈ Q with Nat.Coprime b q, ‖rho q / (Nat.totient q : ℂ)‖ :=
      norm_sum_le _ _
    _ = ∑ q ∈ Q with Nat.Coprime b q, ‖rho q‖ / (Nat.totient q : ℝ) := by
      simp only [norm_div, Complex.norm_natCast]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => by positivity)

/-- At nonzero difference the congruence moduli are actual divisors.
No bound on the displayed modulus envelope Q is needed. -/
theorem norm_countRow_le_distance_divisors
    (Q : Finset ℕ) (rho : ℕ → ℂ) (t b : ℕ) (hne : b ≠ t) :
    ‖countRow Q rho t b‖ ≤
      ∑ q ∈ (distance t b).divisors, ‖rho q‖ := by
  have hsub : Q.filter (fun q => Nat.ModEq q b t) ⊆ (distance t b).divisors := by
    intro q hq
    exact Nat.mem_divisors.mpr
      ⟨(modEq_iff_dvd_distance t b q).mp (Finset.mem_filter.mp hq).2,
        ne_of_gt (distance_pos hne)⟩
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _))

/-- Amplitude control is imposed only on the original finite physical
support; no values of rho outside Q enter the bound. -/
theorem norm_countRow_le_distance_card
    (Q : Finset ℕ) (rho : ℕ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hrho : ∀ q ∈ Q, ‖rho q‖ ≤ R) (t b : ℕ) (hne : b ≠ t) :
    ‖countRow Q rho t b‖ ≤ R * ((distance t b).divisors.card : ℝ) := by
  have hsub : Q.filter (fun q => Nat.ModEq q b t) ⊆ (distance t b).divisors := by
    intro q hq
    exact Nat.mem_divisors.mpr
      ⟨(modEq_iff_dvd_distance t b q).mp (Finset.mem_filter.mp hq).2,
        ne_of_gt (distance_pos hne)⟩
  calc
    _ ≤ ∑ q ∈ Q with Nat.ModEq q b t, ‖rho q‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Q with Nat.ModEq q b t, R := by
      apply Finset.sum_le_sum
      intro q hq
      exact hrho q (Finset.mem_filter.mp hq).1
    _ = ((Q.filter (fun q => Nat.ModEq q b t)).card : ℝ) * R := by simp
    _ ≤ ((distance t b).divisors.card : ℝ) * R := by
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub)) hR
    _ = _ := by ring

/-- A zero difference is handled separately, with all Q, including q=0.
No use is made of the false inclusion Q subset divisors(0). -/
theorem norm_countRow_le_physical_card
    (Q : Finset ℕ) (rho : ℕ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hrho : ∀ q ∈ Q, ‖rho q‖ ≤ R) (t b : ℕ) :
    ‖countRow Q rho t b‖ ≤ R * (Q.card : ℝ) := by
  calc
    _ ≤ ∑ q ∈ Q with Nat.ModEq q b t, ‖rho q‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, ‖rho q‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => norm_nonneg _)
    _ ≤ ∑ q ∈ Q, R := Finset.sum_le_sum hrho
    _ = _ := by simp [mul_comm]

def rowBudget (Q : Finset ℕ) (rho : ℕ → ℂ) (R : ℝ) (t b : ℕ) : ℝ :=
  (if b = t then R * (Q.card : ℝ)
    else R * ((distance t b).divisors.card : ℝ)) + meanBudget Q rho

theorem norm_signedRow_le (Q : Finset ℕ) (rho : ℕ → ℂ)
    (R : ℝ) (hR : 0 ≤ R) (hrho : ∀ q ∈ Q, ‖rho q‖ ≤ R) (t b : ℕ) :
    ‖signedRow Q rho t b‖ ≤ rowBudget Q rho R t b := by
  rw [signedRow_eq_count_sub_mean]
  refine (norm_sub_le _ _).trans ?_
  unfold rowBudget
  by_cases hdiag : b = t
  · rw [if_pos hdiag]
    exact add_le_add (norm_countRow_le_physical_card Q rho R hR hrho t b)
      (norm_meanRow_le Q rho b)
  · rw [if_neg hdiag]
    exact add_le_add (norm_countRow_le_distance_card Q rho R hR hrho t b hdiag)
      (norm_meanRow_le Q rho b)

/-- The q=1 discrepancy vanishes for every product, rather than only on
its exact-product collision. This identity permits a sharper erased budget. -/
theorem signedRow_erase_one (Q : Finset ℕ) (rho : ℕ → ℂ) (t b : ℕ) :
    signedRow (Q.erase 1) rho t b = signedRow Q rho t b := by
  unfold signedRow
  by_cases h1 : 1 ∈ Q
  · have h := Finset.sum_erase_add Q (fun q => rho q * signedKernel q t b) h1
    have hkernel : signedKernel 1 t b = 0 := by simp [signedKernel, Nat.ModEq]
    simpa only [hkernel, mul_zero, add_zero] using h
  · rw [Finset.erase_eq_of_notMem h1]

/-- Exact weight on the original marked integer word, before HB. -/
def wordAmplitude {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (chi eta : ℝ → ℝ) (z T kappa0 : ℝ)
    (js us : List ℕ) : ℝ :=
  ‖sourceTuple chi z js us * ((listExtension L us : ℂ) *
    (eta ((us.prod : ℝ) / T ^ (1-kappa0)) : ℂ))‖

/-- The genuine same-rho proper-power source now has an explicit modulus
payment. It separates exact complete-product collisions before any
proper-power mass estimate or original-policy exponent certificate. -/
theorem norm_signedSource_le_marked_word_budget {k : ℕ}
    {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (chi eta : ℝ → ℝ) (z T kappa0 : ℝ)
    (cap : ℕ) (js : List ℕ) (bad : Fin k)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hrho : ∀ q ∈ Q, ‖rho q‖ ≤ R) (t : ℕ) :
    ‖signedSource L chi eta z T kappa0 cap js bad Q rho t‖ ≤
      ∑ us ∈ markedWords L chi eta T kappa0 cap js bad,
        wordAmplitude L chi eta z T kappa0 js us * rowBudget Q rho R t us.prod := by
  rw [signed_source_eq_tuple_first]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro us hus
  have hprod : sourceTuple chi z js us *
      ((listExtension L us : ℂ) *
        (eta ((us.prod : ℝ) / T ^ (1-kappa0)) : ℂ) * signedRow Q rho t us.prod) =
      (sourceTuple chi z js us * ((listExtension L us : ℂ) *
        (eta ((us.prod : ℝ) / T ^ (1-kappa0)) : ℂ))) * signedRow Q rho t us.prod := by ring
  rw [hprod, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_signedRow_le Q rho R hR hrho t us.prod)
    (norm_nonneg _)

/-- The same absolute bound applies AFTER the licensed exact integer HB
atlas transform: count and coprime mean cannot use different rho or cutoff. -/
theorem norm_signedAtlas_le_marked_word_budget {k : ℕ}
    {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (chi eta : ℝ → ℝ)
    (hone : ∀ x : ℝ, x ≤ 1 → chi x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → chi x = 0)
    {z : ℝ} (hz : 0 ≤ z) (T kappa0 : ℝ)
    (cap : ℕ) (js : List ℕ) (bad : Fin k)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hrho : ∀ q ∈ Q, ‖rho q‖ ≤ R) (t : ℕ) :
    ‖signedAtlas L chi eta z T kappa0 cap js bad Q rho t‖ ≤
      ∑ us ∈ markedWords L chi eta T kappa0 cap js bad,
        wordAmplitude L chi eta z T kappa0 js us * rowBudget Q rho R t us.prod := by
  rw [← signed_source_eq_HB_atlas L chi eta hone hzero hz]
  exact norm_signedSource_le_marked_word_budget L chi eta z T kappa0 cap js bad
    Q rho R hR hrho t

/-- Original labelled proper-power words on the exact-product collision.
They are not quotiented by permutations and need not consist of primes. -/
def collisionWords {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (chi eta : ℝ → ℝ) (T kappa0 : ℝ)
    (cap : ℕ) (js : List ℕ) (bad : Fin k) (t : ℕ) : Finset (List ℕ) :=
  (markedWords L chi eta T kappa0 cap js bad).filter (fun us => us.prod = t)

/-- A fixed complete product has at most tau(t)^k ordered integer words.
This is the missing arithmetic collision multiplicity, not the false
rank^rank bound valid only when every slot is prime. -/
theorem collisionWords_card_le_divisor_power {k : ℕ}
    {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (chi eta : ℝ → ℝ) (T kappa0 : ℝ)
    (cap : ℕ) (js : List ℕ) (bad : Fin k) (t : ℕ) (ht : t ≠ 0) :
    (collisionWords L chi eta T kappa0 cap js bad t).card ≤ t.divisors.card ^ k := by
  let S := collisionWords L chi eta T kappa0 cap js bad t
  have hlen (us : S) : us.val.length = k :=
    (badChartWords_spec (Finset.mem_filter.mp us.property).1).1
  have hdiv (us : S) (i : Fin k) : wordVector k us.val i ∈ t.divisors := by
    have hi : i.val < us.val.length := by simpa [hlen us] using i.isLt
    have hmem : wordVector k us.val i ∈ us.val := by
      dsimp [wordVector]
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    have hproduct : us.val.prod = t := (Finset.mem_filter.mp us.property).2
    exact Nat.mem_divisors.mpr ⟨hproduct ▸ List.dvd_prod hmem, ht⟩
  let encode : S → (Fin k → t.divisors) := fun us i => ⟨wordVector k us.val i, hdiv us i⟩
  have hinj : Function.Injective encode := by
    intro us vs heq
    apply Subtype.ext
    apply wordVector_injOn_length k (hlen us) (hlen vs)
    funext i
    exact congrArg (fun f : Fin k → t.divisors => (f i).val) heq
  have hc := Fintype.card_le_of_injective encode hinj
  simpa only [Fintype.card_pi_const, Fintype.card_coe] using hc

/-- The exact-product diagonal is paid using its TRUE integer-word
multiplicity and the same mean budget. An amplitude A is a local test
licence, not an assumption of the final asymptotic error bound. -/
theorem collision_word_budget_le {k : ℕ}
    {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (chi eta : ℝ → ℝ) (z T kappa0 : ℝ)
    (cap : ℕ) (js : List ℕ) (bad : Fin k) (t : ℕ) (ht : t ≠ 0)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (R A : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hamp : ∀ us ∈ collisionWords L chi eta T kappa0 cap js bad t,
      wordAmplitude L chi eta z T kappa0 js us ≤ A) :
    (∑ us ∈ collisionWords L chi eta T kappa0 cap js bad t,
      wordAmplitude L chi eta z T kappa0 js us * rowBudget Q rho R t us.prod) ≤
        (A * (t.divisors.card ^ k : ℕ)) * (R * (Q.card : ℝ) + meanBudget Q rho) := by
  let C := R * (Q.card : ℝ) + meanBudget Q rho
  have hC : 0 ≤ C := by
    dsimp [C, meanBudget]
    exact add_nonneg (mul_nonneg hR (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun _ _ => by positivity))
  have hcard : ((collisionWords L chi eta T kappa0 cap js bad t).card : ℝ) ≤
      (t.divisors.card ^ k : ℕ) := by
    exact_mod_cast collisionWords_card_le_divisor_power L chi eta T kappa0 cap js bad t ht
  calc
    _ = ∑ us ∈ collisionWords L chi eta T kappa0 cap js bad t,
        wordAmplitude L chi eta z T kappa0 js us * C := by
      apply Finset.sum_congr rfl
      intro us hus
      have hprod := (Finset.mem_filter.mp hus).2
      simp only [rowBudget, hprod, if_pos rfl, C]
    _ ≤ ∑ _us ∈ collisionWords L chi eta T kappa0 cap js bad t, A * C :=
      Finset.sum_le_sum (fun us hus => mul_le_mul_of_nonneg_right (hamp us hus) hC)
    _ = (A * ((collisionWords L chi eta T kappa0 cap js bad t).card : ℝ)) * C := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (A * (t.divisors.card ^ k : ℕ)) * C :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hA) hC
    _ = _ := rfl

end
end ImbalancedChen.P5Z.ProperPowerSignedModulusPayment
