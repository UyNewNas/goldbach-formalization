import ImbalancedChen.P4AOriginalFull87CentrePrimeFibres
import ImbalancedChen.ActualSmallRoughAttachment
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

An arithmetic improvement of the literal full87 centre-prime fibre invoice.
All complete moduli of the original sixth and eighth physical policies are
squarefree AND coprime to the centre, by the existing concrete small/rough
attachment theorems. Their actual signed coefficients are each one-bounded.
Consequently the old-minus-new fibre budget is bounded by TWICE the number
of divisors of N-P that are coprime to N, instead of twice all divisors.

No signed PP theorem is applied, no target-prime deletion is thrown away,
and no H_N-scale asymptotic or reserve payment is claimed.
-/

namespace ImbalancedChen.P4AOriginalFull87CentreCoprimeDivisors
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87SignedSharpReceiver
  (full87PhysicalSupport full87PhysicalRhoChange)
open P4AOriginalFull87CentrePrimeFibres
  (centreDivisorPrimes centre_fibre_dvd_nonzero centreFibreAbsBudget
   full87_receiver_if_sharp_PP_pair_centre_fibres)
open P4AOriginalFull87LicensedSixthPolicy
open P4AOriginalLicensedSixthSignedLedger (physical)
open P4AOriginalFull87EighthPrimeMeanLedger
  (gain primeMass receiverTest densityTest)
open P4AOriginalFull87SignedSharpReceiver (sharpPrimeError)

/-- Genuine, original full-q support. Both old and new policies inherit
the concrete small/rough squarefreeness and target coprimality. -/
theorem original_full87_support_squarefree_coprime
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ full87PhysicalSupport r n e q om N cap w z) :
    Squarefree d ∧ Nat.Coprime d N := by
  change d ∈
    actualSmallRoughModuli ((sixthPolicy n e q om (N : ℝ)) false) N cap w z ∪
    actualSmallRoughModuli ((policy (width r) n e q om (N : ℝ)) false)
      N cap w z at hd
  rcases Finset.mem_union.mp hd with h6 | h8
  · exact ⟨actualSmallRoughModuli_squarefree _ N cap w z h6,
      actualSmallRoughModuli_coprime_target _ N cap w z h6⟩
  · exact ⟨actualSmallRoughModuli_squarefree _ N cap w z h8,
      actualSmallRoughModuli_coprime_target _ N cap w z h8⟩

/-- On the same actual full-modulus coefficient, the signed difference is
two-bounded. Each summand uses its OWN physical support and Rosser sign. -/
theorem original_full87_rho_change_abs_le_two
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (d : ℕ) :
    |full87PhysicalRhoChange r n e q om N cap w z L d| ≤ 2 := by
  let A := actualSmallRoughModuli
    ((sixthPolicy n e q om (N : ℝ)) false) N cap w z
  let B := actualSmallRoughModuli
    ((policy (width r) n e q om (N : ℝ)) false) N cap w z
  let old : ℝ :=
    if d ∈ A then
      actualSmallRoughRho ((sixthPolicy n e q om (N : ℝ)) false)
        N cap w z L d else 0
  let fresh : ℝ :=
    if d ∈ B then
      actualSmallRoughRho ((policy (width r) n e q om (N : ℝ)) false)
        N cap w z L d else 0
  have h_old : |old| ≤ (1 : ℝ) := by
    dsimp [old]
    by_cases hd : d ∈ A
    · simpa only [if_pos hd] using
        (actualSmallRoughRho_abs_le_one
          ((sixthPolicy n e q om (N : ℝ)) false) N cap w z L d)
    · simp [hd]
  have h_fresh : |fresh| ≤ (1 : ℝ) := by
    dsimp [fresh]
    by_cases hd : d ∈ B
    · simpa only [if_pos hd] using
        (actualSmallRoughRho_abs_le_one
          ((policy (width r) n e q om (N : ℝ)) false) N cap w z L d)
    · simp [hd]
  have hdef : full87PhysicalRhoChange r n e q om N cap w z L d =
      old - fresh := rfl
  rw [hdef]
  calc
    |old - fresh| ≤ |old| + |fresh| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add old (-fresh)
    _ ≤ (1 : ℝ) + 1 := add_le_add h_old h_fresh
    _ = 2 := by norm_num

/-- A uniform ARITHMETIC majorant, not a newly defined sieve weight.
Only positive nonzero N-P divisors coprime to N are counted. -/
def centreCoprimeDivisorBudget (N : ℕ) : ℝ :=
  2 * ∑ P ∈ centreDivisorPrimes N,
    ((((N - P).divisors.filter (fun d => Nat.Coprime d N)).card : ℕ) : ℝ)

/-- Elementary finite invoice: the actual signed rho is at most two in
absolute value and its support consists of target-coprime moduli. -/
private theorem finite_coprime_fibre_bound
    (N : ℕ) (hN : ¬Nat.Prime N) (S : Finset ℕ) (rho : ℕ → ℝ)
    (hcop : ∀ d ∈ S, Nat.Coprime d N)
    (hrho : ∀ d ∈ S, |rho d| ≤ (2 : ℝ)) :
    (∑ P ∈ centreDivisorPrimes N,
      ∑ d ∈ S, if Nat.ModEq d P N then |rho d| else 0) ≤
      centreCoprimeDivisorBudget N := by
  classical
  have hterm (P : ℕ) (hP : P ∈ centreDivisorPrimes N) :
      (∑ d ∈ S, if Nat.ModEq d P N then |rho d| else 0) ≤
      (2 : ℝ) *
        (((N - P).divisors.filter (fun d => Nat.Coprime d N)).card : ℝ) := by
    rw [← Finset.sum_filter]
    let T := S.filter (fun d => Nat.ModEq d P N)
    have hsub : T ⊆
        (N - P).divisors.filter (fun d => Nat.Coprime d N) := by
      intro d hd
      obtain ⟨hdS, hcong⟩ := Finset.mem_filter.mp hd
      obtain ⟨hdvd, hpos⟩ := centre_fibre_dvd_nonzero hN hP hcong
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hdvd, Nat.ne_of_gt hpos⟩,
          hcop d hdS⟩
    change (∑ d ∈ T, |rho d|) ≤ _
    calc
      (∑ d ∈ T, |rho d|) ≤ ∑ d ∈ T, (2 : ℝ) :=
        Finset.sum_le_sum (fun d hd => hrho d (Finset.mem_filter.mp hd).1)
      _ = 2 * (T.card : ℝ) := by simp
      _ ≤ 2 * (((N - P).divisors.filter
          (fun d => Nat.Coprime d N)).card : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (by exact_mod_cast Finset.card_le_card hsub)
          (by norm_num)
  calc
    (∑ P ∈ centreDivisorPrimes N,
      ∑ d ∈ S, if Nat.ModEq d P N then |rho d| else 0) ≤
        ∑ P ∈ centreDivisorPrimes N,
          (2 : ℝ) * (((N - P).divisors.filter
            (fun d => Nat.Coprime d N)).card : ℝ) :=
      Finset.sum_le_sum (fun P hP => hterm P hP)
    _ = centreCoprimeDivisorBudget N := by
      simp only [centreCoprimeDivisorBudget, Finset.mul_sum]

/-- THE actual P1.4 sixth-minus-eighth centre invoice is bounded by a
target-coprime divisor count on the SAME complete physical moduli. -/
theorem original_full87_centre_fibre_le_coprime_divisors
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (hN : ¬Nat.Prime N) :
    centreFibreAbsBudget r n e q om N cap w z L ≤
      centreCoprimeDivisorBudget N := by
  unfold centreFibreAbsBudget
  apply finite_coprime_fibre_bound N hN
  · intro d hd
    exact (original_full87_support_squarefree_coprime
      r n e q om N cap w z hd).2
  · intro d _
    exact original_full87_rho_change_abs_le_two
      r n e q om N cap w z L d

/-- Thus the previous 2*tau(N-P) bound applies, but the proven coprime
budget is normally strictly smaller. No asymptotic divisor bound is hidden. -/
theorem centre_coprime_divisor_budget_le_tau (N : ℕ) :
    centreCoprimeDivisorBudget N ≤
      2 * ∑ P ∈ centreDivisorPrimes N,
        (((N - P).divisors.card : ℕ) : ℝ) := by
  unfold centreCoprimeDivisorBudget
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
  apply Finset.sum_le_sum
  intro P _
  have hsubset :
      (N - P).divisors.filter (fun d => Nat.Coprime d N) ⊆
        (N - P).divisors := Finset.filter_subset _ _
  exact_mod_cast Finset.card_le_card hsubset

/-- The sharpened finite centre invoice enters the SAME signed sharp
receiver identity. The two separate original PP hypotheses remain unproved.
In particular there is no modulus-prime term reintroduced here. -/
theorem original_full87_receiver_sharp_coprime_invoice
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (boundSixth boundEighth : ℝ)
    (hN : ¬Nat.Prime N)
    (hSixth :
      |physical (sixthPolicy n e q om (N : ℝ)) N cap w z L
        (sharpPrimeError N)| ≤ boundSixth)
    (hEighth :
      |physical (policy (width r) n e q om (N : ℝ)) N cap w z L
        (sharpPrimeError N)| ≤ boundEighth) :
    |gain (width r) n e q om N cap w z L (receiverTest N) -
      primeMass N * gain (width r) n e q om N cap w z L densityTest| ≤
        boundSixth + boundEighth + centreCoprimeDivisorBudget N := by
  have hprior := full87_receiver_if_sharp_PP_pair_centre_fibres
    r n e q om N cap w z L boundSixth boundEighth hSixth hEighth
  have hcentre := original_full87_centre_fibre_le_coprime_divisors
    r n e q om N cap w z L hN
  linarith

end
end ImbalancedChen.P4AOriginalFull87CentreCoprimeDivisors
