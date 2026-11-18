import ImbalancedChen.P4AOriginalFull87UpperThirdCentreInvoice
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

This continuation keeps the ORIGINAL centre AP correction and the fixed
small/rough physical rho, with its COMPLETE modulus and strict high-q gate.
The earlier single-exception upper-third invoice was an absolute <=1 bound.
Here we compute the exceptional fibre exactly for even centres, and prove
that the ENTIRE correction actually vanishes for N == 2 (mod 4).

The fixed source-only predecessor must be staged as
ImbalancedChen.P4AOriginalFull87UpperThirdCentreInvoice before compilation.
No outside analytic input, asymptotic result, PP estimate, new policy, or
synthetic coefficient is used. This does not identify the stopped occurrence
ledger with the physical rho; that bridge remains an open internal goal.
-/

namespace ImbalancedChen.P4AOriginalFull87UpperThirdCentreExact
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87UpperThirdCentreInvoice
  (centre_ap_upper_third_member_special
   centre_ap_upper_third_zero_unless_special centreUpperThirdHighQ)

/-- The parity obstruction removes the UNIQUE possible centre correction
in the strict upper third when the even centre is 2 modulo 4. This applies
to the actual full modulus d, not merely its rough factor. -/
theorem centre_upper_third_zero_mod_four_two
    (N d : ℕ) (hcomp : ¬ Nat.Prime N)
    (hmod : N % 4 = 2) (hcop : Nat.Coprime d N)
    (hthird : N < 3 * d) :
    chenCentrePrimeAPCount N N d = 0 := by
  have hnot : N - 2 ≠ 2 * d := by
    intro heq
    have hN2 : N % 2 = 0 := by omega
    have hd2 : d % 2 = 0 := by omega
    have h2N : 2 ∣ N := Nat.dvd_of_mod_eq_zero hN2
    have h2d : 2 ∣ d := Nat.dvd_of_mod_eq_zero hd2
    have hcop2 : Nat.Coprime 2 d := (hcop.of_dvd_right h2N).symm
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hcop2) h2d
  exact centre_ap_upper_third_zero_unless_special
    N d hcomp hcop hthird hnot

/-- Exact evaluation at the only possible centre modulus. The condition
N<3*d is strict, and d=(N-2)/2 is the COMPLETE original modulus. -/
theorem centre_upper_third_exception_exact_one
    (N d : ℕ) (hcomp : ¬ Nat.Prime N)
    (hEven : N % 2 = 0) (h2le : 2 ≤ N)
    (hcop : Nat.Coprime d N) (hthird : N < 3 * d)
    (hd : N - 2 = 2 * d) :
    chenCentrePrimeAPCount N N d = 1 := by
  classical
  let F : Finset ℕ :=
    (chenPrimePrefix N).filter (fun P => Nat.ModEq d P N ∧ P ∣ N)
  have hsub : F ⊆ ({2} : Finset ℕ) := by
    intro P hP
    exact Finset.mem_singleton.mpr
      (centre_ap_upper_third_member_special N d P hcomp hcop hthird hP).1
  have h2N : 2 ∣ N := Nat.dvd_of_mod_eq_zero hEven
  have hdiv : d ∣ N - 2 := by
    refine ⟨2, ?_⟩
    omega
  have hmod : Nat.ModEq d 2 N :=
    (dvd_sub_iff_modEq_of_le h2le).mp hdiv
  have htwo : 2 ∈ F := by
    exact Finset.mem_filter.mpr
      ⟨mem_chenPrimePrefix.mpr ⟨h2le, Nat.prime_two⟩, hmod, h2N⟩
  have hF : F = ({2} : Finset ℕ) := by
    apply Finset.Subset.antisymm hsub
    intro P hP
    have hp : P = 2 := Finset.mem_singleton.mp hP
    simpa [hp] using htwo
  unfold chenCentrePrimeAPCount
  change (F.card : ℝ) = 1
  rw [hF]
  norm_num

/-- The old <=1 lemma already contained a single-modulus argument, but its
exact, weighted physical identity was not exposed as an interface. Expose
that identity without replacing the policy, beta, or modulus source. -/
theorem actual_physical_upper_third_centre_exact_single_modulus
    (retainOdd : List ℕ → Bool) (N cap X : ℕ) (w z L : ℝ)
    (hcomp : ¬ Nat.Prime N) :
    (∑ d ∈ actualSmallRoughModuli retainOdd N cap w z,
      actualSmallRoughRho retainOdd N cap w z L d *
        centreUpperThirdHighQ N X d) =
      if (N - 2) / 2 ∈ actualSmallRoughModuli retainOdd N cap w z then
        actualSmallRoughRho retainOdd N cap w z L ((N - 2) / 2) *
          centreUpperThirdHighQ N X ((N - 2) / 2) else 0 := by
  classical
  let S := actualSmallRoughModuli retainOdd N cap w z
  let rho := actualSmallRoughRho retainOdd N cap w z L
  let d0 := (N - 2) / 2
  have hzero (d : ℕ) (hmem : d ∈ S) (hne : d ≠ d0) :
      rho d * centreUpperThirdHighQ N X d = 0 := by
    by_cases hgate : N < 3 * d ∧ X < d
    · have hcop : Nat.Coprime d N :=
        actualSmallRoughModuli_coprime_target retainOdd N cap w z hmem
      have hdiff : N - 2 ≠ 2 * d := by
        intro heq
        have heqd : d = d0 := by dsimp [d0]; omega
        exact hne heqd
      have hz := centre_ap_upper_third_zero_unless_special
        N d hcomp hcop hgate.1 hdiff
      simp [centreUpperThirdHighQ, hgate, hz]
    · simp [centreUpperThirdHighQ, hgate]
  change (∑ d ∈ S, rho d * centreUpperThirdHighQ N X d) =
    if d0 ∈ S then rho d0 * centreUpperThirdHighQ N X d0 else 0
  calc
    _ = ∑ d ∈ S, if d = d0 then
          rho d0 * centreUpperThirdHighQ N X d0 else 0 := by
      apply Finset.sum_congr rfl
      intro d hmem
      by_cases heq : d = d0
      · simp [heq]
      · simp [heq, hzero d hmem heq]
    _ = _ := by simp

/-- The real upper-third centre error is exactly ONE original physical
coefficient when its exceptional modulus belongs to the retained support
and passes BOTH strict gates. This is not a new independent error term. -/
theorem actual_physical_upper_third_centre_exact_coefficient
    (retainOdd : List ℕ → Bool) (N cap X : ℕ) (w z L : ℝ)
    (hcomp : ¬ Nat.Prime N) (hEven : N % 2 = 0) (h2le : 2 ≤ N) :
    (∑ d ∈ actualSmallRoughModuli retainOdd N cap w z,
      actualSmallRoughRho retainOdd N cap w z L d *
        centreUpperThirdHighQ N X d) =
      if (N - 2) / 2 ∈ actualSmallRoughModuli retainOdd N cap w z ∧
          N < 3 * ((N - 2) / 2) ∧ X < (N - 2) / 2 then
        actualSmallRoughRho retainOdd N cap w z L ((N - 2) / 2)
      else 0 := by
  classical
  let d0 := (N - 2) / 2
  have hd0eq : N - 2 = 2 * d0 := by dsimp [d0]; omega
  rw [actual_physical_upper_third_centre_exact_single_modulus
    retainOdd N cap X w z L hcomp]
  by_cases hmem : d0 ∈ actualSmallRoughModuli retainOdd N cap w z
  · simp only [if_pos hmem]
    by_cases hg : N < 3 * d0 ∧ X < d0
    · have hcop : Nat.Coprime d0 N :=
        actualSmallRoughModuli_coprime_target retainOdd N cap w z hmem
      have hcent : chenCentrePrimeAPCount N N d0 = 1 :=
        centre_upper_third_exception_exact_one
          N d0 hcomp hEven h2le hcop hg.1 hd0eq
      simp [centreUpperThirdHighQ, hg, hcent, hmem]
    · simp [centreUpperThirdHighQ, hg, hmem]
  · simp [hmem]

/-- For even centres N congruent 2 modulo 4, the ORIGINAL physical
high-third centre correction is ZERO for every fixed policy, not merely
bounded by 1. Retains the single payment ledger: this is an improvement
of the existing invoice, not a fourth invoice. -/
theorem actual_physical_upper_third_centre_zero_mod_four_two
    (retainOdd : List ℕ → Bool) (N cap X : ℕ) (w z L : ℝ)
    (hcomp : ¬ Nat.Prime N) (hmod : N % 4 = 2) :
    (∑ d ∈ actualSmallRoughModuli retainOdd N cap w z,
      actualSmallRoughRho retainOdd N cap w z L d *
        centreUpperThirdHighQ N X d) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro d hd
  by_cases hg : N < 3 * d ∧ X < d
  · have hcop : Nat.Coprime d N :=
      actualSmallRoughModuli_coprime_target retainOdd N cap w z hd
    have hz := centre_upper_third_zero_mod_four_two
      N d hcomp hmod hcop hg.1
    simp [centreUpperThirdHighQ, hg, hz]
  · simp [centreUpperThirdHighQ, hg]

/-- Both genuine fixed policy centre corrections vanish in this residue
class. This is an equality of original physical invoices, not a claim
that two unrelated stopped event-ledger coefficients coincide. -/
theorem actual_two_physical_upper_third_centre_gap_zero_mod_four_two
    (raw licensed : List ℕ → Bool)
    (N cap X : ℕ) (w z L : ℝ)
    (hcomp : ¬ Nat.Prime N) (hmod : N % 4 = 2) :
    (∑ d ∈ actualSmallRoughModuli raw N cap w z,
        actualSmallRoughRho raw N cap w z L d * centreUpperThirdHighQ N X d) -
      (∑ d ∈ actualSmallRoughModuli licensed N cap w z,
        actualSmallRoughRho licensed N cap w z L d * centreUpperThirdHighQ N X d) = 0 := by
  rw [actual_physical_upper_third_centre_zero_mod_four_two
        raw N cap X w z L hcomp hmod,
      actual_physical_upper_third_centre_zero_mod_four_two
        licensed N cap X w z L hcomp hmod]
  ring

end
end ImbalancedChen.P4AOriginalFull87UpperThirdCentreExact
