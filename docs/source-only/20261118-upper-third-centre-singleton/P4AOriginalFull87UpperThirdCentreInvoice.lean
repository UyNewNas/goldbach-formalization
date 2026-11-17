import ImbalancedChen.ActualSmallRoughAttachment
import ImbalancedChen.ChenInitialPrimeSource
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A quantitative payment for the ORIGINAL centre-prime AP correction, not an
extra extension of the high-modulus prime switch. For every composite centre
N and complete modulus d coprime to N with N < 3*d, the centre AP can only
come from P=2 and N-2=2*d. The centre term is therefore supported at a
SINGLE complete modulus, not one term per fifth/sixth occurrence.

For the literal original small/rough physical coefficient this gives an
absolute bound 1 for the entire high-third centre correction, for any fixed
causal retained policy; comparing two fixed policies costs at most 2. This is
an arithmetic correction invoice, NOT a signed tree-saving estimate and NOT
a bound for primitive discrepancy or the other high-modulus prime sum.

The original complete q, target-coprimality and strict X<q are unchanged.
-/

namespace ImbalancedChen.P4AOriginalFull87UpperThirdCentreInvoice
noncomputable section
open scoped Classical BigOperators

/-- The centre divisor P is forced to be 2, and the divisor quotient is
exactly 2. In particular the P=N exceptional prime-centre case must be
excluded, rather than silently discarded. -/
theorem centre_ap_upper_third_member_special
    (N d P : ℕ) (hcomp : ¬ Nat.Prime N)
    (hcop : Nat.Coprime d N) (hthird : N < 3 * d)
    (hP : P ∈ (chenPrimePrefix N).filter
      (fun P => Nat.ModEq d P N ∧ P ∣ N)) :
    P = 2 ∧ N - 2 = 2 * d := by
  obtain ⟨hpre, hmod, hPdivN⟩ := Finset.mem_filter.mp hP
  obtain ⟨hPle, hPrime⟩ := mem_chenPrimePrefix.mp hpre
  have hne : P ≠ N := by
    intro heq
    exact hcomp (heq ▸ hPrime)
  have hlt : P < N := lt_of_le_of_ne hPle hne
  have hdiv : d ∣ N - P :=
    (dvd_sub_iff_modEq_of_le hPle).mpr hmod
  have hPdiv : P ∣ N - P := Nat.dvd_sub' hPdivN dvd_rfl
  have hnotPdivd : ¬ P ∣ d := by
    have hdp : Nat.Coprime d P := hcop.of_dvd_right hPdivN
    exact hPrime.coprime_iff_not_dvd.mp hdp.symm
  let k : ℕ := (N - P) / d
  have hmul : k * d = N - P := Nat.div_mul_cancel hdiv
  have hkpos : 0 < k := by
    by_contra hnot
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hnot
    have hz : N - P = 0 := by simpa [hkzero] using hmul.symm
    omega
  have hklt : k < 3 := by
    by_contra hnot
    have hge : 3 ≤ k := by omega
    have hthree : 3 * d ≤ N - P := by
      calc
        3 * d ≤ k * d := Nat.mul_le_mul_right d hge
        _ = N - P := hmul
    omega
  have hPdivk : P ∣ k := by
    have hprod : P ∣ k * d := by rw [hmul]; exact hPdiv
    rcases hPrime.dvd_mul.mp hprod with hk | hd
    · exact hk
    · exact False.elim (hnotPdivd hd)
  have hkge : P ≤ k := Nat.le_of_dvd hkpos hPdivk
  have hk2 : k = 2 := by omega
  have hP_le : P ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) (by
    simpa [hk2] using hPdivk)
  have hP2 : P = 2 := Nat.le_antisymm hP_le hPrime.two_le
  refine ⟨hP2, ?_⟩
  simpa [hP2, hk2] using hmul.symm

/-- In the upper-third window the actual centre AP correction has a
single exceptional possible original centre divisor, not omega(N) terms. -/
theorem centre_ap_upper_third_le_one
    (N d : ℕ) (hcomp : ¬ Nat.Prime N)
    (hcop : Nat.Coprime d N) (hthird : N < 3 * d) :
    chenCentrePrimeAPCount N N d ≤ 1 := by
  classical
  have hsub :
      (chenPrimePrefix N).filter (fun P => Nat.ModEq d P N ∧ P ∣ N) ⊆
        ({2} : Finset ℕ) := by
    intro P hP
    exact Finset.mem_singleton.mpr
      (centre_ap_upper_third_member_special N d P hcomp hcop hthird hP).1
  unfold chenCentrePrimeAPCount
  have hc :
      ((chenPrimePrefix N).filter (fun P => Nat.ModEq d P N ∧ P ∣ N)).card ≤ 1 := by
    calc
      _ ≤ ({2} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 1 := by simp
  exact_mod_cast hc

/-- The correction is zero off ONE complete modulus. This is not an
assumption about the compiled support: it is deduced from centre primality,
actual modulus coprimality, and the strict upper-third gate. -/
theorem centre_ap_upper_third_zero_unless_special
    (N d : ℕ) (hcomp : ¬ Nat.Prime N)
    (hcop : Nat.Coprime d N) (hthird : N < 3 * d)
    (hneq : N - 2 ≠ 2 * d) :
    chenCentrePrimeAPCount N N d = 0 := by
  classical
  have hempty :
      (chenPrimePrefix N).filter (fun P => Nat.ModEq d P N ∧ P ∣ N) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro P hP
    have hs := centre_ap_upper_third_member_special
      N d P hcomp hcop hthird hP
    exact hneq hs.2
  simp [chenCentrePrimeAPCount, hempty]

/-- Original strict high-q filter is kept on the COMPLETE physical modulus. -/
def centreUpperThirdHighQ (N X d : ℕ) : ℝ :=
  if N < 3 * d ∧ X < d then chenCentrePrimeAPCount N N d else 0

/-- The full signed physical upper-third centre correction costs at most 1,
for the ORIGINAL (not rebuilt) small/rough physical rho of ANY fixed policy.
Its only possibly nonzero q is (N-2)/2. In particular occurrence-count or
omega(N) losses are unnecessary for this particular correction invoice. -/
theorem actual_physical_upper_third_centre_abs_le_one
    (retainOdd : List ℕ → Bool) (N cap X : ℕ) (w z L : ℝ)
    (hcomp : ¬ Nat.Prime N) :
    |∑ d ∈ actualSmallRoughModuli retainOdd N cap w z,
      actualSmallRoughRho retainOdd N cap w z L d *
        centreUpperThirdHighQ N X d| ≤ 1 := by
  classical
  let S := actualSmallRoughModuli retainOdd N cap w z
  let rho := actualSmallRoughRho retainOdd N cap w z L
  let d0 := (N - 2) / 2
  have hzero (d : ℕ) (hd : d ∈ S) (hne : d ≠ d0) :
      rho d * centreUpperThirdHighQ N X d = 0 := by
    by_cases hg : N < 3 * d ∧ X < d
    · have hcop : Nat.Coprime d N :=
        actualSmallRoughModuli_coprime_target retainOdd N cap w z hd
      have hneq : N - 2 ≠ 2 * d := by
        intro heq
        have hdeq : d = d0 := by dsimp [d0]; omega
        exact hne hdeq
      have hz := centre_ap_upper_third_zero_unless_special
        N d hcomp hcop hg.1 hneq
      simp [centreUpperThirdHighQ, hg, hz]
    · simp [centreUpperThirdHighQ, hg]
  have hsum :
      (∑ d ∈ S, rho d * centreUpperThirdHighQ N X d) =
        if d0 ∈ S then rho d0 * centreUpperThirdHighQ N X d0 else 0 := by
    calc
      _ = ∑ d ∈ S, if d = d0 then
            rho d0 * centreUpperThirdHighQ N X d0 else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hdeq : d = d0
        · simp [hdeq]
        · simp [hdeq, hzero d hd hdeq]
      _ = _ := by simp
  change |∑ d ∈ S, rho d * centreUpperThirdHighQ N X d| ≤ 1
  rw [hsum]
  by_cases hmem : d0 ∈ S
  · simp only [if_pos hmem]
    by_cases hg : N < 3 * d0 ∧ X < d0
    · have hcop : Nat.Coprime d0 N :=
        actualSmallRoughModuli_coprime_target retainOdd N cap w z hmem
      have hcent := centre_ap_upper_third_le_one N d0 hcomp hcop hg.1
      have hcent0 : 0 ≤ chenCentrePrimeAPCount N N d0 := by
        unfold chenCentrePrimeAPCount
        positivity
      have hrho := actualSmallRoughRho_abs_le_one retainOdd N cap w z L d0
      simp only [centreUpperThirdHighQ, if_pos hg]
      rw [abs_mul, abs_of_nonneg hcent0]
      calc
        |rho d0| * chenCentrePrimeAPCount N N d0 ≤ (1 : ℝ) * 1 :=
          mul_le_mul hrho hcent hcent0 (by norm_num)
        _ = 1 := by norm_num
    · simp [centreUpperThirdHighQ, hg]
  · simp [hmem]

/-- The two original fixed policy coefficients can be compared on the same
complete q and with the same centre test. This pays an absolute ERROR, not
an unsigned surrogate for a signed prime-saving. -/
theorem actual_two_physical_upper_third_centre_gap_le_two
    (raw licensed : List ℕ → Bool)
    (N cap X : ℕ) (w z L : ℝ) (hcomp : ¬ Nat.Prime N) :
    |(∑ d ∈ actualSmallRoughModuli raw N cap w z,
        actualSmallRoughRho raw N cap w z L d * centreUpperThirdHighQ N X d) -
      (∑ d ∈ actualSmallRoughModuli licensed N cap w z,
        actualSmallRoughRho licensed N cap w z L d * centreUpperThirdHighQ N X d)| ≤ 2 := by
  let a : ℝ := ∑ d ∈ actualSmallRoughModuli raw N cap w z,
    actualSmallRoughRho raw N cap w z L d * centreUpperThirdHighQ N X d
  let b : ℝ := ∑ d ∈ actualSmallRoughModuli licensed N cap w z,
    actualSmallRoughRho licensed N cap w z L d * centreUpperThirdHighQ N X d
  have hr : |a| ≤ 1 := actual_physical_upper_third_centre_abs_le_one
    raw N cap X w z L hcomp
  have hl : |b| ≤ 1 := actual_physical_upper_third_centre_abs_le_one
    licensed N cap X w z L hcomp
  change |a - b| ≤ 2
  have htri : |a - b| ≤ |a| + |b| := by
    simpa only [sub_eq_add_neg, abs_neg] using (abs_add a (-b))
  linarith

end
end ImbalancedChen.P4AOriginalFull87UpperThirdCentreInvoice
