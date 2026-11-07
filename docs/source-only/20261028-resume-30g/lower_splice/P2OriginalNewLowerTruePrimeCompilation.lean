import ImbalancedChen.P2OriginalI3FullRawActualPlusDensity
import ImbalancedChen.P2OriginalI3TruePrimeSource
import ImbalancedChen.P2OriginalI3ProjectionAttachmentDefects
import ImbalancedChen.ActualLowerFirstExitDensityProjection

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original manuscript 712--734 uses the NEW complete lower policy once:
nonnegative presieve projection plus its actual attachment reserve.
No subtraction of unrelated one-sided projection bounds is required.
This finite receiver uses the genuine original prime/shifted source and
the SAME actual NEW rho in its minorant, density and exact AP discrepancy.
-/
namespace ImbalancedChen.P2OriginalNewLowerTruePrimeCompilation
noncomputable section
open scoped Classical BigOperators
open P2OriginalMixedThirdSignedFrontier
open P2OriginalI3ActualSmallRosserAttachment
open P2OriginalI3ProjectionAttachmentDefects
open P2OriginalI3TruePrimeSource
open P2OriginalI3FullRawActualPlusDensity

private theorem actual_indicator_eq_chen_rough {N n : ℕ} (z : ℝ)
    (hcop : Nat.Coprime n N) :
    actualSmallRoughIndicator N z (n : ℤ) = if ChenPrimeRough z n then 1 else 0 := by
  have hi : (∀ p : ℕ, p.Prime ∧ ¬p ∣ N ∧ (p : ℝ) < z → ¬(p : ℤ) ∣ (n : ℤ)) ↔
      ChenPrimeRough z n := by
    constructor
    · intro h p hp hpn
      by_contra hnot
      have hpz : (p : ℝ) < z := lt_of_not_ge hnot
      have hnotN : ¬p ∣ N := hp.coprime_iff_not_dvd.mp (hcop.of_dvd_left hpn)
      have hpInt : (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hpn
      exact h p ⟨hp,hnotN,hpz⟩ hpInt
    · intro h p hp hpn
      have hpNat : p ∣ n := by exact_mod_cast hpn
      exact (not_lt_of_ge (h p hp.1 hpNat)) hp.2.2
  unfold actualSmallRoughIndicator
  rw [hi]

/-- Any proved minorant for these literal receivers sums to the genuine
original sifted-prime source; source zero/unit conventions are preserved. -/
private theorem sum_new_minorant_le_true_sifted
    (N : ℕ) (z : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hminor : ∀ n : ℤ, physicalDivisorSum Q rho n.natAbs ≤ actualSmallRoughIndicator N z n) :
    (∑ P ∈ chenAdditivePrimeCarrier N, physicalDivisorSum Q rho (N-P)) ≤
      ((chenSiftedPrimeSource N z).card : ℝ) := by
  rw [← sum_chenPrimeReceiverSource]
  calc
    (∑ n ∈ chenPrimeReceiverSource N, physicalDivisorSum Q rho n) ≤
        ∑ n ∈ chenPrimeReceiverSource N, actualSmallRoughIndicator N z (n : ℤ) := by
      apply Finset.sum_le_sum
      intro n hn
      simpa using hminor (n : ℤ)
    _ = ((chenSiftedPrimeSource N z).card : ℝ) := by
      rw [chenSiftedPrimeSource_eq_rough_filter]
      have heq : (∑ n ∈ chenPrimeReceiverSource N, actualSmallRoughIndicator N z (n : ℤ)) =
          ∑ n ∈ chenPrimeReceiverSource N, if ChenPrimeRough z n then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        exact actual_indicator_eq_chen_rough z (chenPrimeReceiverSource_data hn).2.2
      rw [heq,← Finset.sum_filter]
      simp

def newSupport {mesh : ℕ} (D : ThirdStage mesh) (N cap : ℕ) (y z : ℝ) : Finset ℕ :=
  actualLowerSmallRoughModuli (thirdRetain D N) N cap y z

def newRho {mesh : ℕ} (D : ThirdStage mesh) (N cap : ℕ) (y z L : ℝ) : ℕ → ℝ :=
  actualLowerSmallRoughRho (thirdRetain D N) N cap y z L

def newPrimeCoprimeCorrection {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z L : ℝ) : ℝ :=
  ∑ q ∈ newSupport D N cap y z, newRho D N cap y z L q *
    (chenPrimeDivisorCount N q / (Nat.totient q : ℝ))

def newPrimeSignedError {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z L : ℝ) : ℝ :=
  ∑ q ∈ newSupport D N cap y z, newRho D N cap y z L q *
    finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N) (fun _ => 1) N q

/-- Exact actual prime count = total source mass times density minus its
literal modulus-prime correction plus signed coprime-normalized AP error.
All terms use one and the same NEW physical rho. -/
theorem new_true_prime_count_decomposition {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z L : ℝ) :
    (∑ P ∈ chenAdditivePrimeCarrier N, physicalDivisorSum
      (newSupport D N cap y z) (newRho D N cap y z L) (N-P)) =
      ((chenAdditivePrimeCarrier N).card : ℝ) *
        physicalDensitySum (newSupport D N cap y z) (newRho D N cap y z L) -
      newPrimeCoprimeCorrection D N cap y z L + newPrimeSignedError D N cap y z L := by
  have hcount : (∑ P ∈ chenAdditivePrimeCarrier N, physicalDivisorSum
      (newSupport D N cap y z) (newRho D N cap y z L) (N-P)) =
      ∑ q ∈ newSupport D N cap y z, newRho D N cap y z L q *
        finiteCongruenceMass (chenAdditivePrimeCarrier N) (fun _ => 1) N q := by
    unfold physicalDivisorSum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    rw [← true_source_residue_count N q, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hdiv : q ∣ N-P <;> simp [hdiv]
  rw [hcount]
  unfold physicalDensitySum newPrimeCoprimeCorrection newPrimeSignedError
  rw [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hcop : Nat.Coprime q N := actualLowerSmallRoughModuli_coprime_target
    (thirdRetain D N) N cap y z hq
  rw [finitePrimitiveDiscrepancy,chenAdditivePrimeCarrier_coprime_mass hcop]
  ring

/-- The NEW complete-policy projection and actual small-Rosser reserve
are paid once at the same epsilon/threshold as its actual prime count.
The remaining signed AP error is displayed, not assumed bounded. -/
theorem exists_new_true_prime_lower_compilation
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1/8 ∧ epsilon < epsilonMax ∧
      epsilon^2 ≤ r ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ)^(nu*r) ≤ (cap : ℝ) →
      ∀ mesh : ℕ, ∀ D : ThirdStage mesh,
        let y := (N : ℝ)^(nu*epsilon^2)
        let z := (N : ℝ)^(nu*r)
        let L := (N : ℝ)^(nu*epsilon)
        let reserve := eta * singularSeries N / Real.log (N : ℝ)
        ((chenAdditivePrimeCarrier N).card : ℝ) *
          (rawDensity (thirdRetain D N) N cap 0 z - reserve) -
          newPrimeCoprimeCorrection D N cap y z L + newPrimeSignedError D N cap y z L ≤
        ((chenSiftedPrimeSource N z).card : ℝ) := by
  obtain ⟨epsilon,hepsilon,hepsilon8,hepsilonMax',hepsilonr,N0,hN0,hbound⟩ :=
    exists_actualLowerSmallRoughRho_full_density_minorant nu r eta epsilonMax
      hnu hr heta hepsilonMax
  refine ⟨epsilon,hepsilon,hepsilon8,hepsilonMax',hepsilonr,N0,hN0,?_⟩
  intro N hN hEven cap hcap mesh D
  let y := (N : ℝ)^(nu*epsilon^2)
  let z := (N : ℝ)^(nu*r)
  let L := (N : ℝ)^(nu*epsilon)
  let reserve := eta * singularSeries N / Real.log (N : ℝ)
  have hb := hbound N hN hEven cap hcap (thirdRetain D N)
  obtain ⟨hminor,habs,hden⟩ := hb
  have hcount := sum_new_minorant_le_true_sifted N z (newSupport D N cap y z)
    (newRho D N cap y z L) hminor
  have hdecomp := new_true_prime_count_decomposition D N cap y z L
  have hm : (0 : ℝ) ≤ (chenAdditivePrimeCarrier N).card := Nat.cast_nonneg _
  have hscaled : ((chenAdditivePrimeCarrier N).card : ℝ) *
      (rawDensity (thirdRetain D N) N cap 0 z - reserve) ≤
      ((chenAdditivePrimeCarrier N).card : ℝ) *
        physicalDensitySum (newSupport D N cap y z) (newRho D N cap y z L) :=
    mul_le_mul_of_nonneg_left hden hm
  linarith

/-- The original sufficient route now has the COMPLETE actual raw I3 sum
inside the true-prime lower count. Its one NEW projection/attachment reserve
is paid; the original same-rho AP error and modulus-prime correction remain
literal. This is not an integral limit or a distribution estimate. -/
theorem exists_true_prime_lower_from_complete_raw_I3
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1/8 ∧ epsilon < epsilonMax ∧
      epsilon^2 ≤ r ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ)^(nu*r) ≤ (cap : ℝ) →
      ∀ mesh : ℕ, ∀ D : ThirdStage mesh,
        let y := (N : ℝ)^(nu*epsilon^2)
        let z := (N : ℝ)^(nu*r)
        let L := (N : ℝ)^(nu*epsilon)
        let reserve := eta * singularSeries N / Real.log (N : ℝ)
        ((chenAdditivePrimeCarrier N).card : ℝ) *
          (rawDensity (seedRetain D N) N cap 0 z +
            ((D.taggedFrontier N cap z (fun p => 1 / ((p : ℝ)-1))).map
              (actualFullI3PlusTerm D N cap)).sum - reserve) -
          newPrimeCoprimeCorrection D N cap y z L + newPrimeSignedError D N cap y z L ≤
        ((chenSiftedPrimeSource N z).card : ℝ) := by
  obtain ⟨epsilon,hepsilon,hepsilon8,hepsilonMax',hepsilonr,N0,hN0,hbound⟩ :=
    exists_new_true_prime_lower_compilation nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon,hepsilon,hepsilon8,hepsilonMax',hepsilonr,N0,hN0,?_⟩
  intro N hN hEven cap hcap mesh D
  have hN1 : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hraw := complete_raw_I3_eq_actual_plus_frontier D N cap
    ((N : ℝ)^(nu*r)) hN1
  have heq : rawDensity (thirdRetain D N) N cap 0 ((N : ℝ)^(nu*r)) =
      rawDensity (seedRetain D N) N cap 0 ((N : ℝ)^(nu*r)) +
        ((D.taggedFrontier N cap ((N : ℝ)^(nu*r))
          (fun p => 1 / ((p : ℝ)-1))).map (actualFullI3PlusTerm D N cap)).sum := by
    linarith
  have hb := hbound N hN hEven cap hcap mesh D
  dsimp only at hb ⊢
  rw [heq] at hb
  exact hb

end
end ImbalancedChen.P2OriginalNewLowerTruePrimeCompilation
