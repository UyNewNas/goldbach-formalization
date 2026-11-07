import ImbalancedChen.Part3OriginalPaperPsiCoprimeCount
import ImbalancedChen.Part3OriginalMediumS1ActualCoefficientBinding
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal S1 common-m count, its principal coefficient, and its
uniform ordinary-divisor remainder now use the same actual paperPsi
that bindBlock installs as its q majorant. No old dyadic-count remainder
is relabelled: paperCommonMCount and paperMass are the new exact objects.
-/

namespace ImbalancedChen.Part3.OriginalSamePsiS1Remainder

noncomputable section

open Classical Finset
open scoped BigOperators
open OriginalPaperPsiCoprimeCount OriginalMediumPhysicalE3Block
open OriginalMediumS1CommonMCount OriginalMediumS1WeightedRemainder
open OriginalMediumS1SeparatedDivisorMean OriginalMediumS1ActualCoefficientBinding
open OriginalGevreyPoissonPacket20261028 MediumCanonicalFixedBlock20261028

def paperS1PurePair (B : FixedBlock) (S : Finset ℕ) (M : ℝ)
    (q r s : ℕ) : ℂ :=
  B.lambdaD r * star (B.lambdaD s) *
    ((paperCommonMCount S M (q * B.d) r s /
      (((q * B.d * r).totient : ℝ) * ((q * B.d * s).totient : ℝ))) : ℝ) *
    alphaMean B (q * B.d) r * star (alphaMean B (q * B.d) s)

def paperS1PrincipalPair (B : FixedBlock) (M : ℝ) (q r s : ℕ) : ℂ :=
  B.lambdaD r * star (B.lambdaD s) * ((M * paperMass : ℝ) : ℂ) *
    OriginalMediumPrincipalFiniteCRT.paperPrincipalCoefficient (q * B.d) r s *
    alphaMean B (q * B.d) r * star (alphaMean B (q * B.d) s)

def paperS1RemainderPair (B : FixedBlock) (S : Finset ℕ) (M : ℝ)
    (q r s : ℕ) : ℂ :=
  B.lambdaD r * star (B.lambdaD s) *
    (((paperCommonMCount S M (q * B.d) r s -
      (M * paperMass) * ((q * B.d * r * s).totient : ℝ) /
        (q * B.d * r * s : ℕ)) /
      (((q * B.d * r).totient : ℝ) * ((q * B.d * s).totient : ℝ))) : ℝ) *
    alphaMean B (q * B.d) r * star (alphaMean B (q * B.d) s)

/-- The exact principal kernel is unchanged, while its common-m count
and its zero mass are now both for the actual paper profile. -/
theorem paperS1PurePair_eq_principal_add_remainder
    (B : FixedBlock) (S : Finset ℕ) (M : ℝ) (q r s : ℕ) :
    paperS1PurePair B S M q r s =
      paperS1PrincipalPair B M q r s + paperS1RemainderPair B S M q r s := by
  unfold paperS1PurePair paperS1PrincipalPair paperS1RemainderPair
    OriginalMediumPrincipalFiniteCRT.paperPrincipalCoefficient
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

def paperS1ActualRemainder (B : FixedBlock) (S : Finset ℕ) (M : ℝ) : ℂ :=
  ∑ q ∈ B.qCarrier, ∑ r ∈ B.wCarrier, ∑ s ∈ B.wCarrier,
    actualQWeight B q * paperS1RemainderPair B S M q r s

theorem paperS1_finite_sum_eq_principal_add_remainder
    (B : FixedBlock) (S : Finset ℕ) (M : ℝ) :
    (∑ q ∈ B.qCarrier, ∑ r ∈ B.wCarrier, ∑ s ∈ B.wCarrier,
      actualQWeight B q * paperS1PurePair B S M q r s) =
    (∑ q ∈ B.qCarrier, ∑ r ∈ B.wCarrier, ∑ s ∈ B.wCarrier,
      actualQWeight B q * paperS1PrincipalPair B M q r s) +
      paperS1ActualRemainder B S M := by
  unfold paperS1ActualRemainder
  simp_rw [paperS1PurePair_eq_principal_add_remainder, mul_add,
    Finset.sum_add_distrib]

def divisorKernelTerm (B : FixedBlock) (q r s : ℕ) : ℝ :=
  ‖actualQWeight B q‖ * ‖B.lambdaD r‖ * ‖B.lambdaD s‖ *
    (((q * B.d * r * s).divisors.card : ℝ) /
      (((q * B.d * r).totient : ℝ) * ((q * B.d * s).totient : ℝ))) *
    ‖alphaMean B (q * B.d) r‖ * ‖alphaMean B (q * B.d) s‖

private theorem weighted_pair_norm_le
    (B : FixedBlock) (S : Finset ℕ) (M C : ℝ)
    (hcount : ∀ ell r s : ℕ, 0 < ell → 0 < r → 0 < s →
      |paperCommonMCount S M ell r s -
        (M * paperMass) * ((ell * r * s).totient : ℝ) / (ell * r * s : ℕ)| ≤
        C * ((ell * r * s).divisors.card : ℝ))
    {q r s : ℕ} (hq : q ∈ B.qCarrier)
    (hr : r ∈ B.wCarrier) (hs : s ∈ B.wCarrier) :
    ‖actualQWeight B q * paperS1RemainderPair B S M q r s‖ ≤
      C * divisorKernelTerm B q r s := by
  obtain ⟨hqpos, hrpos⟩ := carrier_positive B hq hr
  have hspos := (carrier_positive B hq hs).2
  have hell : 0 < q * B.d := mul_pos hqpos B.d_pos
  have hphi1 : (0 : ℝ) < (q * B.d * r).totient := by
    exact_mod_cast Nat.totient_pos.mpr (mul_pos hell hrpos)
  have hphi2 : (0 : ℝ) < (q * B.d * s).totient := by
    exact_mod_cast Nat.totient_pos.mpr (mul_pos hell hspos)
  let E : ℝ := paperCommonMCount S M (q * B.d) r s -
    (M * paperMass) * ((q * B.d * r * s).totient : ℝ) / (q * B.d * r * s : ℕ)
  let D : ℝ := ((q * B.d * r).totient : ℝ) * ((q * B.d * s).totient : ℝ)
  have hD : 0 < D := mul_pos hphi1 hphi2
  have hE : |E| ≤ C * ((q * B.d * r * s).divisors.card : ℝ) :=
    hcount (q * B.d) r s hell hrpos hspos
  have hED : |E / D| ≤ C * ((q * B.d * r * s).divisors.card : ℝ) / D := by
    rw [abs_div, abs_of_pos hD]
    exact div_le_div_of_nonneg_right hE hD.le
  have hnorm :
      ‖actualQWeight B q * paperS1RemainderPair B S M q r s‖ =
      ‖actualQWeight B q‖ * ‖B.lambdaD r‖ * ‖B.lambdaD s‖ * |E / D| *
        ‖alphaMean B (q * B.d) r‖ * ‖alphaMean B (q * B.d) s‖ := by
    simp [paperS1RemainderPair, E, D, norm_mul, norm_star,
      Complex.norm_real, Real.norm_eq_abs]
    ring
  rw [hnorm]
  calc
    _ ≤ ‖actualQWeight B q‖ * ‖B.lambdaD r‖ * ‖B.lambdaD s‖ *
        (C * ((q * B.d * r * s).divisors.card : ℝ) / D) *
        ‖alphaMean B (q * B.d) r‖ * ‖alphaMean B (q * B.d) s‖ := by
      gcongr
    _ = _ := by dsimp [divisorKernelTerm, D]; ring

/-- One actual-paperPsi common-m constant controls every fixed block.
The positive divisor kernel is exactly the already-paid old kernel;
only the counted profile and its actual mass have changed. -/
theorem paperS1ActualRemainder_le_uniform_divisor_kernel :
    ∃ C : ℝ, 0 < C ∧ ∀ B : FixedBlock, ∀ M : ℝ, 0 < M →
      ∀ S : Finset ℕ, (∀ m, paperWeight M m ≠ 0 → m ∈ S) →
        ‖paperS1ActualRemainder B S M‖ ≤ C * S1DivisorKernel B := by
  obtain ⟨C, hC, hcount⟩ := paperCommonMCount_uniform_error
  refine ⟨C, hC, ?_⟩
  intro B M hM S hS
  have hp := weighted_pair_norm_le B S M C
    (fun ell r s hell hr hs => hcount M hM S hS ell r s hell hr hs)
  unfold paperS1ActualRemainder
  change ‖∑ q ∈ B.qCarrier, ∑ r ∈ B.wCarrier, ∑ s ∈ B.wCarrier,
      actualQWeight B q * paperS1RemainderPair B S M q r s‖ ≤
    C * ∑ q ∈ B.qCarrier, ∑ r ∈ B.wCarrier, ∑ s ∈ B.wCarrier,
      divisorKernelTerm B q r s
  calc
    _ ≤ ∑ q ∈ B.qCarrier, ∑ r ∈ B.wCarrier, ∑ s ∈ B.wCarrier,
        ‖actualQWeight B q * paperS1RemainderPair B S M q r s‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro r _
      exact norm_sum_le _ _
    _ ≤ C * ∑ q ∈ B.qCarrier, ∑ r ∈ B.wCarrier, ∑ s ∈ B.wCarrier,
        divisorKernelTerm B q r s := by
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      exact hp hq hr hs

theorem paperWeight_support {M : ℝ} (hM : 0 < M) {m : ℕ}
    (hm : paperWeight M m ≠ 0) : m ∈ paperPsiNaturalCarrier M := by
  apply paperPsiNaturalCarrier_support hM
  change (paperWeight M m : ℂ) ≠ 0
  exact_mod_cast hm

/-- The same absolute counting constant is retained before the complete
d-block ordinary divisor mean from the first batch is inserted. -/
theorem paperS1ActualRemainder_family_le_kernel :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset ℕ) (F : ℕ → FixedBlock)
      (M : ℝ) (S : Finset ℕ), 0 < M →
      (∀ m, paperWeight M m ≠ 0 → m ∈ S) →
      ‖∑ d ∈ T, paperS1ActualRemainder (F d) S M‖ ≤
        C * ∑ d ∈ T, S1DivisorKernel (F d) := by
  obtain ⟨C, hC, hbound⟩ := paperS1ActualRemainder_le_uniform_divisor_kernel
  refine ⟨C, hC, ?_⟩
  intro T F M S hM hS
  calc
    _ ≤ ∑ d ∈ T, ‖paperS1ActualRemainder (F d) S M‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ T, C * S1DivisorKernel (F d) :=
      Finset.sum_le_sum (fun d _ => hbound (F d) M hM S hS)
    _ = _ := by rw [Finset.mul_sum]

/-- An actual same-paperPsi S1 remainder at original scale M=V, with
literal Lambda, q-majorant and support premises all discharged. The
constant is chosen before the original atom and geometric fixed block. -/
theorem actual_samePsi_fixedBlock_S1_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : FixedBlock) (W : Block) (z : ℝ)
      (hd : W.d = B.d) (k : ℕ) (σ κ c0 : ℝ),
      MediumAdmissible k σ κ c0 B.atom →
      ‖paperS1ActualRemainder (bindBlock B W z hd)
        (paperPsiNaturalCarrier B.atom.V) B.atom.V‖ ≤
      C * ((2 * B.atom.U) ^ 2 *
        P5Z.RoughSquareWeightedBudget.logBudget (physicalCap B) ^ 2 *
        (tauR B.d ^ 3 / (B.d : ℝ) ^ 2) *
        ((1 + Real.log (qCap B : ℝ)) ^ 4 / B.q0) *
        (1 + Real.log (roughCap B : ℝ)) ^ 16) := by
  obtain ⟨C, hC, hbound⟩ := paperS1ActualRemainder_le_uniform_divisor_kernel
  refine ⟨4 * C, by positivity, ?_⟩
  intro B W z hd k σ κ c0 hA
  calc
    _ ≤ C * S1DivisorKernel (bindBlock B W z hd) :=
      hbound (bindBlock B W z hd) B.atom.V B.V_pos
        (paperPsiNaturalCarrier B.atom.V) (fun m hm => paperWeight_support B.V_pos hm)
    _ ≤ C * (4 * (2 * B.atom.U) ^ 2 *
        P5Z.RoughSquareWeightedBudget.logBudget (physicalCap B) ^ 2 *
        (tauR B.d ^ 3 / (B.d : ℝ) ^ 2) *
        ((1 + Real.log (qCap B : ℝ)) ^ 4 / B.q0) *
        (1 + Real.log (roughCap B : ℝ)) ^ 16) :=
      mul_le_mul_of_nonneg_left (bound_actual_boundBlock_kernel B W z hd hA) hC.le
    _ = _ := by ring

end

end ImbalancedChen.Part3.OriginalSamePsiS1Remainder
