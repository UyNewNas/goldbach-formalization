import ImbalancedChen.Part3OriginalCommonPoissonLanesCore
import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson

/-!
# Recovered common Poisson lanes for the physical completed kernel

Source-preserving intake, 2026-11-26. The four marked fragments below retain
original namespaces and statements from these exact blobs:
* ActualReciprocalSquarePoisson: 58e9a86e0bd60aee30ebc7a15c781f2dd96a49c9;
* ActualCompletedSquarePushforward: 04972fd9774d63bfa5aca69b23d2e389446b448b;
* OriginalCommonPoissonLanes: 00a797ac77cb444479ce097f4b44c56930489e32.
The recovered source selection and raw-source hashes are recorded separately.
The sole proof repair makes the two conditional rewrites in weightedC_add
explicit; EXPRESSION_REPAIR.json records the original and staged fragments.

The suppliers here retain the negative Fourier argument, the actual
residue-unit filter and the full integer Poisson series. The resulting
completed kernel splits exactly into zero frequency, common signed dyadic
blocks and an explicit retained tail. No estimate on that tail is asserted.

This extraction uses the already accepted Physical Poisson and common-lanes
cores. It does not import or replace OriginalData, complete the original
source-family coupling, or construct a spectral kernel/PacketData. A later
full original source must import this core instead of redeclaring these
same constants. Strict compilation and owned/kernel acceptance are separate.
-/

noncomputable section
open Classical Finset
open scoped BigOperators SchwartzMap FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.CommonSmoothCutoff
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical

attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly

-- BEGIN recovered sign_frequency
/-- Exact completed-frequency sign conversion by u -> -u on ALL residues,
valid also at modulus1. It does not conjugate or replace any coefficient. -/
theorem kloosterman_both_negative {c : ℕ} [NeZero c] (m n : ℤ) :
    kloosterman c (-m) (-n) = kloosterman c m n := by
  rw [kloosterman_eq_zmod (c := c), kloosterman_eq_zmod (c := c)]
  have hbij : Function.Bijective (fun u : ZMod c => -u) :=
    ⟨fun u v h => neg_injective h, fun u => ⟨-u,neg_neg u⟩⟩
  apply Fintype.sum_bijective (fun u : ZMod c => -u) hbij
  intro u
  by_cases hu : IsUnit u
  · have hnu : IsUnit (-u) := hu.neg
    have hi : (-u)⁻¹ = -u⁻¹ := ZMod.inv_eq_of_mul_eq_one c (-u) (-u⁻¹)
      (by simpa only [neg_mul_neg] using ZMod.mul_inv_of_unit u hu)
    simp only [if_pos hu, if_pos hnu, Int.cast_neg, hi]
    congr 1
    ring
  · have hnu : ¬IsUnit (-u) := fun h => hu (by simpa only [neg_neg] using h.neg)
    simp only [if_neg hu, if_neg hnu]

theorem kloosterman_negative_linear {c : ℕ} [NeZero c] (m n : ℤ) :
    kloosterman c (-m) n = kloosterman c m (-n) := by
  simpa only [neg_neg] using kloosterman_both_negative (c := c) m (-n)

/-- A negative original m keeps the NEGATIVE Fourier argument; the complete
sum has positive |m| and residue -a*y. This is the opposite-sign chart. -/
theorem frequency_negative {c : ℕ} [NeZero c] (M : ℝ) (a y z p : ℤ) :
    frequency M c a y z (-p) =
      (M/(c : ℝ)) • (𝓕 dyadicCutoffSchwartz) (-(M/(c : ℝ))*(p : ℝ)) *
        kloosterman c (p*inverseResidue c z) (-(a*y)) := by
  unfold frequency
  rw [show (-p)*inverseResidue c z = -(p*inverseResidue c z) by ring,
    kloosterman_negative_linear (c := c)]
  simp only [Int.cast_neg, mul_neg, neg_mul]
-- END recovered sign_frequency

end ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly

namespace ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly

-- BEGIN recovered output
abbrev Output := ℕ × ℤ
-- END recovered output

-- BEGIN recovered completed_kernel
/-- Only the residue-unit condition remains in the completed kernel;
all fixed t-unit conditions already belong to beta's source carrier. -/
def completedKernel (M N C : ℝ) (a : ℤ) (zy : Output) : ℂ :=
  ∑ c ∈ Ioc 0 (Nat.floor (10*C)), if c.Coprime zy.1 then
    (scaledDyadicCutoff N c : ℂ) * ∑' m : ℤ, frequency M c a zy.2 (zy.1 : ℤ) m else 0
-- END recovered completed_kernel

end ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly

open ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly
open ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly

namespace ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102

-- BEGIN recovered kernel_lanes
/-- Negative original m keeps the Fourier transform evaluated at -pM/c.
Only the Kloosterman sign chart is changed; beta is not conjugated. -/
theorem negative_block_literal {c : ℕ} [NeZero c] (J j : ℕ)
    (M : ℝ) (a y : ℤ) (z : ℕ) :
    (∑ p ∈ commonMBlock J j, frequency M c a y (z : ℤ) (-(p : ℤ))) =
      ∑ p ∈ commonMBlock J j,
        (M / (c : ℝ)) • (𝓕 dyadicCutoffSchwartz) (-(M / (c : ℝ)) * (p : ℝ)) *
          kloosterman c ((p : ℤ) * inverseResidue c (z : ℤ)) (-(a * y)) := by
  apply sum_congr rfl
  intro p hp
  simpa only [Int.cast_natCast] using frequency_negative (c := c) M a y (z : ℤ) (p : ℤ)

def weightedC (N C : ℝ) (z : ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ c ∈ Ioc 0 (Nat.floor (10 * C)),
    if c.Coprime z then (scaledDyadicCutoff N c : ℂ) * f c else 0

theorem weightedC_add (N C : ℝ) (z : ℕ) (f g : ℕ → ℂ) :
    weightedC N C z (fun c => f c + g c) = weightedC N C z f + weightedC N C z g := by
  unfold weightedC
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro c hc
  by_cases hz : c.Coprime z
  · simp only [if_pos hz, mul_add]
  · simp only [if_neg hz, zero_add]

theorem weightedC_sum {ι : Type*} (N C : ℝ) (z : ℕ) (I : Finset ι) (f : ι → ℕ → ℂ) :
    weightedC N C z (fun c => ∑ i ∈ I, f i c) = ∑ i ∈ I, weightedC N C z (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [weightedC]
  | @insert i I hi ih => simp only [sum_insert hi, weightedC_add, ih]

def zeroMKernel (M N C : ℝ) (a : ℤ) (zy : Output) : ℂ :=
  weightedC N C zy.1 (fun c => frequency M c a zy.2 (zy.1 : ℤ) 0)
def blockKernel (J j : ℕ) (negativeM : Bool) (M N C : ℝ) (a : ℤ) (zy : Output) : ℂ :=
  weightedC N C zy.1 (fun c => ∑ p ∈ commonMBlock J j,
    frequency M c a zy.2 (zy.1 : ℤ) (if negativeM then -(p : ℤ) else (p : ℤ)))
def tailKernel (J : ℕ) (M N C : ℝ) (a : ℤ) (zy : Output) : ℂ :=
  weightedC N C zy.1 (fun c => poissonTail J M c a zy.2 (zy.1 : ℤ))

/-- The true physical Kloosterman kernel, with its c-unit filter, has
separate zero-m, common positive/reflected-negative blocks, and tail. -/
theorem completedKernel_eq_m_lanes {M : ℝ} (hM : 0 < M)
    (J : ℕ) (N C : ℝ) (a : ℤ) (zy : Output) :
    completedKernel M N C a zy = zeroMKernel M N C a zy +
      (∑ j ∈ blockIndices J,
        (blockKernel J j false M N C a zy + blockKernel J j true M N C a zy)) +
      tailKernel J M N C a zy := by
  have hpoint : completedKernel M N C a zy = weightedC N C zy.1 (fun c =>
      frequency M c a zy.2 (zy.1 : ℤ) 0 +
      (∑ j ∈ blockIndices J,
        ((∑ p ∈ commonMBlock J j, frequency M c a zy.2 (zy.1 : ℤ) (p : ℤ)) +
         ∑ p ∈ commonMBlock J j, frequency M c a zy.2 (zy.1 : ℤ) (-(p : ℤ)))) +
      poissonTail J M c a zy.2 (zy.1 : ℤ)) := by
    unfold completedKernel weightedC
    apply sum_congr rfl
    intro c hc
    by_cases hcz : c.Coprime zy.1
    · let : NeZero c := ⟨(mem_Ioc.mp hc).1.ne'⟩
      simp only [if_pos hcz]
      rw [poisson_series_eq_lanes hM J a zy.2 zy.1 hcz]
    · simp only [if_neg hcz]
  rw [hpoint, weightedC_add, weightedC_add, weightedC_sum]
  simp only [weightedC_add, zeroMKernel, blockKernel, tailKernel, Bool.false_eq_true,
    if_false, if_true]
-- END recovered kernel_lanes

end ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102
end
