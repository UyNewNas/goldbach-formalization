import ImbalancedChen.P3ActualRawIntegerRhoCast
import ImbalancedChen.P3ActualRetainedRoughEulerMass
import ImbalancedChen.P3ActualWholeProductPrimitiveMeanPayment
import Mathlib.Tactic

/-!
P3.6, frozen manuscript UyNewNas/chen-imbalanced-semiprimes@
9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§1,3(T),4(F).

The original raw small/rough provider was a REAL weight. Its source-faithful
INTEGER cast was constructed separately; the retained first-exit Euler
mass estimate was proved separately for the REAL raw weight. This packet
joins those two paths on exactly the same physical q, without introducing
an arbitrary replacement rho or discarding the primitive coprimality filter.
The full original ordered three-prime-box HB source is included on the MEAN
side, retaining the actual product and positional W and all multiplicities.

Important: this rho is the genuine integer RAW provider, but it is NOT yet
the final causal compiler rho_N (global squarefree gate, restoration, other
sources). The Euler product remains finite, not uniformly log-bounded.
The nonzero-shift COUNT discrepancy and complete PP remain open.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualIntegerRawSameRhoMean
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualRawIntegerRhoCast
open ImbalancedChen.P3ActualRawPhysicalRhoTotientCap
open ImbalancedChen.P3ActualRetainedRoughEulerMass
open ImbalancedChen.P3ActualSignedPairTotientCap
open ImbalancedChen.P3ActualWholeProductPrimitiveMeanPayment
open ImbalancedChen.P3ActualFrozenTaggedPrimeBox
open ImbalancedChen.P3ActualFixedHBOffshiftSourceLedger

/-- Exactly the same real positive physical totient weight is obtained
from an INTEGER coefficient after taking the complex norm; there is no
signed cancellation or passage to an auxiliary level hidden here. -/
private theorem int_complex_totient_norm (c : ℤ) (q : ℕ) :
    ‖(c : ℂ) * (((Nat.totient q : ℝ)⁻¹ : ℝ) : ℂ)‖ =
      |(c : ℝ)| * (Nat.totient q : ℝ)⁻¹ := by
  have hcast : (c : ℂ) = ((c : ℝ) : ℂ) := by norm_cast
  rw [hcast, norm_mul, Complex.norm_real, Complex.norm_real]
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ (Nat.totient q : ℝ)⁻¹ by positivity)]

/-- The integer RAW rho and the production real RAW rho have IDENTICAL
positive reciprocal-totient physical mass, not just comparable masses. -/
theorem actual_integer_raw_physical_mass_eq
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    physicalReciprocalTotientMass
      (actualSmallRoughModuli retainOdd N cap w z)
      (actualRawIntegerRho retainOdd N cap w z L) =
    actualRawPhysicalTotientMass retainOdd N cap w z L := by
  unfold physicalReciprocalTotientMass actualRawPhysicalTotientMass
  apply Finset.sum_congr rfl
  intro q hq
  rw [int_complex_totient_norm,
    actualRawIntegerRho_cast retainOdd N cap w z L q]

/-- Source-faithful INTEGER raw rho, original full physical q and Euler phi.
Only the strict real Rosser level L≤A is required; no bounded rough rank.
The remaining finite Euler product has NOT been assigned a log^E bound. -/
theorem actual_integer_raw_physical_mass_le_euler
    (retainOdd : List ℕ → Bool) (N cap A : ℕ) (w z L : ℝ)
    (hLA : L ≤ (A : ℝ)) :
    physicalReciprocalTotientMass
      (actualSmallRoughModuli retainOdd N cap w z)
      (actualRawIntegerRho retainOdd N cap w z L) ≤
    logTotientCap A * roughEulerMass N cap w z := by
  rw [actual_integer_raw_physical_mass_eq]
  exact actual_raw_physical_mass_le_active_level_euler
    retainOdd N cap A w z L hLA

/-- The original primitive mean preserves gcd(B,q)=1 at the COMPLETE
product B, and uses the same signed integer RAW rho as the previous line.
This does not estimate the count-minus-mean discrepancy. -/
theorem actual_integer_raw_primitive_mean_le_euler
    (retainOdd : List ℕ → Bool) (N cap A B : ℕ) (w z L : ℝ)
    (hLA : L ≤ (A : ℝ)) :
    ‖primitivePhysicalMean B
        (actualSmallRoughModuli retainOdd N cap w z)
        (actualRawIntegerRho retainOdd N cap w z L)‖ ≤
      logTotientCap A * roughEulerMass N cap w z := by
  exact (primitivePhysicalMean_norm_le B
    (actualSmallRoughModuli retainOdd N cap w z)
    (actualRawIntegerRho retainOdd N cap w z L)).trans
    (actual_integer_raw_physical_mass_le_euler retainOdd N cap A w z L hLA)

/-- The exact ORIGINAL three ordered fine-prime boxes and positional HB
weight, with a full product and unchanged labels/multiplicities, receive
that same INTEGER raw rho in the exact coprime primitive MEAN.

Even N and zHB≥2 are used only to erase the exceptional full product N for
this admitted three-box source (as proved in the inherited HB ledger).
The coefficient L1 factor still needs its own growing-m uniform bound;
this theorem neither states nor assumes the PP error bound.
The producer upper cutoff roughZ and HB rough threshold zHB are DISTINCT. -/
theorem actual_integer_raw_threeHB_mean_le_euler
    (retainOdd : List ℕ → Bool) (N cap A m j : ℕ)
    (w roughZ L τ zHB y : ℝ) (u v r : List ℕ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (hLA : L ≤ (A : ℝ)) (hz : (2 : ℝ) ≤ zHB) (hN : Even N) :
    ‖fixedThreeHBOffshiftMean N m j τ zHB y u v r
      (actualSmallRoughModuli retainOdd N cap w roughZ)
      (actualRawIntegerRho retainOdd N cap w roughZ L) W‖ ≤
    (∑ a ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) u,
      ∑ b ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) v,
        ∑ d ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) r,
          ‖hbPositionalMass m j zHB y W a b d‖) *
      (logTotientCap A * roughEulerMass N cap w roughZ) := by
  let C : ℝ :=
    ∑ a ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) u,
      ∑ b ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) v,
        ∑ d ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) r,
          ‖hbPositionalMass m j zHB y W a b d‖
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hmean := fixedThreeHBOffshiftMean_norm_le
    N m j τ zHB y u v r
    (actualSmallRoughModuli retainOdd N cap w roughZ)
    (actualRawIntegerRho retainOdd N cap w roughZ L) W hz hN
  change _ ≤ C * _ at hmean
  change _ ≤ C * _
  exact hmean.trans (mul_le_mul_of_nonneg_left
    (actual_integer_raw_physical_mass_le_euler
      retainOdd N cap A w roughZ L hLA) hC)

end
end ImbalancedChen.P3ActualIntegerRawSameRhoMean
