import ImbalancedChen.P5OriginalPrimeAtlasReserveBranches
import ImbalancedChen.P5ActualSingletonPrimeTestFamily
import ImbalancedChen.SingletonPrimeProductTransportP5

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual independent singleton prime-test supplier is used with the
production original lower small/rough rho and its FULL original Q.
The smooth prime source extends to 2N; it is not truncated silently at N.
The true upper collar and the sharp-prefix reconstruction are separately
owned by the original singleton source-restoration work. This gives no
negligibility claim for that collar and no all-rank caller coverage.
-/
namespace ImbalancedChen.P5Z.ActualSingletonLowerRhoAllGroupSource
noncomputable section
open Classical
open scoped BigOperators
open OriginalPrimeAllGroupHBDiscrepancy OriginalPrimeAtlasReserveBranches
open ActualSingletonPrimeTestFamily

def originalSmoothSource (beta : ℝ) (N : ℕ) (retainEven : List ℕ → Bool)
    (cap : ℕ) (w z L : ℝ) : ℝ :=
  Part3.primeProductSignedError 1 (2 * N) N
    (actualLowerSmallRoughModuli retainEven N cap w z)
    (actualLowerSmallRoughRho retainEven N cap w z L)
    (fun u => integerWeight beta N (fun i => (u i).val))

/-- Its u is the actual ORIGINAL singleton prime, independent of the
coefficient's small/rough divisors. The same full Q and rho are used in
the true count and primitive-coprime mean on the original receiver. -/
theorem originalSmoothSource_receiver (beta : ℝ) (N : ℕ)
    (retainEven : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) :
    originalSmoothSource beta N retainEven cap w z L =
      ∑ q ∈ actualLowerSmallRoughModuli retainEven N cap w z,
        actualLowerSmallRoughRho retainEven N cap w z L q *
          finitePrimitiveDiscrepancy (chenPrimePrefix (2 * N))
            (fun p => integerWeight beta N (fun _ => p)) N q := by
  change Part3.primeProductSignedError 1 (2 * N) N _ _
    (P5S1SingletonPP.singletonWeight (2 * N) (fun p => integerWeight beta N (fun _ => p))) = _
  exact P5S1SingletonPP.primeProductSignedError_singleton_eq (2 * N) N _ _ _

/-- Concrete exact all-group source connection for a genuinely supplied
independent prime test and the production original lower coefficient.
No bound or final-source matching statement is assumed. The analytic
retained-mode applications and the normalized Fourier-profile transport
are still required after this exact identity. -/
theorem actual_singleton_original_allGroup (beta : ℝ) (N : ℕ) (κ₀ ζ : ℝ)
    (retainEven : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) :
    (originalSmoothSource beta N retainEven cap w z L : ℂ) =
      trimReserve (singletonLicence beta N) (2 * N) N κ₀
        (actualLowerSmallRoughModuli retainEven N cap w z)
        (fun q => (actualLowerSmallRoughRho retainEven N cap w z L q : ℂ)) +
      ∑ js ∈ ExactOriginalSmoothDyadicPartition.chartBank (2 * N) 1,
        (mediumAtlas (singletonLicence beta N) 1 (2 * N) N κ₀
            (originalMediumLow ζ js) (originalMediumHigh ζ js)
            (actualLowerSmallRoughModuli retainEven N cap w z)
            (fun q => (actualLowerSmallRoughRho retainEven N cap w z L q : ℂ)) js +
          noMediumAtlas (singletonLicence beta N) 1 (2 * N) N κ₀
            (originalMediumLow ζ js) (originalMediumHigh ζ js)
            (actualLowerSmallRoughModuli retainEven N cap w z)
            (fun q => (actualLowerSmallRoughRho retainEven N cap w z L q : ℂ)) js -
          properPowerReserve (singletonLicence beta N) 1 (2 * N) N κ₀
            (actualLowerSmallRoughModuli retainEven N cap w z)
            (fun q => (actualLowerSmallRoughRho retainEven N cap w z L q : ℂ)) js +
          roughPrimeReserve (singletonLicence beta N) 1 (2 * N) N κ₀
            (actualLowerSmallRoughModuli retainEven N cap w z)
            (fun q => (actualLowerSmallRoughRho retainEven N cap w z L q : ℂ)) js) := by
  exact original_prime_discrepancy_mode_carriers (singletonLicence beta N) 1 (2 * N) N κ₀ ζ
    (actualLowerSmallRoughModuli retainEven N cap w z)
    (actualLowerSmallRoughRho retainEven N cap w z L)

end
end ImbalancedChen.P5Z.ActualSingletonLowerRhoAllGroupSource
