import ImbalancedChen.P5CanonicalTentNarrowSingletonTransfer
import ImbalancedChen.P5OriginalPrimeAtlasReserveBranches

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
The independently defined original singleton source of the actual
canonical tent lower coefficient is connected to the genuine all-group
HB/dyadic occurrence atlas. The geometric source has the REAL narrow
collar Licence; all ordered roles, medium/no-medium rows, proper powers,
rough-prime correction and complete-product trim are the peer's actual
finite carriers. No final PP estimate or desired source identity is a
hypothesis. This is one present independent rank, not all callers/ranks.
-/
namespace ImbalancedChen.P5CanonicalTentSingletonActualHB
noncomputable section
open Classical
open scoped BigOperators
open P2OriginalPairSourceReceiver
open P5CanonicalTentIndependentSingletonCaller (keep lowerRho activeModuli)
open P5CanonicalTentNarrowSingletonTransfer
open P5Z.OriginalPrimeAllGroupHBDiscrepancy P5Z.OriginalPrimeAtlasReserveBranches
open P5Z.ExactOriginalSmoothDyadicPartition

-- This expression consists of independently constructed EXISTING HB
-- and reserve carriers. Its identity with the original prime source is
-- proved below by the exact peer dictionary, not by a candidate equality.
def actualAllGroupAtlas (kappa : ℝ) (B N : ℕ) (kappa0 zeta : ℝ)
    (retainEven : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) : ℂ :=
  trimReserve (actualLicence kappa B N) (2*N) N kappa0
      (actualLowerSmallRoughModuli retainEven N cap w z)
      (fun q => (actualLowerSmallRoughRho retainEven N cap w z L q : ℂ)) +
    ∑ js ∈ chartBank (2*N) 1,
      (mediumAtlas (actualLicence kappa B N) 1 (2*N) N kappa0
          (originalMediumLow zeta js) (originalMediumHigh zeta js)
          (actualLowerSmallRoughModuli retainEven N cap w z)
          (fun q => (actualLowerSmallRoughRho retainEven N cap w z L q : ℂ)) js +
        noMediumAtlas (actualLicence kappa B N) 1 (2*N) N kappa0
          (originalMediumLow zeta js) (originalMediumHigh zeta js)
          (actualLowerSmallRoughModuli retainEven N cap w z)
          (fun q => (actualLowerSmallRoughRho retainEven N cap w z L q : ℂ)) js -
        properPowerReserve (actualLicence kappa B N) 1 (2*N) N kappa0
          (actualLowerSmallRoughModuli retainEven N cap w z)
          (fun q => (actualLowerSmallRoughRho retainEven N cap w z L q : ℂ)) js +
        roughPrimeReserve (actualLicence kappa B N) 1 (2*N) N kappa0
          (actualLowerSmallRoughModuli retainEven N cap w z)
          (fun q => (actualLowerSmallRoughRho retainEven N cap w z L q : ℂ)) js)

theorem actual_narrow_smooth_allGroup (kappa : ℝ) (B N : ℕ) (kappa0 zeta : ℝ)
    (retainEven : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) :
    (Part3.primeProductSignedError 1 (2*N) N
      (actualLowerSmallRoughModuli retainEven N cap w z)
      (actualLowerSmallRoughRho retainEven N cap w z L)
      (fullSmoothWeight kappa B N) : ℂ) =
      actualAllGroupAtlas kappa B N kappa0 zeta retainEven cap w z L := by
  exact original_prime_discrepancy_mode_carriers (actualLicence kappa B N)
    1 (2*N) N kappa0 zeta (actualLowerSmallRoughModuli retainEven N cap w z)
    (actualLowerSmallRoughRho retainEven N cap w z L)

-- Both external source reserves remain explicit. Their quantitative
-- payment is the preceding narrow source-restoration theorem. HB trim,
-- proper-power and rough-prime reserves remain visible INSIDE the atlas.
theorem canonical_original_source_allGroup (R : PairRange) (mesh : ℕ)
    (buffer seed : ℚ) (kappa : ℝ) (B N : ℕ) (kappa0 zeta : ℝ)
    (cap : ℕ) (w z L : ℝ) :
    (Part3.primeProductSignedError 1 N N
      (activeModuli R mesh buffer seed N cap w z L)
      (lowerRho R mesh buffer seed N cap w z L)
      (P5S1SingletonPP.singletonWeight N (fun _ => 1)) : ℂ) =
      actualAllGroupAtlas kappa B N kappa0 zeta
        (keep R mesh buffer seed N) cap w z L +
      (lowerReserve kappa B N
        (actualLowerSmallRoughModuli (keep R mesh buffer seed N) N cap w z)
        (lowerRho R mesh buffer seed N cap w z L) : ℂ) +
      (upperReserve kappa B N
        (actualLowerSmallRoughModuli (keep R mesh buffer seed N) N cap w z)
        (lowerRho R mesh buffer seed N cap w z L) : ℂ) := by
  have hfull := P5CanonicalTentIndependentSingletonCaller.actual_lower_full_Q_eq_active
    (keep R mesh buffer seed N) N cap 1 N w z L
    (P5S1SingletonPP.singletonWeight N (fun _ => 1))
  have hid := original_source_exact_reserves kappa B N
    (actualLowerSmallRoughModuli (keep R mesh buffer seed N) N cap w z)
    (lowerRho R mesh buffer seed N cap w z L)
  have hHB := actual_narrow_smooth_allGroup kappa B N kappa0 zeta
    (keep R mesh buffer seed N) cap w z L
  change (Part3.primeProductSignedError 1 N N
    (P5S1OriginalLower.active (keep R mesh buffer seed N) N cap w z L)
    (actualLowerSmallRoughRho (keep R mesh buffer seed N) N cap w z L)
    (P5S1SingletonPP.singletonWeight N (fun _ => 1)) : ℂ) = _
  rw [← hfull, hid]
  push_cast
  rw [hHB]

end
end ImbalancedChen.P5CanonicalTentSingletonActualHB
