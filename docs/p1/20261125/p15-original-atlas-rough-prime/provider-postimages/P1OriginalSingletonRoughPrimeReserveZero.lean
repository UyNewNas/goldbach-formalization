import ImbalancedChen.P1OriginalSingletonAtlasRoughPrime
import ImbalancedChen.P1OriginalSingletonMiddleTensor
import ImbalancedChen.P5IndependentTestPrimeChartUniformCutoff

/-!
SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.

The original singleton chart uses the real narrow profile, prime cap 2*N,
and the unchanged pre-HB cutoff. Its rough-prime correction is eventually
exactly zero, uniformly in the collar order, chart, complete modulus set
and signed coefficient. The cutoff supplier is applied at the independent
prime cap 2*N; the moving residue and physical target remain N.

No estimate for medium, two-long, proper powers, the historical middle
differences, or the whole singleton discrepancy is asserted here.
-/
namespace ImbalancedChen.P1OriginalSingletonRoughPrimeReserveZero
noncomputable section
open Classical Filter
open scoped BigOperators
open P5CanonicalTentNarrowSingletonTransfer (actualLicence)
open P5Z.LicensedOriginalIntegerProfile
open P5Z.ExactOriginalSmoothDyadicPartition
open P5Z.ActualLabelledPrimeSmoothCharts
open P5Z.OriginalPrimeAllGroupHBDiscrepancy
open P5Z.OriginalPrimeAtlasReserveBranches
open P5Z.IndependentTestPrimeChartUniformCutoff
open Part3.AllKLambdaChartCorrection Part3.OriginalProperPowerActualChart
open P1OriginalSingletonMiddleTensor (singletonAtlas)
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionTensor (products free)

/-- Read the already defined final-bank singletonAtlas itself. The
physical parameter record and free complete-modulus coefficient are the
original objects. Only the proved-zero rough-prime correction disappears. -/
theorem eventually_original_singletonAtlas_roughPrime_paid
    (K : ℕ) (hK : 1 ≤ K) (kappa : ℝ) (hk : kappa < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ P : Params, P.N = N → ∀ kappa0 zeta : ℝ,
      singletonAtlas P kappa K kappa0 zeta =
        let L := actualLicence kappa 6 P.N
        let S := products P
        let c := fun d => (free P d : ℂ)
        trimReserve L (2*P.N) P.N kappa0 S c +
          ∑ js ∈ chartBank (2*P.N) 1,
            (mediumAtlas L K (2*P.N) P.N kappa0
                (originalMediumLow zeta js) (originalMediumHigh zeta js) S c js +
              noMediumAtlas L K (2*P.N) P.N kappa0
                (originalMediumLow zeta js) (originalMediumHigh zeta js) S c js -
              properPowerReserve L K (2*P.N) P.N kappa0 S c js) := by
  obtain ⟨N0, _, hz⟩ := exists_original_singleton_roughPrimeReserve_zero K hK kappa hk
  filter_upwards [eventually_ge_atTop N0] with N hN
  intro P hPN kappa0 zeta
  subst N
  unfold singletonAtlas
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro js hjs
  rw [hz P.N hN 6 kappa0 (products P) (fun d => (free P d : ℂ)) js hjs, add_zero]

end
end ImbalancedChen.P1OriginalSingletonRoughPrimeReserveZero
