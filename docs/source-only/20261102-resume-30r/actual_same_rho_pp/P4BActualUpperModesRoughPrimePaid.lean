import ImbalancedChen.P4BActualUpperRoughPrimeReserveZero
import ImbalancedChen.P4BUpperPairOrderedRowModes

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Apply the actual rough-prime zero supplier to the existing original
attachedUpper occurrence/Fourier source.  Its two independent prime
coordinates, repeated primes, signed coefficient, chart/HB multiplicities
and exact coprime mean are unchanged.  The trim and proper-power correction
and the full retained arithmetic mode estimate remain to be paid.
This is not a UniformPrimeProductTarget theorem or a new PP consumer.
-/
namespace ImbalancedChen.P4BActualUpperModesRoughPrimePaid

noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOuterRampRoughness P4BArbitraryWidthUpperPairProfile
open P5Z.ExactOriginalSmoothDyadicPartition
open P5Z.OriginalPrimeAllGroupHBDiscrepancy
open P4BUpperPairOrderedRowModes P4BActualUpperRoughPrimeReserveZero

/-- The actual source loses its rough-prime correction by proof, with
fixed K before N and one threshold before all legal physical widths and
the unchanged epsilon/retain/cap inputs.  Both displayed remaining terms
are explicit arithmetic objects, not assumed small remainders. -/
theorem eventually_attachedUpper_modes_roughPrime_paid
    (K : ℕ) (hK : 2 ≤ K) {b kappa nu r : ℝ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, ∀ (width : ℝ) (hw : 0 < width)
      (hgap : 2 * width ≤ baseline b kappa - nu * r)
      (kappa0 epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ),
      (Part3.primeProductSignedError 2 N N
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N)
        (P4B.smoothPhysicalPairOuterRamp b N
          (manuscriptHalfProductCutoff kappa N) width) : ℂ) =
      trimReserve (licence hb hnu hr hw hgap N) N N kappa0
        (attachedUpperModuli nu r epsilon retain cap N)
        (fun q => (attachedUpperCoefficient nu r epsilon retain cap N q : ℂ)) +
        ∑ js ∈ chartBank N 2,
          (modeBank b kappa width N K (js.getD 0 0) (js.getD 1 0) kappa0
            (attachedUpperModuli nu r epsilon retain cap N)
            (fun q => (attachedUpperCoefficient nu r epsilon retain cap N q : ℂ)) -
          properPowerReserve (licence hb hnu hr hw hgap N) K N N kappa0
            (attachedUpperModuli nu r epsilon retain cap N)
            (fun q => (attachedUpperCoefficient nu r epsilon retain cap N q : ℂ)) js) := by
  obtain ⟨N0, hz⟩ := exists_actual_upper_roughPrimeReserve_zero K hK hb hnu hr
  filter_upwards [eventually_attachedUpper_source_modes hb hnu hr,
    Filter.eventually_ge_atTop N0] with N hsource hN
  intro width hw hgap kappa0 epsilon retain cap
  rw [hsource width hw hgap K kappa0 epsilon retain cap]
  unfold restoredModes
  congr 1
  apply Finset.sum_congr rfl
  intro js hjs
  rw [hz N hN width hw hgap kappa0
    (attachedUpperModuli nu r epsilon retain cap N)
    (fun q => (attachedUpperCoefficient nu r epsilon retain cap N q : ℂ)) js hjs,
    add_zero]

end
end ImbalancedChen.P4BActualUpperModesRoughPrimePaid
