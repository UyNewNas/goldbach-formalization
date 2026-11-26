import ImbalancedChen.P1OriginalSingletonRoughSharpPaid
import ImbalancedChen.P4BOriginalSharpNativeRow
import ImbalancedChen.P1OriginalSingletonLogNormalization

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The generic same-Q/rho fibre identity and the existing sharp_fibre_identity
identify the original historical rectangle mode with the already paid rough
sharp sum. Only the finite outer sums are reordered here. The P4-specific
nativeMode_eq_sharpSum, whose coefficient is P4 rho, is not instantiated.

The actual remaining singleton dictionary supplies the two positions and
their original one/logarithm roles before the frequency is quantified. Its
original chart and assigned tuple, together with the existing normalized
profile supplier, supply every hypothesis of the local sharp payment.
The original dictionary's zeta <= 1/20000 range is retained. No activity
of an aggregate block coefficient or of every rectangle point is inferred.

This attaches one local bound to the exact native arithmetic Fourier mode
on the original right-closed block rectangle. It does not integrate Fourier
amplitudes, pay tails, or sum the outer HB atlas. The inherited missing
FixedM source and unique-owner import-closure boundaries remain.
-/

namespace ImbalancedChen.P1OriginalSingletonNativeTwoLongPaid
noncomputable section
open Classical Filter
open scoped BigOperators
open PrimeProducts
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.LiteralHeathBrownOccurrenceWords (factorTuples)
open P5Z.ActualRoughHeathBrownWords (Role roles)
open P5Z.ActualHBDyadicOccurrenceFamily (assignedWeight)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.ActualHBMediumBranchPartition (longBlocks)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P5Z.PerGroupIntegerHBAtlasPushforward (Row hbCutoff originalProducts typeIValue)
open P5Z.LicensedOriginalIntegerProfile (listExtension)
open P5Z.IndependentPrimeSourceWordDictionary (wordKernel)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (originalChart)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P5CanonicalTentNarrowSingletonTransfer (actualLicence)
open P5Z.ActualEtaPsiOccurrenceBudget (eta)
open P5Z.OrderedFactorTupleRectangleReindex (blockVector)
open Part3.OriginalProperPowerActualChart (wordVector)
open P5Z.ActualLowerNormalizedAtlasOccurrence (rowRoles scalarProfile integerProfile)
open P5Z.ActualLowerNormalizedBlockGeometry (rectangle scales)
open P5Z.ActualHBPostModulusLogCutoff (hbSlots completeProduct)
open P5Z.ActualAllRankOccurrenceFourierBridge (occurrenceMode)
open Part3.TwoLongActualHBShortMass (ShortPositions shortScale shortSupport shortSequence)
open P4BOriginalNoMediumPairRows (longPositions)
open P4BOriginalTwoLongActualDictionary (same_rho_mode_eq_fibres)
open P4BOriginalSharpLongProfiles (sharpProfile)
open P4BOriginalSharpNativeRow (sharp_fibre_identity)
open P1OriginalHistoricalTwoLongP2 (historicalModuli historicalRho)
open P1OriginalHistoricalTwoLongRoughComparison (historicalRoughSum)
open P1OriginalSingletonRoughSharpPaid (eventually_actual_singleton_rough_sharp_paid)
open P1OriginalSingletonRoughComparison (eventually_actual_singleton_rough_comparison_gates)
open P1OriginalSingletonRemainingTypeIGeometry
  (eventually_original_singleton_numeric_reserves)
open P1OriginalSingletonTwoLongDictionary (eventually_actual_remaining_tuple_dictionary)
open P1OriginalSingletonLogNormalization (eventually_actual_tuple_normalized_profile)

/-- Composition of the existing generic finite equalities for precisely
the historical P1 carrier and signed coefficient. Both the congruence sum
and its exact coprime mean use the same complete integer and physical N.
Short unit blocks and repeated occurrence values are retained. -/
theorem historical_native_mode_eq_rough_sharp {r : ℕ}
    (bs : Fin r → Block) (Z : ℝ) (ys xi : Fin r → ℝ) (rs : Fin r → Role)
    (i k : Fin r) (hik : i ≠ k)
    (hU : (1 : ℝ) < lower (bs i)) (hV : (1 : ℝ) < lower (bs k))
    (hZ : 0 ≤ Z) (hri : rs i = .one ∨ rs i = .logarithm)
    (hrk : rs k = .one ∨ rs k = .logarithm)
    (levelB : ℝ) (old fresh : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    MellinInsertion20261028.exactDiscrepancy (rectangle bs)
      (historicalModuli levelB old fresh N cap w z)
      (historicalRho old fresh N cap w z L) completeProduct N
      (fun ns => hbSlots Z ys rs ns * occurrenceMode (scales bs) ns xi) =
      historicalRoughSum levelB old fresh N cap w z L
        (sharpProfile (decide (rs i = .logarithm)) (lower (bs i)) (xi i))
        (sharpProfile (decide (rs k = .logarithm)) (lower (bs k)) (xi k))
        (lower (bs i)) (lower (bs k)) Z
        (shortSupport (fun a : ShortPositions i k => bs a.val))
        (shortSequence (fun a : ShortPositions i k => bs a.val) Z
          (fun a => ys a.val) (fun a => xi a.val) (fun a => rs a.val)) := by
  rw [same_rho_mode_eq_fibres bs Z ys xi rs i k hik N
    (historicalModuli levelB old fresh N cap w z)
    (historicalRho old fresh N cap w z L)]
  unfold historicalRoughSum
  simp_rw [sharp_fibre_identity bs Z ys xi rs i k hU hV hZ hri hrk]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro short hshort
  ring

/-- The original nonzero remaining source row supplies a pair, chosen
before xi, whose native historical rectangle mode is paid in the retained
long-frequency band. All fixed orders precede the physical-N threshold;
the historical policies and every actual row are quantified after it. -/
theorem eventually_actual_remaining_native_two_long_paid
    (accuracy frequencyOrder cutoffOrder : ℕ)
    {kappa kap0 zeta : ℝ} (hkappa : 0 < kappa)
    (hsmall : kappa ≤ zeta / 10000) (hzeta : zeta ≤ 1 / 20000)
    (htrim : kap0 < kappa / (4*(1+kappa))) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ), kap < 1 →
      ∀ (Bprofile cj : ℕ) (row : Row) (levelB : ℝ)
        (old fresh : List ℕ → Bool) (cap : ℕ) (w z L : ℝ),
      originalChart (actualLicence kap Bprofile N) N kap0 [cj] [row.factors.prod] ≠ 0 →
      row.order ∈ Finset.range 3 →
      row.factors ∈ factorTuples (2*(row.order+1)) row.factors.prod →
      assignedWeight (beforeHBCutoff cutoffOrder [cj]) (hbCutoff cj)
        (roles row.order) row.blocks row.factors ≠ 0 →
      (if (longBlocks (originalMediumHigh zeta [cj])
          ([row].flatMap Row.blocks)).length = 1 then (0 : ℂ)
        else typeIValue (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj])
          (fun rows => (listExtension (actualLicence kap Bprofile N) (originalProducts rows) : ℂ) *
            (eta (((originalProducts rows).prod : ℝ) / (N : ℝ)^(1-kap0)) : ℂ) *
            wordKernel (historicalModuli levelB old fresh N cap w z)
              (historicalRho old fresh N cap w z L) N (originalProducts rows)) [row]) ≠ 0 →
      let r := 2*(row.order+1)
      let bs := blockVector r row.blocks
      let X0 : ℝ := shortScale bs
      ∃ i k : Fin r, i ≠ k ∧
        longPositions (originalMediumHigh zeta [cj]) bs = {i,k} ∧
        (rowRoles row.order i = .one ∨ rowRoles row.order i = .logarithm) ∧
        (rowRoles row.order k = .one ∨ rowRoles row.order k = .logarithm) ∧
        ∀ xi : Fin r → ℝ,
          |xi i| ≤ (Real.log X0)^frequencyOrder →
          |xi k| ≤ (Real.log X0)^frequencyOrder →
          ‖MellinInsertion20261028.exactDiscrepancy (rectangle bs)
              (historicalModuli levelB old fresh N cap w z)
              (historicalRho old fresh N cap w z L) completeProduct N
              (fun ns => hbSlots (beforeHBCutoff cutoffOrder [cj]) (fun _ => hbCutoff cj)
                (rowRoles row.order) ns * occurrenceMode (scales bs) ns xi)‖ ≤
            X0/(Real.log X0)^accuracy := by
  have hzeta0 : 0 < zeta := by linarith only [hkappa, hsmall]
  have h400 : zeta ≤ 1 / 400 := hzeta.trans (by norm_num)
  have hkap0 : kap0 < 1 := by
    have H := manuscript_kappaZero_lt_quarter hkappa htrim
    linarith
  filter_upwards [eventually_actual_singleton_rough_sharp_paid
      accuracy frequencyOrder cutoffOrder hkappa hsmall h400 htrim,
    eventually_actual_remaining_tuple_dictionary hkap0 hzeta0 hzeta,
    eventually_actual_tuple_normalized_profile hkap0 hzeta0 hzeta,
    eventually_original_singleton_numeric_reserves hkap0 hzeta0 hzeta,
    eventually_actual_singleton_rough_comparison_gates cutoffOrder
      hkappa hsmall h400 htrim]
      with N hpaid hdict hnorm hnumeric hgates
  intro kap hkap Bprofile cj row levelB old fresh cap w z L hactive hj hfs hassigned hremaining
  let r := 2*(row.order+1)
  let bs := blockVector r row.blocks
  let ns := wordVector r row.factors
  let Q := historicalModuli levelB old fresh N cap w z
  let rho := historicalRho old fresh N cap w z L
  obtain ⟨_, _, hrect, _, _, i, k, hik, hpair, hri, hrk, _, _, hshort, _⟩ :=
    hdict kap Bprofile cutoffOrder cj row Q rho hactive hj hfs hassigned hremaining
  obtain ⟨_, _, _, hprofile, _, _, _⟩ :=
    hnorm kap hkap Bprofile cutoffOrder cj row.order row.factors.prod
      row.blocks row.factors Q rho hactive hfs hassigned
  have hscalar : scalarProfile kap Bprofile N cj kap0 (completeProduct ns) ≠ 0 := by
    simpa only [integerProfile] using hprofile
  obtain ⟨_, hhi, _, _, _⟩ := hnumeric kap Bprofile cj row.factors.prod hactive
  have hlong {a : Fin r} (ha : a ∈ ({i,k} : Finset (Fin r))) :
      (1 : ℝ) < lower (bs a) := by
    have hm : a ∈ longPositions (originalMediumHigh zeta [cj]) bs := by
      rw [hpair]
      exact ha
    exact hhi.trans_lt (Finset.mem_filter.mp hm).2
  have hU : (1 : ℝ) < lower (bs i) := hlong (by simp)
  have hV : (1 : ℝ) < lower (bs k) := hlong (by simp)
  have hZ : 0 ≤ beforeHBCutoff cutoffOrder [cj] :=
    zero_le_one.trans
      (hgates kap hkap Bprofile cj row.order bs ns i k hj hik hrect hscalar hshort).2.1
  refine ⟨i, k, hik, hpair, hri, hrk, ?_⟩
  intro xi hxi hxi'
  rw [historical_native_mode_eq_rough_sharp bs (beforeHBCutoff cutoffOrder [cj])
    (fun _ => hbCutoff cj) xi (rowRoles row.order) i k hik hU hV hZ hri hrk
    levelB old fresh N cap w z L]
  exact hpaid kap hkap Bprofile cj row.order bs ns i k hj hik hrect hscalar hshort hpair
    levelB old fresh cap w z L (xi i) (xi k)
    (decide (rowRoles row.order i = .logarithm))
    (decide (rowRoles row.order k = .logarithm)) xi hxi hxi'

end
end ImbalancedChen.P1OriginalSingletonNativeTwoLongPaid
