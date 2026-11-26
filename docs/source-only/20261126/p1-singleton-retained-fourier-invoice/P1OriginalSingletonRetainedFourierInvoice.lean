import ImbalancedChen.P1OriginalSingletonNativeTwoLongPaid
import ImbalancedChen.P1OriginalHistoricalSingletonFourier
import ImbalancedChen.P5NativeFullQHBAtlasTailPayment

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

For the actual remaining singleton row, the historical Fourier tail and
the retained native-mode integral now use the SAME normalized blockChart
and the SAME original singleton selected cutoff. The old log^72 L1 bound
is used directly; the frequency-cube volume is never charged.

The fixed cutoff exponent is bounded at dimension six before N. The
original complete-rectangle scale supplies the logarithmic band of the
already proved native theorem. No retained-mode, mass, tail, derivative,
Family or physical-family payment is an input to the public invoice.

The result deliberately displays the retained L1 bill and the separately
paid omitted-frequency bill. It does not identify remainingTypeIAtlas with
an outer rectangle sum, handle dead source rows for that selector, absorb
the seven outer inventory logarithms, or assert a final P1.5 estimate.
-/

namespace ImbalancedChen.P1OriginalSingletonRetainedFourierInvoice
noncomputable section
open Classical Filter MeasureTheory Set
open scoped BigOperators
open PrimeProducts
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.LiteralHeathBrownOccurrenceWords (factorTuples)
open P5Z.ActualRoughHeathBrownWords (roles)
open P5Z.ActualHBDyadicOccurrenceFamily (assignedWeight)
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
open P5Z.ActualLowerNormalizedAtlasOccurrence (rowRoles scalarProfile)
open P5Z.ActualLowerNormalizedBlockGeometry (rectangle scales Meets)
open P5Z.ActualHBPostModulusLogCutoff (hbSlots completeProduct paymentExponent selectedCutoff)
open P5Z.ActualAllRankOccurrenceFourierBridge (occurrenceMode)
open P5Z.AllRankCauchyCubeTail (outsideCube measurableSet_outsideCube)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P5Z.ActualLowerNormalizedPostModulusTail
  (countingScale countingScale_one_le cutoff)
open Part3.TwoLongActualHBShortMass (shortScale)
open P1OriginalHistoricalTwoLongP2 (historicalModuli historicalRho)
open P1OriginalHistoricalSingletonFourier
  (amplitude amplitude_integrable exists_amplitude_l1_budget originalAtom retainedAtom
    retained_eq_band exists_historical_tail_paid)
open P1OriginalSingletonNativeTwoLongPaid (eventually_actual_remaining_native_two_long_paid)
open P1OriginalSingletonLogNormalization (eventually_actual_tuple_normalized_profile)
open P1OriginalSingletonFixedRectangleScale (eventually_actual_singleton_fixed_rectangle_level)

def cutoffExponent (accuracy : ℕ) : ℕ := accuracy+72+paymentExponent 6 0+3
def frequencyOrder (accuracy : ℕ) : ℕ := cutoffExponent accuracy+1

/-- Elementary transport of the EXISTING selected singleton cutoff to
the complete local scale. The order is fixed before N, m, x and xi. -/
theorem eventually_selected_cutoff_twists (accuracy : ℕ)
    {kappa : ℝ} (hkappa : kappa ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ (x : ℝ), 1 < x → (N : ℝ) ≤ x^(1+kappa) →
      ∀ (m : ℕ) (xi : Fin m → ℝ),
      xi ∈ (outsideCube m (cutoff 6 N 6 accuracy))ᶜ →
      ∀ a, |xi a| ≤ (Real.log x)^frequencyOrder accuracy := by
  let E := cutoffExponent accuracy
  have tend := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    tend.eventually_ge_atTop (2*max (1+Real.log (896 : ℝ)) ((4 : ℝ)^E))]
      with N hN hbig
  intro x hx hNx m xi hxi a
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hx0 : 0 < Real.log x := Real.log_pos hx
  have hlogN : Real.log (N : ℝ) ≤ 2*Real.log x := by
    have h := Real.log_le_log hNp hNx
    rw [Real.log_rpow (zero_lt_one.trans hx)] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hx0.le)
  have hlarge : max (1+Real.log (896 : ℝ)) ((4 : ℝ)^E) ≤ Real.log x := by
    linarith
  have hconst := (le_max_left (1+Real.log (896 : ℝ)) ((4 : ℝ)^E)).trans hlarge
  have hfour := (le_max_right (1+Real.log (896 : ℝ)) ((4 : ℝ)^E)).trans hlarge
  have hL : 1 ≤ logScale (countingScale N) :=
    logScale_one_le (countingScale_one_le (by omega))
  have hlog : logScale (countingScale N) ≤ 4*Real.log x := by
    have heq : logScale (countingScale N) =
        1+Real.log (896 : ℝ)+Real.log (N : ℝ) := by
      unfold logScale countingScale
      rw [show 7*(128*(N : ℝ)) = (896 : ℝ)*(N : ℝ) by ring,
        Real.log_mul (by norm_num : (896 : ℝ) ≠ 0) hNp.ne']
      ring
    rw [heq]
    linarith
  have hband : |xi a| ≤ cutoff 6 N 6 accuracy :=
    le_of_not_gt (fun h => hxi ⟨a,h⟩)
  calc
    _ ≤ cutoff 6 N 6 accuracy := hband
    _ = logScale (countingScale N)^E := rfl
    _ ≤ (4*Real.log x)^E :=
      pow_le_pow_left₀ (zero_le_one.trans hL) hlog _
    _ ≤ (Real.log x)^(E+1) := by
      rw [mul_pow, pow_succ]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_right hfour (pow_nonneg hx0.le E)
    _ = _ := rfl

/-- The actual row has a retained L1 bill and a separate full-Q tail
bill at one selected cutoff. Neither bill is supplied as a premise.
The final line is the complete original normalized rectangle atom. -/
theorem exists_actual_remaining_fourier_invoice :
    ∃ Cband Ctail : ℝ, 0 ≤ Cband ∧ 0 ≤ Ctail ∧
      ∀ (accuracy tailAccuracy cutoffOrder : ℕ) {kappa kap0 zeta : ℝ},
      0 < kappa → kappa ≤ zeta/10000 → zeta ≤ 1/20000 →
      kap0 < kappa/(4*(1+kappa)) →
      ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ), kap < 1 →
      ∀ (cj : ℕ) (row : Row) (levelB : ℝ)
        (old fresh : List ℕ → Bool) (cap : ℕ) (w z L : ℝ),
      originalChart (actualLicence kap 6 N) N kap0 [cj] [row.factors.prod] ≠ 0 →
      row.order ∈ Finset.range 3 →
      row.factors ∈ factorTuples (2*(row.order+1)) row.factors.prod →
      assignedWeight (beforeHBCutoff cutoffOrder [cj]) (hbCutoff cj)
        (roles row.order) row.blocks row.factors ≠ 0 →
      (if (longBlocks (originalMediumHigh zeta [cj])
          ([row].flatMap Row.blocks)).length = 1 then (0 : ℂ)
        else typeIValue (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj])
          (fun rows => (listExtension (actualLicence kap 6 N) (originalProducts rows) : ℂ) *
            (eta (((originalProducts rows).prod : ℝ)/(N : ℝ)^(1-kap0)) : ℂ) *
            wordKernel (historicalModuli levelB old fresh N cap w z)
              (historicalRho old fresh N cap w z L) N (originalProducts rows)) [row]) ≠ 0 →
      let r := 2*(row.order+1)
      let bs := blockVector r row.blocks
      let X0 : ℝ := shortScale bs
      let Z := beforeHBCutoff cutoffOrder [cj]
      let ys := fun _ : Fin r => hbCutoff cj
      let rs := rowRoles row.order
      let original := originalAtom kap N cj kap0 bs Z ys rs levelB old fresh cap w z L
      let retained := retainedAtom kap N cj kap0 bs Z ys rs levelB old fresh cap w z L
        (cutoff 6 N 6 tailAccuracy)
      let bandBill := (Cband*Real.log ((N : ℝ)+2)^72/2^r)*(X0/(Real.log X0)^accuracy)
      let tailBill := Ctail*(N : ℝ)/logScale (countingScale N)^(tailAccuracy+3)
      ‖retained‖ ≤ bandBill ∧ ‖original-retained‖ ≤ tailBill ∧
        ‖original‖ ≤ bandBill+tailBill := by
  obtain ⟨CB, hCB, hL1⟩ := exists_amplitude_l1_budget
  obtain ⟨CT, hCT, htail⟩ := exists_historical_tail_paid
  refine ⟨CB, CT, hCB, hCT, ?_⟩
  intro accuracy tailAccuracy cutoffOrder kappa kap0 zeta hkappa hsmall hzeta htrim
  have hk1 : kappa ≤ 1 := by linarith
  have hzeta0 : 0 < zeta := by linarith only [hkappa, hsmall]
  have h400 : zeta ≤ 1/400 := hzeta.trans (by norm_num)
  have hkap0 : kap0 < 1 := by
    have h := manuscript_kappaZero_lt_quarter hkappa htrim
    linarith
  filter_upwards [eventually_actual_remaining_native_two_long_paid
      accuracy (frequencyOrder tailAccuracy) cutoffOrder hkappa hsmall hzeta htrim,
    eventually_selected_cutoff_twists tailAccuracy hk1,
    eventually_actual_tuple_normalized_profile hkap0 hzeta0 hzeta,
    eventually_actual_singleton_fixed_rectangle_level hkappa hsmall h400 htrim,
    eventually_ge_atTop (1 : ℕ)] with N hnative htwists hnorm hrectangle hN
  intro kap hkap cj row levelB old fresh cap w z L hactive hj hfs hassigned hremaining
  let r := 2*(row.order+1)
  let bs := blockVector r row.blocks
  let ns := wordVector r row.factors
  let X0 : ℝ := shortScale bs
  let Z := beforeHBCutoff cutoffOrder [cj]
  let ys := fun _ : Fin r => hbCutoff cj
  let rs := rowRoles row.order
  let Q := historicalModuli levelB old fresh N cap w z
  let rho := historicalRho old fresh N cap w z L
  let H := cutoff 6 N 6 tailAccuracy
  let E := X0/(Real.log X0)^accuracy
  let a := amplitude kap N cj kap0 bs
  let mode := fun xi : Fin r → ℝ =>
    MellinInsertion20261028.exactDiscrepancy (rectangle bs) Q rho completeProduct N
      (fun n => hbSlots Z ys rs n * occurrenceMode (scales bs) n xi)
  let original := originalAtom kap N cj kap0 bs Z ys rs levelB old fresh cap w z L
  let retained := retainedAtom kap N cj kap0 bs Z ys rs levelB old fresh cap w z L H
  let bandBill := (CB*Real.log ((N : ℝ)+2)^72/2^r)*E
  let tailBill := CT*(N : ℝ)/logScale (countingScale N)^(tailAccuracy+3)
  have hNpos : 0 < N := by omega
  have hr : r ≤ 6 := by have hj' := Finset.mem_range.mp hj; dsimp only [r]; omega
  obtain ⟨i, k, hik, _, _, _, hmode⟩ :=
    hnative kap hkap 6 cj row levelB old fresh cap w z L hactive hj hfs hassigned hremaining
  obtain ⟨hrect, _, _, hprofile, _, _, _⟩ :=
    hnorm kap hkap 6 cutoffOrder cj row.order row.factors.prod row.blocks row.factors
      Q rho hactive hfs hassigned
  have hscalar : scalarProfile kap 6 N cj kap0 (completeProduct ns) ≠ 0 := by
    simpa only [P5Z.ActualLowerNormalizedAtlasOccurrence.integerProfile] using hprofile
  have hMeet : Meets kap 6 N cj kap0 bs := ⟨ns, hrect, hprofile⟩
  obtain ⟨_, _, _, _, _, hx, _, hNx, _, _, _⟩ :=
    hrectangle kap hkap 6 cj row.order bs ns i k hj hik hrect hscalar
  have hE : 0 ≤ E := div_nonneg (zero_lt_one.trans hx).le
    (pow_nonneg (Real.log_pos hx).le _)
  have ha := amplitude_integrable kap N cj kap0 bs
  have hmodeBand (xi : Fin r → ℝ) (hxi : xi ∈ (outsideCube r H)ᶜ) : ‖mode xi‖ ≤ E :=
    hmode xi (htwists X0 hx hNx r xi hxi i) (htwists X0 hx hNx r xi hxi k)
  have hretained : ‖retained‖ ≤ bandBill := by
    rw [show retained = _ from retained_eq_band kap N cj kap0 bs Z ys rs
      levelB old fresh cap w z L H]
    change ‖∫ xi in (outsideCube r H)ᶜ, a xi*mode xi‖ ≤ bandBill
    calc
      _ ≤ ∫ xi in (outsideCube r H)ᶜ, ‖a xi‖*E := by
        apply norm_integral_le_of_norm_le (ha.norm.mul_const E).integrableOn
        filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_outsideCube r H).compl]
          with xi hxi
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hmodeBand xi hxi) (norm_nonneg _)
      _ = (∫ xi in (outsideCube r H)ᶜ, ‖a xi‖)*E := integral_mul_const E _
      _ ≤ (∫ xi, ‖a xi‖)*E := mul_le_mul_of_nonneg_right
        (setIntegral_le_integral ha.norm (Eventually.of_forall (fun xi => norm_nonneg (a xi)))) hE
      _ ≤ bandBill := mul_le_mul_of_nonneg_right (hL1 kap N cj kap0 r bs hNpos hr) hE
  have herror : ‖original-retained‖ ≤ tailBill :=
    htail kap N cj kap0 r bs hkap hNpos hr hMeet Z ys rs
      levelB old fresh cap w z L tailAccuracy
  refine ⟨hretained, herror, ?_⟩
  calc
    _ ≤ ‖original-retained‖+‖retained‖ := by
      simpa only [sub_add_cancel] using norm_add_le (original-retained) retained
    _ ≤ tailBill+bandBill := add_le_add herror hretained
    _ = _ := add_comm _ _

end
end ImbalancedChen.P1OriginalSingletonRetainedFourierInvoice
