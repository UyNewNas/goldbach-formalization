import ImbalancedChen.P4AOriginalFull87RawChronology
import ImbalancedChen.P4AActualJointDensitySchedule

/-! Two endpoint payments on the actual licensed raw chronology. The full
old fifth archive converges at fixed data on the same e,q,a as the
above-mu second fallback. Its arithmetic error and the original fourth
mean use the remaining half of the requested local tolerance. -/

namespace ImbalancedChen.P4AOriginalFull87SlotTwoFive

noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P4AOriginalFull87RawChronology
open P5OriginalCommonRefinedConstructor (old3)
open P5OriginalCommonPositivePresieve (normalize)
open P5OriginalCommonFourthSourceLedger
  (originalFourthSaving originalFourthIntegral eventually_original_fourth_error)
open P5OriginalArchiveCommonRawMean (eventually_actual_common_rawDifference_error)
open P5OriginalFourthFifthSourceInputs (originalRows4 originalAdmission4)
open P4ACatalogFiveGlobalLossReduction (normalizedActualSaving)
open P4AOriginalCatalogFiveArchiveSchedule (original_slot_five_deficit_le_cap_error)
open P4AActualJointDensitySchedule (exists_joint_original_density_schedule)
open OriginalThirdFiniteReserveSourceOnly (originalDensityReserve)

theorem original_old_fifth_slot :
    currentUpperEighteenGains 1 = (3037921066812732539869 / 302231454903657293676544 : ℝ) := by
  norm_num [currentUpperEighteenGains]

/-- Expression on the right of the partial estimate, built from the
historical third coefficient, its third fallback, the original fourth
integral, two original slots and three independently generated frontiers. -/
def sourceBound (trim : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) : ℝ :=
  let d := archiveData e q a
  normalize N (rawRoot (old3 d (N : ℝ)) N) + normalize N (thirdIncrement e q a N) -
    originalFourthIntegral d - currentUpperEighteenGains 1 - currentUpperEighteenGains 4 +
    normalize N (fifthAdjustment n e q a N + sixthIncrement n e q a N +
      eighthIncrement trim n e q a N)

private theorem covering_target :
    ∀ᶠ N : ℕ in P1OriginalFifthMovingScaleLimit.evenTargets,
      cutoff N ≤ (N : ℝ) := by
  filter_upwards [(eventually_ge_atTop (1 : ℕ)).filter_mono
    (show P1OriginalFifthMovingScaleLimit.evenTargets ≤ atTop from inf_le_left)] with N hN
  have h : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  simpa only [cutoff, Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le h (show (19 / 96 : ℝ) ≤ 1 by norm_num)

/-- The original fourth count-to-integral conversion, the literal old
fifth slot, and the second fallback saving share one total tolerance.
The old fifth uses its archive reserve only once. The later strict
eventual inequality holds for the licensed tree with its actual
requantized fifth, sixth and eighth increments in sourceBound. -/
theorem exists_paid_original_sources (eta eMax : ℝ) (heta : 0 < eta) (heMax : 0 < eMax) :
    ∃ a0 : ℝ, 0 < a0 ∧ a0 ≤ 1 / 800 ∧ a0 < (19 / 96 : ℝ) ∧
      ∀ a : ℝ, 0 < a → a ≤ a0 →
      ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ eMax ∧ e0 ≤ 3 / 51200 ∧
      ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < e0 →
      ∀ qMin mMin : ℕ, ∃ q0 : ℕ, 0 < q0 ∧ qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q →
        let d := archiveData e q a
        mMin ≤ d.m ∧
        (P4ASameRhoCompact.originalOrdinaryRoot + actualExtendedThirdFiniteFunctional (e : ℝ) d.m ≤
          (∑ i, currentUpperEighteenPositive i) + originalDensityReserve / 4) ∧
        ∀ trim : ℝ, ∀ n : ℕ, ∀ᶠ N : ℕ in atTop, Even N →
          (originalFourthIntegral d + currentUpperEighteenGains 1 + currentUpperEighteenGains 4 -
              eta < normalize N (originalFourthSaving d N N (cutoff N)) +
                fifthSaving e q a N + normalizedActualSaving d N) ∧
          normalize N (rawRoot (licensed trim n e q a (N : ℝ)) N) <
            sourceBound trim n e q a N + eta := by
  have hhalf := half_pos heta
  have hquarter := half_pos hhalf
  obtain ⟨a0, ha0, ha0max, ha0rho, hA⟩ :=
    exists_joint_original_density_schedule (eta / 2) eMax hhalf heMax
  refine ⟨a0, ha0, ha0max, ha0rho, ?_⟩
  intro a ha haa0
  have harho := haa0.trans_lt ha0rho
  obtain ⟨e0, he0, he0max, he0bound, hE⟩ := hA a ha haa0
  refine ⟨e0, he0, he0max, he0bound, ?_⟩
  intro e he hee qMin mMin
  have heQ : (0 : ℚ) ≤ e := by exact_mod_cast he.le
  have hemax : (e : ℝ) ≤ 11 / 64000 := by linarith only [hee, he0bound]
  obtain ⟨q0, hq0, hqMin, _hgate, hQ⟩ := hE e he hee qMin mMin
  refine ⟨q0, hq0, hqMin, ?_⟩
  intro q hq
  let d := archiveData e q a
  obtain ⟨hmMin, _hstep, hrough, _hthird, hpositive, _hreserve, _hliteral, _hsafe,
      m, buffer, _hb, _hbe, _hgains, Nc, hNc, hcost⟩ := hQ q hq
  refine ⟨hmMin, hpositive, ?_⟩
  intro trim n
  have h4 := eventually_original_fourth_error d heQ ha harho hrough
    (fun N : ℕ => N) covering_target ((eta / 2) / 2) hquarter
  have h5 := eventually_actual_common_rawDifference_error originalRows4 originalAdmission4
    e heQ q ((e : ℝ) / 20) a ha harho (fun N : ℕ => N)
    covering_target ((eta / 2) / 2) hquarter
  rw [Filter.eventually_inf_principal] at h4 h5
  have hfloor := P5OriginalFullFifthFloorIntegral.original_fifth_endpoint_sub_reserve
    e heQ q ((e : ℝ) / 20) a ha harho
  filter_upwards [h4, h5, eventually_ge_atTop Nc] with N h4N h5N hN
  intro hEven
  have hN2 := hNc.trans hN
  have hpos : 0 < N ∧ Even N := ⟨by omega, hEven⟩
  have hNR : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hfour := (abs_lt.mp (h4N hpos)).1
  have hfifth := (abs_lt.mp (h5N hpos)).1
  have hcat := original_slot_five_deficit_le_cap_error d m (buffer : ℝ) a N
  have htotal := (hcost N hN hEven).2.2
  have hnumeric : originalFourthIntegral d + currentUpperEighteenGains 1 +
      currentUpperEighteenGains 4 - eta <
      normalize N (originalFourthSaving d N N (cutoff N)) +
        fifthSaving e q a N + normalizedActualSaving d N := by
    change -((eta / 2) / 2) <
      fifthSaving e q a N -
        P5OriginalFifthArchiveActualMean.archiveFifthIntegral
          originalRows4 originalAdmission4 e q ((e : ℝ) / 20) a at hfifth
    change -((eta / 2) / 2) < normalize N (originalFourthSaving d N N (cutoff N)) -
      originalFourthIntegral d at hfour
    change P4AActualSmallTailDensityCatalogue.catalogFiveCapError d m (buffer : ℝ) a N +
      _ < eta / 2 at htotal
    rw [original_old_fifth_slot,
      P4AAll22OriginalKLedger20261024zSourceOnly.fifth_saving_slot_is_coarse_endpoint]
    linarith only [hfour, hfifth, hfloor, hcat, htotal]
  refine ⟨hnumeric, ?_⟩
  rw [normalized_licensed_raw_chronology trim n e q a N he.le hemax hNR]
  unfold sourceBound
  change _ < normalize N (rawRoot (old3 d (N : ℝ)) N) + _ - _ - _ - _ + _ + eta
  linarith only [hnumeric]

end
end ImbalancedChen.P4AOriginalFull87SlotTwoFive
