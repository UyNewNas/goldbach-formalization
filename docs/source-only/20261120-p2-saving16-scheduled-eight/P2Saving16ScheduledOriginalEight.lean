import ImbalancedChen.P2Saving16OriginalEightNegativeFibre
import ImbalancedChen.P2OriginalFourteenRetainedTupleOwnership

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
The ordinary source cutoff N^mu and the compiler cutoff N^(19/96) are
kept distinct. The original policy is tested on the same eight ordered
primes, and the full rough modulus may have a nonempty tail. -/
namespace ImbalancedChen.P2Saving16ScheduledOriginalEight
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P4AUpperTaggedFrozenAdmissionCatalogue P2CanonicalWallFullResidualPayment
open P2Saving16ActualCompilerDifference P2Saving16SignedCorrectionFamilies
open P2Saving16OriginalEightNegativeFibre P2Saving16SameRhoDistributionFrontier
open P2Saving16FirstRowCompilerFibre
open P2OriginalFourteenRetainedTupleOwnership
open P2OriginalSaving16TrimmedHistory
open P2OriginalSaving16FourteenPhysicalAtlas
open P5OriginalCommonRefinedConstructor
open P4AOriginalFull87StrictActionTrim (trim)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P2OriginalSaving16Full87SourceBinding (sourceCell)
open P4AOriginalOrderedThirdActualCoefficient (coefficient keep)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalR17EighthParent (orderedSixth)
open P4AOriginalFull87UnionHistory (sixthPolicy policy)
open P4AOriginalFull87CompiledCounting (moduli)

/-- The original tuple coordinates and the actual eighth ancestor use the
same entries and order, including at each endpoint. -/
theorem original_tuple_log_eq_actual_eight (N d : ℕ)
    (hrank : 8 ≤ d.primeFactorsList.length) :
    actualPrimeTupleLog N (canonicalPrefix 8 d) = firstEightCoordinates N d := by
  rw [← history_log N (canonicalPrefix 8 d), original_history_eq_actual_eighth d hrank]
  rfl

/-- For an actual modulus in the rough universe, the original trim gives
the exact lower-closed, upper-open original prime box. -/
theorem actual_eight_in_original_box (delta : ℝ) (hdelta : 0 < delta)
    (N cap : ℕ) (w z : ℝ) {d : ℕ} (hN : 1 < N)
    (hrank : 8 ≤ d.primeFactorsList.length) (hd : d ∈ universe N cap w z)
    (ht : firstEightCoordinates N d ∈ trimmedRegion delta) :
    canonicalPrefix 8 d ∈ actualPrimeBoxTuples N
      (fun _ : Fin 8 => P2OriginalSaving16FourteenPhysicalAtlas.cutoff)
      (fun _ => VariableEnvelope.mu) := by
  let p := canonicalPrefix 8 d
  have hs := (P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N cap w z hd).1
  have hsub : List.ofFn p <+ roughPrimeUniverse N cap w z := by
    dsimp only [p]
    rw [canonicalPrefix_ofFn hrank]
    exact (List.take_sublist 8 d.primeFactorsList.reverse).trans hs
  have hmembers (i : Fin 8) : p i ∈ roughPrimeUniverse N cap w z :=
    hsub.subset (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hprime (i : Fin 8) : Nat.Prime (p i) ∧ ¬p i ∣ N :=
    ⟨mem_roughPrimeUniverse_prime (hmembers i), mem_roughPrimeUniverse_not_dvd (hmembers i)⟩
  have ht' : actualPrimeTupleLog N p ∈ trimmedRegion delta := by
    simpa only [p, original_tuple_log_eq_actual_eight N d hrank] using ht
  obtain ⟨c, hc⟩ := mem_iUnion.mp (trimmedRegion_subset_region delta hdelta ht')
  have hb := sourceRows_coordinate_bounds c (actualPrimeTupleLog N p) hc
  apply (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
  refine ⟨hprime, mem_logPrimeBox.mpr ?_⟩
  intro i
  exact ⟨(hb i).1.le, (hb i).2⟩

/-- With the same historical decisions, admission transfers from the
original smaller cutoff to the compiler's actual cutoff. The positive-w
full modulus provides the larger carrier; no assumption is made about
its primes after the first eight. -/
theorem original_admission_from_small_box
    (data : OriginalData) (N : ℕ) (w z : ℝ) {d : ℕ}
    (hrank : 8 ≤ d.primeFactorsList.length) (hd : d ∈ universe N N w z)
    (hp : canonicalPrefix 8 d ∈ admitted data N N ((N : ℝ)^VariableEnvelope.mu)) :
    canonicalPrefix 8 d ∈ admitted data N N z := by
  let p := canonicalPrefix 8 d
  have hv := (mem_firstExitAdmittedTuples_iff 8 (policy6 data (N : ℝ))
    (roughPrimeUniverse N N 0 ((N : ℝ)^VariableEnvelope.mu)) p).mp hp
  have hs := (P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N N w z hd).1
  have hsub : List.ofFn p <+ roughPrimeUniverse N N w z := by
    dsimp only [p]
    rw [canonicalPrefix_ofFn hrank]
    exact (List.take_sublist 8 d.primeFactorsList.reverse).trans hs
  have hanti : StrictAnti p := List.pairwise_ofFn.mp
    ((roughPrimeUniverse_pairwise_gt N N w z).sublist hsub)
  have hmembers (i : Fin 8) : p i ∈ roughPrimeUniverse N N 0 z := by
    have hi := mem_roughPrimeUniverse.mp (hsub.subset (List.mem_ofFn.mpr ⟨i, rfl⟩))
    exact mem_roughPrimeUniverse.mpr ⟨hi.1, hi.2.1, hi.2.2.1,
      Nat.cast_nonneg _, hi.2.2.2.2⟩
  change p ∈ firstExitAdmittedTuples 8 (policy6 data (N : ℝ)) (roughPrimeUniverse N N 0 z)
  exact (mem_firstExitAdmittedTuples_iff_of_decreasing 8 (policy6 data (N : ℝ)) _
    (roughPrimeUniverse_pairwise_gt N N 0 z) p).mpr ⟨hanti, hmembers, hv.2⟩

/-- The original common schedule supplies the formerly assumed ordinary
admission uniformly before N, on the intersection of the two stated trims.
The common bank is the exact full87 bank. -/
theorem scheduled_negative_inner_original_admission
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∀ chi : ℝ, 0 < chi → chi ≤ (e : ℝ) / 10 →
      ∃ m0 : ℕ, ∀ (r n q : ℕ) (a nu beta tau : ℝ),
        let bank := P4AOriginalFull87UnionHistory.bank e q a
        bank.e = e → bank.chi = chi → m0 ≤ bank.m → bank.omega ≤ 1 / 100 →
        ∀ N : ℕ, 1 < N → ∀ {d : ℕ},
          8 ≤ d.primeFactorsList.length →
          firstEightCoordinates N d ∈ trimmedRegion delta →
          (ArithmeticFunction.moebius d : ℝ) < 0 →
          changed (keep r n e q a (nu * beta^2) N) (fun _ => []) N N
            ((N : ℝ)^(nu * beta^2)) (cutoff N) tau d →
          canonicalPrefix 8 d ∈ admitted bank N N (cutoff N) := by
  obtain ⟨e0, he0, hschedule⟩ := exists_retained_tuple_ownership delta hdelta
  refine ⟨e0, he0, ?_⟩
  intro e he he0e chi hchi hchie
  obtain ⟨m0, hm0⟩ := hschedule e he he0e chi hchi hchie
  refine ⟨m0, ?_⟩
  intro r n q a nu beta tau
  dsimp only
  intro hde hdc hdm homega N hN d hrank ht hneg hchanged
  let bank := P4AOriginalFull87UnionHistory.bank e q a
  have hraw : d ∈ rawSupport (keep r n e q a (nu * beta^2) N) N N
      ((N : ℝ)^(nu * beta^2)) (cutoff N) :=
    (negative_inner_actual_witness (keep r n e q a (nu * beta^2) N)
      (fun _ => []) N N ((N : ℝ)^(nu * beta^2)) (cutoff N) tau hneg hchanged).1
  have hu := rawSupport_subset_universe (keep r n e q a (nu * beta^2) N)
    N N ((N : ℝ)^(nu * beta^2)) (cutoff N) hraw
  have hbox := actual_eight_in_original_box delta hdelta N N
    ((N : ℝ)^(nu * beta^2)) (cutoff N) hN hrank hu ht
  have hNreal : (1 : ℝ) < N := by exact_mod_cast hN
  have hcap : (N : ℝ)^VariableEnvelope.mu ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hNreal.le (by norm_num [VariableEnvelope.mu] : VariableEnvelope.mu ≤ 1))
  have ht' : actualPrimeTupleLog N (canonicalPrefix 8 d) ∈ trimmedRegion delta := by
    simpa only [original_tuple_log_eq_actual_eight N d hrank] using ht
  have hp := (hm0 bank hde hdc hdm homega N N hN hcap _ hbox ht').1
  exact original_admission_from_small_box bank N _ _ hrank hu hp


/-- The same scheduled original occurrence is fed to the existing
same-Q negative-inner consumer. Both trims are explicit: their uniform
compatibility is a further geometric obligation. -/
theorem scheduled_negative_inner_same_Q_summand
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∀ chi : ℝ, 0 < chi → chi ≤ (e : ℝ) / 10 →
      ∃ m0 : ℕ, ∀ (r n q : ℕ) (a nu beta tau : ℝ),
        let bank := P4AOriginalFull87UnionHistory.bank e q a
        bank.e = e → bank.chi = chi → m0 ≤ bank.m → bank.omega ≤ 1 / 100 →
        nu * beta^2 ≤ a → HistoryOnTrim r e q a →
        ∀ (N : ℕ), 1 < N → ∀ (i : Fin 14) {d s : ℕ},
          8 ≤ d.primeFactorsList.length →
          firstEightCoordinates N d ∈ trimmedRegion delta →
          firstEightCoordinates N d ∈ trim (sourceCell i) (width r) →
          s ∈ actualSmallRosserSupport N N ((N : ℝ)^(nu * beta^2)) →
          (ArithmeticFunction.moebius d : ℝ) < 0 →
          changed (keep r n e q a (nu * beta^2) N) (fun _ => []) N N
            ((N : ℝ)^(nu * beta^2)) (cutoff N) tau d → ∀ b T : ℝ,
          let omega := nu * beta^2
          let w := (N : ℝ)^omega
          let z := cutoff N
          let L := (N : ℝ)^(nu*beta)
          let f := keep r n e q a omega N
          let word := history (canonicalPrefix 8 d)
          let G := realHalfProductDiscrepancy b N T
          canonicalPrefix 8 d ∈ firstExitAdmittedTuples 8 (policy6 bank (N : ℝ))
            (roughPrimeUniverse N N w z) ∧
          primeHistoryTuple 4 (rosserAncestor 4 word) ∈
            firstExitAdmittedTuples 4 (oddFirstExitPolicy f) (roughPrimeUniverse N N w z) ∧
          P4AOriginalFull87DataPolicy.level4Exponent n bank N (rosserAncestor 4 word) ≤
            P4AOriginalR17EighthParent.parent n e q a omega N word ∧
          s*d ∈ moduli N w ∧
          coefficient r n e q a omega N tau L (s*d) * G (s*d) =
            (actualSmallRoughRho (orderedSixth n e q a omega N false) N N w z L (s*d) -
              (actualSmallRoughRho (sixthPolicy n e q a N false) N N w z L (s*d) -
                actualSmallRoughRho (policy (width r) n e q a N false) N N w z L (s*d)) +
              actualSmallRosserMinus N N w L s) * G (s*d) := by
  obtain ⟨e0, he0, h⟩ := scheduled_negative_inner_original_admission delta hdelta
  refine ⟨e0, he0, ?_⟩
  intro e he he0e chi hchi hchie
  obtain ⟨m0, hm0⟩ := h e he he0e chi hchi hchie
  refine ⟨m0, ?_⟩
  intro r n q a nu beta tau
  dsimp only
  intro hde hdc hdm homega hcut hh N hN i d s hrank htold htfull hs hneg hchanged b T
  have hp := hm0 r n q a nu beta tau hde hdc hdm homega N hN hrank htold hneg hchanged
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  exact original_eight_negative_summand_on_same_error r n e q a nu beta tau
    he.le hcut hh N hNr i hrank hp htfull hs hneg hchanged b T

end
end ImbalancedChen.P2Saving16ScheduledOriginalEight
