import ImbalancedChen.P4AOriginalCommonArchiveSchedule
import ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.

The historical fourteen-cell schedule is cofinal in its original grid400
parameter. This is a statement about the held original fourth/fifth and
eleven-cell sixth constructor, not its identification with the final 87
policy or with a signed compiler. The ordinary complement stays inside the
imported whole-family estimate. -/
namespace ImbalancedChen.P2Saving16CofinalArchiveSchedule
noncomputable section
open scoped Classical BigOperators
open MeasureTheory VariableEnvelope
open P4AOriginalCausalHistory P4AOriginalCommonArchiveSchedule
open P5OriginalCommonRefinedConstructor P5OriginalCommonFourthFallbackExcision
open P5OriginalCommonFourthSourceNavigation P1Pair12RetainedSignedSource
open P2OriginalFourthCapProducerInterface P2OriginalAscendingEighthCapDictionary
open P2OriginalSaving16FourteenPhysicalAtlas P2OriginalSaving16TrimmedHistory
open P2OriginalFourteenWeightedTrim
open P5OriginalFourthFifthSourceInputs P5OriginalCommonRefinedSource
open P4AOriginalArchiveFourteenPositivePresieve
open P5OriginalCommonPositivePresieve P4AOriginalVariableFifthPhysicalLedger

/-- The old source and history thresholds work for every sufficiently large
archive q, with one N0 uniform in those q. Arbitrary signed tests and the
original fourth/fifth occurrence carriers are unchanged. -/
theorem exists_cofinal_archive_and_whole_fourteen_schedule
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ, ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 11 / 64000 ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 N0 : ℕ, 0 < q0 ∧ 2 ≤ N0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ omega : ℝ, omega ≤ 1 / 100 →
        let s := fixedSchedule rows4 licensed4 e q omega
        FourteenHistory s (width n) ∧
        (∀ N cap : ℕ, N0 ≤ N → Even N → ∀ z : ℝ,
          (N : ℝ) ^ mu ≤ z → z ≤ (cap : ℝ) →
          |(∫ t in region, sourceDensity t) -
            (∫ t in trimmedRegion (width n), sourceDensity t)| < epsilon / 4 ∧
          (∫ t in region, sourceDensity t) - epsilon <
            P2OriginalFourteenSignedParentLedger.charge N cap 0 z
              (lambda6 s.data (N : ℝ)) P4AOriginalAscending14Literal42.literalPattern
              (policy5 s.data (N : ℝ)) * Real.log (N : ℝ) / singularSeries N) ∧
        (∀ N : ℝ, 1 ≤ N → ∀ h : ℕ → ℝ, ∀ T : Bool → List ℕ → ℝ,
          ∀ carrier : List ℕ,
          signedTest (common3 s.data N) h T [] true 1 carrier -
              signedTest (policy4 s.data N) h T [] true 1 carrier =
            signedTest (old3 s.data N) h T [] true 1 carrier -
              signedTest (original4 s.data N) h T [] true 1 carrier) ∧
        (∀ N : ℝ, 1 ≤ N → ∀ h : ℕ → ℝ, ∀ T : Bool → List ℕ → ℝ,
          ∀ carrier : List ℕ,
          signedTest (policy4 s.data N) h T [] true 1 carrier -
              signedTest (policy5 s.data N) h T [] true 1 carrier =
            signedTest (original4 s.data N) h T [] true 1 carrier -
              signedTest (original5 s.data N) h T [] true 1 carrier) := by
  obtain ⟨n, es, hes, hsource⟩ :=
    P2OriginalFourteenWholeFamilyLower.exists_actual_whole_family_lower_at_original_cutoff
      epsilon hepsilon
  obtain ⟨eh, heh, hhistory⟩ :=
    P2OriginalSaving16CommonOldPolicy.exists_common_actual_parent_on_trim (width n) (width_pos n)
  let e0 := min es (min eh (11 / 64000 : ℝ))
  have he0 : 0 < e0 := lt_min hes (lt_min heh (by norm_num))
  refine ⟨n, e0, he0, (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro e he hee
  have hchie : (e : ℝ) / 20 ≤ (e : ℝ) / 10 := by
    have heR : (0 : ℝ) < e := by exact_mod_cast he
    linarith
  have hees : (e : ℝ) < es := hee.trans_le (min_le_left _ _)
  have heeh : (e : ℝ) < eh :=
    hee.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨ms, N0, hN0, hwhole⟩ :=
    hsource e he hees ((e : ℝ) / 20) (by positivity) hchie
  obtain ⟨mh, hparent⟩ :=
    hhistory e he heeh ((e : ℝ) / 20) (by positivity) hchie
  refine ⟨max ms mh + 1, N0, by omega, hN0, ?_⟩
  intro q hq omega homega
  let s := fixedSchedule rows4 licensed4 e q omega
  have hq1 : 1 ≤ q := by omega
  have hsub : q - 1 + 1 = q := Nat.sub_add_cancel hq1
  have hres : q - 1 ≤ s.data.m := by
    change q - 1 ≤ P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q
    simpa only [hsub] using refinedMesh_above_resolution (q - 1)
  have hms : ms ≤ s.data.m := (by omega : ms ≤ q - 1).trans hres
  have hmh : mh ≤ s.data.m := (by omega : mh ≤ q - 1).trans hres
  have hg : FourthGeometry s.data := hgeometry
  change FourteenHistory s (width n) ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hparent s.data rfl rfl hmh homega
  · exact hwhole s.data rfl rfl hms homega
  · intro N hN h T carrier
    exact fourth_signed_gain_preserved s.data hg N hN h T carrier
  · intro N hN h T carrier
    exact archive_fifth_signed_gain_preserved s hg N hN h T carrier

/-- Specialization to the literal original fourth bank and the attached
full-modulus tests. The same cofinal q supplies the old history, the
ordinary fourteen-cell charge, and both signed fourth/fifth identities.
This does not identify this held tree with the final 87 tree or the
rectangular compiler coefficient. -/
theorem original_bank_cofinal_attached_sources (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ, ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 11 / 64000 ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 N0 : ℕ, 0 < q0 ∧ 2 ≤ N0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ omega : ℝ, omega ≤ 1 / 100 →
        FourteenHistory (schedule e q omega) (width n) ∧
        (∀ N cap : ℕ, N0 ≤ N → Even N → ∀ z : ℝ,
          (N : ℝ) ^ mu ≤ z → z ≤ (cap : ℝ) →
          |(∫ t in region, sourceDensity t) -
            (∫ t in trimmedRegion (width n), sourceDensity t)| < epsilon / 4 ∧
          (∫ t in region, sourceDensity t) - epsilon <
            P2OriginalFourteenSignedParentLedger.charge N cap 0 z
              (lambda6 (data e q omega) (N : ℝ))
              P4AOriginalAscending14Literal42.literalPattern
              (policy5 (data e q omega) (N : ℝ)) * Real.log (N : ℝ) / singularSeries N) ∧
        (∀ N cap : ℕ, 1 ≤ (N : ℝ) → ∀ w z L : ℝ, ∀ G : ℕ → ℝ,
          let d := data e q omega
          let T := attachedLeafTest N cap 1 w L G
          let carrier := roughPrimeUniverse N cap w z
          sourceChange d .fourth N cap w z L G =
            signedTest (original4 d (N : ℝ)) (fun _ => 1) T [] true 1 carrier -
              signedTest (old3 d (N : ℝ)) (fun _ => 1) T [] true 1 carrier ∧
          sourceChange d .fifth N cap w z L G =
            signedTest (original5 d (N : ℝ)) (fun _ => 1) T [] true 1 carrier -
              signedTest (original4 d (N : ℝ)) (fun _ => 1) T [] true 1 carrier) := by
  obtain ⟨n, e0, he0, he0bound, hs⟩ :=
    exists_cofinal_archive_and_whole_fourteen_schedule
      originalRows4 originalAdmission4 (fun r _hr hr => originalAdmission4_geometry r hr)
      epsilon hepsilon
  refine ⟨n, e0, he0, he0bound, ?_⟩
  intro e he hee
  obtain ⟨q0, N0, hq0, hN0, hq⟩ := hs e he hee
  refine ⟨q0, N0, hq0, hN0, ?_⟩
  intro q hqq omega homega
  obtain ⟨hhistory, hwhole, _hfourth, _hfifth⟩ := hq q hqq omega homega
  refine ⟨?_, ?_, ?_⟩
  · exact hhistory
  · exact hwhole
  · intro N cap hN w z L G
    exact original_fourth_fifth_attached_sources e q omega N cap hN w z L G

/-- Positive-w version of the same held historical schedule. The beta is
chosen once, before the archive q; the full fourth/fifth signed identities
are for arbitrary attached tests at that very q. The beta payment here is
the single eta/2 projection for the fourteen tree; it is not a compiler
payment and must not be booked again as a new saving. -/
theorem original_bank_cofinal_positive_w
    (nu eta betaMax : ℝ) (hnu : 0 < nu) (heta : 0 < eta) (hbetaMax : 0 < betaMax) :
    ∃ beta : ℝ, 0 < beta ∧ beta < 1 / 8 ∧ beta < betaMax ∧
      beta ^ 2 ≤ (19 / 96 : ℝ) / nu ∧
    ∃ n : ℕ, ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 11 / 64000 ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 N0 : ℕ, 0 < q0 ∧ 2 ≤ N0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ omega : ℝ, omega ≤ 1 / 100 →
        FourteenHistory (schedule e q omega) (width n) ∧
        (∀ N cap : ℕ, N0 ≤ N → Even N → (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
          let w := (N : ℝ) ^ (nu * beta ^ 2)
          let z := (N : ℝ) ^ (19 / 96 : ℝ)
          let L := (N : ℝ) ^ (nu * beta)
          1 < w ∧ w ≤ z ∧
          |(∫ t in region, sourceDensity t) -
            (∫ t in trimmedRegion (width n), sourceDensity t)| < eta / 8 ∧
          normalize N (physical (fourteenPolicy e q omega (N : ℝ)) N cap w z L) <
            normalize N (raw (policy6 (data e q omega) (N : ℝ)) N cap 0 z) -
              (∫ t in region, sourceDensity t) + eta) ∧
        (∀ N cap : ℕ, 1 ≤ (N : ℝ) → ∀ w z L : ℝ, ∀ G : ℕ → ℝ,
          let d := data e q omega
          let T := attachedLeafTest N cap 1 w L G
          let carrier := roughPrimeUniverse N cap w z
          sourceChange d .fourth N cap w z L G =
            signedTest (original4 d (N : ℝ)) (fun _ => 1) T [] true 1 carrier -
              signedTest (old3 d (N : ℝ)) (fun _ => 1) T [] true 1 carrier ∧
          sourceChange d .fifth N cap w z L G =
            signedTest (original5 d (N : ℝ)) (fun _ => 1) T [] true 1 carrier -
              signedTest (original4 d (N : ℝ)) (fun _ => 1) T [] true 1 carrier) := by
  have hr : 0 < (19 / 96 : ℝ) / nu := div_pos (by norm_num) hnu
  have hnr : nu * ((19 / 96 : ℝ) / nu) = (19 / 96 : ℝ) := by
    field_simp [hnu.ne'] <;> ring
  obtain ⟨beta, hb, hb8, hbMax, hbr, Nb, _hNb, hbeta⟩ :=
    exists_actualSmallRoughRho_density_le_full_reserve
      nu ((19 / 96 : ℝ) / nu) (eta / 2) betaMax hnu hr (half_pos heta) hbetaMax
  obtain ⟨n, e0, he0, he0bound, hschedule⟩ :=
    original_bank_cofinal_attached_sources (eta / 2) (half_pos heta)
  refine ⟨beta, hb, hb8, hbMax, hbr, n, e0, he0, he0bound, ?_⟩
  intro e he hee
  obtain ⟨q0, Ns, hq0, hNs, hs⟩ := hschedule e he hee
  refine ⟨q0, max Ns Nb, hq0, hNs.trans (le_max_left _ _), ?_⟩
  intro q hq omega homega
  obtain ⟨hhistory, hordinary, hattached⟩ := hs q hq omega homega
  refine ⟨hhistory, ?_, hattached⟩
  intro N cap hN hEven hcap
  have hN2 : 2 ≤ N := hNs.trans ((le_max_left _ _).trans hN)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hz : (N : ℝ) ^ mu ≤ (N : ℝ) ^ (19 / 96 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1.le (by norm_num [mu])
  have hbs := hbeta N ((le_max_right _ _).trans hN) hEven cap
    (by simpa only [hnr] using hcap) (fourteenPolicy e q omega (N : ℝ) false)
  dsimp only at hbs
  simp only [hnr] at hbs
  change physical (fourteenPolicy e q omega (N : ℝ)) N cap
      ((N : ℝ) ^ (nu * beta ^ 2)) ((N : ℝ) ^ (19 / 96 : ℝ)) ((N : ℝ) ^ (nu * beta)) ≤
    raw (fourteenPolicy e q omega (N : ℝ)) N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)) +
      (eta / 2) * singularSeries N / Real.log (N : ℝ) at hbs
  have hnorm := normalize_mono N hN2 hbs
  rw [normalize_add, normalize_reserve N hN2] at hnorm
  obtain ⟨htrim, hlower⟩ := hordinary N cap ((le_max_left _ _).trans hN) hEven
    ((N : ℝ) ^ (19 / 96 : ℝ)) hz hcap
  change (∫ t in region, sourceDensity t) - eta / 2 <
    normalize N (P2OriginalFourteenSignedParentLedger.charge N cap 0
      ((N : ℝ) ^ (19 / 96 : ℝ)) (lambda6 (data e q omega) (N : ℝ))
      P4AOriginalAscending14Literal42.literalPattern
      (policy5 (data e q omega) (N : ℝ))) at hlower
  rw [← raw_current_sub_fourteen_eq_original_charge, normalize_sub] at hlower
  dsimp only
  refine ⟨Real.one_lt_rpow hN1 (mul_pos hnu (sq_pos_of_pos hb)), ?_, ?_, ?_⟩
  · apply Real.rpow_le_rpow_of_exponent_le hN1.le
    simpa only [hnr] using mul_le_mul_of_nonneg_left hbr hnu.le
  · convert htrim using 1 <;> ring
  · linarith only [hnorm, hlower]

end
end ImbalancedChen.P2Saving16CofinalArchiveSchedule
