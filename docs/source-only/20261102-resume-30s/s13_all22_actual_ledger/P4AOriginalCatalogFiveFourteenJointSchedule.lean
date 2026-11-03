import ImbalancedChen.P4AOriginalCatalogFiveArchiveSchedule

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

Actual slot five and the fourteen-family slot sixteen now share the SAME
original fourth/fifth byte banks, e, q, chi=e/20 and omega. Both schedules
are stable under every later q above one threshold. Existing O/M/Q/R
source and endpoint proofs are consumed without redoing their integrals.

The two displayed errors are each eta, not one shared eta. This supplies
neither the other twenty entries nor the final full87/compiled policy.
In particular the buffered cap payment and the unbuffered fourteen tree
remain the two identified objects of R08/R06; no equality is invented.
-/

namespace ImbalancedChen.P4AOriginalCatalogFiveFourteenJointSchedule

noncomputable section
open MeasureTheory VariableEnvelope
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P4AOriginalCausalHistory
open P4AOriginalCommonArchiveSchedule
open P2OriginalSaving16TrimmedHistory P2OriginalFourteenWeightedTrim
open P4AOriginalArchiveFourteenPositivePresieve P5OriginalCommonPositivePresieve
open P4AActualSmallTailDensityCatalogue P4ACatalogFiveGlobalLossReduction
open P4AOriginalCatalogFiveArchiveSchedule

/-- Shared actual history, original slot-five lower endpoint, and the
original fourteen-cell lower endpoint as CURRENT minus NEW raw density.
The q threshold precedes N and is closed upward, so additional finite
archive/history resolutions can use the same original data. -/
theorem exists_actual_catalog_five_and_fourteen_schedule
    (eta : ℝ) (heta : 0 < eta) :
    ∃ n : ℕ, ∃ a0 : ℝ, 0 < a0 ∧ a0 ≤ 1 / 100 ∧
      ∀ a : ℝ, 0 < a → a ≤ a0 →
      ∃ e0 : ℝ, 0 < e0 ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧
      ∀ q : ℕ, q0 ≤ q →
        FourteenHistory (schedule e q a) (width n) ∧
        ∃ m : ℕ, ∃ buffer : ℚ, 0 < (buffer : ℝ) ∧
          (buffer : ℝ) ≤ 2 * (e : ℝ) ∧
          ∃ N0 : ℕ, 2 ≤ N0 ∧
          ∀ N cap : ℕ, N0 ≤ N → Even N →
            (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
            catalogFiveCapError (data e q a) m buffer a N < eta ∧
            (640339 / 15210735000 : ℝ) - eta <
              normalizedActualSaving (data e q a) N ∧
            (1222997719565324892497827 : ℝ) / (2 : ℝ)^96 - eta <
              normalize N
                (raw (policy6 (data e q a) (N : ℝ)) N cap 0
                    ((N : ℝ) ^ (19 / 96 : ℝ)) -
                  raw (fourteenPolicy e q a (N : ℝ)) N cap 0
                    ((N : ℝ) ^ (19 / 96 : ℝ))) := by
  obtain ⟨n, es, hes, hsource⟩ :=
    P2OriginalFourteenWholeFamilyLower.exists_actual_whole_family_lower_at_original_cutoff
      eta heta
  obtain ⟨eh, heh, hhistory⟩ :=
    P2OriginalSaving16CommonOldPolicy.exists_common_actual_parent_on_trim
      (width n) (width_pos n)
  obtain ⟨ac, hac, _hacrho, hcatalog⟩ :=
    exists_actual_original_catalog_five_schedule eta heta
  let a0 : ℝ := min ac (1 / 100)
  refine ⟨n, a0, lt_min hac (by norm_num), min_le_right _ _, ?_⟩
  intro a ha haa0
  have hacut : a ≤ ac := haa0.trans (min_le_left _ _)
  have ha100 : a ≤ (1 / 100 : ℝ) := haa0.trans (min_le_right _ _)
  obtain ⟨ec, hec, hcatalogE⟩ := hcatalog a ha hacut
  let e0 : ℝ := min es (min eh ec)
  refine ⟨e0, lt_min hes (lt_min heh hec), ?_⟩
  intro e he hee
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hees : (e : ℝ) < es := hee.trans_le (min_le_left _ _)
  have heeh : (e : ℝ) < eh :=
    hee.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heec : (e : ℝ) < ec :=
    hee.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hchi : (0 : ℝ) < (e : ℝ) / 20 := by positivity
  have hchie : (e : ℝ) / 20 ≤ (e : ℝ) / 10 := by linarith only [heR]
  obtain ⟨ms, Ns, hNs, hwhole⟩ := hsource e he hees ((e : ℝ) / 20) hchi hchie
  obtain ⟨mh, hparent⟩ := hhistory e he heeh ((e : ℝ) / 20) hchi hchie
  obtain ⟨qc, hqc, hcatalogQ⟩ := hcatalogE e he heec
  let q0 : ℕ := max qc (max ms mh + 1)
  refine ⟨q0, lt_of_lt_of_le hqc (le_max_left _ _), ?_⟩
  intro q hq
  have hqcq : qc ≤ q := (le_max_left _ _).trans hq
  have hqmesh : max ms mh + 1 ≤ q := (le_max_right _ _).trans hq
  have hms : ms ≤ (data e q a).m := by
    change ms ≤ P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q
    unfold P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh
    have := le_max_left ms mh
    omega
  have hmh : mh ≤ (data e q a).m := by
    change mh ≤ P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q
    unfold P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh
    have := le_max_right ms mh
    omega
  have hhist : FourteenHistory (schedule e q a) (width n) :=
    hparent (data e q a) rfl rfl hmh ha100
  obtain ⟨m, buffer, hb, hbe, _hpreserve, Nc, hNc, hpaid⟩ := hcatalogQ q hqcq
  refine ⟨hhist, m, buffer, hb, hbe, max Ns Nc,
    hNs.trans (le_max_left _ _), ?_⟩
  intro N cap hN hEven hcap
  have hNsN : Ns ≤ N := (le_max_left _ _).trans hN
  have hNcN : Nc ≤ N := (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := hNs.trans hNsN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hz : (N : ℝ) ^ mu ≤ (N : ℝ) ^ (19 / 96 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num [mu])
  have h16 := (hwhole (data e q a) rfl rfl hms ha100 N cap hNsN hEven
    ((N : ℝ) ^ (19 / 96 : ℝ)) hz hcap).2
  have h16endpoint :=
    (sub_le_sub_right
      P2OriginalSaving16OwnedIntegral.historical_endpoint_le_source_integral eta).trans_lt h16
  change (1222997719565324892497827 : ℝ) / (2 : ℝ)^96 - eta <
    normalize N (P2OriginalFourteenSignedParentLedger.charge N cap 0
      ((N : ℝ) ^ (19 / 96 : ℝ)) (lambda6 (data e q a) (N : ℝ))
      P4AOriginalAscending14Literal42.literalPattern (policy5 (data e q a) (N : ℝ))) at h16endpoint
  rw [← raw_current_sub_fourteen_eq_original_charge] at h16endpoint
  exact ⟨(hpaid N hNcN hEven).1, (hpaid N hNcN hEven).2, h16endpoint⟩

end
end ImbalancedChen.P4AOriginalCatalogFiveFourteenJointSchedule
