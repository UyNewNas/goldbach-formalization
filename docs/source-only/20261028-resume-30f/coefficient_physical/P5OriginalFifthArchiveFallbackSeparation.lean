import ImbalancedChen.P5OriginalCommonRefinedArchiveHull
import ImbalancedChen.P5OriginalCommonRefinedFifthGainDefect

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The licensed ORIGINAL fifth archive lives strictly below mu in its first
coordinate: its grid is 400 and its first lower key is at most 77. Both
corrected second/third fallback regions require the SAME first coordinate
strictly above mu. Consequently the shared fourth seed is unchanged on
every actual eligible archive row. Outside the eligible archive the fifth
maximum is its own current parent on BOTH policies. Thus the local fifth
increment is unchanged everywhere, even though the policies and their
third/fourth parents are NOT globally equal.

This is a source-specific separation proof, not a manuscript defect or a
claim that arbitrary OriginalData has zero changed-parent gain loss. The
whole adopted fourth bank, other six/eight-rank sources and common finite
compact approximation are not supplied here.
-/
namespace ImbalancedChen.P5OriginalFifthArchiveFallbackSeparation
noncomputable section
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFourthContinuation hiding exponent4
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedSeedHull
open P5OriginalCommonRefinedFifthGainDefect
open P5OriginalAboveMuThirdLowerPhysicalCoefficient
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthCommonPolicyInputs

theorem original_box_first_lt_mu (raw : FifthWireRow)
    (hg : raw.grid = 400) (hk : raw.lo 0 ≤ 77)
    (t : Fin 5 → ℝ) (ht : t ∈ raw.originalBox) : t 0 < VariableEnvelope.mu := by
  have hkey : (raw.lo 0 : ℝ) ≤ 77 := by exact_mod_cast hk
  have hh : t 0 < ((raw.lo 0 : ℝ) + 1) / 400 := by
    simpa [FifthWireRow.upper, hg] using (ht 0).2
  have hcut : t 0 < (39 / 200 : ℝ) := by linarith
  exact hcut.trans (by norm_num [VariableEnvelope.mu])

theorem ancestor_fallback_guards_false (N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 5)
    (hx : primeHistoryLogCoordinates N 5 pre 0 ≤ VariableEnvelope.mu) :
    ¬thirdGuard N (rosserAncestor 4 pre) ∧ ¬secondGuard N (rosserAncestor 4 pre) := by
  have h3 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 5) (0 : Fin 3)
  have h2 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 2 ≤ 5) (0 : Fin 2)
  constructor
  · intro hg
    have hh := hg.1
    change VariableEnvelope.mu <
      primeHistoryLogCoordinates N 3 (rosserAncestor 3 (rosserAncestor 4 pre)) 0 at hh
    rw [rosserAncestor_nested 3 4 (by decide)] at hh
    have hc : primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 0 =
        primeHistoryLogCoordinates N 5 pre 0 := h3
    exact (not_lt_of_ge hx) (hc ▸ hh)
  · intro hg
    have hh := hg.1
    change VariableEnvelope.mu <
      primeHistoryLogCoordinates N 2 (rosserAncestor 2 (rosserAncestor 4 pre)) 0 at hh
    rw [rosserAncestor_nested 2 4 (by decide)] at hh
    have hc : primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 0 =
        primeHistoryLogCoordinates N 5 pre 0 := h2
    exact (not_lt_of_ge hx) (hc ▸ hh)

/-- This actual equality is derived from source geometry. It is not an
identification of the two policies by their names. -/
theorem inherited_eq_old_below_mu (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 5)
    (hx : primeHistoryLogCoordinates N 5 pre 0 ≤ VariableEnvelope.mu) :
    commonInherited d N pre = oldInherited d N pre := by
  have hg := ancestor_fallback_guards_false N pre hlen hx
  have hs : originalSeed d N (rosserAncestor 4 pre) ≤ oldInherited d N pre :=
    seedExponent_le_exponent4 (d.e : ℝ) d.chi d.m d.omega N d.rows4
      (producerEligible d.licensed4) (fun r => r.bufferedCandidate (d.e : ℝ))
      (rosserAncestor 4 pre)
  rw [inherited_eq_old_max_fallback]
  simp only [inheritedFallback, fallbackSeed, if_neg hg.1, if_neg hg.2, max_eq_left hs]

theorem fifth_eq_old_below_mu (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 5)
    (hx : primeHistoryLogCoordinates N 5 pre 0 ≤ VariableEnvelope.mu) :
    exponent5 d N pre = oldFifth d N pre := by
  apply fifth_eq_old_off_changedParents d N pre hlen
  rintro ⟨_, hn⟩
  exact hn (inherited_eq_old_below_mu d N pre hlen hx)

variable (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
  (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
  (e : ℚ) (q : ℕ) (chi omega N : ℝ)

/-- Every eligible row of the complete independently loaded licensed
archive is below mu. No all-row geometry check is an extra hypothesis. -/
theorem eligible_archive_first_lt_mu (r : P1OriginalVariableFifthContinuation.FifthRow (refinedMesh q))
    (hr : r ∈ (sourceData rows4 licensed4 e q chi omega).rows5)
    (t : Fin 5 → ℝ)
    (he : P1OriginalVariableFifthContinuation.eligible e chi (refinedMesh q) omega
      (sourceData rows4 licensed4 e q chi omega).J5 r t) : t 0 < VariableEnvelope.mu := by
  obtain ⟨i, hi, _hj, _hrow, hdecoded⟩ :=
    full_archive_licensed_rows_source rows4 licensed4 e q chi omega r hr
  have hbox := (decodeFifthRows_source_geometry (archiveRow i) (refinedMesh q) r
    hdecoded t he.2.2).2.2.2
  have hg := licensedIndex_geometry i hi
  exact original_box_first_lt_mu (archiveRow i) hg.1 hg.2.2.2 t hbox

theorem actual_archive_parent_unchanged_on_eligible (pre : List ℕ) (hlen : pre.length = 5)
    (r : P1OriginalVariableFifthContinuation.FifthRow (refinedMesh q))
    (hr : r ∈ (sourceData rows4 licensed4 e q chi omega).rows5)
    (he : P1OriginalVariableFifthContinuation.eligible e chi (refinedMesh q) omega
      (sourceData rows4 licensed4 e q chi omega).J5 r (primeHistoryLogCoordinates N 5 pre)) :
    commonInherited (sourceData rows4 licensed4 e q chi omega) N pre =
      oldInherited (sourceData rows4 licensed4 e q chi omega) N pre :=
  inherited_eq_old_below_mu _ N pre hlen
    (eligible_archive_first_lt_mu rows4 licensed4 e q chi omega r hr _ he).le

/-- Above-mu restored histories receive no inherited fifth-row gain:
both the original and common maxima equal their OWN current parent. -/
theorem actual_archive_fifth_outside_below_mu (pre : List ℕ) (hlen : pre.length = 5)
    (hx : VariableEnvelope.mu ≤ primeHistoryLogCoordinates N 5 pre 0) :
    oldFifth (sourceData rows4 licensed4 e q chi omega) N pre =
        oldInherited (sourceData rows4 licensed4 e q chi omega) N pre ∧
      exponent5 (sourceData rows4 licensed4 e q chi omega) N pre =
        commonInherited (sourceData rows4 licensed4 e q chi omega) N pre := by
  have hn : ∀ r ∈ (sourceData rows4 licensed4 e q chi omega).rows5,
      ¬P1OriginalVariableFifthContinuation.eligible e chi (refinedMesh q) omega
        (sourceData rows4 licensed4 e q chi omega).J5 r (primeHistoryLogCoordinates N 5 pre) := by
    intro r hr he
    exact not_lt_of_ge hx (eligible_archive_first_lt_mu rows4 licensed4 e q chi omega r hr _ he)
  constructor
  · unfold oldFifth P1OriginalVariableFifthContinuation.exponent5
    rw [if_pos hlen]
    exact finiteMax_eq_seed_of_outside _ _ _ _ hn
  · unfold exponent5
    rw [if_pos hlen]
    exact finiteMax_eq_seed_of_outside _ _ _ _ hn

/-- The exact clipped defect from the generic computation VANISHES for
this original licensed fifth source, for a proved source-specific reason. -/
theorem actual_archive_fifth_gain_unchanged (pre : List ℕ) (hlen : pre.length = 5) :
    commonGain (sourceData rows4 licensed4 e q chi omega) N pre =
      oldGain (sourceData rows4 licensed4 e q chi omega) N pre := by
  by_cases hx : primeHistoryLogCoordinates N 5 pre 0 < VariableEnvelope.mu
  · unfold commonGain oldGain
    rw [inherited_eq_old_below_mu _ N pre hlen hx.le, fifth_eq_old_below_mu _ N pre hlen hx.le]
  · have he := actual_archive_fifth_outside_below_mu rows4 licensed4 e q chi omega N
      pre hlen (le_of_not_gt hx)
    simp only [commonGain, oldGain, he.1, he.2, P1OriginalFifthIntegral.cellKernel,
      sub_self, zero_mul]

theorem actual_archive_defect_zero (pre : List ℕ) (hlen : pre.length = 5) :
    parentGainDefect (sourceData rows4 licensed4 e q chi omega) N pre = 0 := by
  rw [← oldGain_sub_commonGain, actual_archive_fifth_gain_unchanged
    rows4 licensed4 e q chi omega N pre hlen, sub_self]

end
end ImbalancedChen.P5OriginalFifthArchiveFallbackSeparation
