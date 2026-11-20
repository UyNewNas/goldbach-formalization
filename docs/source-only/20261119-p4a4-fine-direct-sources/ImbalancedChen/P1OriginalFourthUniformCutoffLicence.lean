import ImbalancedChen.P1OriginalFourthSameScheduleLicence

/-! SOURCE_ONLY / UNCOMPILED.
The same original q0 works for EVERY later cutoff omega<=3/200.
Take the existing actual source cover at omega=3/200 once. Its selected
active label is unchanged, and only its inclusive rough gate becomes
weaker. No mesh, row geometry or source producer is repeated.
-/
namespace ImbalancedChen.P1OriginalFourthUniformCutoffLicence
noncomputable section
open scoped Classical BigOperators
open Set
open P2OriginalFourthCapProducerInterface
open P5OriginalFourthFifthSourceInputs
open P1OriginalFourthCommonHistoricalMesh P1OriginalFourthActualSourceCoverage
open P1OriginalVariableFourthContinuation P1OriginalCoarseFourthResidual
open P1OriginalVariableFourthFullSourceActivation P1OriginalVariableFourthActiveOnly
open P1OriginalVariableFourthFullActiveIntegral
open P1OriginalFourthSameScheduleLicence
open P1OriginalFourthActualQuantizedLicence (bank actualFourth)
open P4AOriginalFull87HistoryCore (width)
open P1QuantizedActionLicense (LowerLicense)
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)

theorem positive_active_source_mono_cutoff (e : ℚ) (chi : ℝ) (m : ℕ)
    (small large : ℝ) (hcut : small ≤ large) (label : Label m)
    (hl : label ∈ activeAdoptedLabels (e : ℝ) chi m) :
    positiveActiveCell e chi m large label ⊆ positiveActiveCell e chi m small label := by
  intro t ht
  have hflag := ((mem_activeAdoptedLabels (e : ℝ) chi m label).mp hl).1
  have hrough : large ≤ t 2 := by
    simpa only [activationRegion,hflag,if_true] using ht.2.1.2
  refine ⟨ht.1,⟨ht.2.1.1,?_⟩,ht.2.2⟩
  simpa only [activationRegion,hflag,if_true] using hcut.trans hrough

/-- The q-threshold is chosen before the cutoff, as required by the
stronger original saved-endpoint schedule as well as the final union.
-/
theorem exists_common_uniform_cutoff_source_cover (delta : ℝ) (hd : 0 < delta)
    (e : ℚ) (he : 0 < e) (he0 : (e : ℝ) < commonE0 delta) (mMin qMin : ℕ) :
    ∃ q0 : ℕ, qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q →
      mMin ≤ refinedMesh q ∧ ∀ omega : ℝ, omega ≤ 3 / 200 →
      ∀ r ∈ originalRows4, ∀ t : Point, t ∈ trimmedBox r delta →
      ∃ label ∈ activeAdoptedLabels (e : ℝ) ((e : ℝ)/20) (refinedMesh q),
        t ∈ positiveActiveCell e ((e : ℝ)/20) (refinedMesh q) omega label := by
  obtain ⟨q0,hq0,hq⟩ := exists_common_original_source_cover delta hd e he he0
    (3 / 200) le_rfl mMin qMin
  refine ⟨q0,hq0,?_⟩
  intro q hqq
  refine ⟨(hq q hqq).1,?_⟩
  intro omega homega r hr t ht
  obtain ⟨label,hl,hs⟩ := (hq q hqq).2 r hr t ht
  exact ⟨label,hl,positive_active_source_mono_cutoff e ((e : ℝ)/20) (refinedMesh q)
    omega (3 / 200) homega label hl hs⟩

/-- Full original order, including the stronger cutoff quantifier:
fixed n; every later small e; ONE q0; every q>=q0 and omega<=3/200;
then every original row, target and actual tuple.
-/
theorem exists_same_schedule_uniform_cutoff_fourth :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ delta : ℝ, 0 < delta →
      ∀ e : ℚ, 0 < e → (e : ℝ) < commonE0 delta → ∀ mMin qMin : ℕ,
      ∃ q0 : ℕ, qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q → mMin ≤ refinedMesh q ∧
      ∀ omega : ℝ, omega ≤ 3 / 200 →
      ∀ r ∈ originalRows4, ∀ N : ℕ, 1 < N → ∀ p : Fin 4 → ℕ,
      (∀ i, 0 < p i) → actualPrimeTupleLog N p ∈ trimmedBox r delta →
      ∃ w ∈ originalRows4, producerEligible originalAdmission4 w (actualPrimeTupleLog N p) ∧
        P5OriginalCommonRefinedConstructor.exponent4 (bank e q omega) (N : ℝ) (tupleHistory p) =
          w.bufferedCandidate (e : ℝ) (actualPrimeTupleLog N p) ∧
        oldCap (actualPrimeTupleLog N p) < actualFourth n e q omega (N : ℝ) (tupleHistory p) ∧
        LowerLicense w.selected (actualPrimeTupleLog N p)
          (actualFourth n e q omega (N : ℝ) (tupleHistory p)) ∧
        actualFourth n e q omega (N : ℝ) (tupleHistory p)+width n ≤
          w.bufferedCandidate (e : ℝ) (actualPrimeTupleLog N p) ∧
        actualFourth n e q omega (N : ℝ) (tupleHistory p)+width n ≤
          VariableEnvelope.v (∑ j ∈ w.selected,actualPrimeTupleLog N p j) := by
  obtain ⟨n0,hn0⟩ := exists_quantizer_before_all_small_e
  refine ⟨n0,?_⟩
  intro n hn delta hd e he he0 mMin qMin
  have heM := hn0 n hn delta (e : ℝ) he0
  obtain ⟨q0,hq0,hq⟩ := exists_common_uniform_cutoff_source_cover delta hd e he he0 mMin qMin
  refine ⟨q0,hq0,?_⟩
  intro q hqq
  refine ⟨(hq q hqq).1,?_⟩
  intro omega homega r hr N hN p hp ht
  obtain ⟨label,hl,hs⟩ := (hq q hqq).2 omega homega r hr _ ht
  exact actual_fourth_original_winner_same_schedule n e he.le q omega heM N hN p hp r hr
    (trimmedBox_subset r hd.le ht) label hl hs

end
end ImbalancedChen.P1OriginalFourthUniformCutoffLicence
