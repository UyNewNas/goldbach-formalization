import ImbalancedChen.P4AOriginalFourthFifthTaggedProvenance

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Manuscript-internal integration only. The old scalar/sixth-tag library is
refined by actual fourth/fifth ROW traces. One certified own-rank box now
fixes both cap and row, hence its selected mask, at each of ranks 4/5/6.
All prior source states, source guards, archived arrays and policies remain
unchanged. New conclusions do not assume a tag, a box, or an action licence.
External analytic inputs are documentation-only and are not implemented.
-/
namespace ImbalancedChen.P4AOriginalFull87AllRankBoxedProvenance
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter MeasureTheory
open P1FiniteAffineDecisionProgram P1AffineTaggedDecision P1FiniteAffineQuantizerTable
open P1FiniteMaxRowProvenance (CapTagBox capTagBox_of_covered)
open P1AffineCertifiedMesh P1AffineCertifiedLookup
open P4AOriginalFourthFifthAffinePrograms P4AOriginalFourthFifthTaggedProvenance
open P4AOriginalCompleteSixthChronology P5OriginalCommonRefinedConstructor
open P1OriginalVariableFourthContinuation
open P4AOriginalFull87FiniteParentCaps P1GuardFrozenFiniteCapAlgebra
open P4AOriginalFull87CertifiedBoxRealization
open P4AOriginalFull87BoxedWinner
open P4AOriginalFourthFifthUniformActionLicense
open P4AOriginalFull87ActionLicenseIntegration
open P4AOriginalFull87SixthMarginIntegration
open P4AOriginalSixthCommonMargin
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87TrimOmission (totalOmitted source_volume_lt_top)
open P1QuantizedActionLicense (LowerLicense)

abbrev Index (e : ℚ) (q : ℕ) (om : ℝ) :=
  ((Seed e q om × Stage) ⊕ Seed e q om) ⊕ (Seed e q om × Bool)

/-- Only the analysis certificate library grows. No extra action is added
and no future-coordinate test is projected into an earlier decision. -/
def allLibrary (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) : Index e q om → Spec 8
  | .inl i => jointLibrary n e q om i
  | .inr (b,false) => ⟨4,(trace4 n (data e q om) b.val).code,
      ⟨fun i => i.castLE (by decide), by intro i j h; exact Fin.ext (congrArg Fin.val h)⟩⟩
  | .inr (b,true) => ⟨5,(trace5 n (data e q om) b.val).code,
      ⟨fun i => i.castLE (by decide), by intro i j h; exact Fin.ext (congrArg Fin.val h)⟩⟩

theorem accepted_refines_joint (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (m : ℕ) :
    accepted (allLibrary n e q om) m ⊆ accepted (jointLibrary n e q om) m := by
  intro t ht
  exact mem_iInter.mpr (fun i => mem_iInter.mp ht (.inl i))

def allOmitted (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (m : ℕ)
    (f : Cell → Point → ℝ) : ℝ :=
  ∑ c : Cell, omitted (allLibrary n e q om) (sourceSet c) (f c) m

/-- One union of scalar/tag rejections; no separate full allowance is
spent for each stage, source, seed or row. -/
theorem allOmitted_exact (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (m : ℕ)
    (f : Cell → Point → ℝ) :
    allOmitted n e q om m f =
      ∑ c : Cell, ∫ t in sourceSet c \ accepted (allLibrary n e q om) m, ‖f c t‖ := by
  apply Finset.sum_congr rfl
  intro c _
  rw [omitted_eq_sdiff]
  congr 1
  ext t
  constructor
  · exact fun h => ⟨h.1,h.2.2⟩
  · exact fun h => ⟨h.1,source_mem_unit_cube c t h.1,h.2⟩

theorem exists_all_L1_mesh (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (f : Cell → Point → ℝ) (hf : ∀ c, IntegrableOn (f c) (sourceSet c))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ m0 : ℕ, ∀ m ≥ m0, allOmitted n e q om m f < epsilon := by
  have ht := tendsto_finset_sum (Finset.univ : Finset Cell)
    (fun c _ => tendsto_omitted (allLibrary n e q om) (sourceSet c) (f c) (hf c))
  have hlim : Tendsto (fun m => allOmitted n e q om m f) atTop (𝓝 0) := by
    simpa only [allOmitted,Finset.sum_const_zero] using ht
  exact Filter.eventually_atTop.mp (hlim.eventually (gt_mem_nhds hepsilon))

theorem exists_all_volume_mesh (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ m0 : ℕ, ∀ m ≥ m0,
      allOmitted n e q om m (fun _ _ => (1 : ℝ)) < epsilon := by
  apply exists_all_L1_mesh n e q om (fun _ _ => (1 : ℝ)) _ epsilon hepsilon
  intro c
  exact integrableOn_const (source_volume_lt_top c).ne

/-- A returned statement, never an input record. It binds the selected
ROW to the raw producer, finite cap and that row's own square/tent tests. -/
def RowResult {k : ℕ} {ι : Type*} [Fintype ι]
    (trace : Trace k (Option ι)) (m n : ℕ) (e : ℝ) (t : Fin k → ℝ)
    (eligible : ι → Prop) (candidate : ι → ℝ) (mask : ι → Finset (Fin k))
    (old rawValue value : ℝ) : Prop :=
  (trace.lookup m t = none ↔ ¬old < value) ∧
  ∀ r, trace.lookup m t = some r →
    old < value ∧ eligible r ∧ rawValue = candidate r ∧
    value = (rounded n (candidate r) : ℝ) ∧ LowerLicense (mask r) t value ∧
    value + width n + 2 * e ≤ VariableEnvelope.v (∑ i ∈ mask r, t i)

def FourthResult (n m : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) : Prop :=
  let d := data e q om
  let t := primeHistoryLogCoordinates N 4 pre
  RowResult (trace4 n d b) m n (d.e : ℝ) t
    (fun r => producerEligible d.licensed4 r.val t)
    (fun r => r.val.bufferedCandidate (d.e : ℝ) t) (fun r => r.val.selected)
    (predecessor4 n e q om N pre) (exponent4 d N pre) (cap4 n e q om N pre)

def FifthResult (n m : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) : Prop :=
  let d := data e q om
  let t := primeHistoryLogCoordinates N 5 pre
  RowResult (trace5 n d b) m n (d.e : ℝ) t
    (fun r => P1OriginalVariableFifthContinuation.eligible d.e d.chi d.m d.omega d.J5 r.val t)
    (fun r => P1OriginalVariableFifthContinuation.candidate (d.e : ℝ) r.val.selected t)
    (fun r => r.val.selected) (cap4 n e q om N (rosserAncestor 4 pre))
    (exponent5 d N pre) (cap5 n e q om N pre)

/-- Both boxes are at their own ranks with the same original third entry.
Each single mesh label certifies cap AND ROW simultaneously. The upstream
third-tagged half-open refinement remains necessary and unchanged. -/
def LowerWinnerSupply (n m : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) : Prop :=
  ∀ N : ℝ, ∀ pre : List ℕ, pre.length = 8 → ∀ c : Cell,
  Source c (primeHistoryLogCoordinates N 8 pre) →
    ∃ b ∈ thirdAlphabet (data e q om).e (data e q om).chi (data e q om).m,
      originalSeed (data e q om) N pre = (b : ℝ) ∧
      FourthResult n m e q om N b (rosserAncestor 4 pre) ∧
      FifthResult n m e q om N b (rosserAncestor 5 pre) ∧
      (primeHistoryLogCoordinates N 8 pre ∈ accepted (allLibrary n e q om) m →
        CapTagBox n m b (fourthProgram (data e q om) b) (trace4 n (data e q om) b)
          (primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre)) ∧
        CapTagBox n m b (fifthProgram (data e q om) b) (trace5 n (data e q om) b)
          (primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre)))

theorem lowerWinnerSupply_of_archive (n m : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (ha : ArchiveLicenses n e q om) : LowerWinnerSupply n m e q om := by
  intro N pre hlen c hs
  obtain ⟨b,hb,hseed,hanc⟩ := source_seed_all e q om N pre hlen c hs
  have hlen4 : (rosserAncestor 4 pre).length = 4 := by simp [hlen]
  have hlen5 : (rosserAncestor 5 pre).length = 5 := by simp [hlen]
  have h4 := hanc 4 (by decide)
  have h5 := hanc 5 (by decide)
  refine ⟨b,hb,hseed,?_,?_,?_⟩
  · exact ⟨fourth_none_iff n e q om N b _ hlen4 h4.2 h4.1 m,
      fun r ht => fourth_some_licensed n e q om N b _ hlen4 h4.2 h4.1 ha m r ht⟩
  · exact ⟨fifth_none_iff n e q om N b _ hlen5 h5.2 h5.1 m,
      fun r ht => fifth_some_licensed n e q om N b _ hlen5 h5.2 h5.1 ha m r ht⟩
  · intro haccept
    let entry : Seed e q om := ⟨b,hb⟩
    have hc4 := mem_iInter.mp haccept (.inl (.inl (entry,Stage.fourth)))
    have ht4 := mem_iInter.mp haccept (.inr (entry,false))
    have hc5 := mem_iInter.mp haccept (.inl (.inl (entry,Stage.fifth)))
    have ht5 := mem_iInter.mp haccept (.inr (entry,true))
    have hp4 : (fun i : Fin 4 => primeHistoryLogCoordinates N 8 pre (i.castLE (by decide))) =
        primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre) := by
      funext i
      exact (primeHistoryLogCoordinates_ancestor N hlen (by decide : 4 ≤ 8) i).symm
    have hp5 : (fun i : Fin 5 => primeHistoryLogCoordinates N 8 pre (i.castLE (by decide))) =
        primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre) := by
      funext i
      exact (primeHistoryLogCoordinates_ancestor N hlen (by decide : 5 ≤ 8) i).symm
    change (fun i : Fin 4 => primeHistoryLogCoordinates N 8 pre (i.castLE (by decide))) ∈
      covered (protectedProgram n b (fourthProgram (data e q om) b)) m at hc4
    change (fun i : Fin 4 => primeHistoryLogCoordinates N 8 pre (i.castLE (by decide))) ∈
      covered (trace4 n (data e q om) b).code m at ht4
    change (fun i : Fin 5 => primeHistoryLogCoordinates N 8 pre (i.castLE (by decide))) ∈
      covered (protectedProgram n b (fifthProgram (data e q om) b)) m at hc5
    change (fun i : Fin 5 => primeHistoryLogCoordinates N 8 pre (i.castLE (by decide))) ∈
      covered (trace5 n (data e q om) b).code m at ht5
    rw [hp4] at hc4 ht4
    rw [hp5] at hc5 ht5
    exact ⟨capTagBox_of_covered n m b _ _ _ hc4 ht4,
      capTagBox_of_covered n m b _ _ _ hc5 ht5⟩

/-- All added predicates are CONCLUSIONS. The actual archive precision,
common sixth margins and saved-source guard equivalence are reused, not
assumed. Fine m is chosen after fixed e,q,n,om and before N or prime tuples.
The budget here is volume only; no arithmetic reserve or saving is paid. -/
theorem exists_shared_all_rank_winner_schedule
    (epsilonSource epsilonBox epsilonSixth : ℝ)
    (hSource : 0 < epsilonSource) (hBox : 0 < epsilonBox)
    (hSixth : 0 < epsilonSixth) :
    ∃ s r : ℕ, ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 11 / 64000 ∧
      totalSixthOmitted s (fun _ _ => (1 : ℝ)) < epsilonSixth ∧
      totalOmitted r (fun _ _ => (1 : ℝ)) < epsilonSource ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ om : ℝ, om ≤ 1 / 100 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        ArchiveLicenses n e q om ∧ SixthLicenses s n e q om ∧
        ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
          allOmitted n e q om m (fun _ _ => (1 : ℝ)) < epsilonBox ∧
          SourceSupply r n m e q om ∧ WinnerSupply s n m e q om ∧
          SavedSourceSupply r e q om ∧ LowerWinnerSupply n m e q om := by
  obtain ⟨s,r,e0,he0,hemax,hsixth,hsource,hchoose⟩ :=
    exists_shared_boxed_winner_schedule epsilonSource epsilonBox epsilonSixth
      hSource hBox hSixth
  refine ⟨s,r,e0,he0,hemax,hsixth,hsource,?_⟩
  intro e he hee
  obtain ⟨q0,hq0,hq⟩ := hchoose e he hee
  refine ⟨q0,hq0,?_⟩
  intro q hqq om hom
  obtain ⟨n0,hn0⟩ := hq q hqq om hom
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨ha,h6,mOld,hmOld⟩ := hn0 n hn
  obtain ⟨mAll,hmAll⟩ := exists_all_volume_mesh n e q om epsilonBox hBox
  refine ⟨ha,h6,max mOld mAll,?_⟩
  intro m hm
  obtain ⟨_holdMass,hstates,hwin,hsaved⟩ := hmOld m ((le_max_left _ _).trans hm)
  exact ⟨hmAll m ((le_max_right _ _).trans hm),hstates,hwin,hsaved,
    lowerWinnerSupply_of_archive n m e q om ha⟩

end
end ImbalancedChen.P4AOriginalFull87AllRankBoxedProvenance
