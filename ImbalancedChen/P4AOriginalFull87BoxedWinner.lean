import ImbalancedChen.P4AOriginalSixthTaggedWinner
import ImbalancedChen.P4AOriginalSavedSixthActualAdmission

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

The old scalar certificates do NOT fix a winning mask. The actual
sixth provenance code is added to the common library. The resulting
certified boxes fix BOTH scalar programs and one deterministic actual
action tag, on the original frozen third-entry slice. Exact fallback
keeps all rejected-box/equality decisions and all old source states.

No original archive gain, saved-row acceptance completeness, arithmetic
wall error or compiler/density reserve is supplied by this representation.
-/
namespace ImbalancedChen.P4AOriginalFull87BoxedWinner
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter MeasureTheory
open P1FiniteAffineDecisionProgram P1AffineTaggedDecision
open P1AffineCertifiedMesh P1AffineCertifiedLookup
open P4AOriginalSixthActionBank P4AOriginalSixthTaggedWinner
open P4AOriginalSixthCommonMargin P4AOriginalSixthWinningAction
open P4AOriginalFull87SixthMarginIntegration
open P4AOriginalCompleteSixthChronology P5OriginalCommonRefinedConstructor
open P4AOriginalFull87FiniteParentCaps P1GuardFrozenFiniteCapAlgebra
open P4AOriginalFull87CertifiedBoxRealization
open P4AOriginalFull87ActionLicenseIntegration
open P4AOriginalFourthFifthUniformActionLicense
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87SevenCubeAdmission P4AOriginalFull87StrictActionTrim
open P4AOriginalSavedSixthActualAdmission
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87TrimOmission (totalOmitted source_volume_lt_top)

/-- A NEW refinement certificate library, not a new policy or a replacement
state list. All prior scalar programs remain as the left summand. -/
def jointLibrary (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) :
    (Seed e q om × Stage) ⊕ Seed e q om → Spec 8
  | .inl i => library n e q om i
  | .inr b => ⟨6, (decision n (data e q om) b.val).code,
      ⟨fun i => i.castLE (by decide), by intro i j h; exact Fin.ext (congrArg Fin.val h)⟩⟩

theorem joint_accepted_scalar (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (m : ℕ) :
    accepted (jointLibrary n e q om) m ⊆ accepted (library n e q om) m := by
  intro t ht
  exact mem_iInter.mpr (fun i => mem_iInter.mp ht (.inl i))

def jointOmitted (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (m : ℕ) (f : Cell → Point → ℝ) : ℝ :=
  ∑ c : Cell, omitted (jointLibrary n e q om) (sourceSet c) (f c) m

/-- The loss is one UNION of old scalar and new provenance rejections,
not one full tolerance spent independently on each program. -/
theorem jointOmitted_exact (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (m : ℕ) (f : Cell → Point → ℝ) :
    jointOmitted n e q om m f =
      ∑ c : Cell, ∫ t in sourceSet c \ accepted (jointLibrary n e q om) m, ‖f c t‖ := by
  apply Finset.sum_congr rfl
  intro c _
  rw [omitted_eq_sdiff]
  congr 1
  ext t
  constructor
  · exact fun h => ⟨h.1,h.2.2⟩
  · exact fun h => ⟨h.1,source_mem_unit_cube c t h.1,h.2⟩

theorem exists_joint_L1_mesh (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (f : Cell → Point → ℝ) (hf : ∀ c, IntegrableOn (f c) (sourceSet c))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ m0 : ℕ, ∀ m ≥ m0, jointOmitted n e q om m f < epsilon := by
  have ht := tendsto_finset_sum (Finset.univ : Finset Cell)
    (fun c _ => tendsto_omitted (jointLibrary n e q om) (sourceSet c) (f c) (hf c))
  have hlim : Tendsto (fun m => jointOmitted n e q om m f) atTop (𝓝 0) := by
    simpa only [jointOmitted,Finset.sum_const_zero] using ht
  exact Filter.eventually_atTop.mp (hlim.eventually (gt_mem_nhds hepsilon))

theorem exists_joint_volume_mesh (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ m0 : ℕ, ∀ m ≥ m0,
      jointOmitted n e q om m (fun _ _ => (1 : ℝ)) < epsilon := by
  apply exists_joint_L1_mesh n e q om (fun _ _ => (1 : ℝ)) _ epsilon hepsilon
  intro c
  exact integrableOn_const (source_volume_lt_top c).ne

/-- Full closed-box constancy of the action label; this includes the
inheritance tag none. The old original third entry b remains explicit. -/
theorem covered_fixed_tag (n : ℕ) (d : OriginalData) (b : ℚ) (m : ℕ)
    (t : Fin 6 → ℝ) (ht : t ∈ covered (decision n d b).code m) :
    ∃ j ∈ approved (decision n d b).code m,
      t ∈ cell m j ∧
      ∀ u : Fin 6 → ℝ, (∀ i, lo m j i ≤ u i) → (∀ i, u i ≤ hi m j i) →
        (decision n d b).eval u = (decision n d b).lookup m t := by
  obtain ⟨j,hj⟩ := mem_iUnion.mp ht
  obtain ⟨hcert,htj⟩ := mem_iUnion.mp hj
  have hc := (mem_approved _ _ _).mp hcert
  have hb := mem_logPrimeMeshCell.mp htj
  have htag := (decision n d b).tag_on_closed_box _ _ _ hc t
    (fun i => (hb i).1) (fun i => (hb i).2.le)
  refine ⟨j,hcert,htj,?_⟩
  intro u hl hu
  rw [Trace.lookup_exact,htag]
  exact (decision n d b).tag_on_closed_box _ _ _ hc u hl hu

/-- Output specification. No input frontier, winning action or rectangle
licence is hidden here. The seed is selected at the original third ancestor.
The licence consequence is restricted to the previously explicit safe8
stratum; the lookup and original states are not restricted by safe8. -/
def WinnerSupply (s n m : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) : Prop :=
  ∀ N : ℝ, ∀ pre : List ℕ, pre.length = 8 → ∀ c : Cell,
  Source c (primeHistoryLogCoordinates N 8 pre) →
    ∃ b ∈ thirdAlphabet (data e q om).e (data e q om).chi (data e q om).m,
      originalSeed (data e q om) N pre = (b : ℝ) ∧
      let t := primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)
      let tag := (decision n (data e q om) b).lookup m t
      (tag = none ↔ ¬cap5 n e q om N (rosserAncestor 5 pre) <
        cap6 n e q om N (rosserAncestor 6 pre)) ∧
      (∀ a : Entry, tag = some a →
        ActualEligible e q om N (rosserAncestor 6 pre) a.val ∧
        currentSixthExponent e q om N (rosserAncestor 6 pre) = endpoint a.val t ∧
        cap6 n e q om N (rosserAncestor 6 pre) = (rounded n (endpoint a.val t) : ℝ) ∧
        (primeHistoryLogCoordinates N 8 pre ∈ safe8 (width s) →
          (∀ g : P1QuantizedActionLicense.Gate 6,
            P1QuantizedActionLicense.gate (selected a.val) t g + width s / 2 <
              cap6 n e q om N (rosserAncestor 6 pre)) ∧
          cap6 n e q om N (rosserAncestor 6 pre) + width n ≤
            VariableEnvelope.v (∑ i ∈ selected a.val, t i))) ∧
      (primeHistoryLogCoordinates N 8 pre ∈ accepted (jointLibrary n e q om) m →
        ∃ j ∈ approved (decision n (data e q om) b).code m,
          t ∈ cell m j ∧
          ∀ u : Fin 6 → ℝ, (∀ i, lo m j i ≤ u i) → (∀ i, u i ≤ hi m j i) →
            (decision n (data e q om) b).eval u = tag)

/-- The only intermediate licence used here is the previous ACTUAL
sixth supplier; the public terminal below constructs it, not the caller. -/
theorem winnerSupply_of_sixthLicenses (s n m : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (hlic : SixthLicenses s n e q om) : WinnerSupply s n m e q om := by
  intro N pre hlen c hs
  obtain ⟨b,hb,hseed,hseed6,hb6⟩ := source_seed e q om N pre hlen c hs
  have hlen6 : (rosserAncestor 6 pre).length = 6 := by simp [hlen]
  refine ⟨b,hb,hseed,?_,?_,?_⟩
  · dsimp only
    rw [Trace.lookup_exact]
    simpa only [rosserAncestor_nested 5 6 (by decide)] using
      decision_none_iff n e q om N b (rosserAncestor 6 pre) hlen6 hb6 hseed6
  · intro a ha
    rw [Trace.lookup_exact] at ha
    obtain ⟨_,hel,hraw,hcap⟩ := decision_some_sound n e q om N b
      (rosserAncestor 6 pre) hlen6 hb6 hseed6 a ha
    refine ⟨hel,hraw,hcap,?_⟩
    intro hsafe
    have h := (hlic N pre hlen c hs hsafe).1 a.val hel
    constructor
    · rw [hcap]
      exact h.2.1
    · rw [hcap]
      exact h.2.2
  · intro haccept
    have hc := mem_iInter.mp haccept (.inr (⟨b,hb⟩ : Seed e q om))
    apply covered_fixed_tag n (data e q om) b m
    have hproj : (jointLibrary n e q om (.inr (⟨b,hb⟩ : Seed e q om))).project
        (primeHistoryLogCoordinates N 8 pre) =
          primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre) := by
      funext i
      exact (primeHistoryLogCoordinates_ancestor N hlen (by decide : 6 ≤ 8) i).symm
    simpa only [hproj] using hc

/-- Every saved geometric source in the retained original87 slice is
actually accepted. This does not certify every original array rectangle
or assert that all saved rows contribute to any numerical endpoint. -/
def SavedSourceSupply (r : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) : Prop :=
  ∀ N : ℕ, 1 < (N : ℝ) → ∀ p : Fin 8 → ℕ,
    (∀ i, (p i).Prime) → (∀ i, ¬p i ∣ N) →
    ∀ c : Cell, point (N : ℝ) p ∈ trim c (width r) → ∀ i : SavedRow,
      savedEligible e q om (N : ℝ) i (rosserAncestor 6 (pre p)) ↔
        P4AOriginalSavedSixthArchive.Source i
          (primeHistoryLogCoordinates (N : ℝ) 6 (rosserAncestor 6 (pre p)))

theorem savedSupply_of_sourceSupply (r n m : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (he : 0 ≤ e) (hsupply : SourceSupply r n m e q om) :
    SavedSourceSupply r e q om := by
  intro N hN p hp hdelete c ht i
  have hr := (hsupply N hN p hp hdelete c ht).1
  have hs := trim_subset_source c (width_pos r) ht
  exact savedEligible_iff_source i e q om (N : ℝ) he (pre p) (pre_length p) c hs hr

/-- The inherited original state supplier is retained verbatim. Only the
fine certificate library is refined to fix the provenance tag as well.
The fine threshold is chosen AFTER fixed e,q,n,om and BEFORE N or primes.
All loss bounds below are volume budgets, not arithmetic reserve payments. -/
theorem exists_shared_boxed_winner_schedule
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
          jointOmitted n e q om m (fun _ _ => (1 : ℝ)) < epsilonBox ∧
          SourceSupply r n m e q om ∧ WinnerSupply s n m e q om ∧
          SavedSourceSupply r e q om := by
  obtain ⟨s,r,e0,he0,hemax,hSixthMass,hSourceMass,hchoose⟩ :=
    exists_shared_all_action_licensed_schedule epsilonSource epsilonBox epsilonSixth
      hSource hBox hSixth
  refine ⟨s,r,e0,he0,hemax,hSixthMass,hSourceMass,?_⟩
  intro e he hee
  obtain ⟨q0,hq0,hq⟩ := hchoose e he hee
  refine ⟨q0,hq0,?_⟩
  intro q hqq om hom
  obtain ⟨n0,hn0⟩ := hq q hqq om hom
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨ha,h6,mOld,hmOld⟩ := hn0 n hn
  obtain ⟨mTag,hmTag⟩ := exists_joint_volume_mesh n e q om epsilonBox hBox
  refine ⟨ha,h6,max mOld mTag,?_⟩
  intro m hm
  have hsource := (hmOld m ((le_max_left _ _).trans hm)).2
  exact ⟨hmTag m ((le_max_right _ _).trans hm),hsource,
    winnerSupply_of_sixthLicenses s n m e q om h6,
    savedSupply_of_sourceSupply r n m e q om he.le hsource⟩

end
end ImbalancedChen.P4AOriginalFull87BoxedWinner
