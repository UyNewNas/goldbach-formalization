import ImbalancedChen.P4AOriginalLicensedSixthBoxedWitness
import ImbalancedChen.P4AOriginalFull87LicensedSixthRealization

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Manuscript-internal compilation of the NEW licensed filter and its OWN
winner tag, including the former unsafe margin complement. It preserves
exact fallback and the already constructed new occurrence-state supplier.
The old scalar/tag library is retained only as part of a joint refinement;
its old sixth tag is NOT used as the new filtered winner.
-/
namespace ImbalancedChen.P4AOriginalFull87LicensedBoxIntegration
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter MeasureTheory
open P1FiniteAffineDecisionProgram P1AffineTaggedDecision
open P1AffineCertifiedMesh
open P4AOriginalSixthActionBank P4AOriginalSixthLicensedFilter
open P4AOriginalLicensedSixthAffineProgram P4AOriginalLicensedSixthBoxedWitness
open P4AOriginalCompleteSixthChronology P5OriginalCommonRefinedConstructor
open P4AOriginalFull87FiniteParentCaps P1GuardFrozenFiniteCapAlgebra
open P4AOriginalFull87CertifiedBoxRealization (Seed source_mem_unit_cube)
open P4AOriginalFull87AllRankBoxedProvenance (LowerWinnerSupply)
open P4AOriginalFull87LicensedSixthRealization
open P4AOriginalFourthFifthUniformActionLicense (ArchiveLicenses)
open P4AOriginalFull87SixthMarginIntegration (SixthLicenses)
open P4AOriginalFull87BoxedWinner (SavedSourceSupply)
open P4AOriginalSixthCommonMargin (totalSixthOmitted)
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87TrimOmission (totalOmitted source_volume_lt_top)
open P1QuantizedActionLicense (LowerLicense)

abbrev Index (e : ℚ) (q : ℕ) (om : ℝ) :=
  P4AOriginalFull87AllRankBoxedProvenance.Index e q om ⊕ (Seed e q om × Bool)

/-- One library for the entire old refinement plus the NEW value and tag
at the SAME own-sixth projection, for every possible original third entry. -/
def licensedLibrary (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) : Index e q om → Spec 8
  | .inl i => P4AOriginalFull87AllRankBoxedProvenance.allLibrary n e q om i
  | .inr (b,false) => ⟨6,program n (data e q om) b.val,
      ⟨fun i => i.castLE (by decide), by intro i j h; exact Fin.ext (congrArg Fin.val h)⟩⟩
  | .inr (b,true) => ⟨6,(decision n (data e q om) b.val).code,
      ⟨fun i => i.castLE (by decide), by intro i j h; exact Fin.ext (congrArg Fin.val h)⟩⟩

theorem accepted_refines_old (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (m : ℕ) :
    accepted (licensedLibrary n e q om) m ⊆
      accepted (P4AOriginalFull87AllRankBoxedProvenance.allLibrary n e q om) m := by
  intro t ht
  exact mem_iInter.mpr (fun i => mem_iInter.mp ht (.inl i))

def licensedBoxOmitted (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (m : ℕ) (f : Cell → Point → ℝ) : ℝ :=
  ∑ c : Cell, omitted (licensedLibrary n e q om) (sourceSet c) (f c) m

/-- One rejection UNION for all scalar/tag programs, not a separate full
allowance per program. This remains a real integral, not an arithmetic error. -/
theorem licensedBoxOmitted_exact (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (m : ℕ) (f : Cell → Point → ℝ) :
    licensedBoxOmitted n e q om m f =
      ∑ c : Cell, ∫ t in sourceSet c \ accepted (licensedLibrary n e q om) m, ‖f c t‖ := by
  apply Finset.sum_congr rfl
  intro c _
  rw [omitted_eq_sdiff]
  congr 1
  ext t
  constructor
  · exact fun h => ⟨h.1,h.2.2⟩
  · exact fun h => ⟨h.1,source_mem_unit_cube c t h.1,h.2⟩

theorem exists_licensed_L1_mesh (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (f : Cell → Point → ℝ) (hf : ∀ c, IntegrableOn (f c) (sourceSet c))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ m0 : ℕ, ∀ m ≥ m0, licensedBoxOmitted n e q om m f < epsilon := by
  have ht := tendsto_finset_sum (Finset.univ : Finset Cell)
    (fun c _ => tendsto_omitted (licensedLibrary n e q om) (sourceSet c) (f c) (hf c))
  have hlim : Tendsto (fun m => licensedBoxOmitted n e q om m f) atTop (𝓝 0) := by
    simpa only [licensedBoxOmitted,Finset.sum_const_zero] using ht
  exact Filter.eventually_atTop.mp (hlim.eventually (gt_mem_nhds hepsilon))

theorem exists_licensed_volume_mesh (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ m0 : ℕ, ∀ m ≥ m0,
      licensedBoxOmitted n e q om m (fun _ _ => (1 : ℝ)) < epsilon := by
  apply exists_licensed_L1_mesh n e q om (fun _ _ => (1 : ℝ)) _ epsilon hepsilon
  intro c
  exact integrableOn_const (source_volume_lt_top c).ne

/-- Output only. The third entry is derived at its own ancestor. On all
source points the lookup is exact and tags have actual licence; on jointly
approved boxes BOTH are constant. Neither assertion assumes safe8. -/
def CompiledLicensedSupply (n m : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) : Prop :=
  ∀ N : ℝ, ∀ pre : List ℕ, pre.length = 8 → ∀ c : Cell,
  Source c (primeHistoryLogCoordinates N 8 pre) →
    ∃ b ∈ thirdAlphabet (data e q om).e (data e q om).chi (data e q om).m,
      originalSeed (data e q om) N pre = (b : ℝ) ∧
      let t := primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)
      let tag := (decision n (data e q om) b).lookup m t
      valueLookup n (data e q om) b m t =
        licensedCap n e q om N (rosserAncestor 6 pre) ∧
      (tag = none ↔ licensedCap n e q om N (rosserAncestor 6 pre) =
        cap5 n e q om N (rosserAncestor 5 pre)) ∧
      (∀ a : Entry, tag = some a →
        Accepted n e q om N (rosserAncestor 6 pre) a.val ∧
        licensedCap n e q om N (rosserAncestor 6 pre) = (rounded n (endpoint a.val t) : ℝ) ∧
        LowerLicense (selected a.val) t (licensedCap n e q om N (rosserAncestor 6 pre)) ∧
        licensedCap n e q om N (rosserAncestor 6 pre) + width n ≤
          VariableEnvelope.v (∑ i ∈ selected a.val, t i)) ∧
      (primeHistoryLogCoordinates N 8 pre ∈ accepted (licensedLibrary n e q om) m →
        CertifiedBox n (data e q om) b m t)

theorem compiledLicensedSupply (n m : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) :
    CompiledLicensedSupply n m e q om := by
  intro N pre hlen c hs
  obtain ⟨b,hb,hseed,hseed6,hb6⟩ :=
    P4AOriginalSixthTaggedWinner.source_seed e q om N pre hlen c hs
  have hlen6 : (rosserAncestor 6 pre).length = 6 := by simp [hlen]
  refine ⟨b,hb,hseed,?_,?_,?_,?_⟩
  · dsimp only
    rw [valueLookup_exact, program_at_history n e q om N b _ hlen6 hb6 hseed6]
  · dsimp only
    rw [Trace.lookup_exact, decision_none_iff,
      program_at_history n e q om N b _ hlen6 hb6 hseed6,
      P4AOriginalSixthTaggedWinner.finiteFifth_at_history n e q om N b _ hlen6 hb6 hseed6,
      rosserAncestor_nested 5 6 (by decide)]
  · intro a ha
    exact some_at_history n e q om N b (rosserAncestor 6 pre) hlen6 hb6 hseed6 m a ha
  · intro haccept
    have hv := mem_iInter.mp haccept (.inr ((⟨b,hb⟩ : Seed e q om),false))
    have ht := mem_iInter.mp haccept (.inr ((⟨b,hb⟩ : Seed e q om),true))
    have hproj : (fun i : Fin 6 =>
        primeHistoryLogCoordinates N 8 pre (i.castLE (by decide : 6 ≤ 8))) =
        primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre) := by
      funext i
      exact (primeHistoryLogCoordinates_ancestor N hlen (by decide : 6 ≤ 8) i).symm
    change (fun i : Fin 6 => primeHistoryLogCoordinates N 8 pre
      (i.castLE (by decide : 6 ≤ 8))) ∈ covered (program n (data e q om) b) m at hv
    change (fun i : Fin 6 => primeHistoryLogCoordinates N 8 pre
      (i.castLE (by decide : 6 ≤ 8))) ∈ covered (decision n (data e q om) b).code m at ht
    rw [hproj] at hv ht
    exact certifiedBox_of_covered n (data e q om) b m _ hv ht

/-- Same producer, SAME new state list and same source/third/coarse choices.
The added m threshold is picked only after fixed e,q,n,om, before N/primes.
Old rank4/5 witnesses remain valid; the old rank6 winner is NOT returned as
if it were the winner of this filter. No original source tuple is removed. -/
theorem exists_shared_licensed_box_schedule
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
          licensedBoxOmitted n e q om m (fun _ _ => (1 : ℝ)) < epsilonBox ∧
          FilteredSourceSupply s r n e q om ∧ CompiledLicensedSupply n m e q om ∧
          SavedSourceSupply r e q om ∧ LowerWinnerSupply n m e q om := by
  obtain ⟨s,r,e0,he0,hemax,hsixth,hsource,hchoose⟩ :=
    exists_shared_licensed_sixth_schedule epsilonSource epsilonBox epsilonSixth hSource hBox hSixth
  refine ⟨s,r,e0,he0,hemax,hsixth,hsource,?_⟩
  intro e he hee
  obtain ⟨q0,hq0,hq⟩ := hchoose e he hee
  refine ⟨q0,hq0,?_⟩
  intro q hqq om hom
  obtain ⟨n0,hn0⟩ := hq q hqq om hom
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨ha,h6,mOld,hmOld⟩ := hn0 n hn
  obtain ⟨mNew,hmNew⟩ := exists_licensed_volume_mesh n e q om epsilonBox hBox
  refine ⟨ha,h6,max mOld mNew,?_⟩
  intro m hm
  obtain ⟨_holdMass,_holdSource,_holdWinner,hsaved,hlower,hfiltered⟩ :=
    hmOld m ((le_max_left _ _).trans hm)
  exact ⟨hmNew m ((le_max_right _ _).trans hm),hfiltered,
    compiledLicensedSupply n m e q om,hsaved,hlower⟩

end
end ImbalancedChen.P4AOriginalFull87LicensedBoxIntegration
