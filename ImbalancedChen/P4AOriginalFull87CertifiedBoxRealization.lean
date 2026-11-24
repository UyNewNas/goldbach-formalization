import ImbalancedChen.P1AffineCertifiedLookup
import ImbalancedChen.P4AOriginalFull87AffineGuardRealization

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

One finite, actual program library includes ALL original third-table entries
and ranks4/5/6. Its approved own-rank closed boxes cover almost every source
point as the SAME fine mesh is refined. The e/q/n/omega library is fixed before
this fine resolution and before N. The actual existing finite-parent policy
and occurrence state list are unchanged, including rejected-box/equality
points. Such points use the existing exact sign-table fallback.

This is not the original action-square/gain audit. Euclidean/L1 omission is
not a prime-count bound, a numerical saving transport, or a reserve payment.
-/
namespace ImbalancedChen.P4AOriginalFull87CertifiedBoxRealization
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter MeasureTheory
open P1FiniteAffineDecisionProgram P1AffineCertifiedMesh P1AffineCertifiedLookup
open P1FiniteAffineQuantizerTable
open P4AOriginalFourthFifthAffinePrograms P4AOriginalCompleteSixthAffinePrograms
open P4AOriginalFull87AffineGuardRealization
open P4AOriginalCompleteSixthChronology
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalFull87FiniteParentCaps
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87StrictActionTrim
open P4AOriginalFull87SevenCubeAdmission
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87ActualSourceMembership (canonicalState)
open P4AOriginalFull87TrimOmission (totalOmitted source_volume_lt_top)

inductive Stage where
  | fourth | fifth | sixth
  deriving DecidableEq, Fintype

abbrev Seed (e : ℚ) (q : ℕ) (om : ℝ) :=
  {b : ℚ // b ∈ thirdAlphabet (data e q om).e (data e q om).chi (data e q om).m}

/-- The WHOLE finite third-entry family is fixed before N; the actual
entry is still read at its own third ancestor, not chosen from a child. -/
def library (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) : Seed e q om × Stage → Spec 8
  | (b, .fourth) => ⟨4, code4 n e q om b.val,
      ⟨fun i => i.castLE (by decide), by intro i j h; exact Fin.ext (congrArg Fin.val h)⟩⟩
  | (b, .fifth) => ⟨5, code5 n e q om b.val,
      ⟨fun i => i.castLE (by decide), by intro i j h; exact Fin.ext (congrArg Fin.val h)⟩⟩
  | (b, .sixth) => ⟨6, code6 n e q om b.val,
      ⟨fun i => i.castLE (by decide), by intro i j h; exact Fin.ext (congrArg Fin.val h)⟩⟩

def totalBoxOmitted (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (m : ℕ) (f : Cell → Point → ℝ) : ℝ :=
  ∑ c : Cell, P1AffineCertifiedMesh.omitted (library n e q om) (sourceSet c) (f c) m


theorem source_mem_unit_cube (c : Cell) (t : Point) (hs : Source c t) : t ∈ cube 8 := by
  obtain ⟨hl, hu⟩ := P4AOriginalFull87HistoryCore.source_in_cube hs
  apply mem_logPrimeBox.mpr
  intro i
  exact ⟨hl i, (hu i).trans_lt (by norm_num [VariableEnvelope.mu])⟩

/-- No outside-cube mass is omitted from the accounting: every ORIGINAL
source is in the common cube. Thus this is exactly the unboxed source. -/
theorem source_rejected_exact (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (m : ℕ) (c : Cell) :
    sourceSet c ∩ rejected (library n e q om) m =
      sourceSet c \ accepted (library n e q om) m := by
  ext t
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · exact fun h => ⟨h.1, source_mem_unit_cube c t h.1, h.2⟩

theorem totalBoxOmitted_exact (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (m : ℕ) (f : Cell → Point → ℝ) :
    totalBoxOmitted n e q om m f =
      ∑ c : Cell, ∫ t in sourceSet c \ accepted (library n e q om) m, ‖f c t‖ := by
  simp only [totalBoxOmitted, P1AffineCertifiedMesh.omitted_eq_sdiff, source_rejected_exact]

/-- No per-source, per-third-entry, or per-stage fine meshes: one m works
for the sum of the actual87 omitted L1 masses. -/
theorem exists_common_L1_box_mesh (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (f : Cell → Point → ℝ) (hf : ∀ c, IntegrableOn (f c) (sourceSet c))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ m0 : ℕ, ∀ m ≥ m0, totalBoxOmitted n e q om m f < epsilon := by
  have ht := tendsto_finset_sum (Finset.univ : Finset Cell)
    (fun c _ => P1AffineCertifiedMesh.tendsto_omitted
      (library n e q om) (sourceSet c) (f c) (hf c))
  have hlim : Tendsto (fun m => totalBoxOmitted n e q om m f) atTop (𝓝 0) := by
    simpa only [totalBoxOmitted, Finset.sum_const_zero] using ht
  exact Filter.eventually_atTop.mp (hlim.eventually (gt_mem_nhds hepsilon))

theorem exists_common_volume_box_mesh (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ m0 : ℕ, ∀ m ≥ m0, totalBoxOmitted n e q om m (fun _ _ => (1 : ℝ)) < epsilon := by
  apply exists_common_L1_box_mesh n e q om (fun _ _ => (1 : ℝ)) _ epsilon hepsilon
  intro c
  exact integrableOn_const (source_volume_lt_top c).ne

/-- Output of the exact safe lookup, including unapproved boxes. -/
def ExactLookupParents (n m : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) : Prop :=
  ∃ b ∈ thirdAlphabet (data e q om).e (data e q om).chi (data e q om).m,
    originalSeed (data e q om) N pre = (b : ℝ) ∧
    cap4 n e q om N (rosserAncestor 4 pre) =
      scalarLookup n b (fourthProgram (data e q om) b) m
        (primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre)) ∧
    cap5 n e q om N (rosserAncestor 5 pre) =
      scalarLookup n b (fifthProgram (data e q om) b) m
        (primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre)) ∧
    cap6 n e q om N (rosserAncestor 6 pre) =
      scalarLookup n b (completeProgram (data e q om) b) m
        (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre))

theorem exact_lookup_parents_on_source (n m : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre)) :
    ExactLookupParents n m e q om N pre := by
  obtain ⟨b, hb, hseed, h4, h5, h6⟩ := raw_codes_at_own_ancestors e q om N pre hlen c hs
  refine ⟨b, hb, hseed, ?_, ?_, ?_⟩
  · rw [scalarLookup_exact, h4, cap4,
      originalSeed_ancestor _ _ 4 (by decide), hseed]
  · rw [scalarLookup_exact, h5, cap5_eq_protect,
      originalSeed_ancestor _ _ 5 (by decide), hseed]
  · rw [scalarLookup_exact, h6, cap6_eq_protect,
      originalSeed_ancestor _ _ 6 (by decide), hseed]

/-- A concrete own-rank box and its CHECKED closed-box signature. The
constant output is for the recorded third entry b; different b values are
not silently merged into a single third history. -/
def OwnBox {k : ℕ} (n m : ℕ) (b : ℚ) (p : Program k)
    (t : Fin k → ℝ) (value : ℝ) : Prop :=
  let code := protectedProgram n b p
  ∃ j ∈ approved code m, t ∈ cell m j ∧
    code.BoxCertificate (code.signature (center m j)) (lo m j) (hi m j) ∧
    value = scalarTable n b p (code.signature (center m j))

private theorem ownBox_of_covered {k : ℕ} (n m : ℕ) (b : ℚ) (p : Program k)
    (t : Fin k → ℝ) (value : ℝ)
    (ht : t ∈ covered (protectedProgram n b p) m)
    (hv : value = scalarLookup n b p m t) : OwnBox n m b p t value := by
  obtain ⟨hc, hj⟩ := (mem_covered_iff _ m t).mp ht
  refine ⟨gridLabel m t, hj, gridLabel_mem m t hc, (mem_approved _ _ _).mp hj, ?_⟩
  rw [hv, scalarLookup, if_pos ⟨hc, hj⟩]

/-- No independent cap or history licence is assumed: original Source
provides the actual third slice and the preceding exact program theorem. -/
def BoxedParents (n m : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) : Prop :=
  ∃ b ∈ thirdAlphabet (data e q om).e (data e q om).chi (data e q om).m,
    originalSeed (data e q om) N pre = (b : ℝ) ∧
    OwnBox n m b (fourthProgram (data e q om) b)
      (primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre))
      (cap4 n e q om N (rosserAncestor 4 pre)) ∧
    OwnBox n m b (fifthProgram (data e q om) b)
      (primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre))
      (cap5 n e q om N (rosserAncestor 5 pre)) ∧
    OwnBox n m b (completeProgram (data e q om) b)
      (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre))
      (cap6 n e q om N (rosserAncestor 6 pre))

theorem boxed_parents_on_accepted_source (n m : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre))
    (ha : primeHistoryLogCoordinates N 8 pre ∈ accepted (library n e q om) m) :
    BoxedParents n m e q om N pre := by
  obtain ⟨b, hb, hseed, h4, h5, h6⟩ := exact_lookup_parents_on_source n m e q om N pre hlen c hs
  have hp (k : ℕ) (hk : k ≤ 8) :
      primeHistoryLogCoordinates N k (rosserAncestor k pre) =
        fun i => primeHistoryLogCoordinates N 8 pre (i.castLE hk) := by
    funext i
    exact primeHistoryLogCoordinates_ancestor N hlen hk i
  have hc4 := mem_iInter.mp ha ((⟨b, hb⟩ : Seed e q om), Stage.fourth)
  have hc5 := mem_iInter.mp ha ((⟨b, hb⟩ : Seed e q om), Stage.fifth)
  have hc6 := mem_iInter.mp ha ((⟨b, hb⟩ : Seed e q om), Stage.sixth)
  refine ⟨b, hb, hseed, ?_, ?_, ?_⟩
  · apply ownBox_of_covered n m b _ _ _ _ h4
    rw [hp 4 (by decide)]
    exact hc4
  · apply ownBox_of_covered n m b _ _ _ _ h5
    rw [hp 5 (by decide)]
    exact hc5
  · apply ownBox_of_covered n m b _ _ _ _ h6
    rw [hp 6 (by decide)]
    exact hc6


/-- Actual selected third ownership gives a finite COMMON refinement of
all three own-rank grids. This theorem has no fine-box acceptance premise.
The third raw seed tag is not inferred from a fourth or later child. -/
theorem original_third_tagged_boxes (m : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre))
    (hr : RealizedHistory e q om N pre c) :
    ∃ j3 : HistoricalThirdCoarse.Cell (data e q om).m,
      j3 ∈ HistoricalThirdCoarse.cells ((data e q om).e : ℝ)
        (data e q om).chi (data e q om).m ∧
      (∀ k : ℕ, ∀ hk : 3 ≤ k, k ≤ 8 →
        primeHistoryLogCoordinates N k (rosserAncestor k pre) ∈
          taggedCell hk (data e q om).m m j3
            (gridLabel m (primeHistoryLogCoordinates N k (rosserAncestor k pre)))) := by
  obtain ⟨_hactive, j3, hj3, ht3⟩ := hr.2.1
  refine ⟨j3, hj3, ?_⟩
  intro k hk hk8
  apply (taggedCell_exact hk _ m j3 _ _).mpr
  have hc8 := source_mem_unit_cube c _ hs
  have hc : primeHistoryLogCoordinates N k (rosserAncestor k pre) ∈ cube k := by
    apply mem_logPrimeBox.mpr
    intro i
    rw [primeHistoryLogCoordinates_ancestor N hlen hk8 i]
    exact mem_logPrimeBox.mp hc8 (i.castLE hk8)
  refine ⟨gridLabel_mem m _ hc, ?_⟩
  have hanc : (fun i : Fin 3 =>
      primeHistoryLogCoordinates N k (rosserAncestor k pre) (i.castLE hk)) =
        primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) := by
    funext i
    rw [primeHistoryLogCoordinates_ancestor N hlen hk8,
      primeHistoryLogCoordinates_ancestor N hlen (by omega : 3 ≤ 8)]
    rfl
  rwa [hanc]

/-- Same existing states for ALL original trimmed tuples, including those
on an unapproved fine box. Only the rectangular fast path needs acceptance;
the exact fallback and source membership do not. Fine m is chosen after the
fixed e/q/n/omega program library but still before N and every prime tuple. -/
theorem exists_shared_boxed_source_schedule
    (epsilonSource epsilonBox : ℝ) (hSource : 0 < epsilonSource) (hBox : 0 < epsilonBox) :
    ∃ r n0 : ℕ, ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 11 / 64000 ∧
      totalOmitted r (fun _ _ => (1 : ℝ)) < epsilonSource ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ n : ℕ, n0 ≤ n → ∀ om : ℝ, om ≤ 1 / 100 →
      ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
      totalBoxOmitted n e q om m (fun _ _ => (1 : ℝ)) < epsilonBox ∧
      (∀ N : ℕ, 1 < (N : ℝ) → ∀ p : Fin 8 → ℕ,
        (∀ i, (p i).Prime) → (∀ i, ¬p i ∣ N) →
        ∀ c : Cell, point (N : ℝ) p ∈ trim c (width r) →
          RealizedHistory e q om (N : ℝ) (pre p) c ∧
          ParentBounds n e q om (N : ℝ) (pre p) c ∧
          ExactLookupParents n m e q om (N : ℝ) (pre p) ∧
          (point (N : ℝ) p ∈ accepted (library n e q om) m →
            BoxedParents n m e q om (N : ℝ) (pre p)) ∧
          (∀ enumerationCap : ℕ, ∀ w z : ℝ,
            w ≤ (N : ℝ) ^ (53 / 13824 : ℝ) →
            (N : ℝ)^VariableEnvelope.mu ≤ z → z ≤ (enumerationCap : ℝ) →
            ∀ weight : ℕ → ℝ,
            canonicalState N enumerationCap w weight p ∈
              P4AOriginalFull87FiniteParentRealization.states
                (width r) n e q om N enumerationCap w z weight c)) := by
  obtain ⟨r, n0, e0, he0, hebound, hvolume, hchoose⟩ :=
    exists_shared_finite_guard_schedule epsilonSource hSource
  refine ⟨r, n0, e0, he0, hebound, hvolume, ?_⟩
  intro e he hee
  obtain ⟨q0, hq0, hh⟩ := hchoose e he hee
  refine ⟨q0, hq0, ?_⟩
  intro q hq n hn om hom
  obtain ⟨m0, hm⟩ := exists_common_volume_box_mesh n e q om epsilonBox hBox
  refine ⟨m0, ?_⟩
  intro m hmt
  refine ⟨hm m hmt, ?_⟩
  intro N hN p hp hdelete c ht
  obtain ⟨hreal, hparent, _hcompiled, hmember⟩ := hh q hq n hn om hom N hN p hp hdelete c ht
  have hs := trim_subset_source c (width_pos r) ht
  exact ⟨hreal, hparent,
    exact_lookup_parents_on_source n m e q om (N : ℝ) (pre p) (pre_length p) c hs,
    fun ha => boxed_parents_on_accepted_source n m e q om (N : ℝ) (pre p) (pre_length p) c hs ha,
    hmember⟩

end
end ImbalancedChen.P4AOriginalFull87CertifiedBoxRealization
