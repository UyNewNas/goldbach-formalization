import ImbalancedChen.P4AOriginalCompleteSixthAffinePrograms
import ImbalancedChen.P1FiniteAffineQuantizerTable
import ImbalancedChen.P4AOriginalFull87FiniteParentRealization

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Exact finite affine-sign tables for the SAME finite-parent construction.
The raw current in later guards has been expanded into the original
saved/eleven/later comparison program. The finite floor has also been
expanded into fixed affine thresholds. Nothing re-runs original eligibility
on a rounded predecessor. Third-table entries are selected at their own
ancestor; all possible entries and the programs are fixed before N.

This does not certify a full rectangular box cover, every action's square
licence after freezing, saved-gain transport, a prime mean or either reserve.
-/
namespace ImbalancedChen.P4AOriginalFull87AffineGuardRealization
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram P1FiniteAffineQuantizerTable
open P4AOriginalFourthFifthAffinePrograms P4AOriginalCompleteSixthAffinePrograms
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalCompleteSixthChronology
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87FiniteParentCaps
open P4AOriginalFull87SevenCubeAdmission
open P4AOriginalFull87StrictActionTrim
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87ActualSourceMembership (canonicalState)
open P4AOriginalFull87TrimOmission (totalOmitted)

/-- These libraries depend on e,q,omega,precision and the finite third
entry only. N, prime labels and any later child are absent. -/
def code4 (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (b : ℚ) : Program 4 :=
  protectedProgram n b (fourthProgram (data e q om) b)
def code5 (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (b : ℚ) : Program 5 :=
  protectedProgram n b (fifthProgram (data e q om) b)
def code6 (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (b : ℚ) : Program 6 :=
  protectedProgram n b (completeProgram (data e q om) b)

abbrev JointSignature (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (b : ℚ) :=
  (code4 n e q om b).Signature ×
    (code5 n e q om b).Signature × (code6 n e q om b).Signature

def jointSignature (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (b : ℚ)
    (t : Fin 6 → ℝ) : JointSignature n e q om b :=
  ⟨(code4 n e q om b).signature (fun i => t i.castSucc.castSucc),
    (code5 n e q om b).signature (fun i => t i.castSucc),
    (code6 n e q om b).signature t⟩

def jointRegion (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (b : ℚ)
    (s : JointSignature n e q om b) : Set (Fin 6 → ℝ) :=
  {t | jointSignature n e q om b t = s}

theorem joint_cover (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (b : ℚ) :
    (⋃ s : JointSignature n e q om b, jointRegion n e q om b s) = Set.univ := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨jointSignature n e q om b t, rfl⟩

/-- A later coordinate can refine the joint analysis cell but cannot
change either predecessor's own label. No child-wall projection is removed. -/
theorem joint_predecessor_labels (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (b : ℚ)
    (t u : Fin 6 → ℝ)
    (h4 : ∀ i : Fin 4, t i.castSucc.castSucc = u i.castSucc.castSucc)
    (h5 : ∀ i : Fin 5, t i.castSucc = u i.castSucc) :
    (jointSignature n e q om b t).1 = (jointSignature n e q om b u).1 ∧
    (jointSignature n e q om b t).2.1 = (jointSignature n e q om b u).2.1 := by
  exact ⟨congrArg _ (funext h4), congrArg _ (funext h5)⟩

/-- Exact code equalities on the original below-mu87 source. This is
independent of trim membership and of any positivity or approximation bound. -/
theorem raw_codes_at_own_ancestors (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre)) :
    ∃ b ∈ thirdAlphabet (data e q om).e (data e q om).chi (data e q om).m,
      originalSeed (data e q om) N pre = (b : ℝ) ∧
      (fourthProgram (data e q om) b).eval
        (primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre)) =
          exponent4 (data e q om) N (rosserAncestor 4 pre) ∧
      (fifthProgram (data e q om) b).eval
        (primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre)) =
          exponent5 (data e q om) N (rosserAncestor 5 pre) ∧
      (completeProgram (data e q om) b).eval
        (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) =
          currentSixthExponent e q om N (rosserAncestor 6 pre) := by
  let d := data e q om
  obtain ⟨b, hbmem, hbval⟩ := Finset.mem_image.mp (originalSeed_mem d N pre)
  have h3 : lambda3 d N pre = originalSeed d N pre := by
    have h := P4AOriginalFull87CompleteSixthBound.actual_third_eq_original d N pre hlen c hs
    change lambda3 d N (rosserAncestor 4 pre) = originalSeed d N pre at h
    rwa [lambda3_ancestor d N 4 (by decide)] at h
  have hb (k : ℕ) (hk : 3 ≤ k) : lambda3 d N (rosserAncestor k pre) = (b : ℝ) := by
    rw [lambda3_ancestor d N k hk, h3, ← hbval]
  refine ⟨b, hbmem, hbval.symm, ?_, ?_, ?_⟩
  · exact fourth_at_history d b N _ (by simp [hlen]) (hb 4 (by decide))
  · exact fifth_at_history d b N _ (by simp [hlen]) (hb 5 (by decide))
  · exact completeProgram_at_history e q om N b _ (by simp [hlen]) (hb 6 (by decide))

/-- Output predicate only: each cap is obtained by a finite table lookup
on its OWN ancestor. The tables output rational constants, not raw reals. -/
def CompiledParents (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) : Prop :=
  ∃ b ∈ thirdAlphabet (data e q om).e (data e q om).chi (data e q om).m,
    originalSeed (data e q om) N pre = (b : ℝ) ∧
    cap4 n e q om N (rosserAncestor 4 pre) =
      scalarTable n b (fourthProgram (data e q om) b)
        ((code4 n e q om b).signature (primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre))) ∧
    cap5 n e q om N (rosserAncestor 5 pre) =
      scalarTable n b (fifthProgram (data e q om) b)
        ((code5 n e q om b).signature (primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre))) ∧
    cap6 n e q om N (rosserAncestor 6 pre) =
      scalarTable n b (completeProgram (data e q om) b)
        ((code6 n e q om b).signature (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)))

/-- No support, current-cap bound, table correctness, guard agreement or
frontier licence is an input. Original Source alone supplies the required
below-mu identification; the exact raw programs then supply every comparison. -/
theorem compiled_parents_on_source (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre)) :
    CompiledParents n e q om N pre := by
  obtain ⟨b, hb, hseed, h4, h5, h6⟩ := raw_codes_at_own_ancestors e q om N pre hlen c hs
  refine ⟨b, hb, hseed, ?_, ?_, ?_⟩
  · rw [scalarTable_exact, h4, cap4,
      originalSeed_ancestor _ _ 4 (by decide), hseed]
  · rw [scalarTable_exact, h5, cap5_eq_protect,
      originalSeed_ancestor _ _ 5 (by decide), hseed]
  · rw [scalarTable_exact, h6, cap6_eq_protect,
      originalSeed_ancestor _ _ 6 (by decide), hseed]

/-- A closed-box certificate really fixes the scalar output throughout
that box. The original source / seed slice is kept explicit; this theorem
does not assert that every archived rectangle satisfies the certificate. -/
theorem sixth_table_on_certified_box (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (b : ℚ)
    (s : (code6 n e q om b).Signature) (lo hi : Fin 6 → ℝ)
    (hc : (code6 n e q om b).BoxCertificate s lo hi)
    (N : ℝ) (pre : List ℕ) (hlen : pre.length = 8) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre))
    (hb : originalSeed (data e q om) N pre = (b : ℝ))
    (hlo : ∀ i, lo i ≤ primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre) i)
    (hhi : ∀ i, primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre) i ≤ hi i) :
    cap6 n e q om N (rosserAncestor 6 pre) =
      scalarTable n b (completeProgram (data e q om) b) s := by
  have hr := (code6 n e q om b).boxCertificate_sound s lo hi hc _ hlo hhi
  obtain ⟨b', _, hseed', _, _, h6⟩ := raw_codes_at_own_ancestors e q om N pre hlen c hs
  have hbb : b' = b := by exact_mod_cast hseed'.symm.trans hb
  subst b'
  rw [scalarTable_on_region n b _ s _ hr.1, h6, cap6_eq_protect,
    originalSeed_ancestor _ _ 6 (by decide), hb]

/-- Same existing finite-parent policy, source states and original e/q
schedule. There is no new surrogate rho or swapped state list.
The omitted budget is still volume only; no analytical reserve is spent. -/
theorem exists_shared_finite_guard_schedule (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ r n0 : ℕ, ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 11 / 64000 ∧
      totalOmitted r (fun _ _ => (1 : ℝ)) < epsilon ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ n : ℕ, n0 ≤ n → ∀ om : ℝ, om ≤ 1 / 100 →
      ∀ N : ℕ, 1 < (N : ℝ) → ∀ p : Fin 8 → ℕ,
      (∀ i, (p i).Prime) → (∀ i, ¬p i ∣ N) →
      ∀ c : Cell, point (N : ℝ) p ∈ trim c (width r) →
        RealizedHistory e q om (N : ℝ) (pre p) c ∧
        ParentBounds n e q om (N : ℝ) (pre p) c ∧
        CompiledParents n e q om (N : ℝ) (pre p) ∧
        (∀ enumerationCap : ℕ, ∀ w z : ℝ,
          w ≤ (N : ℝ) ^ (53 / 13824 : ℝ) →
          (N : ℝ)^VariableEnvelope.mu ≤ z → z ≤ (enumerationCap : ℝ) →
          ∀ weight : ℕ → ℝ,
          canonicalState N enumerationCap w weight p ∈
            P4AOriginalFull87FiniteParentRealization.states
              (width r) n e q om N enumerationCap w z weight c) := by
  obtain ⟨r, n0, e0, he0, hemax, hvolume, hchoose⟩ :=
    P4AOriginalFull87FiniteParentRealization.exists_shared_finite_parent_schedule epsilon hepsilon
  refine ⟨r, n0, e0, he0, hemax, hvolume, ?_⟩
  intro e he hee
  obtain ⟨q0, hq0, hh⟩ := hchoose e he hee
  refine ⟨q0, hq0, ?_⟩
  intro q hq n hn om hom N hN p hp hdelete c ht
  obtain ⟨hreal, hparent, _, _, _, _, _, _, _, _, hmember⟩ :=
    hh q hq n hn om hom N hN p hp hdelete c ht
  have hs := trim_subset_source c (width_pos r) ht
  exact ⟨hreal, hparent,
    compiled_parents_on_source n e q om (N : ℝ) (pre p) (pre_length p) c hs, hmember⟩

end
end ImbalancedChen.P4AOriginalFull87AffineGuardRealization
