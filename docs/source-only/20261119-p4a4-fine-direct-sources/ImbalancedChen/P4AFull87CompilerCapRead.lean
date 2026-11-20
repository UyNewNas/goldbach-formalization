import ImbalancedChen.P4AOriginalFull87LicensedSixthPolicy
import ImbalancedChen.P4AHeldTaggedFiniteAdmissionPayment

/-! Coarse cap reads of the original licensed tree. A missing read preserves
the original policy decision, including the variable inherited fallback. -/
namespace ImbalancedChen.P4AFull87CompilerCapRead
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87FiniteParentPolicy (active)
open P4AOriginalFull87FiniteParentCaps (cap5)
open P4AOriginalSixthLicensedFilter (licensedCap)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap)
open P4AOriginalFull87LicensedSixthPolicy (policy)

/-- Each entry is a frozen scalar actually used in the licensed tree. -/
inductive Stage | fifth | sixth | eighth
  deriving DecidableEq, Fintype

def levels (n : ℕ) (e : ℚ) (q : ℕ) : Finset ℝ :=
  (P4AOriginalFull87FiniteParentCaps.alphabet n e q).image (fun a => (a : ℝ)) ∪
  (P4AOriginalFull87FiniteEighthCap.alphabet n).image (fun a => (a : ℝ))

def readStage (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (h : List ℕ) : Stage → Option ℝ
  | .fifth => let a := rosserAncestor 5 h
              if active e q om N a then some (cap5 n e q om N a) else none
  | .sixth => let a := rosserAncestor 6 h
              if active e q om N a then some (licensedCap n e q om N a) else none
  | .eighth => (selectedCap delta n N (rosserAncestor 8 h)).map fun a => (a : ℝ)

theorem readStage_mem {delta : ℝ} (hd : 0 < delta) (n : ℕ) (e : ℚ)
    (q : ℕ) (om N : ℝ) (h : List ℕ) (s : Stage) {a : ℝ}
    (ha : readStage delta n e q om N h s = some a) : a ∈ levels n e q := by
  cases s with
  | fifth =>
    simp only [readStage] at ha
    split at ha
    · cases ha
      exact Finset.mem_union_left _ (P4AOriginalFull87FiniteParentCaps.caps_mem_alphabet
        n e q om N (rosserAncestor 5 h)).2.1
    · contradiction
  | sixth =>
    simp only [readStage] at ha
    split at ha
    · cases ha
      exact Finset.mem_union_left _ (P4AOriginalSixthLicensedFilter.licensedCap_mem_alphabet
        n e q om N (rosserAncestor 6 h))
    · contradiction
  | eighth =>
    cases hs : selectedCap delta n N (rosserAncestor 8 h) with
    | none => simp [readStage, hs] at ha
    | some b =>
      have hb : (b : ℝ) = a := by simpa [readStage, hs] using ha
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨b, P4AOriginalFull87FiniteEighthPolicy.selectedCap_mem_alphabet
          delta hd n N _ b hs, hb⟩)

/-- A rejected eighth action inherits the sixth read on this same word. -/
def atRank (r : ℕ) (keys : Stage → Option ℝ) : Option ℝ :=
  if r ≤ 4 then none else if r ≤ 6 then keys .fifth else
  if r ≤ 8 then keys .sixth else
    match keys .eighth with
    | some a => some a
    | none => keys .sixth

theorem atRank_mem {delta : ℝ} (hd : 0 < delta) (n : ℕ) (e : ℚ)
    (q : ℕ) (om N : ℝ) (h : List ℕ) (r : ℕ) {a : ℝ}
    (ha : atRank r (readStage delta n e q om N h) = some a) : a ∈ levels n e q := by
  unfold atRank at ha
  split at ha
  · contradiction
  split at ha
  · exact readStage_mem hd n e q om N h .fifth ha
  split at ha
  · exact readStage_mem hd n e q om N h .sixth ha
  cases hs : readStage delta n e q om N h .eighth with
  | none =>
    exact readStage_mem hd n e q om N h .sixth (by simpa only [hs] using ha)
  | some b =>
    have heq : b = a := by simpa only [hs, Option.some.injEq] using ha
    exact readStage_mem hd n e q om N h .eighth (hs.trans (congrArg some heq))

private theorem eighth_ancestor (delta : ℝ) (n : ℕ) (N : ℝ) (h : List ℕ)
    (r : ℕ) (hr : 8 ≤ r) (hl : r ≤ h.length) :
    selectedCap delta n N (rosserAncestor r h) =
      selectedCap delta n N (rosserAncestor 8 h) := by
  have h1 : 8 ≤ (rosserAncestor r h).length := by simp [Nat.min_eq_left hl, hr]
  have h2 : 8 ≤ (rosserAncestor 8 h).length := by simp [Nat.min_eq_left (hr.trans hl)]
  simp only [selectedCap, P4AOriginalFull87SourceDispatch.ownerAtPrefix,
    P4AOriginalFull87SourceDispatch.point8, if_pos h1, if_pos h2,
    rosserAncestor_nested 8 r hr, rosserAncestor_nested 8 8 le_rfl]

/-- Exact Boolean test at the charged prefix, including every test built
into ordinaryRosserPrefixAdmissible. The rough modulus can have any rank. -/
theorem policy_at_read (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (h : List ℕ) (r : ℕ) (hr : r ≤ h.length) {a : ℝ}
    (ha : atRank r (readStage delta n e q om N h) = some a) :
    policy delta n e q om N false (rosserAncestor r h) =
      decide (ordinaryRosserPrefixAdmissible false (N ^ a) (rosserAncestor r h)) := by
  have hlen : (rosserAncestor r h).length = r := by simp [Nat.min_eq_left hr]
  by_cases h4 : r ≤ 4
  · simp [atRank,h4] at ha
  by_cases h6 : r ≤ 6
  · have h8 : r ≤ 8 := by omega
    have h5r : 5 ≤ r := by omega
    have hg : active e q om N (rosserAncestor 5 h) := by
      by_contra hn
      simp [atRank,h4,h6,readStage,hn] at ha
    have heq : cap5 n e q om N (rosserAncestor 5 h) = a := by
      simpa [atRank,h4,h6,readStage,hg] using ha
    simp [policy, P4AOriginalFull87LicensedSixthPolicy.sixthPolicy,
      P4AOriginalFull87FiniteParentPolicy.fifthPolicy, firstExitDepthSplicePolicy,
      hlen,h4,h6,h8,frozenParityRosserPolicy,ancestorFrozenPolicy,
      P4AOriginalFull87FiniteParentPolicy.level5Exponent,
      rosserAncestor_nested 5 r h5r,hg,heq,ordinaryParityRosserPolicy,oddFirstExitPolicy]
  have sixth (hk : readStage delta n e q om N h .sixth = some a) :
      P4AOriginalFull87LicensedSixthPolicy.sixthPolicy n e q om N false (rosserAncestor r h) =
        decide (ordinaryRosserPrefixAdmissible false (N ^ a) (rosserAncestor r h)) := by
    have hg : active e q om N (rosserAncestor 6 h) := by
      by_contra hn
      simp [readStage,hn] at hk
    have heq : licensedCap n e q om N (rosserAncestor 6 h) = a := by
      simpa [readStage,hg] using hk
    simp [P4AOriginalFull87LicensedSixthPolicy.sixthPolicy, firstExitDepthSplicePolicy,
      hlen,h6,frozenParityRosserPolicy,ancestorFrozenPolicy,
      P4AOriginalFull87LicensedSixthPolicy.level6Exponent,
      rosserAncestor_nested 6 r (by omega),hg,heq,ordinaryParityRosserPolicy,oddFirstExitPolicy]
  by_cases h8 : r ≤ 8
  · rw [P4AOriginalFull87LicensedSixthPolicy.through_eight delta n e q om N false _
      (hlen.trans_le h8)]
    exact sixth (by simpa only [atRank,if_neg h4,if_neg h6,if_pos h8] using ha)
  have hanc := eighth_ancestor delta n N h r (by omega) hr
  cases hs : selectedCap delta n N (rosserAncestor 8 h) with
  | none =>
    have hk : readStage delta n e q om N h .sixth = some a := by
      simpa only [atRank, if_neg h4, if_neg h6, if_neg h8, readStage, hs, Option.map_none] using ha
    simpa only [policy, firstExitDepthSplicePolicy, hlen, if_neg h8,
      P4AOriginalFull87LicensedSixthPolicy.eighthContinuation,hanc,hs] using sixth hk
  | some b =>
    have heq : (b : ℝ) = a := by simpa [atRank,h4,h6,h8,readStage,hs] using ha
    simp [policy,firstExitDepthSplicePolicy,hlen,h8,
      P4AOriginalFull87LicensedSixthPolicy.eighthContinuation,hanc,hs,heq,
      ordinaryParityRosserPolicy,oddFirstExitPolicy]

/-- Encode the three coarse stage reads with the *pre-N* alphabet. The
caller may append all other frozen history tags without losing these bits. -/
def bits (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (d : ℕ) : List Bool :=
  let K := Stage × (levels n e q : Type)
  List.ofFn fun j : Fin (Fintype.card K) =>
    let t := (Fintype.equivFin K).symm j
    decide (readStage delta n e q om N d.primeFactorsList t.1 = some t.2.val)

def tag (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (history : ℕ → List Bool) (d : ℕ) :=
  bits delta n e q om N d ++ history d

theorem reads_eq_of_tag_eq {delta : ℝ} (hd : 0 < delta) (n : ℕ) (e : ℚ)
    (q : ℕ) (om N : ℝ) (history : ℕ → List Bool) {d f : ℕ}
    (ht : tag delta n e q om N history f = tag delta n e q om N history d) :
    readStage delta n e q om N f.primeFactorsList =
      readStage delta n e q om N d.primeFactorsList := by
  let K := Stage × (levels n e q : Type)
  have hb := congrArg (List.take (Fintype.card K)) ht
  have len (x : ℕ) : (bits delta n e q om N x).length = Fintype.card K := by
    simp only [bits,List.length_ofFn,K]
  simp only [tag, List.take_left' (len f), List.take_left' (len d)] at hb
  unfold bits at hb
  have hf := List.ofFn_injective hb
  funext s
  have hiff (a : ℝ) (ha : a ∈ levels n e q) :
      readStage delta n e q om N f.primeFactorsList s = some a ↔
      readStage delta n e q om N d.primeFactorsList s = some a := by
    let t : K := (s, ⟨a,ha⟩)
    have hv := congrFun hf ((Fintype.equivFin K) t)
    have hv' : decide (readStage delta n e q om N f.primeFactorsList s = some a) =
        decide (readStage delta n e q om N d.primeFactorsList s = some a) := by
      simpa only [Equiv.symm_apply_apply,t] using hv
    constructor
    · intro hh
      exact of_decide_eq_true (hv'.symm.trans (decide_eq_true hh))
    · intro hh
      exact of_decide_eq_true (hv'.trans (decide_eq_true hh))
  cases hs : readStage delta n e q om N f.primeFactorsList s with
  | some a => exact ((hiff a (readStage_mem hd n e q om N _ s hs)).mp hs).symm
  | none =>
    cases hj : readStage delta n e q om N d.primeFactorsList s with
    | none => rfl
    | some b =>
      have hbad := (hiff b (readStage_mem hd n e q om N _ s hj)).mpr hj
      simp [hs] at hbad

end
end ImbalancedChen.P4AFull87CompilerCapRead
