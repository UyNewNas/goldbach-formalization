import ImbalancedChen.P4AFull87HistoricalCompilerRate

namespace ImbalancedChen.P4AFull87DataCompilerReads
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor
open P4AOriginalFull87DataPolicy (policy fifthPolicy sixthPolicy level5Exponent level6Exponent
  cap5 licensedCap active active_ancestor)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap)
open P4AOriginalFull87FiniteParentCaps (thirdAlphabet originalSeed_mem)
open P1GuardFrozenFiniteCapAlgebra P4AFull87SamePieceCapVariation (readWord word_inj)
open P4ACommonPolicyTaggedCompiler (historicalTag stageTag)
open P4AFull87HistoricalCompilerRate (selected_on_ancestor)

def scalars (n : ℕ) (d : OriginalData) : Finset ℝ :=
  ((thirdAlphabet d.e d.chi d.m ∪ roundedAlphabet n).image fun q => (q:ℝ)) ∪
    ((P4AOriginalFull87FiniteEighthCap.alphabet n).image fun q => (q:ℝ))

theorem cap5_mem (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    cap5 n d N pre ∈ scalars n d := by
  apply Finset.mem_union_left
  rw [P4AOriginalFull87DataPolicy.cap5_eq_protect]
  exact protect_mem_union n _ _ _ (originalSeed_mem d N pre)

theorem cap6_mem (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    licensedCap n d N pre ∈ scalars n d := by
  unfold licensedCap
  rcases finiteMax_attained P4AOriginalSixthActionBank.allActions
    (P4AOriginalFull87DataPolicy.Accepted n d N pre)
    (fun a => (rounded n (P4AOriginalSixthActionBank.endpoint a (primeHistoryLogCoordinates N 6 pre)) : ℝ))
    (cap5 n d N (rosserAncestor 5 pre)) with he | ⟨a,_,_,he⟩
  · rw [he]; exact cap5_mem n d N _
  · rw [he]
    exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨_,Finset.mem_union_right _ (rounded_mem n _),rfl⟩)

abbrev Reads (n : ℕ) (d : OriginalData) := Option (scalars n d : Type) ×
  Option (scalars n d : Type) × Option (scalars n d : Type)

def reads (delta : ℝ) (hdelta : 0 < delta) (n : ℕ) (d : OriginalData) (N : ℕ) (x : ℕ) :
    Reads n d :=
  let h := x.primeFactorsList
  let f := rosserAncestor 5 h
  let s := rosserAncestor 6 h
  let e := rosserAncestor 8 h
  (if active d N f then some ⟨_,cap5_mem n d N f⟩ else none,
   if active d N s then some ⟨_,cap6_mem n d N s⟩ else none,
   match he : selectedCap delta n N e with
   | none => none
   | some a => some ⟨(a:ℝ),Finset.mem_union_right _ (Finset.mem_image.mpr
       ⟨a,P4AOriginalFull87FiniteEighthPolicy.selectedCap_mem_alphabet delta hdelta n N e a he,rfl⟩)⟩)

def tag (delta : ℝ) (hdelta : 0 < delta) (n : ℕ) (d : OriginalData) (N x : ℕ) :=
  readWord (reads delta hdelta n d N x) ++ historicalTag d N x

theorem read_tag {delta : ℝ} (hdelta : 0 < delta) {n : ℕ} {d : OriginalData} {N x y : ℕ}
    (ht : tag delta hdelta n d N x=tag delta hdelta n d N y) :
    reads delta hdelta n d N x=reads delta hdelta n d N y ∧ historicalTag d N x=historicalTag d N y := by
  let B := Fintype.card (Reads n d)
  have L (z : ℕ) : (readWord (reads delta hdelta n d N z)).length=B := List.length_ofFn
  exact ⟨word_inj (by simpa only [tag,List.take_left' (L x),List.take_left' (L y)] using
    congrArg (List.take B) ht),by simpa only [tag,List.drop_left' (L x),List.drop_left' (L y)] using
    congrArg (List.drop B) ht⟩

inductive Mode (A : Type) | common | oldFifth | fixed (a : A) | native

def mode {n : ℕ} {d : OriginalData} (r : ℕ) (q : Reads n d) : Mode (scalars n d : Type) :=
  let s := q.2.1.elim .native .fixed
  if r≤4 then .common else if r≤6 then q.1.elim .oldFifth .fixed
  else if r≤8 then s else q.2.2.elim s .fixed

def evaluate (d : OriginalData) (N r x : ℕ) {A : Finset ℝ} : Mode (A : Type) → Bool
  | .common => common3 d N false (rosserAncestor r x.primeFactorsList)
  | .oldFifth => policy5 d N false (rosserAncestor r x.primeFactorsList)
  | .fixed a => decide (ordinaryRosserPrefixAdmissible false ((N:ℝ)^a.val) (rosserAncestor r x.primeFactorsList))
  | .native => decide (ordinaryRosserPrefixAdmissible false
      ((N:ℝ)^(P4AOriginalFull87DataPolicy.currentSixthExponent d N (rosserAncestor 6 x.primeFactorsList)))
      (rosserAncestor r x.primeFactorsList))

theorem policy_read (delta : ℝ) (hdelta : 0 < delta) (n : ℕ) (d : OriginalData)
    (N r x : ℕ) (hr : r ≤ x.primeFactorsList.length) :
    policy delta n d N false (rosserAncestor r x.primeFactorsList) =
      evaluate d N r x (mode r (reads delta hdelta n d N x)) := by
  let h := x.primeFactorsList
  have hlen : (rosserAncestor r h).length=r := by simp [h,Nat.min_eq_left hr]
  by_cases h4 : r≤4
  · have h6 : r≤6 := by omega
    have h8 : r≤8 := by omega
    simp [h,policy,sixthPolicy,fifthPolicy,firstExitDepthSplicePolicy,hlen,h4,h6,h8,mode,evaluate]
  by_cases h6 : r≤6
  · have h8 : r≤8 := by omega
    by_cases ha : active d N (rosserAncestor 5 h) <;>
      simp [h,policy,sixthPolicy,fifthPolicy,policy5,level5,firstExitDepthSplicePolicy,hlen,
        frozenParityRosserPolicy,ancestorFrozenPolicy,level5Exponent,rosserAncestor_nested 5 r (by omega),
        h4,h6,h8,mode,reads,ha,evaluate,ordinaryParityRosserPolicy,oddFirstExitPolicy] at *
  let q := reads delta hdelta n d N x
  have base : sixthPolicy n d N false (rosserAncestor r h)=
      evaluate d N r x (q.2.1.elim .native .fixed) := by
    by_cases ha : active d N (rosserAncestor 6 h) <;>
      simp [q,reads,h,sixthPolicy,firstExitDepthSplicePolicy,hlen,h6,
        frozenParityRosserPolicy,ancestorFrozenPolicy,level6Exponent,rosserAncestor_nested 6 r (by omega),
        ha,evaluate,ordinaryParityRosserPolicy,oddFirstExitPolicy] at *
  by_cases h8 : r≤8
  · simpa only [policy,firstExitDepthSplicePolicy,hlen,if_pos h8,mode,if_neg h4,if_neg h6] using base
  · have he := selected_on_ancestor delta n N h r (by omega) hr
    cases hcap : selectedCap delta n N (rosserAncestor 8 h) with
    | none =>
      simpa [policy,firstExitDepthSplicePolicy,hlen,h8,P4AOriginalFull87DataPolicy.eighthContinuation,
        he,hcap,mode,h4,h6,reads,q] using base
    | some a =>
      simp [policy,firstExitDepthSplicePolicy,hlen,h8,P4AOriginalFull87DataPolicy.eighthContinuation,
        he,hcap,mode,h4,h6,reads,evaluate,ordinaryParityRosserPolicy,oddFirstExitPolicy]

theorem mode_bounds {n : ℕ} {d : OriginalData} (r : ℕ) (q : Reads n d) :
    (mode r q = .common → r≤4) ∧ (mode r q = .oldFifth → r≤6) ∧
    (mode r q = .native → 6<r) := by
  rcases q with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> unfold mode <;> split_ifs <;> simp_all <;> omega

private theorem blocks {F G : ℕ → List Bool} (n : ℕ)
    (hF : ∀ x, (F x).length=n) (hG : ∀ x, (G x).length=n) :
    ∀ xs : List ℕ, xs.flatMap F=xs.flatMap G → ∀ i ∈ xs, F i=G i := by
  intro xs
  induction xs with
  | nil => simp
  | cons a xs ih =>
    intro h i hi
    change F a++xs.flatMap F=G a++xs.flatMap G at h
    rcases List.mem_cons.mp hi with rfl | ht
    · simpa only [List.take_left' (hF a),List.take_left' (hG a)] using congrArg (List.take n) h
    · exact ih (by simpa only [List.drop_left' (hF a),List.drop_left' (hG a)] using
        congrArg (List.drop n) h) i ht

private theorem parity (p : Bool) (xs : List ℕ) :
    polarityAfter p xs.length = if evenListLength xs then p else !p := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih => rw [List.length_cons,polarityAfter,ih,evenListLength]
                    cases evenListLength xs <;> cases p <;> rfl

theorem early_agree (d : OriginalData) (N x y r : ℕ) (hr : r≤6)
    (hx : r ≤ x.primeFactorsList.length) (hy : r ≤ y.primeFactorsList.length)
    (ht : historicalTag d N x = historicalTag d N y) (ho : polarityAfter true r=false) :
    common3 d N false (rosserAncestor r x.primeFactorsList) =
      common3 d N false (rosserAncestor r y.primeFactorsList) ∧
    policy5 d N false (rosserAncestor r x.primeFactorsList) =
      policy5 d N false (rosserAncestor r y.primeFactorsList) := by
  let F (z i : ℕ) := stageTag d N (rosserAncestor i z.primeFactorsList)
  have hblocks : (List.range 9).flatMap (F x)=(List.range 9).flatMap (F y) := ht
  have hb := blocks 5 (F := F x) (G := F y) (fun _ => rfl) (fun _ => rfl)
    _ hblocks r (List.mem_range.mpr (by omega))
  have par (z : ℕ) (hz : r≤z.primeFactorsList.length) :
      evenListLength (rosserAncestor r z.primeFactorsList)=false := by
    have hlen : (rosserAncestor r z.primeFactorsList).length=r := by simp [Nat.min_eq_left hz]
    have hp := ho
    rw [← hlen,parity] at hp
    cases he : evenListLength (rosserAncestor r z.primeFactorsList) <;> simp_all
  have h3 := congrArg (fun lst : List Bool => lst[1]?) hb
  have h5 := congrArg (fun lst : List Bool => lst[3]?) hb
  change some (common3 _ _ _ _) = some (common3 _ _ _ _) at h3
  change some (policy5 _ _ _ _) = some (policy5 _ _ _ _) at h5
  simpa only [par x hx,par y hy] using And.intro (Option.some.inj h3) (Option.some.inj h5)

end
end ImbalancedChen.P4AFull87DataCompilerReads
