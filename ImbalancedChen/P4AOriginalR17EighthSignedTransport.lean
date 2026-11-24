import ImbalancedChen.P4AOriginalR17EighthParent
import ImbalancedChen.P4AUpperTaggedMixedWallPayment

/-! Exact signed transport at the canonical modulus. All branch decisions
of a selected eighth word have the same historical third owner. If its
eighth ancestor has no action, its sixth and eighth decisions coincide
at every rank, including the complete residual word. -/
namespace ImbalancedChen.P4AOriginalR17EighthSignedTransport
noncomputable section
open scoped Classical BigOperators
open P4AOriginalR17EighthParent (orderedSixth orderedEighth)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P4AOriginalFull87UnionHistory (bank sixthPolicy policy)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap selectedCap_some_spec)
open P4AOriginalFull87SourceDispatch (ownerAtPrefix point8)
open P4AOriginalOrderedThirdFullPolicy (Root current prior base common five six eight
  root_on_old_owner six_prior original_evaluation)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AUpperTaggedParityCompiler (universe rawSupport rawSupport_subset_universe raw_value)
open P4AUpperTaggedMixedWallPayment (raw_support_iff_canonical_validSelection)
open P4AOriginalVariableFifthPhysicalLedger (raw)

private theorem selection_reads (u v : List ℕ → Bool) (xs pre : List ℕ) (pos : Bool)
    (h : ∀ k≤(xs.reverse++pre).length,
      u (rosserAncestor k (xs.reverse++pre))=v (rosserAncestor k (xs.reverse++pre))) :
    FirstExitValidSelection (oddFirstExitPolicy u) pre pos xs ↔
    FirstExitValidSelection (oddFirstExitPolicy v) pre pos xs := by
  induction xs generalizing pre pos with
  | nil => rfl
  | cons x xs ih =>
    have hj : (x::xs).reverse++pre=xs.reverse++(x::pre) := by simp
    rw [hj] at h
    have hl : (x::pre).length≤(xs.reverse++(x::pre)).length := by simp
    have hx := h (x::pre).length hl
    rw [rosserAncestor_append _ xs.reverse (x::pre) le_rfl,
      rosserAncestor_self_of_length _ _ rfl] at hx
    simp only [FirstExitValidSelection,oddFirstExitPolicy,hx]
    exact and_congr_right (fun _ => ih (x::pre) (!pos) h)

private theorem coefficient_reads (u v : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (x : ℕ)
    (h : ∀ k≤x.primeFactorsList.length,
      u (rosserAncestor k x.primeFactorsList)=v (rosserAncestor k x.primeFactorsList)) :
    fixedRoughCoefficient u N cap w z x=fixedRoughCoefficient v N cap w z x := by
  have hv := selection_reads u v x.primeFactorsList.reverse [] true (by simpa only
    [List.reverse_reverse,List.append_nil] using h)
  have hs : x∈rawSupport u N cap w z ↔ x∈rawSupport v N cap w z := by
    rw [raw_support_iff_canonical_validSelection,raw_support_iff_canonical_validSelection]
    exact and_congr_right (fun _ => hv)
  change P4AUpperTaggedParityCompiler.raw u _ _ _ _ x=P4AUpperTaggedParityCompiler.raw v _ _ _ _ x
  rw [raw_value,raw_value,propext hs]

private theorem selected_ancestor (delta : ℝ) (n : ℕ) (N : ℝ) (word : List ℕ)
    (k : ℕ) (hk : 8≤k) (hl : k≤word.length) :
    selectedCap delta n N (rosserAncestor k word)=selectedCap delta n N word := by
  have h8w := hk.trans hl
  have h8p : 8≤(rosserAncestor k word).length := by
    rw [rosserAncestor_length,min_eq_left hl]
    exact hk
  simp only [selectedCap,ownerAtPrefix,if_pos h8w,if_pos h8p,point8,rosserAncestor_nested 8 k hk]

private theorem short_six (R S : Root) (d : OriginalData) (N : ℝ) (n : ℕ)
    (b : Bool) (p : List ℕ) (h : p.length≤2) :
    six R d N n b p=six S d N n b p := by
  have h3 : p.length≤3 := by omega
  have h4 : p.length≤4 := by omega
  have h6 : p.length≤6 := by omega
  simp only [six,five,common,base,firstExitDepthSplicePolicy,if_pos h6,if_pos h4,if_pos h3,if_pos h]

private theorem inherited_read (R : Root) (d : OriginalData) (N delta : ℝ) (n : ℕ)
    (word : List ℕ) (ho : selectedCap delta n N word=none) (k : ℕ) (hk : k≤word.length) (b : Bool) :
    six R d N n b (rosserAncestor k word)=eight R d N delta n b (rosserAncestor k word) := by
  by_cases h : (rosserAncestor k word).length≤8
  · simp only [eight,firstExitDepthSplicePolicy,if_pos h]
  · have h8 : 8≤k := by rw [rosserAncestor_length,min_eq_left hk] at h; omega
    have hx := (selected_ancestor delta n N word k h8 hk).trans ho
    simp only [eight,firstExitDepthSplicePolicy,if_neg h,hx]

/-- Every rank reads the same previous policy on a selected word.
The first two ranks precede the third cap. All later ranks read its
same frozen third ancestor, including ranks greater than eight. -/
private theorem selected_word_reads (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (he : 0≤e) (hcut : omega≤a) (hh : HistoryOnTrim r e q a) (N : ℕ)
    (hN : 1<(N:ℝ)) (word : List ℕ) (hp : ∀ p∈word,0<p) (v : ℚ)
    (hv : selectedCap (width r) n N word=some v) (k : ℕ) (hk : k≤word.length) (b : Bool) :
    let p := rosserAncestor k word
    orderedSixth n e q a omega N b p=sixthPolicy n e q a N b p ∧
    orderedEighth r n e q a omega N b p=policy (width r) n e q a N b p := by
  let d := bank e q a
  let p := rosserAncestor k word
  obtain ⟨c,ho,ht,_⟩ := selectedCap_some_spec _ _ _ _ _ hv
  have hl : 8≤word.length := by
    by_contra h
    simp [ownerAtPrefix,h] at ho
  have hl8 : (rosserAncestor 8 word).length=8 := by simp [min_eq_left hl]
  have hp8 : ∀ x∈rosserAncestor 8 word,0<x := fun x hx =>
    hp x ((List.drop_sublist _ _).subset hx)
  have hr := hh N hN _ hl8 hp8 c ht
  have hsup : P1ThirdFallbackSupport.supported (d.e:ℝ) d.chi d.m d.omega N (rosserAncestor 3 word) := by
    simpa only [rosserAncestor_nested 3 8 (by decide)] using hr.2.1
  have heR : 0≤(d.e:ℝ) := by exact_mod_cast he
  have h6 : six (current d omega N p) d N n b p=six (prior d N p) d N n b p ∧
      eight (current d omega N p) d N (width r) n b p=eight (prior d N p) d N (width r) n b p := by
    by_cases hk3 : 3≤k
    · have hs : P1ThirdFallbackSupport.frozenSupported d.e d.chi d.m d.omega N p := by
        change P1ThirdFallbackSupport.supported _ _ _ _ _ (rosserAncestor 3 (rosserAncestor k word))
        rw [rosserAncestor_nested 3 k hk3]
        exact hsup
      have eqRoot := root_on_old_owner heR hN.le hcut hs
      exact ⟨congrArg (fun R => six R d N n b p) eqRoot,
        congrArg (fun R => eight R d N (width r) n b p) eqRoot⟩
    · have h2 : p.length≤2 := by change (rosserAncestor k word).length≤2; rw [rosserAncestor_length]; omega
      have h8 : p.length≤8 := by omega
      have hshort := short_six (current d omega N p) (prior d N p) d N n b p h2
      exact ⟨hshort,by simpa only [eight,firstExitDepthSplicePolicy,if_pos h8] using hshort⟩
  exact ⟨h6.1.trans (six_prior n d N b p),h6.2.trans (original_evaluation (width r) n d N b p)⟩

/-- Same signed Möbius coefficient at every original modulus, for the
complete canonical prime word and every rough carrier. -/
theorem coefficient_difference (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (he : 0≤e) (hcut : omega≤a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1<(N:ℝ)) (cap : ℕ) (w z : ℝ) (x : ℕ) :
    fixedRoughCoefficient (orderedSixth n e q a omega N false) N cap w z x -
      fixedRoughCoefficient (orderedEighth r n e q a omega N false) N cap w z x =
    fixedRoughCoefficient (sixthPolicy n e q a N false) N cap w z x -
      fixedRoughCoefficient (policy (width r) n e q a N false) N cap w z x := by
  let word := x.primeFactorsList
  let d := bank e q a
  have hp : ∀ p∈word,0<p := fun p hp => (Nat.prime_of_mem_primeFactorsList hp).pos
  cases ho : selectedCap (width r) n (N:ℝ) word with
  | none =>
    have ha := coefficient_reads (orderedSixth n e q a omega N false)
      (orderedEighth r n e q a omega N false) N cap w z x (fun k hk =>
        inherited_read (current d omega N (rosserAncestor k word)) d N (width r) n word ho k hk false)
    have hb := coefficient_reads (sixthPolicy n e q a N false)
      (policy (width r) n e q a N false) N cap w z x (fun k hk =>
        (six_prior n d N false (rosserAncestor k word)).symm.trans
          ((inherited_read (prior d N (rosserAncestor k word)) d N (width r) n word ho k hk false).trans
            (original_evaluation (width r) n d N false (rosserAncestor k word))))
    simp only [ha,hb,sub_self]
  | some v =>
    have h := selected_word_reads r n e q a omega he hcut hh N hN word hp v ho
    exact congrArg₂ (fun y z : ℝ => y-z)
      (coefficient_reads _ _ N cap w z x (fun k hk => (h k hk false).1))
      (coefficient_reads _ _ N cap w z x (fun k hk => (h k hk false).2))

private theorem raw_on_universe (s : Bool → List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    raw s N cap w z =
      ∑ x ∈ universe N cap w z, P4AUpperTaggedParityCompiler.raw (s false) N cap w z x/(Nat.totient x:ℝ) := by
  change (∑ x ∈ rawSupport (s false) N cap w z,
    P4AUpperTaggedParityCompiler.raw (s false) N cap w z x/(Nat.totient x:ℝ)) = _
  apply Finset.sum_subset (rawSupport_subset_universe (s false) N cap w z)
  intro x _ hx
  rw [raw_value,if_neg hx,zero_div]

theorem raw_difference (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (he : 0≤e) (hcut : omega≤a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1<(N:ℝ)) (cap : ℕ) (w z : ℝ) :
    raw (orderedSixth n e q a omega N) N cap w z-raw (orderedEighth r n e q a omega N) N cap w z =
    raw (sixthPolicy n e q a N) N cap w z-raw (policy (width r) n e q a N) N cap w z := by
  simp only [raw_on_universe,← Finset.sum_sub_distrib,← sub_div]
  exact Finset.sum_congr rfl (fun x _ => congrArg (fun b : ℝ => b/(Nat.totient x:ℝ))
    (coefficient_difference r n e q a omega he hcut hh N hN cap w z x))

end
end ImbalancedChen.P4AOriginalR17EighthSignedTransport
