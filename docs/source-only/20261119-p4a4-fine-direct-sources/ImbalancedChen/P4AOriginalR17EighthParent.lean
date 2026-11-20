import ImbalancedChen.P4AOriginalNonsingletonEighthParent

/-! The physical sixth parent on each original eighth trim, including
the four R17 actions and the full ordered-third policy. -/
namespace ImbalancedChen.P4AOriginalR17EighthParent
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary (Cell Point Source comparison)
open P4AOriginalFull87StrictActionTrim (trim trim_subset_source)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87EighthKernelControl
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P4AOriginalFull87UnionHistory (bank oldBank)
open P4AOriginalOrderedThirdFullPolicy (current prior six after cap6 cap6_prior after_prior root_on_old_owner)
open P4AOriginalFull87CompleteSixthBound (firstSix source_sixth_tents)

abbrev orderedSixth (n : ℕ) (e : ℚ) (q : ℕ) (a omega N : ℝ)
    (pos : Bool) (pre : List ℕ) :=
  six (current (bank e q a) omega N pre) (bank e q a) N n pos pre

abbrev orderedEighth (r n : ℕ) (e : ℚ) (q : ℕ) (a omega N : ℝ) :=
  P4AOriginalOrderedThirdFullPolicy.policy (width r) n (bank e q a) omega N

def parent (n : ℕ) (e : ℚ) (q : ℕ) (a omega N : ℝ) (word : List ℕ) : ℝ :=
  let d := bank e q a
  let pre := rosserAncestor 6 word
  let R := current d omega N pre
  if R.lower then cap6 R d N n pre else after R d N pre 8

/-- The original mask 17 belongs to the 63 physical first-six subsets in
every family. Its descending plane is the active plane on precisely the
side prescribed by row 3 of each of the four G14 sources. -/
theorem seventeenth_tent (c : Cell) (t : Point) (hs : Source c t) :
    VariableEnvelope.v (t 0+t 4) ≤ comparison c t := by
  have h := source_sixth_tents c t hs 17 (by decide)
  simpa [Certificates.P2OriginalSixthElevenLogSemantics.selectedSum,
    Certificates.P2OriginalSixthElevenLogSemantics.bit, firstSix, Fin.sum_univ_succ] using h

private theorem pair17_side (j : Fin 4) (u : Fin 6 → ℝ)
    (hs : P4AOriginalSixthLaterSemantics.Source (P4AOriginalNonsingletonComparison.action j) u) :
    VariableEnvelope.mu < u 0+u 4 := by
  let b : P4AOriginalSixthLaterLiteral.Affine := ![-25/128,1,0,0,0,1,0]
  let C := P4AOriginalNonsingletonComparison.action j
  have hb : 3 < (P4AOriginalSixthLaterLiteral.rows C).length ∧
      (P4AOriginalSixthLaterLiteral.rows C)[3]?=some b ∧ P4AOriginalSixthLaterLiteral.mapped C=false := by
    fin_cases j <;> exact ⟨by decide,rfl,rfl⟩
  have he : (P4AOriginalSixthLaterLiteral.rows C)[3] = b :=
    Option.some.inj (by simpa [hb.1] using hb.2.1)
  have hm : b ∈ P4AOriginalSixthLaterLiteral.rows C := he ▸ List.getElem_mem hb.1
  have hg := hs b hm
  change 0 < P4AOriginalSixthLaterSemantics.eval b (P4AOriginalSixthLaterSemantics.coordinates C u) at hg
  norm_num [P4AOriginalSixthLaterSemantics.eval,P4AOriginalSixthLaterSemantics.coordinates,
    hb.2.2,b,Fin.sum_univ_succ] at hg
  dsimp only [VariableEnvelope.mu]
  linarith

theorem pair17_on_overlap (j : Fin 4) (c : Cell) (t : Point) (hs : Source c t)
    (h6 : P4AOriginalSixthLaterSemantics.Source (P4AOriginalNonsingletonComparison.action j) (firstSix t)) :
    P4AOriginalSixthLaterSemantics.R17 (firstSix t) = VariableEnvelope.v (t 0+t 4) ∧
    P4AOriginalSixthLaterSemantics.R17 (firstSix t) ≤ comparison c t ∧
    P4AOriginalSixthLaterSemantics.endpoint (P4AOriginalNonsingletonComparison.action j) (firstSix t) <
      comparison c t := by
  have hside : VariableEnvelope.mu < t 0+t 4 := pair17_side j (firstSix t) h6
  have hr : P4AOriginalSixthLaterSemantics.R17 (firstSix t) = VariableEnvelope.v (t 0+t 4) := by
    rw [VariableEnvelope.v_eq_C hside.le]
    change 57/64-3*(t 0+t 4)/2 = 57/64-3/2*(t 0+t 4)
    ring
  exact ⟨hr,hr.trans_le (seventeenth_tent c t hs),
    P4AOriginalNonsingletonComparison.actual_candidate_below_eighth j c t hs h6⟩

/-- The selected eighth word is a supported member of the original
common mesh. Its third scalar and its lower/upper mode are therefore
identical for both third policies under the late cutoff. -/
theorem parent_on_owner (n : ℕ) (e : ℚ) (q : ℕ) (a omega N : ℝ)
    (he : 0≤e) (hN : 1≤N) (hcut : omega≤a) (word : List ℕ)
    (hsup : P1ThirdFallbackSupport.supported (e:ℝ) (bank e q a).chi (bank e q a).m
      a N (rosserAncestor 3 word)) :
    parent n e q a omega N word = P4AOriginalFull87UnionHistory.actualParent n e q a N word := by
  let d := bank e q a
  have h6 : P1ThirdFallbackSupport.frozenSupported d.e d.chi d.m d.omega N (rosserAncestor 6 word) := by
    change P1ThirdFallbackSupport.supported _ _ _ _ _ (rosserAncestor 3 (rosserAncestor 6 word))
    rw [rosserAncestor_nested 3 6 (by decide)]
    exact hsup
  have hR := root_on_old_owner (d:=d) (by exact_mod_cast he : 0≤(d.e:ℝ)) hN hcut h6
  change (if (current d omega N (rosserAncestor 6 word)).lower then _ else _) = _
  rw [hR,cap6_prior,after_prior] <;> rfl

/-- The bounds use the literal fifth bank and every saved, eleven and
later action. The unrounded bound reads each candidate's own source
tent. The finite bound uses its true rounded cap and buffer. -/
theorem compact_parent (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (he : 0≤e) (hcut : omega≤a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1<(N:ℝ)) (word : List ℕ) (hlen : word.length=8)
    (hp : ∀ p∈word,0<p) (c : Cell) (ht : primeHistoryLogCoordinates (N:ℝ) 8 word∈trim c (width r)) :
    let t := primeHistoryLogCoordinates (N:ℝ) 8 word
    let d := bank e q a
    let h6 := rosserAncestor 6 word
    after (current d omega N h6) d N h6 8 ≤ comparison c t ∧
    P5OriginalCommonRefinedConstructor.lambda3 (oldBank e q a) N (rosserAncestor 4 word) ≤
      parent n e q a omega N word ∧ parent n e q a omega N word ≤ comparison c t := by
  have hs := trim_subset_source c (width_pos r) ht
  have hr := hh N hN word hlen hp c ht
  have h6 : P1ThirdFallbackSupport.frozenSupported (bank e q a).e (bank e q a).chi
      (bank e q a).m (bank e q a).omega (N:ℝ) (rosserAncestor 6 word) := by
    change P1ThirdFallbackSupport.supported _ _ _ _ _ (rosserAncestor 3 (rosserAncestor 6 word))
    rw [rosserAncestor_nested 3 6 (by decide)]
    exact hr.2.1
  have heR : 0≤((bank e q a).e:ℝ) := by exact_mod_cast he
  refine ⟨?_,P4AOriginalNonsingletonEighthParent.ordered_cap_bounds n e q a omega N he hN.le hcut
    word hlen c hs hr.1 hr.2.1 hr.2.2.1⟩
  dsimp only
  rw [root_on_old_owner heR hN.le hcut h6,after_prior]
  exact P4AOriginalFull87UnionHistory.raw_current_le_comparison e q a N he word hlen c hs hr

theorem compact_kernel (r n : ℕ) (hn : 4*width n<width r) (e : ℚ) (q : ℕ)
    (a omega : ℝ) (he : 0≤e) (hcut : omega≤a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1<(N:ℝ)) (word : List ℕ) (hlen : word.length=8)
    (hp : ∀ p∈word,0<p) (c : Cell) (ht : primeHistoryLogCoordinates (N:ℝ) 8 word∈trim c (width r)) :
    let t := primeHistoryLogCoordinates (N:ℝ) 8 word
    let P := parent n e q a omega N word
    let M := (finiteCap n c t:ℝ)
    cutoff<t 7 ∧ t 7<P-total t ∧ P≤comparison c t ∧ comparison c t<M ∧ M-total t<3*t 7 ∧
      kernel c t≤residual (total t) (product t) P M+roundingConstant*width n := by
  dsimp only
  have hr := hh N hN word hlen hp c ht
  rw [parent_on_owner n e q a omega N he hN.le hcut word hr.2.1]
  exact P4AOriginalFull87UnionHistory.actual_eighth_kernel_transport r n hn e q a N he word hlen c ht hr

end
end ImbalancedChen.P4AOriginalR17EighthParent
