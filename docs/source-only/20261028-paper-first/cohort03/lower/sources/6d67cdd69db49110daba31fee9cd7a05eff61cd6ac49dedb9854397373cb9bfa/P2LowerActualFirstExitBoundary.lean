import ImbalancedChen.P2LowerChronologicalFirstChange
import ImbalancedChen.P2LowerCanonicalRetainedTrace
import ImbalancedChen.P2OriginalLowerParentFrozenStageExistence

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / HELD.
-- Exact first-exit and literal rawSupport chronology for the original
-- lower coefficient. The policy may be the corrected compact [epsilon,w]
-- plan, but its selected support-mask licence remains a separate witness.
-- A cell-upper firstStop is a sufficient whole-box test, not an exact
-- replacement for the integer Trace admission predicate.

namespace ImbalancedChen.P2LowerActualFirstExitBoundary

noncomputable section
open scoped Classical
open P2LowerCapPlanIntegerRetention P2LowerFiniteCellRounding
open P2LowerCanonicalRetainedTrace P2LowerChronologicalFirstChange
open P2OriginalLowerParentFrozenStageExistence
open P2OriginalLowerCompactStartCapConstructor

-- At an even selected rank the tree's select branch is present exactly
-- when the *old* retained history passes the actual incoming-cap test.
-- The new cap is frozen only afterward by Trace.step.
theorem even_select_iff_actual_incoming_gate {depth mesh : ℕ}
    (P : CapPlan depth mesh) (a b seed : ℝ) (N p : ℕ)
    (history : List ℕ) (hpos : 0<history.length)
    (heven : (history.length+1)%2=0) :
    evenFirstExitPolicy (retainEven P a b seed N) true (p::history)=true ↔
      retainEven P a b seed N history=true ∧
        (physicalWord N history).sum+3*coordinate N p<
          (integerTrace P a b seed N history).cap := by
  change retainEven P a b seed N (p::history)=true ↔ _
  constructor
  · intro h
    obtain ⟨hparent,hgate⟩ :=
      (retainEven_cons_iff P a b seed N p history).mp h
    exact ⟨hparent,(even_rank_cube P a b seed N p history hpos heven).mp hgate⟩
  · rintro ⟨hparent,hgate⟩
    exact (retainEven_cons_iff P a b seed N p history).mpr
      ⟨hparent,(even_rank_cube P a b seed N p history hpos heven).mpr hgate⟩

-- With the incoming history actually retained, this is the exact first
-- stop condition. Its weak inequality includes the arithmetic equality
-- wall. An upper-corner `firstStop` is deliberately not substituted.
theorem even_first_stop_iff_actual_cube_nonpass {depth mesh : ℕ}
    (P : CapPlan depth mesh) (a b seed : ℝ) (N p : ℕ)
    (history : List ℕ) (hpos : 0<history.length)
    (heven : (history.length+1)%2=0)
    (hparent : retainEven P a b seed N history=true) :
    evenFirstExitPolicy (retainEven P a b seed N) true (p::history)=false ↔
      (integerTrace P a b seed N history).cap≤
        (physicalWord N history).sum+3*coordinate N p := by
  have hselect := even_select_iff_actual_incoming_gate P a b seed N p
    history hpos heven
  constructor
  · intro hstop
    by_contra hn
    have hgate : (physicalWord N history).sum+3*coordinate N p<
        (integerTrace P a b seed N history).cap := lt_of_not_ge hn
    have htrue := hselect.mpr ⟨hparent,hgate⟩
    exact Bool.false_ne_true (hstop.symm.trans htrue)
  · intro hge
    by_cases htrue : evenFirstExitPolicy (retainEven P a b seed N)
        true (p::history)=true
    · exact False.elim ((not_lt_of_ge hge) (hselect.mp htrue).2)
    · cases hval : evenFirstExitPolicy (retainEven P a b seed N)
          true (p::history) with
      | false => rfl
      | true => exact False.elim (htrue hval)

-- If an actual even test fails, the select subtree is literally absent;
-- the skip subtree keeps its incoming selected history and parent cap.
theorem failed_even_select_prunes_subtree
    (retainEven : List ℕ → Bool) (h : ℕ → ℝ)
    (history : List ℕ) (mass : ℝ) (p : ℕ) (remaining : List ℕ)
    (hfail : retainEven (p::history)=false) :
    firstExitRetainedLeaves (evenFirstExitPolicy retainEven) h
      history false mass (p::remaining)=
    firstExitRetainedLeaves (evenFirstExitPolicy retainEven) h
      history false mass remaining := by
  simp [firstExitRetainedLeaves,evenFirstExitPolicy,hfail]

-- A rank-four integer cube failure against its actual frozen rank-three
-- cap therefore becomes a first exit in the recursive tree. This uses the
-- CapPlan frozen-parent theorem, not a later ideal C3 or new fourth cap.
theorem compact_rank_four_failed_select_prunes_subtree (S : CompactStart)
    {mesh : ℕ} (table : BranchTable mesh) (rho : ℝ)
    (N p : ℕ) (history : List ℕ) (remaining : List ℕ) (mass : ℝ)
    (hlen : history.length=3)
    (hfail :
      (integerTrace (compactPlan S table rho)
        (S.epsilon : ℝ) (startCutoff S.start : ℝ)
        (baselineCap rho) N history).cap ≤
          (physicalWord N history).sum+3*coordinate N p) :
    firstExitRetainedLeaves
      (evenFirstExitPolicy
        (retainEven (compactPlan S table rho)
          (S.epsilon : ℝ) (startCutoff S.start : ℝ)
          (baselineCap rho) N))
      (fun _=>1) history false mass (p::remaining)=
    firstExitRetainedLeaves
      (evenFirstExitPolicy
        (retainEven (compactPlan S table rho)
          (S.epsilon : ℝ) (startCutoff S.start : ℝ)
          (baselineCap rho) N))
      (fun _=>1) history false mass remaining := by
  have hret := rank_four_failure_at_actual_trace S table rho N p history hlen hfail
  exact failed_even_select_prunes_subtree
    (retainEven (compactPlan S table rho)
      (S.epsilon : ℝ) (startCutoff S.start : ℝ)
      (baselineCap rho) N)
    (fun _=>1) history mass p remaining hret

-- The already established canonical-retained-trace theorem identifies
-- literal rawSupport with the unique prime-factor history. Consequently
-- a genuinely mixed fine-label fibre yields different final accepted
-- flags on two actual integer traces, not merely a geometric surrogate.
theorem mixed_fibre_has_actual_trace_disagreement {depth mesh : ℕ}
    (P : CapPlan depth mesh) (a b seed : ℝ)
    {N : ℕ} (hN : 1<(N:ℝ)) (cap : ℕ)
    (z0 w tau : ℝ) (hmargin : 2*w<seed)
    (d : ℕ) (hd : d∈universe N cap z0 ((N:ℝ)^w))
    (hm : P2LowerRoundingTaggedMass.mixed
      (retainEven P a b seed N) N cap z0 ((N:ℝ)^w) tau d) :
    ∃ e∈cell N cap z0 ((N:ℝ)^w) tau d,
      (integerTrace P a b seed N d.primeFactorsList).accepted≠
        (integerTrace P a b seed N e.primeFactorsList).accepted ∧
      (physicalWord N d.primeFactorsList).length=
        (physicalWord N e.primeFactorsList).length := by
  obtain ⟨e,he,hdiff⟩ := hm
  have heU : e∈universe N cap z0 ((N:ℝ)^w) :=
    (Finset.mem_filter.mp he).1
  have hlabel : label N tau e=label N tau d :=
    (Finset.mem_filter.mp he).2
  have hrank := same_label_same_rank N cap e d z0 ((N:ℝ)^w) tau hlabel
  have hlen : (physicalWord N d.primeFactorsList).length=
      (physicalWord N e.primeFactorsList).length := by
    simpa only [physicalWord,List.length_map,List.length_reverse] using hrank.symm
  refine ⟨e,he,?_,hlen⟩
  intro haccepted
  have hretain : retainEven P a b seed N d.primeFactorsList=
      retainEven P a b seed N e.primeFactorsList := haccepted
  have hrawD := raw_support_iff_canonical_trace P a b seed
    hN cap z0 w hmargin d
  have hrawE := raw_support_iff_canonical_trace P a b seed
    hN cap z0 w hmargin e
  have hiff : e∈rawSupport (retainEven P a b seed N)
      N cap z0 ((N:ℝ)^w) ↔
      d∈rawSupport (retainEven P a b seed N)
        N cap z0 ((N:ℝ)^w) := by
    rw [hrawE,hrawD]
    simp only [heU,hd,true_and,hretain]
  exact hdiff hiff

-- The output of the previous theorem enters the chronological
-- first-state-change lemma with the *same* canonical physical word.
theorem mixed_fibre_has_first_changed_integer_prefix {depth mesh : ℕ}
    (P : CapPlan depth mesh) (a b seed : ℝ)
    {N : ℕ} (hN : 1<(N:ℝ)) (cap : ℕ)
    (z0 w tau : ℝ) (hmargin : 2*w<seed)
    (d : ℕ) (hd : d∈universe N cap z0 ((N:ℝ)^w))
    (hm : P2LowerRoundingTaggedMass.mixed
      (retainEven P a b seed N) N cap z0 ((N:ℝ)^w) tau d) :
    ∃ e∈cell N cap z0 ((N:ℝ)^w) tau d,
      ∃ (beforeD beforeE : List ℝ) (x y : ℝ)
        (afterD afterE : List ℝ),
        physicalWord N d.primeFactorsList=beforeD++x::afterD ∧
        physicalWord N e.primeFactorsList=beforeE++y::afterE ∧
        beforeD.length=beforeE.length ∧
        stateAgree (run P a b (root seed) beforeD)
          (run P a b (root seed) beforeE) ∧
        ¬stateAgree
          (step P a b (run P a b (root seed) beforeD) x)
          (step P a b (run P a b (root seed) beforeE) y) := by
  obtain ⟨e,he,hacc,hlen⟩ :=
    mixed_fibre_has_actual_trace_disagreement P a b seed
      hN cap z0 w tau hmargin d hd hm
  have hfinal : ¬stateAgree
      (run P a b (root seed) (physicalWord N d.primeFactorsList))
      (run P a b (root seed) (physicalWord N e.primeFactorsList)) := by
    intro hs
    exact hacc hs.2
  obtain ⟨bd,be,x,y,ad,ae,hwd,hwe,hbl,hpre,hbad⟩ :=
    first_state_change_from_root P a b seed
      (physicalWord N d.primeFactorsList)
      (physicalWord N e.primeFactorsList) hlen hfinal
  exact ⟨e,he,bd,be,x,y,ad,ae,hwd,hwe,hbl,hpre,hbad⟩

end
end ImbalancedChen.P2LowerActualFirstExitBoundary
