import ImbalancedChen.P2Historical246SmallCeilingCollision

/-! SOURCE ONLY / UNEVALUATED. Localize the remaining actual prefix
collision to a labelled old-prime slot and bound the total reciprocal
mass of all slots. No full collision sum or H247 endpoint is paid. -/
namespace ImbalancedChen.P2Historical246PrefixSlotLocalization
noncomputable section
open Set Finset Filter
open scoped Classical BigOperators Topology
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalSuccessorTheta
open P2EnhancedSwitchedTrueNormalization P2Historical246PairCarrierPartition
open P2Historical246SuccessorParentWindow P2Historical246RepeatedCeilingBook
open P2Historical246RepeatedCeilingDecomposition P2Historical246SmallCeilingCollision
open P2OriginalChildPhysicalNormalization P2OriginalBankChildPrimeMass
open P2OriginalBankThetaMassLimits P2OriginalHalfOpenProfileCarrier
open P2OriginalCompactScaledPrimeMass P2OriginalCompactThetaMass

/-- A prime dividing a finite labelled product divides some literal
factor. This proof keeps the label rather than quotienting duplicates. -/
theorem prime_dvd_labelled_factor {ι : Type*} (S : Finset ι) (f : ι → ℕ)
    {p : ℕ} (hp : p.Prime) (h : p ∣ ∏ x ∈ S, f x) :
    ∃ x ∈ S, p ∣ f x := by
  classical
  revert h
  induction S using Finset.induction_on with
  | empty =>
      intro h
      simp only [Finset.prod_empty] at h
      exact (hp.ne_one (Nat.dvd_one.mp h)).elim
  | @insert x S hx ih =>
      intro h
      rw [Finset.prod_insert hx] at h
      rcases hp.dvd_mul.mp h with hleft | hright
      · exact ⟨x,Finset.mem_insert_self _ _,hleft⟩
      · obtain ⟨y,hy,hydiv⟩ := ih hright
        exact ⟨y,Finset.mem_insert_of_mem hy,hydiv⟩

/-- The actual successor source supplies a global rank bound even when
the root rank is not fixed: each slot has the same positive lower
physical floor and the true residual level remains positive. -/
theorem successor_rank_floor_bound {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (hnu : nu ≤ 1)
    (m : Mark) (choice : SuccessorChoice) (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu) :
    ((advance m choice).rank : ℝ)*floorAt eta (horizon+1) ≤ 1 := by
  let lo := floorAt eta (horizon+1)
  have hlo : 0 < lo := floorAt_pos he (horizon+1)
  have hf := (advance m choice).source_facts hN he (advance_boxRows m choice hm) ht
  have htrue := facts_trueAlpha hN hlo hf
  have hres : 6*lo ≤ residualExponent N (Part3.labelledProduct t) nu := htrue.2.1
  have hprefix : prefixExponent N (Part3.labelledProduct t) ≤ 1 := by
    unfold residualExponent at hres
    linarith only [hres,hnu,hlo]
  have hsum : (∑ _j : Fin (advance m choice).rank, lo) ≤
      ∑ j : Fin (advance m choice).rank, physicalPrime N (t j).val := by
    exact Finset.sum_le_sum (fun j _ => (hf.1 j).2.2)
  have hpref := tuple_prefixExponent hN t (fun j => ((hf.1 j).1).pos)
  rw [← hpref] at hsum
  have hcard : (∑ _j : Fin (advance m choice).rank, lo) =
      ((advance m choice).rank : ℝ)*lo := by simp
  rw [hcard] at hsum
  exact hsum.trans hprefix

/-- The reciprocal sum counts repeated labelled prime occurrences; it
is still bounded uniformly by the actual source floor and same N. -/
theorem successor_slot_reciprocal_bound {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (hnu : nu ≤ 1)
    (m : Mark) (choice : SuccessorChoice) (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu) :
    (∑ j : Fin (advance m choice).rank, 1/(((t j).val : ℝ)-1)) ≤
      2/(floorAt eta (horizon+1) * (N : ℝ)^(floorAt eta (horizon+1))) := by
  let lo := floorAt eta (horizon+1)
  have hlo : 0 < lo := floorAt_pos he (horizon+1)
  have hNpow : (0 : ℝ) < (N : ℝ)^lo := by positivity
  have hf := (advance m choice).source_facts hN he (advance_boxRows m choice hm) ht
  have hrank := successor_rank_floor_bound hN he hnu m choice hm ht
  have hrank' : ((advance m choice).rank : ℝ) ≤ 1/lo :=
    (le_div_iff₀ hlo).2 hrank
  have hterm (j : Fin (advance m choice).rank) :
      1/(((t j).val : ℝ)-1) ≤ 2/(N : ℝ)^lo := by
    have hp := (hf.1 j).1
    have htwo : (2 : ℝ) ≤ (t j).val := by exact_mod_cast hp.two_le
    have hfloor : (N : ℝ)^lo ≤ (t j).val :=
      physical_floor_to_power hN hp.pos (hf.1 j).2.2
    have hden : (0 : ℝ) < ((t j).val : ℝ)-1 := by linarith
    apply (div_le_div_iff₀ hden hNpow).2
    nlinarith
  calc
    (∑ j : Fin (advance m choice).rank, 1/(((t j).val : ℝ)-1)) ≤
        ∑ _j : Fin (advance m choice).rank, 2/(N : ℝ)^lo :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = ((advance m choice).rank : ℝ)*(2/(N : ℝ)^lo) := by simp
    _ ≤ (1/lo)*(2/(N : ℝ)^lo) :=
      mul_le_mul_of_nonneg_right hrank' (div_nonneg (by norm_num) hNpow.le)
    _ = _ := by dsimp [lo]; ring


/-- A single threshold before all actual books and all ranks makes the
sum over all labelled old-prime reciprocal factors small. -/
theorem successor_slot_reciprocal_uniform {eta epsilon : ℝ}
    (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (m : Mark) (choice : SuccessorChoice), m.BoxRows nu eta horizon →
      ∀ t ∈ (advance m choice).source N nu,
        (∑ j : Fin (advance m choice).rank, 1/(((t j).val : ℝ)-1)) < epsilon := by
  let lo := floorAt eta (horizon+1)
  have hlo : 0 < lo := floorAt_pos he (horizon+1)
  have hpow := tendsto_nat_log_pow_div_rpow 0 hlo
  simp only [pow_zero] at hpow
  have hlimit : Tendsto (fun N : ℕ => (2/lo)/(N : ℝ)^lo) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,mul_one_div] using (hpow.const_mul (2/lo))
  obtain ⟨T0,hT0⟩ := eventually_atTop.mp (hlimit.eventually (gt_mem_nhds heps))
  refine ⟨max 4 T0,le_max_left _ _,?_⟩
  intro N hN nu hnu m choice hm t ht
  have hN1 : 1 < N := by omega
  have hsmall := hT0 N ((le_max_right _ _).trans hN)
  have heq : (2/lo)/(N : ℝ)^lo = 2/(lo*(N : ℝ)^lo) := by ring
  rw [heq] at hsmall
  exact (successor_slot_reciprocal_bound hN1 he hnu m choice hm ht).trans_lt hsmall

/-- Any failed prefix coprimality in the actual N-deleted half-box is
caused by one actual labelled prime in the parent word. -/
theorem collision_has_parent_slot {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (m : Mark) (choice : SuccessorChoice)
    (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu)
    (j : Fin 36) (k : Fin 4) {p : Pair}
    (hp : p ∈ halfCarrier N (residualExponent N (parentProduct (oldWord t)) nu) j k)
    (hbad : ¬ bothCoprime N (oldWord t) p) :
    ∃ (i : Fin 2) (a : Fin (advance m choice).rank), p i = (t a).val := by
  have hbox := (Finset.mem_filter.mp hp).1
  have hf := (advance m choice).source_facts hN he (advance_boxRows m choice hm) ht
  have hslot (i : Fin 2) (hfail : ¬ (p i).Coprime (N*parentProduct (oldWord t))) :
      ∃ a : Fin (advance m choice).rank, p i = (t a).val := by
    have hprime := ((mem_actualPrimeBoxTuples_iff.mp hbox) i).1
    have hNnot := ((mem_actualPrimeBoxTuples_iff.mp hbox) i).2.1
    have hdiv : p i ∣ N*parentProduct (oldWord t) := by
      by_contra h
      exact hfail (hprime.coprime_iff_not_dvd.mpr h)
    have hdivold : p i ∣ parentProduct (oldWord t) := (hprime.dvd_mul.mp hdiv).resolve_left hNnot
    rw [oldWord_product] at hdivold
    unfold Part3.labelledProduct at hdivold
    obtain ⟨a,_,ha⟩ := prime_dvd_labelled_factor Finset.univ (fun a => (t a).val) hprime hdivold
    exact ⟨a,(Nat.prime_dvd_prime_iff_eq hprime ((hf.1 a).1)).mp ha⟩
  have hc : ¬ (p 0).Coprime (N*parentProduct (oldWord t)) ∨
      ¬ (p 1).Coprime (N*parentProduct (oldWord t)) := by
    simpa [bothCoprime] using (not_and_or.mp hbad)
  rcases hc with h0 | h1
  · obtain ⟨a,ha⟩ := hslot 0 h0
    exact ⟨0,a,ha⟩
  · obtain ⟨a,ha⟩ := hslot 1 h1
    exact ⟨1,a,ha⟩

/-- The remaining bucket after both ceiling-equality slices still has
an actual old-slot witness, and its witnessed prime differs from c. -/
theorem remaining_collision_has_non_ceiling_slot {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (m : Mark) (choice : SuccessorChoice)
    (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu)
    (j : Fin 36) (k : Fin 4) (c : ℕ) {p : Pair}
    (hp : p ∈ (otherCollision N ((N : ℝ)^nu)
      (residualExponent N (parentProduct (oldWord t)) nu)
      ((advance m choice).history.ceiling (advance m choice).ceiling t)
      (oldWord t) j k c).filter (fun p => p 0 ≠ c)) :
    ∃ (i : Fin 2) (a : Fin (advance m choice).rank), p i = (t a).val ∧ (t a).val ≠ c := by
  obtain ⟨hother,h0⟩ := Finset.mem_filter.mp hp
  obtain ⟨hhalf,_,_,hbad,h1⟩ := Finset.mem_filter.mp hother
  obtain ⟨i,a,heq⟩ := collision_has_parent_slot hN he m choice hm ht j k hhalf hbad
  refine ⟨i,a,heq,?_⟩
  have hne : p i ≠ c := by fin_cases i <;> assumption
  simpa only [← heq] using hne

end
end ImbalancedChen.P2Historical246PrefixSlotLocalization
