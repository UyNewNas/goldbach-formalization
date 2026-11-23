import ImbalancedChen.P2LowerCapPlanIntegerRetention
import ImbalancedChen.FirstExitValidSelection
import ImbalancedChen.FixedEvenRoughCoefficients

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The raw retained-modulus support is now identified with the COMPUTED
integer cap trace on the actual rough-prime carrier. The active physical
cutoff proves the initial square margin; it is not an assumed retention
or coefficient comparison. The existing constructive valid-selection
theorem is reused, including its reverse direction.

The finite CapPlan remains the named geometric input. Its original bank
instantiation and selected-branch legality are not invented here. No
rounding-loss smallness or final density/count bound is assumed.
-/

namespace ImbalancedChen.P2LowerIntegerRetainedSupport

noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention

private theorem parity (pre : List ℕ) : evenListLength pre=decide (Even pre.length) := by
  induction pre with
  | nil => simp [evenListLength]
  | cons p pre ih =>
      simp only [evenListLength,ih,List.length_cons,Nat.even_add_one,decide_not]

theorem run_accepted_incoming {depth m : ℕ} (P : CapPlan depth m)
    (a b : ℝ) (H : Trace) (xs : List ℝ) (h : (run P a b H xs).accepted=true) :
    H.accepted=true := by
  induction xs generalizing H with
  | nil => exact h
  | cons x xs ih =>
      have hs := ih (step P a b H x) h
      exact ((step_accepted_iff P a b H x).mp hs).1

/-- An actual later selected-prime word cannot alter or erase acceptance
of its physical incoming prefix. -/
theorem retainEven_of_newer {depth m : ℕ} (P : CapPlan depth m)
    (a b seedCap : ℝ) (N : ℕ) (newer older : List ℕ)
    (h : retainEven P a b seedCap N (newer++older)=true) :
    retainEven P a b seedCap N older=true := by
  unfold retainEven integerTrace at h ⊢
  have hw : physicalWord N (newer++older)=physicalWord N older++physicalWord N newer := by
    simp only [physicalWord,List.reverse_append,List.map_append]
  rw [hw,run_append] at h
  exact run_accepted_incoming P a b _ _ h

/-- The only odd step with an initial square is supplied explicitly;
all later odd ranks bypass the cube. No odd first exclusion is added. -/
private theorem next_policy_iff_trace {depth m : ℕ} (P : CapPlan depth m)
    (a b seedCap : ℝ) (N p : ℕ) (pre : List ℕ)
    (hpre : retainEven P a b seedCap N pre=true) (hsquare : 2*coordinate N p<seedCap) :
    evenFirstExitPolicy (retainEven P a b seedCap N) (!(evenListLength pre)) (p::pre)=true ↔
      retainEven P a b seedCap N (p::pre)=true := by
  cases hs : evenListLength pre with
  | false => simp only [hs,Bool.not_false,evenFirstExitPolicy,Bool.not_true,Bool.false_or]
  | true =>
      have hnext : retainEven P a b seedCap N (p::pre)=true := by
        by_cases hnil : pre=[]
        · subst pre
          rw [retainEven_cons_iff]
          exact ⟨hpre,by simpa only [integerTrace,physicalWord,List.reverse_nil,List.map_nil,
            run,List.foldl_nil,root,admission,List.length_nil,if_pos rfl] using hsquare⟩
        · have he : Even pre.length := by
            have hs' := hs
            rw [parity] at hs'
            exact of_decide_eq_true hs'
          obtain ⟨k,hk⟩ := he
          have hodd : (pre.length+1)%2≠0 := by omega
          exact (odd_rank_bypass P a b seedCap N p pre (List.length_pos.mpr hnil) hodd).mpr hpre
      simp only [hs,Bool.not_true,evenFirstExitPolicy,Bool.not_false,Bool.true_or]
      exact iff_of_true trivial hnext

/-- The complete computed trace replaces the generic valid-selection
obligation; all earlier tests are recovered, rather than assumed anew. -/
theorem validSelection_iff_computed_trace {depth m : ℕ} (P : CapPlan depth m)
    (a b seedCap : ℝ) (N : ℕ) (chosen : List ℕ) :
    ∀pre : List ℕ,retainEven P a b seedCap N pre=true →
      (∀p∈chosen,2*coordinate N p<seedCap) →
      (FirstExitValidSelection (evenFirstExitPolicy (retainEven P a b seedCap N))
        pre (evenListLength pre) chosen ↔
        retainEven P a b seedCap N (chosen.reverse++pre)=true) := by
  induction chosen with
  | nil =>
      intro pre hpre hsquare
      simp only [FirstExitValidSelection,List.reverse_nil,List.nil_append,hpre]
  | cons p ps ih =>
      intro pre hpre hsquare
      have hnext := next_policy_iff_trace P a b seedCap N p pre hpre
        (hsquare p (List.mem_cons_self p ps))
      have htailSquare : ∀q∈ps,2*coordinate N q<seedCap :=
        fun q hq=>hsquare q (List.mem_cons_of_mem p hq)
      rw [FirstExitValidSelection]
      constructor
      · rintro ⟨hpass,hvalid⟩
        have hpassed := hnext.mp hpass
        have htail : FirstExitValidSelection (evenFirstExitPolicy (retainEven P a b seedCap N))
            (p::pre) (evenListLength (p::pre)) ps := hvalid
        have hfinal := (ih (p::pre) hpassed htailSquare).mp htail
        simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hfinal
      · intro hfinal
        have hfinal' : retainEven P a b seedCap N (ps.reverse++p::pre)=true := by
          simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hfinal
        have hpassed := retainEven_of_newer P a b seedCap N ps.reverse (p::pre) hfinal'
        exact ⟨hnext.mpr hpassed,(ih (p::pre) hpassed htailSquare).mpr hfinal'⟩

/-- Every actual rough prime below N^w has the initial square margin.
This is derived from the physical carrier cutoff and 2w<seedCap. -/
theorem actual_prime_initial_square {N cap p : ℕ} (hN : 1<(N:ℝ))
    (z0 w seedCap : ℝ) (hmargin : 2*w<seedCap)
    (hp : p∈roughPrimeUniverse N cap z0 ((N:ℝ)^w)) : 2*coordinate N p<seedCap := by
  have hupper := mem_roughPrimeUniverse_upper hp
  have hcoord : coordinate N p<w := by
    apply (Real.rpow_lt_rpow_left_iff hN).mp
    rwa [coordinate_power hN (mem_roughPrimeUniverse_prime hp).pos]
  linarith

/-- Actual retained divisors are exactly the products of chronological
rough subwords whose computed original-parity cap trace is accepted.
The reverse direction constructs a genuine retained leaf. -/
theorem raw_support_iff_actual_trace {depth m : ℕ} (P : CapPlan depth m)
    (a b seedCap : ℝ) {N : ℕ} (hN : 1<(N:ℝ)) (cap : ℕ)
    (z0 w : ℝ) (hmargin : 2*w<seedCap) (d : ℕ) :
    d∈fixedEvenRoughSupport (retainEven P a b seedCap N) N cap z0 ((N:ℝ)^w) ↔
      ∃chosen : List ℕ,chosen <+ roughPrimeUniverse N cap z0 ((N:ℝ)^w) ∧
        retainEven P a b seedCap N chosen.reverse=true ∧ chosen.prod=d := by
  rw [fixedEvenRoughSupport,mem_firstExitRetainedModuli_iff_validSelection]
  constructor
  · rintro ⟨chosen,hsub,hvalid,hprod⟩
    have hsquare : ∀p∈chosen,2*coordinate N p<seedCap :=
      fun p hp=>actual_prime_initial_square hN z0 w seedCap hmargin (hsub.subset hp)
    have htrace := (validSelection_iff_computed_trace P a b seedCap N chosen [] rfl hsquare).mp hvalid
    exact ⟨chosen,hsub,by simpa only [List.append_nil] using htrace,hprod⟩
  · rintro ⟨chosen,hsub,htrace,hprod⟩
    have hsquare : ∀p∈chosen,2*coordinate N p<seedCap :=
      fun p hp=>actual_prime_initial_square hN z0 w seedCap hmargin (hsub.subset hp)
    refine ⟨chosen,hsub,?_,hprod⟩
    apply (validSelection_iff_computed_trace P a b seedCap N chosen [] rfl hsquare).mpr
    simpa only [List.append_nil] using htrace

end
end ImbalancedChen.P2LowerIntegerRetainedSupport
