import ImbalancedChen.P2LowerIntegerRetainedSupport
import ImbalancedChen.P2LowerFiniteCellRounding

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original whole raw-support predicate in the finite-cell compiler is
identified with the computed cap trace of the canonical prime-factor
history. There is no existential choice of another ordering or cap plan
inside an ALL/ANY cell test. The actual decreasing rough-prime carrier
and unique factorization derive the canonical history and its reverse
retained-leaf construction.

This removes the raw-support/canonical-word identification gap. It does
not assert a coarse-boundary band estimate or validate an arbitrary
finite CapPlan as the original geometric branch bank.
-/

namespace ImbalancedChen.P2LowerCanonicalRetainedTrace

noncomputable section
open scoped Classical BigOperators
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2LowerIntegerRetainedSupport P2LowerFiniteCellRounding

/-- An actual chronological subword with product d has exactly the
decreasing canonical prime-factor word, not a policy-dependent ordering. -/
theorem actual_chosen_eq_canonical (N cap : ℕ) (z0 z : ℝ)
    (chosen : List ℕ) (hsub : chosen <+ roughPrimeUniverse N cap z0 z)
    {d : ℕ} (hprod : chosen.prod=d) : chosen=d.primeFactorsList.reverse := by
  have hprime : ∀p∈chosen,p.Prime := fun p hp=>mem_roughPrimeUniverse_prime (hsub.subset hp)
  have hge : chosen.Pairwise (·≥·) :=
    ((roughPrimeUniverse_pairwise_gt N cap z0 z).sublist hsub).imp (fun h=>h.le)
  have hperm : chosen ~ d.primeFactorsList.reverse :=
    (Nat.primeFactorsList_unique hprod hprime).trans (List.reverse_perm d.primeFactorsList).symm
  exact hperm.eq_of_pairwise' hge (Nat.primeFactorsList_sorted d).reverse.pairwise

/-- Every divisor in the COMPLETE actual rough carrier constructs its
canonical chronological subword. No retained-support premise is needed. -/
theorem canonical_subword_of_universe (N cap : ℕ) (z0 z : ℝ) {d : ℕ}
    (hd : d∈universe N cap z0 z) :
    d.primeFactorsList.reverse <+ roughPrimeUniverse N cap z0 z ∧
      d.primeFactorsList.reverse.prod=d := by
  let carrier:=roughPrimeUniverse N cap z0 z
  have hdvd : d∣carrier.prod := (Nat.mem_divisors.mp hd).1
  have hcarrier0 : carrier.prod≠0 := (roughProduct_squarefree N cap z0 z).ne_zero
  have hpf : carrier.prod.primeFactors=carrier.toFinset := by
    have heq : (∏p∈carrier.toFinset,p)=carrier.prod := by
      simpa using List.prod_toFinset (fun p : ℕ=>p) (roughPrimeUniverse_nodup N cap z0 z)
    rw [←heq]
    exact Nat.primeFactors_prod (fun p hp=>mem_roughPrimeUniverse_prime (List.mem_toFinset.mp hp))
  have hsubset : d.primeFactors⊆carrier.toFinset := by
    rw [←hpf]
    exact Nat.primeFactors_mono hdvd hcarrier0
  let chosen:=carrier.filter (fun p=>p∈d.primeFactors)
  have hsub : chosen <+ carrier := List.filter_sublist
  have hcset : chosen.toFinset=d.primeFactors := by
    ext p
    simp only [chosen,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    constructor
    · exact fun h=>h.2
    · exact fun hp=>⟨List.mem_toFinset.mp (hsubset hp),hp⟩
  have hcprod : chosen.prod=d := by
    have heq : (∏p∈chosen.toFinset,p)=chosen.prod := by
      simpa using List.prod_toFinset (fun p : ℕ=>p)
        ((roughPrimeUniverse_nodup N cap z0 z).sublist hsub)
    rw [←heq,hcset]
    exact Nat.prod_primeFactors_of_squarefree (universe_squarefree N cap z0 z hd)
  have hcanonical := actual_chosen_eq_canonical N cap z0 z chosen hsub hcprod
  exact ⟨hcanonical ▸ hsub,hcanonical ▸ hcprod⟩

/-- This is the literal whole rawSupport tested by the finite ALL/ANY
rounding constructor. Its policy is computed from the same finite plan. -/
theorem raw_support_iff_canonical_trace {depth m : ℕ} (P : CapPlan depth m)
    (a b seedCap : ℝ) {N : ℕ} (hN : 1<(N:ℝ)) (cap : ℕ)
    (z0 w : ℝ) (hmargin : 2*w<seedCap) (d : ℕ) :
    d∈rawSupport (retainEven P a b seedCap N) N cap z0 ((N:ℝ)^w) ↔
      d∈universe N cap z0 ((N:ℝ)^w) ∧
        retainEven P a b seedCap N d.primeFactorsList=true := by
  constructor
  · intro hd
    have hU := rawSupport_subset_universe (retainEven P a b seedCap N) N cap z0 ((N:ℝ)^w) hd
    obtain ⟨chosen,hsub,htrace,hprod⟩ :=
      (raw_support_iff_actual_trace P a b seedCap hN cap z0 w hmargin d).mp hd
    have hc := actual_chosen_eq_canonical N cap z0 ((N:ℝ)^w) chosen hsub hprod
    refine ⟨hU,?_⟩
    simpa only [hc,List.reverse_reverse] using htrace
  · rintro ⟨hU,htrace⟩
    obtain ⟨hsub,hprod⟩ := canonical_subword_of_universe N cap z0 ((N:ℝ)^w) hU
    apply (raw_support_iff_actual_trace P a b seedCap hN cap z0 w hmargin d).mpr
    exact ⟨d.primeFactorsList.reverse,hsub,by simpa only [List.reverse_reverse] using htrace,hprod⟩

/-- Exact raw lambda at every actual natural modulus, using the canonical
trace tested by the compiler; outside the rough carrier it is zero. -/
theorem actual_raw_coefficient_canonical {depth m : ℕ} (P : CapPlan depth m)
    (a b seedCap : ℝ) {N : ℕ} (hN : 1<(N:ℝ)) (cap : ℕ)
    (z0 w : ℝ) (hmargin : 2*w<seedCap) (d : ℕ) :
    raw (retainEven P a b seedCap N) N cap z0 ((N:ℝ)^w) d=
      if d∈universe N cap z0 ((N:ℝ)^w) ∧ retainEven P a b seedCap N d.primeFactorsList=true
      then (ArithmeticFunction.moebius d:ℝ) else 0 := by
  rw [raw_value,raw_support_iff_canonical_trace P a b seedCap hN cap z0 w hmargin d]

end
end ImbalancedChen.P2LowerCanonicalRetainedTrace
