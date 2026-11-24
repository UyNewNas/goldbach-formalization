import ImbalancedChen.P2OriginalPairRootRoughProducer
import ImbalancedChen.P2RoundedCausalFibreLossAndLevel
import ImbalancedChen.P2OriginalLowerCompactStartCapConstructor

/-!
# Deriving full-prefix raw level and rank from the actual pair-root run

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The raw support/rank conclusion needed by the previous rounding theorem is
not a hypothesis here. Its inputs are the finite plan's emitted-cap ceiling,
the actual root cap, and the original sixth-pair/rough-prime carrier.
Acceptance, even cubes, odd bypass and decreasing physical order derive the
full-prefix bound. A positive rough cutoff exponent derives a uniform rank.

The finite emitted-cap check is independent of the arithmetic target. The
old ordinary compactPlan is shown to satisfy it, but is not thereby
identified with the selected marked-pair SourceForm plan: that receiver and
its stored pair seed must be bound separately.
-/

namespace ImbalancedChen.P2ActualPairPlanRawSupport

noncomputable section
open scoped Classical BigOperators
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairRootRoughProducer P2LowerCanonicalRetainedTrace
open P2OriginalLowerCompactStartCapConstructor P5SelectedMaskTransport

/-- A local finite cap check; it supplies no retained-modulus bound. -/
def PlanCeiling {depth mesh : ℕ} (P : CapPlan depth mesh) (nu : ℝ) : Prop :=
  ∀ rank code incoming, incoming ≤ nu → (P.choose rank code).freeze incoming ≤ nu

private theorem checkedChoice_freeze_le_top (S : CompactStart) {mesh : ℕ}
    (table : P2OriginalLowerSelectedCapConstructor.BranchTable mesh)
    (rank : Fin 6) (parent : ℝ)
    (code : P2OriginalLowerSelectedCapConstructor.Code mesh)
    (incoming : ℝ) (hi : incoming ≤ topCap) :
    (checkedChoice S table rank parent code).freeze incoming ≤ topCap := by
  unfold checkedChoice
  cases hr : table.row rank
      (P2OriginalLowerSelectedCapConstructor.prefixCode rank.val code) with
  | none => simpa only [CapChoice.freeze] using hi
  | some pair =>
      rcases pair with ⟨candidate, argument⟩
      by_cases hg : branchGates S rank parent candidate
          (P2OriginalLowerSelectedCapConstructor.prefixCode rank.val code)
      · simp only [if_pos hg, CapChoice.freeze]
        exact hg.2.1
      · simpa only [if_neg hg, CapChoice.freeze] using hi

/-- This finite property of the old ordinary receiver is proved, not
assumed. It alone does not license that receiver as a marked-pair plan. -/
theorem ordinary_compactPlan_ceiling (S : CompactStart) {mesh : ℕ}
    (table : P2OriginalLowerSelectedCapConstructor.BranchTable mesh) (rho : ℝ) :
    PlanCeiling (compactPlan S table rho) topCap := by
  intro rank code incoming hi
  fin_cases rank <;> dsimp [compactPlan, CapChoice.freeze]
  all_goals first
    | exact hi
    | exact checkedChoice_freeze_le_top S table _ _ _ incoming hi

theorem step_cap_le {depth mesh : ℕ} (P : CapPlan depth mesh) (nu : ℝ)
    (hP : PlanCeiling P nu) (a b : ℝ) (H : Trace) (x : ℝ)
    (hcap : H.cap ≤ nu) : (step P a b H x).cap ≤ nu := by
  change (planChoice P a b (H.word ++ [x])).freeze H.cap ≤ nu
  unfold planChoice
  split_ifs
  · unfold incomingChoice
    exact hP _ _ _ hcap
  · exact hcap

theorem run_cap_le {depth mesh : ℕ} (P : CapPlan depth mesh) (nu : ℝ)
    (hP : PlanCeiling P nu) (a b : ℝ) (H : Trace) (xs : List ℝ)
    (hcap : H.cap ≤ nu) : (run P a b H xs).cap ≤ nu := by
  induction xs generalizing H with
  | nil => exact hcap
  | cons x xs ih =>
      exact ih (step P a b H x) (step_cap_le P nu hP a b H x hcap)

/-- Every accepted even cube creates two copies of the last exponent in
reserve. At the next odd bypass, decreasing order spends at most one copy.
No odd cube or tail-modulus conclusion is supplied as a premise. -/
private theorem accepted_run_sum_le {depth mesh : ℕ} (P : CapPlan depth mesh)
    (nu : ℝ) (hP : PlanCeiling P nu) (a b : ℝ) (xs : List ℝ) :
    ∀ (H : Trace) (ceiling : ℝ), 0 < H.word.length → H.cap ≤ nu →
      H.word.sum ≤ nu →
      (H.word.length % 2 = 0 → H.word.sum + 2 * ceiling ≤ nu) →
      (H.word.length % 2 = 0 → ∀ x ∈ xs, x ≤ ceiling) →
      xs.Pairwise (· ≥ ·) → (∀ x ∈ xs, 0 ≤ x) →
      (run P a b H xs).accepted = true → (run P a b H xs).word.sum ≤ nu := by
  induction xs with
  | nil => intros; assumption
  | cons x xs ih =>
      intro H ceiling hlen hcap hsum hcarry hceil hsort hnonneg haccept
      have hacc : (step P a b H x).accepted = true :=
        P2LowerIntegerRetainedSupport.run_accepted_incoming P a b _ _ haccept
      have hadm := ((step_accepted_iff P a b H x).mp hacc).2
      have hx0 := hnonneg x (List.mem_cons_self x xs)
      have hcube (he : (H.word.length + 1) % 2 = 0) :
          H.word.sum + 3 * x < H.cap := by
        have hn : H.word.length ≠ 0 := by omega
        simpa only [admission, if_neg hn, if_pos he] using hadm
      have hword : (step P a b H x).word.sum = H.word.sum + x := by
        simp only [step, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
      have hnextsum : (step P a b H x).word.sum ≤ nu := by
        rw [hword]
        by_cases he : (H.word.length + 1) % 2 = 0
        · linarith [hcube he]
        · have hprev : H.word.length % 2 = 0 := by omega
          have hc := hcarry hprev
          have hx := hceil hprev x (List.mem_cons_self x xs)
          linarith
      have hnextcarry : (step P a b H x).word.length % 2 = 0 →
          (step P a b H x).word.sum + 2 * x ≤ nu := by
        intro he
        have he' : (H.word.length + 1) % 2 = 0 := by
          simpa only [step, List.length_append, List.length_singleton] using he
        rw [hword]
        linarith [hcube he']
      have hnextceil : (step P a b H x).word.length % 2 = 0 →
          ∀ y ∈ xs, y ≤ x := by
        intro _ y hy
        exact (List.pairwise_cons.mp hsort).1 y hy
      have hnextlen : 0 < (step P a b H x).word.length := by
        simp only [step, List.length_append, List.length_singleton]
        omega
      exact ih (step P a b H x) x hnextlen
        (step_cap_le P nu hP a b H x hcap) hnextsum hnextcarry hnextceil
        (List.pairwise_cons.mp hsort).2
        (fun y hy => hnonneg y (List.mem_cons_of_mem x hy)) haccept

private theorem coordinate_le_of_prime_le_power {N p : ℕ} (hN : 1 < (N : ℝ))
    (hp : 0 < p) {u : ℝ} (h : (p : ℝ) ≤ (N : ℝ) ^ u) : coordinate N p ≤ u := by
  rw [← coordinate_power hN hp] at h
  exact (Real.rpow_le_rpow_left_iff hN).mp h

private theorem coordinate_ge_of_power_le_prime {N p : ℕ} (hN : 1 < (N : ℝ))
    (hp : 0 < p) {u : ℝ} (h : (N : ℝ) ^ u ≤ (p : ℝ)) : u ≤ coordinate N p := by
  rw [← coordinate_power hN hp] at h
  exact (Real.rpow_le_rpow_left_iff hN).mp h

private theorem coordinate_nonneg {N p : ℕ} (hN : 1 < (N : ℝ)) (hp : 1 ≤ p) :
    0 ≤ coordinate N p := by
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp)) (Real.log_pos hN).le

private theorem coordinates_power {N : ℕ} (hN : 1 < (N : ℝ))
    (ps : List ℕ) (hpos : ∀ p ∈ ps, 0 < p) :
    (N : ℝ) ^ (ps.map (coordinate N)).sum = (ps.prod : ℝ) := by
  simpa only [physicalWord, List.reverse_reverse, List.prod_reverse] using
    physicalWord_power hN ps.reverse (fun p hp => hpos p (by simpa using hp))

private theorem length_mul_le_sum (xs : List ℝ) (omega : ℝ)
    (hx : ∀ x ∈ xs, omega ≤ x) : (xs.length : ℝ) * omega ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have h1 := hx x (List.mem_cons_self x xs)
      have h2 := ih (fun y hy => hx y (List.mem_cons_of_mem x hy))
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.sum_cons]
      nlinarith

/-- The original U6 marked pair has sufficient root reserve for the first
odd rough bypass. These are exactly its original H,D and rough A cutoffs. -/
theorem original_sixth_root_reserve {N : ℕ} (hN : 1 < (N : ℝ))
    {p : ℕ × ℕ} (hp : p ∈ sixthSupport N) (seed : ℝ) :
    (pairRoot N p seed).word.sum + 2 * (417 / 5000 : ℝ) ≤ topCap ∧
      0 ≤ (pairRoot N p seed).word.sum := by
  obtain ⟨hc, hA, hp1H, hH, hp2D⟩ := Finset.mem_filter.mp hp
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hc
  have h1prime := (mem_chenAdditivePrimeCarrier.mp h1).2.1
  have h2prime := (mem_chenAdditivePrimeCarrier.mp h2).2.1
  have ht1 := coordinate_le_of_prime_le_power hN h1prime.pos hp1H.le
  have ht2 := coordinate_le_of_prime_le_power hN h2prime.pos hp2D.le
  have h10 := coordinate_nonneg hN h1prime.one_lt.le
  have h20 := coordinate_nonneg hN h2prime.one_lt.le
  simp only [pairRoot, List.sum_cons, List.sum_nil, add_zero]
  constructor
  · norm_num [topCap] at *
    linarith
  · positivity

/-- ACTUAL pairPolicy raw support yields a full-prefix physical level and
uniform rank. Neither raw conclusion is a supplied licence. The finite
plan ceiling and original pair carrier are the only source-specific inputs. -/
theorem actual_pair_raw_full_prefix_rank {depth mesh : ℕ}
    (P : CapPlan depth mesh) (hP : PlanCeiling P topCap)
    (a b seed : ℝ) (hseed : seed ≤ topCap) {N : ℕ} (hN : 1 < (N : ℝ))
    (enum : ℕ) {p : ℕ × ℕ} (hp : p ∈ sixthSupport N)
    (omega : ℝ) (homega : 0 < omega) {r : ℕ}
    (hr : r ∈ fixedEvenRoughSupport (pairPolicy P a b seed N p) N enum
      ((N : ℝ) ^ omega) ((N : ℝ) ^ (417 / 5000 : ℝ))) :
    (((p.1 * p.2) * r : ℕ) : ℝ) ≤ (N : ℝ) ^ topCap ∧
      r.primeFactorsList.length ≤ Nat.ceil (topCap / omega) := by
  obtain ⟨chosen, hsub, haccept, hprod⟩ :=
    (pair_policy_support_iff P a b seed N enum p _ _ r).mp hr
  have hprime : ∀ q ∈ chosen, q.Prime :=
    fun q hq => mem_roughPrimeUniverse_prime (hsub.subset hq)
  have hnonneg : ∀ x ∈ chosen.map (coordinate N), 0 ≤ x := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact coordinate_nonneg hN (hprime q hq).one_lt.le
  have hupper : ∀ x ∈ chosen.map (coordinate N), x ≤ (417 / 5000 : ℝ) := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact coordinate_le_of_prime_le_power hN (hprime q hq).pos
      (mem_roughPrimeUniverse_upper (hsub.subset hq)).le
  have hlower : ∀ x ∈ chosen.map (coordinate N), omega ≤ x := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact coordinate_ge_of_power_le_prime hN (hprime q hq).pos
      (mem_roughPrimeUniverse_lower (hsub.subset hq))
  have hsort : (chosen.map (coordinate N)).Pairwise (· ≥ ·) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hi' : i < chosen.length := by simpa only [List.length_map] using hi
    have hj' : j < chosen.length := by simpa only [List.length_map] using hj
    have hqsort := ((roughPrimeUniverse_pairwise_gt N enum _ _).sublist hsub)
    have hge := ((List.pairwise_iff_getElem.mp hqsort) i j hi' hj' hij).le
    have hm := coordinate_le_of_prime_le_power hN
      (hprime chosen[j] (List.getElem_mem hj')).pos
      (by rw [coordinate_power hN (hprime chosen[i] (List.getElem_mem hi')).pos]
          exact_mod_cast hge)
    simpa only [List.getElem_map] using hm
  have hroot := original_sixth_root_reserve hN hp seed
  have hfinal := accepted_run_sum_le P topCap hP a b (chosen.map (coordinate N))
    (pairRoot N p seed) (417 / 5000 : ℝ) (by simp [pairRoot]) hseed
    (by have h := hroot.1; norm_num at h; linarith)
    (fun _ => hroot.1) (fun _ => hupper) hsort hnonneg haccept
  have hsum : (pairRoot N p seed).word.sum +
      (chosen.map (coordinate N)).sum ≤ topCap := by
    simpa only [run_word, List.sum_append] using hfinal
  have hcanonical := actual_chosen_eq_canonical N enum _ _ chosen hsub hprod
  have hlen : chosen.length = r.primeFactorsList.length := by
    rw [hcanonical, List.length_reverse]
  have hrank : (r.primeFactorsList.length : ℝ) * omega ≤ topCap := by
    have hl := length_mul_le_sum (chosen.map (coordinate N)) omega hlower
    simp only [List.length_map, hlen] at hl
    linarith [hroot.2]
  have hrankR : (r.primeFactorsList.length : ℝ) ≤ topCap / omega :=
    (le_div_iff₀ homega).mpr hrank
  have hrankNat : r.primeFactorsList.length ≤ Nat.ceil (topCap / omega) := by
    exact_mod_cast hrankR.trans (Nat.le_ceil (topCap / omega))
  refine ⟨?_, hrankNat⟩
  obtain ⟨hcarrier, _⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hcarrier
  have h1pos := (mem_chenAdditivePrimeCarrier.mp hp1).2.1.pos
  have h2pos := (mem_chenAdditivePrimeCarrier.mp hp2).2.1.pos
  have hpower := coordinates_power hN (p.2 :: p.1 :: chosen) (by
    intro q hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | rfl | hq
    · exact h2pos
    · exact h1pos
    · exact (hprime q hq).pos)
  have hpower' : (N : ℝ) ^ ((pairRoot N p seed).word.sum +
      (chosen.map (coordinate N)).sum) = (((p.1 * p.2) * r : ℕ) : ℝ) := by
    simpa [pairRoot, List.map_cons, List.sum_cons, List.prod_cons, hprod,
      Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc] using hpower
  rw [← hpower']
  exact Real.rpow_le_rpow_of_exponent_le hN.le hsum

/-- The actual pair-root raw test has a unique canonical history, with
its external pair and original stored seed preserved. No cold-start square
margin or ordinary L1/L2 receiver is inserted. -/
theorem pair_raw_iff_canonical_warm {depth mesh : ℕ}
    (P : CapPlan depth mesh) (a b seed : ℝ) (N enum : ℕ)
    (p : ℕ × ℕ) (z0 z : ℝ) (r : ℕ) :
    r ∈ P2LowerFiniteCellRounding.rawSupport (pairPolicy P a b seed N p)
      N enum z0 z ↔ r ∈ P2LowerFiniteCellRounding.universe N enum z0 z ∧
      pairPolicy P a b seed N p r.primeFactorsList = true := by
  constructor
  · intro hr
    have hU := P2LowerFiniteCellRounding.rawSupport_subset_universe
      (pairPolicy P a b seed N p) N enum z0 z hr
    obtain ⟨chosen, hsub, haccept, hprod⟩ :=
      (pair_policy_support_iff P a b seed N enum p z0 z r).mp hr
    have hc := actual_chosen_eq_canonical N enum z0 z chosen hsub hprod
    refine ⟨hU, ?_⟩
    simpa only [pairPolicy, warmRetain, warmTrace, physicalWord, hc] using haccept
  · rintro ⟨hU, haccept⟩
    obtain ⟨hsub, hprod⟩ := canonical_subword_of_universe N enum z0 z hU
    apply (pair_policy_support_iff P a b seed N enum p z0 z r).mpr
    refine ⟨r.primeFactorsList.reverse, hsub, ?_, hprod⟩
    simpa only [pairPolicy, warmRetain, warmTrace, physicalWord] using haccept

/-- The actual pair-root ALL/ANY loss sees canonical WARM traces. The pair
seed and external coordinates are fixed while two same-label rough words
are compared; the ordinary cold trace is not substituted. -/
theorem mixed_pair_iff_canonical_warm {depth mesh : ℕ}
    (P : CapPlan depth mesh) (a b seed : ℝ) (N enum : ℕ)
    (p : ℕ × ℕ) (z0 z tau : ℝ) (d : ℕ) :
    P2RoundedCausalFibreLossAndLevel.mixed (pairPolicy P a b seed N p)
      N enum z0 z tau d ↔
      ∃ r ∈ P2LowerFiniteCellRounding.cell N enum z0 z tau d,
      ∃ s ∈ P2LowerFiniteCellRounding.cell N enum z0 z tau d,
        pairPolicy P a b seed N p r.primeFactorsList = true ∧
        pairPolicy P a b seed N p s.primeFactorsList ≠ true := by
  constructor
  · rintro ⟨⟨r, hr, hrraw⟩, s, hs, hsraw⟩
    refine ⟨r, hr, s, hs, ?_, ?_⟩
    · exact ((pair_raw_iff_canonical_warm P a b seed N enum p z0 z r).mp hrraw).2
    · intro ht
      exact hsraw ((pair_raw_iff_canonical_warm P a b seed N enum p z0 z s).mpr
        ⟨(Finset.mem_filter.mp hs).1, ht⟩)
  · rintro ⟨r, hr, s, hs, htr, hts⟩
    refine ⟨⟨r, hr, ?_⟩, ⟨s, hs, ?_⟩⟩
    · exact (pair_raw_iff_canonical_warm P a b seed N enum p z0 z r).mpr
        ⟨(Finset.mem_filter.mp hr).1, htr⟩
    · intro hraw
      exact hts ((pair_raw_iff_canonical_warm P a b seed N enum p z0 z s).mp hraw).2


/-- The previous fixed-mesh inflation theorem now consumes DERIVED actual
raw support/rank, so neither raw conclusion is a premise. The positive mesh
is selected before N and all later plans, pair seeds and arithmetic rows. -/
theorem exists_uniform_rounded_pair_level (omega ell nu : ℝ) (homega : 0 < omega)
    (hgap : topCap + ell < nu) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ N : ℕ, 1 < (N : ℝ) →
      ∀ (depth mesh : ℕ) (P : CapPlan depth mesh), PlanCeiling P topCap →
      ∀ (a b seed : ℝ), seed ≤ topCap → ∀ (enum : ℕ) (p : ℕ × ℕ),
      p ∈ sixthSupport N → ∀ q : ℕ,
      P2LowerFiniteCellBetaCompiler.rho (pairPolicy P a b seed N p) N enum
        ((N : ℝ) ^ omega) ((N : ℝ) ^ (417 / 5000 : ℝ)) tau ((N : ℝ) ^ ell) q ≠ 0 →
      (((p.1 * p.2) * q : ℕ) : ℝ) ≤ (N : ℝ) ^ nu := by
  obtain ⟨tau, htau, hbound⟩ :=
    P2RoundedCausalFibreLossAndLevel.exists_uniform_mesh_physical_level
      topCap ell nu (Nat.ceil (topCap / omega)) hgap
  refine ⟨tau, htau, ?_⟩
  intro N hN depth mesh P hP a b seed hseed enum p hp q hq
  apply hbound N hN (pairPolicy P a b seed N p) enum (p.1 * p.2)
    ((N : ℝ) ^ omega) ((N : ℝ) ^ (417 / 5000 : ℝ)) ?_ q hq
  intro r hr
  exact actual_pair_raw_full_prefix_rank P hP a b seed hseed hN enum hp omega homega hr


end
end ImbalancedChen.P2ActualPairPlanRawSupport
