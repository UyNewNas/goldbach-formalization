import ImbalancedChen.P2ActualMixedWarmDecisionWalls

/-!
# Concrete tent cap alphabet and whole-residual coarse-wall payment

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The alphabet is the independently computed canonical tent bank's actual
finite output, with its fixed rational seed. Every actual frozen parent
lies in that fixed alphabet, including inherited and rank4/5 parents.
The arithmetic part instantiates E at literal canonical-prefix coordinate
mesh walls and pays all their residual moduli. It does not bound the full
beta-attached absolute norm by the rough Euler constant.

This file is not full W/adopted L56 coverage or total density convergence:
the actual admission catalogue/root-offset and complete adoption bindings
are still separate obligations.
-/

namespace ImbalancedChen.P2CanonicalTentFiniteCapsAndCoarsePayment

noncomputable section
open scoped Classical BigOperators
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairSourceReceiver P2OriginalPairRootRoughProducer
open P2OriginalCanonicalPairTentBank P2ActualMixedWarmDecisionWalls
open P2CanonicalWallFullResidualPayment

/-- Fixed before N or any arithmetic prime word. -/
def capAlphabet (R : PairRange) (mesh : ℕ) (buffer seed : ℚ) : Finset ℝ :=
  insert (seed : ℝ) ((outputAlphabet R mesh buffer seed).image
    (fun c => c.freeze (seed : ℝ)))

private theorem freeze_mem_capAlphabet (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (c : CapChoice) (hc : c ∈ outputAlphabet R mesh buffer seed) (parent : ℝ)
    (hp : parent ∈ capAlphabet R mesh buffer seed) :
    c.freeze parent ∈ capAlphabet R mesh buffer seed := by
  cases c with
  | inherit s => exact hp
  | fresh v s =>
      apply Finset.mem_insert.mpr
      right
      exact Finset.mem_image.mpr ⟨.fresh v s, hc, rfl⟩

theorem actual_step_cap_in_fixed_alphabet (R : PairRange) (mesh : ℕ)
    (buffer seed : ℚ) (H : Trace) (x : ℝ)
    (hp : H.cap ∈ capAlphabet R mesh buffer seed) :
    (step (plan R mesh buffer seed) R.epsilon ceiling H x).cap ∈
      capAlphabet R mesh buffer seed := by
  change (planChoice (plan R mesh buffer seed) R.epsilon ceiling
    (H.word ++ [x])).freeze H.cap ∈ _
  unfold planChoice
  split_ifs
  · apply freeze_mem_capAlphabet R mesh buffer seed _ ?_ H.cap hp
    exact choice_mem_fixed_outputAlphabet R mesh buffer seed _ _
  · exact hp

/-- Every true frozen incoming cap, before and after rank4/5, is one of
these finite actual outputs. There is no ideal maximum or cap equality input. -/
theorem actual_run_cap_in_fixed_alphabet (R : PairRange) (mesh : ℕ)
    (buffer seed : ℚ) (H : Trace) (xs : List ℝ)
    (hp : H.cap ∈ capAlphabet R mesh buffer seed) :
    (run (plan R mesh buffer seed) R.epsilon ceiling H xs).cap ∈
      capAlphabet R mesh buffer seed := by
  induction xs generalizing H with
  | nil => exact hp
  | cons x xs ih =>
      exact ih (step (plan R mesh buffer seed) R.epsilon ceiling H x)
        (actual_step_cap_in_fixed_alphabet R mesh buffer seed H x hp)

theorem actual_pair_prefix_cap_in_fixed_alphabet (R : PairRange) (mesh : ℕ)
    (buffer seed : ℚ) (N : ℕ) (p : ℕ × ℕ) (xs : List ℝ) (j : ℕ) :
    (run (plan R mesh buffer seed) R.epsilon ceiling (pairRoot N p seed) (xs.take j)).cap ∈
      capAlphabet R mesh buffer seed := by
  apply actual_run_cap_in_fixed_alphabet
  exact Finset.mem_insert_self _ _

/-- Every witnessed actual admission wall has a cap from the PRE-N finite
alphabet. The root coordinates remain literal: their varying sum is not
silently treated as a fixed intercept in the arithmetic wall theorem. -/
theorem actual_pair_admission_finite_cap_wall (R : PairRange) (mesh : ℕ)
    (buffer seed : ℚ) (N : ℕ) (p : ℕ × ℕ) (xs : List ℝ) (j : ℕ) (width : ℝ)
    (hw : |(run (plan R mesh buffer seed) R.epsilon ceiling
      (pairRoot N p seed) (xs.take j)).word.sum + 3 * xs.getD j 0 -
        (run (plan R mesh buffer seed) R.epsilon ceiling
          (pairRoot N p seed) (xs.take j)).cap| ≤ width) :
    ∃ c ∈ capAlphabet R mesh buffer seed,
      |(pairRoot N p seed).word.sum + (xs.take j).sum + 3 * xs.getD j 0 - c| ≤ width := by
  refine ⟨_, actual_pair_prefix_cap_in_fixed_alphabet R mesh buffer seed N p xs j, ?_⟩
  simpa only [run_word, List.sum_append] using hw

/-- Literal proper affine walls for the LAST coordinate of a canonical
prefix. Every actual changed coarse coordinate is some such prefix's last
coordinate; the boundary alphabet includes both receiver endpoints. -/
def coarseForms (j mesh : ℕ) :
    Fin (mesh + 2) → (Fin (j + 1) → ℝ) →L[ℝ] ℝ :=
  fun _ => ContinuousLinearMap.proj (Fin.last j)

def coarseHeights (a b : ℝ) (mesh : ℕ) : Fin (mesh + 2) → ℝ :=
  fun q => logPrimeMeshPoint a b mesh q.val

theorem coarseForms_ne_zero (j mesh : ℕ) : ∀ q, coarseForms j mesh q ≠ 0 := by
  intro q h
  have heq := congrArg (fun f : (Fin (j + 1) → ℝ) →L[ℝ] ℝ => f (fun _ => 1)) h
  simp only [coarseForms, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply] at heq
  norm_num at heq

private theorem getD_take_self (xs : List ℕ) (j : ℕ) :
    (xs.take (j + 1)).getD j 0 = xs.getD j 0 := by
  induction xs generalizing j with
  | nil => simp
  | cons x xs ih =>
      cases j with
      | zero => simp
      | succ j => simpa only [List.take_succ_cons, List.getD_cons_succ] using ih j

private theorem getD_coordinate_map (N : ℕ) (xs : List ℕ) (j : ℕ) :
    (xs.map (coordinate N)).getD j 0 = coordinate N (xs.getD j 0) := by
  induction xs generalizing j with
  | nil => simp [coordinate]
  | cons x xs ih =>
      cases j with
      | zero => simp
      | succ j => simpa only [List.map_cons, List.getD_cons_succ] using ih j

/-- The actual canonical arithmetic prefix, not a newly defined proxy,
has precisely the compiler coordinate at this genuine prime slot. -/
theorem canonical_last_coordinate (N d j : ℕ) :
    coarseForms j 0 0 (actualPrimeTupleLog N (canonicalPrefix (j + 1) d)) =
      (physicalWord N d.primeFactorsList).getD j 0 := by
  simp only [coarseForms, ContinuousLinearMap.proj_apply, actualPrimeTupleLog,
    canonicalPrefix, primeHistoryTuple, List.reverse_reverse, Fin.val_last,
    getD_take_self, physicalWord, getD_coordinate_map, coordinate]

/-- A literal actual coordinate mesh wall enters the already-paid E
arithmetic canonical-wall carrier. The full residual tail remains attached. -/
theorem canonical_coarse_wall_membership (N enum d j mesh : ℕ) (omega v a b delta : ℝ)
    (hd : d ∈ P2LowerFiniteCellRounding.universe
      N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ v))
    (hj : j < d.primeFactorsList.length)
    (hw : ∃ q : Fin (mesh + 2),
      |(physicalWord N d.primeFactorsList).getD j 0 -
        logPrimeMeshPoint a b mesh q.val| ≤ delta) :
    d ∈ canonicalWallModuli N enum omega v (coarseForms j mesh) (coarseHeights a b mesh) delta := by
  apply Finset.mem_filter.mpr
  refine ⟨hd, by omega, ?_⟩
  obtain ⟨q, hq⟩ := hw
  refine ⟨q, ?_⟩
  have hc : coarseForms j mesh q (actualPrimeTupleLog N (canonicalPrefix (j + 1) d)) =
      (physicalWord N d.primeFactorsList).getD j 0 :=
    canonical_last_coordinate N d j
  simpa only [hc, coarseHeights] using hq

private theorem exists_getD_of_mem (xs : List ℝ) (x : ℝ) (hx : x ∈ xs) :
    ∃ j : ℕ, j < xs.length ∧ xs.getD j 0 = x := by
  revert hx
  induction xs with
  | nil => intro hx; simp at hx
  | cons y ys ih =>
      intro hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨0, by simp, by simp⟩
      · obtain ⟨j, hj, heq⟩ := ih hx
        exact ⟨j + 1, by simpa using Nat.succ_lt_succ hj,
          by simpa only [List.getD_cons_succ] using heq⟩

/-- Any coarse wall found anywhere in the actual canonical word belongs
to one of the finite prefix-wall carriers paid below, with its true rank.
This removes a possible gap between a coordinate witness and a modulus. -/
theorem coarse_coordinate_enters_finite_paid_bank
    (N enum d R mesh : ℕ) (omega v a b delta : ℝ)
    (hd : d ∈ P2LowerFiniteCellRounding.universe
      N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ v))
    (hR : d.primeFactorsList.length ≤ R)
    (hw : ∃ x ∈ physicalWord N d.primeFactorsList, ∃ q : Fin (mesh + 2),
      |x - logPrimeMeshPoint a b mesh q.val| ≤ delta) :
    ∃ j : Fin R, d ∈ canonicalWallModuli N enum omega v
      (coarseForms j.val mesh) (coarseHeights a b mesh) delta := by
  obtain ⟨x, hx, q, hq⟩ := hw
  obtain ⟨j, hj, heq⟩ := exists_getD_of_mem _ x hx
  have hjrank : j < d.primeFactorsList.length := by
    simpa only [physicalWord, List.length_map, List.length_reverse] using hj
  refine ⟨⟨j, hjrank.trans_le hR⟩, ?_⟩
  apply canonical_coarse_wall_membership N enum d j mesh omega v a b delta hd hjrank
  exact ⟨q, by simpa only [heq] using hq⟩

/-- E's FULL residual-modulus mass theorem now applies to the actual
coarse-code walls just constructed, before N/cap/policy/fine mesh. -/
theorem exists_actual_coarse_full_residual_payment (j mesh : ℕ)
    (omega v a b : ℝ) (homega : 0 < omega) (hov : omega < v)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ enum : ℕ,
      ∀ (keep : List ℕ → Bool) (tau : ℝ),
        wallRoundingCharge keep N enum omega v tau
          (coarseForms j mesh) (coarseHeights a b mesh) delta < eta := by
  exact exists_uniform_full_residual_wall_payment omega v homega hov
    (coarseForms j mesh) (coarseHeights a b mesh) (coarseForms_ne_zero j mesh) eta heta

/-- The same literal coarse walls are paid for the ACTUAL lower beta
physical rho at the manuscript normalization, using E's proven swap.
This is not a claim about the complete attached absolute mean norm. -/
theorem exists_actual_coarse_lower_density_reserve (j mesh : ℕ)
    (nu epsilon v a b : ℝ) (hnu : 0 < nu) (he : 0 < epsilon) (he8 : epsilon < 1 / 8)
    (hv : nu * epsilon ^ 2 < v) (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ enum : ℕ,
      (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (enum : ℝ) →
      ∀ (keep : List ℕ → Bool) (tau : ℝ),
      let omega := nu * epsilon ^ 2
      let level := (N : ℝ) ^ (nu * epsilon)
      |P2ActualLowerCanonicalWallDensity.lowerWallDensity N enum omega v level
          (coarseForms j mesh) (coarseHeights a b mesh) delta
          (P2LowerFiniteCellRounding.coefficient keep N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau) -
        P2ActualLowerCanonicalWallDensity.lowerWallDensity N enum omega v level
          (coarseForms j mesh) (coarseHeights a b mesh) delta
          (P2LowerFiniteCellRounding.raw keep N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ v))| ≤
        eta * (singularSeries N / Real.log (N : ℝ)) := by
  exact P2ActualLowerCanonicalWallDensity.exists_actual_lower_full_residual_wall_reserve
    nu epsilon v hnu he he8 hv (coarseForms j mesh) (coarseHeights a b mesh)
      (coarseForms_ne_zero j mesh) eta heta

private theorem exists_common_positive_width {ι : Type*} (s : Finset ι)
    (width : ι → ℝ) (hwidth : ∀ i ∈ s, 0 < width i) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ i ∈ s, delta ≤ width i := by
  revert hwidth
  induction s using Finset.induction_on with
  | empty => intro _; exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
      intro hwidth
      obtain ⟨delta, hd, hs⟩ := ih (fun j hj => hwidth j (Finset.mem_insert_of_mem hj))
      refine ⟨min (width i) delta, lt_min (hwidth i (Finset.mem_insert_self _ _)) hd, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hs j hj)

theorem wallRoundingCharge_mono {j k : ℕ} (keep : List ℕ → Bool)
    (N enum : ℕ) (omega v tau : ℝ)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ)
    {delta width : ℝ} (hd : delta ≤ width) :
    wallRoundingCharge keep N enum omega v tau L c delta ≤
      wallRoundingCharge keep N enum omega v tau L c width := by
  unfold wallRoundingCharge
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    obtain ⟨hrU, hj, q, hq⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hrU, hj, q, hq.trans hd⟩
  · intro r _ _
    positivity

/-- Complete finite coarse-wall charge, at every possible prefix rank
below R, with ALL residual moduli kept in each literal canonical carrier.
Overlapping walls may safely overcount the nonnegative coefficient error. -/
def coarseBankCharge (R mesh : ℕ) (keep : List ℕ → Bool) (N enum : ℕ)
    (omega v tau a b delta : ℝ) : ℝ :=
  ∑ j : Fin R, wallRoundingCharge keep N enum omega v tau
    (coarseForms j.val mesh) (coarseHeights a b mesh) delta

/-- ONE positive width BEFORE ONE N threshold pays the entire fixed-rank
coarse-code catalogue. This is a full finite-bank residual mass estimate,
not an entry bound or a per-N/per-rank choice of mesh. -/
theorem exists_uniform_full_coarse_bank_payment (R mesh : ℕ)
    (omega v a b : ℝ) (homega : 0 < omega) (hov : omega < v)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ enum : ℕ,
      ∀ (keep : List ℕ → Bool) (tau : ℝ),
        coarseBankCharge R mesh keep N enum omega v tau a b delta < eta := by
  let budget : ℝ := eta / (2 * ((R : ℝ) + 1))
  have hb : 0 < budget := by dsimp [budget]; positivity
  have hsupply : ∀ j : Fin R, ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ enum : ℕ,
      ∀ (keep : List ℕ → Bool) (tau : ℝ),
        wallRoundingCharge keep N enum omega v tau
          (coarseForms j.val mesh) (coarseHeights a b mesh) delta < budget :=
    fun j => exists_actual_coarse_full_residual_payment j.val mesh
      omega v a b homega hov budget hb
  choose width hwidth Nstart hNstart hpay using hsupply
  obtain ⟨delta, hd, hdle⟩ := exists_common_positive_width Finset.univ width
    (fun j _ => hwidth j)
  let N0 := max 2 (Finset.univ.sup Nstart)
  refine ⟨delta, hd, N0, le_max_left _ _, ?_⟩
  intro N hN hEven enum keep tau
  have heach (j : Fin R) : wallRoundingCharge keep N enum omega v tau
      (coarseForms j.val mesh) (coarseHeights a b mesh) delta ≤ budget := by
    have hNj : Nstart j ≤ N :=
      (Finset.le_sup (f := Nstart) (Finset.mem_univ j)).trans
        ((le_max_right _ _).trans hN)
    exact (wallRoundingCharge_mono keep N enum omega v tau _ _
      (hdle j (Finset.mem_univ j))).trans (hpay j N hNj hEven enum keep tau).le
  have htotal : (R : ℝ) * budget < eta := by
    dsimp [budget]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * ((R : ℝ) + 1))).mpr
    have hR : 0 ≤ (R : ℝ) := by positivity
    have hmul : 0 ≤ eta * (R : ℝ) := mul_nonneg heta.le hR
    nlinarith
  calc
    coarseBankCharge R mesh keep N enum omega v tau a b delta ≤
        ∑ _j : Fin R, budget := Finset.sum_le_sum (fun j _ => heach j)
    _ = (R : ℝ) * budget := by simp
    _ < eta := htotal

end
end ImbalancedChen.P2CanonicalTentFiniteCapsAndCoarsePayment
