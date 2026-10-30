import ImbalancedChen.FirstExitValidSelection
import ImbalancedChen.ActualSmallRosserFiniteDensity
import ImbalancedChen.ActualPrimePresieveSplit
import ImbalancedChen.FinitePrimeGeometryCore

/-!
# Literal ordinary Rosser retention policies

The prefix predicate checks both the strict total-product cutoff and all
parity-selected cubic tests. The tree stores a prefix in increasing order,
opposite to its decreasing processing order. Checking this full prefix
predicate retains precisely the ordinary Rosser divisors: earlier prefixes
are recovered by repeatedly deleting the least selected prime.

The Boolean `lower` selects the lower rather than upper admissibility test.
The policy records the full test at each branch; it is not a claim that
arbitrary, unreachable histories have the alternating first-exit parity.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical List BigOperators
open MathlibNt.SieveTheory

/-- A constant-level ordinary policy, expressed on the actual selected prefix. -/
def ordinaryRosserRetainedPolicy (lower : Bool) (R : ℝ)
    (_positive : Bool) (pre : List ℕ) : Bool :=
  decide (ordinaryRosserPrefixAdmissible lower R pre)

theorem ordinaryRosserPrefixAdmissible_nil (lower : Bool) {R : ℝ} (hR : 1 < R) :
    ordinaryRosserPrefixAdmissible lower R [] := by
  cases lower <;> simp [ordinaryRosserPrefixAdmissible,
    LiLiuPrereqWF.SmallRosser.LowerAdmissibleSet,
    LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet, hR]

/-- Removing the least selected prime preserves every earlier parity test.
The total-product test is preserved because the removed prime is positive. -/
theorem ordinaryRosserPrefixAdmissible_tail
    (lower : Bool) (R : ℝ) (q : ℕ) (pre : List ℕ)
    (hq : q.Prime) (hsort : (q :: pre).Pairwise (· < ·))
    (hadm : ordinaryRosserPrefixAdmissible lower R (q :: pre)) :
    ordinaryRosserPrefixAdmissible lower R pre := by
  have hmin := (List.pairwise_cons.mp hsort).1
  have hnot : q ∉ pre.toFinset := by
    intro hqmem
    exact (lt_irrefl q) (hmin q (List.mem_toFinset.mp hqmem))
  have hmin' : ∀ p ∈ pre.toFinset, q ≤ p :=
    fun p hp => (hmin p (List.mem_toFinset.mp hp)).le
  have hprod : (pre.prod : ℝ) < R := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_lt.le
    have h := hadm.1
    simp only [List.prod_cons, Nat.cast_mul] at h
    nlinarith [Nat.cast_nonneg (α := ℝ) pre.prod]
  refine ⟨hprod, ?_⟩
  cases lower with
  | false =>
      exact LiLiuPrereqWF.SmallRosser.upperAdmissible_of_insert_min hnot hmin'
        (by simpa only [ordinaryRosserPrefixAdmissible, Bool.false_eq_true, if_false,
          List.toFinset_cons] using hadm.2)
  | true =>
      exact LiLiuPrereqWF.SmallRosser.admissible_of_insert_min hnot hmin'
        (by simpa only [ordinaryRosserPrefixAdmissible, if_true,
          List.toFinset_cons] using hadm.2)

theorem ordinaryRosserPrefixAdmissible_of_append
    (lower : Bool) (R : ℝ) (small pre : List ℕ)
    (hprime : ∀ p ∈ small ++ pre, p.Prime)
    (hsort : (small ++ pre).Pairwise (· < ·))
    (hadm : ordinaryRosserPrefixAdmissible lower R (small ++ pre)) :
    ordinaryRosserPrefixAdmissible lower R pre := by
  induction small with
  | nil => simpa using hadm
  | cons q qs ih =>
      have hp := hprime q (by simp)
      have htail := ordinaryRosserPrefixAdmissible_tail lower R q (qs ++ pre) hp hsort hadm
      exact ih (fun p hp => hprime p (List.mem_cons_of_mem q hp))
        (List.pairwise_cons.mp hsort).2 htail

/-- Valid selection is equivalent to the final full ordinary test, provided
the incoming prefix is valid and the completed selection is increasing. -/
theorem firstExitValidSelection_ordinaryRosser_iff
    (lower : Bool) (R : ℝ) (chosen pre : List ℕ) (positive : Bool)
    (hpre : ordinaryRosserPrefixAdmissible lower R pre)
    (hprime : ∀ p ∈ chosen.reverse ++ pre, p.Prime)
    (hsort : (chosen.reverse ++ pre).Pairwise (· < ·)) :
    FirstExitValidSelection (ordinaryRosserRetainedPolicy lower R) pre positive chosen ↔
      ordinaryRosserPrefixAdmissible lower R (chosen.reverse ++ pre) := by
  induction chosen generalizing pre positive with
  | nil => simpa [FirstExitValidSelection] using hpre
  | cons p ps ih =>
      have hprime' : ∀ q ∈ ps.reverse ++ p :: pre, q.Prime := by
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hprime
      have hsort' : (ps.reverse ++ p :: pre).Pairwise (· < ·) := by
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hsort
      rw [FirstExitValidSelection]
      constructor
      · rintro ⟨htest, htail⟩
        have hnext : ordinaryRosserPrefixAdmissible lower R (p :: pre) := by
          simpa only [ordinaryRosserRetainedPolicy, decide_eq_true_eq] using htest
        have h := (ih (p :: pre) (!positive) hnext hprime' hsort').mp htail
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using h
      · intro h
        have hfinal : ordinaryRosserPrefixAdmissible lower R (ps.reverse ++ p :: pre) := by
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using h
        have hnext := ordinaryRosserPrefixAdmissible_of_append lower R ps.reverse (p :: pre)
          hprime' hsort' hfinal
        refine ⟨by simpa only [ordinaryRosserRetainedPolicy, decide_eq_true_eq] using hnext, ?_⟩
        exact (ih (p :: pre) (!positive) hnext hprime' hsort').mpr hfinal

private theorem primeFactors_list_prod_eq_toFinset
    (xs : List ℕ) (hnodup : xs.Nodup) (hprime : ∀ p ∈ xs, p.Prime) :
    xs.prod.primeFactors = xs.toFinset := by
  have hprod : (∏ p ∈ xs.toFinset, p) = xs.prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p) hnodup
  rw [← hprod]
  exact Nat.primeFactors_prod (fun p hp => hprime p (List.mem_toFinset.mp hp))

/-- Exact retained support, including the reverse inclusion constructing a
retained leaf for every provider-admissible divisor. -/
theorem mem_ordinaryRosserRetainedModuli_iff
    (lower : Bool) (R : ℝ) (hR : 1 < R) (carrier : List ℕ)
    (hsort : carrier.Pairwise (· > ·)) (hprime : ∀ p ∈ carrier, p.Prime) (d : ℕ) :
    d ∈ firstExitRetainedModuli (ordinaryRosserRetainedPolicy lower R) carrier ↔
      d ∈ carrier.prod.divisors ∧ (d : ℝ) < R ∧
        (if lower then LiLiuPrereqWF.SmallRosser.LowerAdmissibleSet R d.primeFactors
          else LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R d.primeFactors) := by
  have hnodup := hsort.nodup
  have hcarrier0 : carrier.prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hzero
    exact (hprime 0 hzero).ne_zero rfl
  have hpf := primeFactors_list_prod_eq_toFinset carrier hnodup hprime
  rw [mem_firstExitRetainedModuli_iff_validSelection]
  constructor
  · rintro ⟨chosen, hsub, hvalid, rfl⟩
    have hcprime : ∀ p ∈ chosen, p.Prime := fun p hp => hprime p (hsub.subset hp)
    have hcnodup := hnodup.sublist hsub
    have hcsort : chosen.reverse.Pairwise (· < ·) := by
      simpa only [List.pairwise_reverse] using hsort.sublist hsub
    have hfull := (firstExitValidSelection_ordinaryRosser_iff lower R chosen [] true
      (ordinaryRosserPrefixAdmissible_nil lower hR)
      (by simpa using hcprime) (by simpa using hcsort)).mp hvalid
    simp only [List.append_nil, ordinaryRosserPrefixAdmissible, List.prod_reverse,
      List.toFinset_reverse] at hfull
    refine ⟨Nat.mem_divisors.mpr ⟨hsub.prod_dvd_prod, hcarrier0⟩, hfull.1, ?_⟩
    simpa only [primeFactors_list_prod_eq_toFinset chosen hcnodup hcprime] using hfull.2
  · rintro ⟨hdiv, hlevel, hadm⟩
    have hdvd : d ∣ carrier.prod := (Nat.mem_divisors.mp hdiv).1
    have hdsq : Squarefree d := fun x hx =>
      list_prod_squarefree_of_nodup_primes carrier hnodup hprime x (hx.trans hdvd)
    have hsubset : d.primeFactors ⊆ carrier.toFinset := by
      rw [← hpf]
      exact Nat.primeFactors_mono hdvd hcarrier0
    let chosen := carrier.filter (fun p => p ∈ d.primeFactors)
    have hsub : chosen <+ carrier := List.filter_sublist
    have hcset : chosen.toFinset = d.primeFactors := by
      ext p
      simp only [chosen, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · exact fun hp => ⟨List.mem_toFinset.mp (hsubset hp), hp⟩
    have hcprod : chosen.prod = d := by
      have heq : (∏ p ∈ chosen.toFinset, p) = chosen.prod := by
        simpa using List.prod_toFinset (fun p : ℕ => p) (hnodup.sublist hsub)
      rw [← heq]
      simpa only [hcset] using Nat.prod_primeFactors_of_squarefree hdsq
    have hcprime : ∀ p ∈ chosen, p.Prime := fun p hp => hprime p (hsub.subset hp)
    have hcsort : chosen.reverse.Pairwise (· < ·) := by
      simpa only [List.pairwise_reverse] using hsort.sublist hsub
    refine ⟨chosen, hsub, ?_, hcprod⟩
    apply (firstExitValidSelection_ordinaryRosser_iff lower R chosen [] true
      (ordinaryRosserPrefixAdmissible_nil lower hR)
      (by simpa using hcprime) (by simpa using hcsort)).mpr
    simpa only [ordinaryRosserPrefixAdmissible, List.append_nil, List.prod_reverse,
      List.toFinset_reverse, hcprod, hcset] using And.intro hlevel hadm

/-- The literal real-level ordinary coefficient selected by the parity flag. -/
def ordinaryRosserWeight (lower : Bool) (M : ℕ) (R : ℝ) : ℕ → ℝ :=
  if lower then LiLiuPrereqWF.SmallRosser.lowerWeight M R
  else LiLiuPrereqWF.SmallRosser.upperWeight M R

/-- The full-prefix tree gives exactly the provider's coefficient at every
natural modulus, including zero and moduli outside the retained support. -/
theorem firstExitRetainedCoefficient_ordinaryRosser
    (lower : Bool) (R : ℝ) (hR : 1 < R) (carrier : List ℕ)
    (hsort : carrier.Pairwise (· > ·)) (hprime : ∀ p ∈ carrier, p.Prime) (d : ℕ) :
    (firstExitRetainedCoefficient (ordinaryRosserRetainedPolicy lower R) carrier d : ℝ) =
      ordinaryRosserWeight lower carrier.prod R d := by
  have hiff := mem_ordinaryRosserRetainedModuli_iff lower R hR carrier hsort hprime d
  have hmu (hd : d ∈ firstExitRetainedModuli (ordinaryRosserRetainedPolicy lower R) carrier) :
      (ArithmeticFunction.moebius d : ℝ) = (-1 : ℝ) ^ d.primeFactors.card := by
    obtain ⟨chosen, hsub, _hvalid, rfl⟩ :=
      (mem_firstExitRetainedModuli_iff_validSelection _ _ _).mp hd
    have hcnodup := hsort.nodup.sublist hsub
    have hcprime : ∀ p ∈ chosen, p.Prime := fun p hp => hprime p (hsub.subset hp)
    rw [primeFactors_list_prod_eq_toFinset chosen hcnodup hcprime,
      List.toFinset_card_of_nodup hcnodup,
      moebius_list_prod_eq_negOnePow_length chosen hcnodup hcprime]
    norm_cast
  by_cases hd : d ∈ firstExitRetainedModuli (ordinaryRosserRetainedPolicy lower R) carrier
  · have ha := hiff.mp hd
    rw [firstExitRetainedCoefficient, if_pos hd, hmu hd]
    cases lower <;>
      simp only [ordinaryRosserWeight, Bool.false_eq_true, if_false, if_true,
        LiLiuPrereqWF.SmallRosser.lowerWeight_apply,
        LiLiuPrereqWF.SmallRosser.upperWeight_apply] at ha ⊢ <;> rw [if_pos ha]
  · have ha := fun h => hd (hiff.mpr h)
    rw [firstExitRetainedCoefficient, if_neg hd, Int.cast_zero]
    cases lower <;>
      simp only [ordinaryRosserWeight, Bool.false_eq_true, if_false, if_true,
        LiLiuPrereqWF.SmallRosser.lowerWeight_apply,
        LiLiuPrereqWF.SmallRosser.upperWeight_apply] at ha ⊢ <;> rw [if_neg ha]

/-- The root polynomial is the ordinary Rosser sum with arbitrary local
prime weights. This identity is independent of any analytic estimate. -/
theorem firstExitRetainedPolynomial_ordinaryRosser
    (lower : Bool) (R : ℝ) (hR : 1 < R) (carrier : List ℕ)
    (hsort : carrier.Pairwise (· > ·)) (hprime : ∀ p ∈ carrier, p.Prime)
    (h : ℕ → ℝ) :
    firstExitRetainedPolynomial (ordinaryRosserRetainedPolicy lower R) h [] true 1 carrier =
      ∑ d ∈ carrier.prod.divisors, ordinaryRosserWeight lower carrier.prod R d *
        d.primeFactors.prod h := by
  rw [firstExitRetainedPolynomial_eq_retainedModuli_sum _ _ _ hsort.nodup hprime]
  simp_rw [firstExitRetainedCoefficient_ordinaryRosser lower R hR carrier hsort hprime]
  apply Finset.sum_subset
  · intro d hd
    exact ((mem_ordinaryRosserRetainedModuli_iff lower R hR carrier hsort hprime d).mp hd).1
  · intro d _hd hdnot
    rw [← firstExitRetainedCoefficient_ordinaryRosser lower R hR carrier hsort hprime,
      firstExitRetainedCoefficient, if_neg hdnot, Int.cast_zero, zero_mul]

private theorem actualSmallPrimeProduct_eq_universe_prod (N cap : ℕ) (y : ℝ) :
    actualSmallPrimeProduct N cap y = (roughPrimeUniverse N cap 0 y).prod := by
  unfold actualSmallPrimeProduct actualSmallPrimeFinset
  rw [← roughPrimeUniverse_toFinset N cap 0 y]
  simpa using List.prod_toFinset (fun p : ℕ => p) (roughPrimeUniverse_nodup N cap 0 y)

/-- Exact actual upper coefficient dictionary. The real strict level is the
same argument of `actualSmallRosserPlus`, hence its natural level is `ceil R`. -/
theorem firstExitRetainedCoefficient_eq_actualSmallRosserPlus
    (N cap : ℕ) (y R : ℝ) (hR : 1 < R) (d : ℕ) :
    (firstExitRetainedCoefficient (ordinaryRosserRetainedPolicy false R)
      (roughPrimeUniverse N cap 0 y) d : ℝ) = actualSmallRosserPlus N cap y R d := by
  rw [firstExitRetainedCoefficient_ordinaryRosser false R hR _
    (roughPrimeUniverse_pairwise_gt N cap 0 y) (fun _ hp => mem_roughPrimeUniverse_prime hp)]
  simp only [ordinaryRosserWeight, Bool.false_eq_true, if_false, actualSmallRosserPlus,
    actualSmallPrimeProduct_eq_universe_prod]

/-- Exact actual lower coefficient dictionary, also without a cap-coverage
or prime-level hypothesis: the displayed finite carrier is used literally. -/
theorem firstExitRetainedCoefficient_eq_actualSmallRosserMinus
    (N cap : ℕ) (y R : ℝ) (hR : 1 < R) (d : ℕ) :
    (firstExitRetainedCoefficient (ordinaryRosserRetainedPolicy true R)
      (roughPrimeUniverse N cap 0 y) d : ℝ) = actualSmallRosserMinus N cap y R d := by
  rw [firstExitRetainedCoefficient_ordinaryRosser true R hR _
    (roughPrimeUniverse_pairwise_gt N cap 0 y) (fun _ hp => mem_roughPrimeUniverse_prime hp)]
  simp only [ordinaryRosserWeight, if_true, actualSmallRosserMinus,
    actualSmallPrimeProduct_eq_universe_prod]

theorem firstExitRetainedPolynomial_eq_actualSmallRosserDensity
    (lower : Bool) (N cap : ℕ) (y R : ℝ) (hR : 1 < R) :
    firstExitRetainedPolynomial (ordinaryRosserRetainedPolicy lower R)
        (fun p => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 y) =
      if lower then actualSmallRosserMinusDensity N cap y R
        else actualSmallRosserPlusDensity N cap y R := by
  rw [firstExitRetainedPolynomial_ordinaryRosser lower R hR _
    (roughPrimeUniverse_pairwise_gt N cap 0 y) (fun _ hp => mem_roughPrimeUniverse_prime hp)]
  rw [← actualSmallPrimeProduct_eq_universe_prod]
  have hsquare : ∀ d ∈ (actualSmallPrimeProduct N cap y).divisors, Squarefree d := by
    intro d hd x hx
    exact actualSmallPrimeProduct_squarefree N cap y x (hx.trans (Nat.mem_divisors.mp hd).1)
  cases lower <;>
    simp only [ordinaryRosserWeight, Bool.false_eq_true, if_false, if_true,
      actualSmallRosserMinusDensity, actualSmallRosserPlusDensity,
      reciprocalTotientDensity, actualSmallRosserSupport, actualSmallRosserMinus,
      actualSmallRosserPlus]
  all_goals
    apply Finset.sum_congr rfl
    intro d hd
    rw [primeFactors_prod_reciprocalTotient (hsquare d hd)]
    ring

@[simp] theorem ordinaryParityRosserPolicy_upper_even (R : ℝ) (pre : List ℕ) :
    ordinaryParityRosserPolicy false R true pre = true := by
  simp [ordinaryParityRosserPolicy]

@[simp] theorem ordinaryParityRosserPolicy_lower_odd (R : ℝ) (pre : List ℕ) :
    ordinaryParityRosserPolicy true R false pre = true := by
  simp [ordinaryParityRosserPolicy]

/-- A valid incoming prefix makes the inactive parity automatically pass
the total and cubic tests. For lower weights the first prime must be below
the level; upper weights obtain this from their first cube. -/
theorem ordinaryParityRosserPolicy_eq_full_on_valid_prefix
    (lower : Bool) (R : ℝ) (pre : List ℕ) (positive : Bool) (q : ℕ)
    (hpre : ordinaryRosserPrefixAdmissible lower R pre)
    (hsign : positive = evenListLength pre) (hq : q.Prime)
    (hqR : lower = true → (q : ℝ) < R)
    (hsort : (q :: pre).Pairwise (· < ·)) :
    ordinaryParityRosserPolicy lower R (!positive) (q :: pre) =
      ordinaryRosserRetainedPolicy lower R (!positive) (q :: pre) := by
  have hmin := (List.pairwise_cons.mp hsort).1
  have hnot : q ∉ pre.toFinset := by
    intro hqmem
    exact (lt_irrefl q) (hmin q (List.mem_toFinset.mp hqmem))
  have hmin' : ∀ p ∈ pre.toFinset, q ≤ p :=
    fun p hp => (hmin p (List.mem_toFinset.mp hp)).le
  have hnd := (List.pairwise_cons.mp hsort).2.nodup
  have hprod : (∏ p ∈ pre.toFinset, p) = pre.prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p) hnd
  have hparity : ∀ xs : List ℕ, evenListLength xs = decide (Even xs.length) := by
    intro xs
    induction xs with
    | nil => simp [evenListLength]
    | cons x xs ih =>
        simp only [evenListLength, ih, List.length_cons, Nat.even_add_one, decide_not]
  cases lower <;> cases positive
  · have hodd : ¬Even pre.toFinset.card := by
      simpa only [List.toFinset_card_of_nodup hnd, hparity, decide_eq_false_iff_not]
        using hsign.symm
    have ha := LiLiuPrereqWF.SmallRosser.upperAdmissible_insert_min_of_odd
      hnot hmin' hpre.2 hodd
    have hl := LiLiuPrereqWF.SmallRosser.prod_insert_min_lt_of_odd
      hnot hq hmin' hpre.2 hodd
    have hfull : ordinaryRosserPrefixAdmissible false R (q :: pre) := by
      refine ⟨?_, ?_⟩
      · simpa only [Finset.prod_insert hnot, id_eq, hprod, List.prod_cons] using hl
      · simpa only [Bool.false_eq_true, if_false, List.toFinset_cons] using ha
    simp [ordinaryParityRosserPolicy, ordinaryRosserRetainedPolicy, hfull]
  · rfl
  · rfl
  · have heven : Even pre.toFinset.card := by
      simpa only [List.toFinset_card_of_nodup hnd, hparity, decide_eq_true_iff]
        using hsign.symm
    have ha := LiLiuPrereqWF.SmallRosser.admissible_insert_min_of_even
      hnot hmin' hpre.2 heven
    have hl := LiLiuPrereqWF.SmallRosser.prod_insert_min_lt_of_even
      hnot hq (hqR rfl) hmin' hpre.2 heven
    have hfull : ordinaryRosserPrefixAdmissible true R (q :: pre) := by
      refine ⟨?_, ?_⟩
      · simpa only [Finset.prod_insert hnot, id_eq, hprod, List.prod_cons] using hl
      · simpa only [if_true, List.toFinset_cons] using ha
    simp [ordinaryParityRosserPolicy, ordinaryRosserRetainedPolicy, hfull]

theorem firstExitValidSelection_ordinaryParityRosser_iff
    (lower : Bool) (R : ℝ) (chosen pre : List ℕ) (positive : Bool)
    (hpre : ordinaryRosserPrefixAdmissible lower R pre)
    (hsign : positive = evenListLength pre)
    (hprime : ∀ p ∈ chosen.reverse ++ pre, p.Prime)
    (hlevel : lower = true → ∀ p ∈ chosen, (p : ℝ) < R)
    (hsort : (chosen.reverse ++ pre).Pairwise (· < ·)) :
    FirstExitValidSelection (ordinaryParityRosserPolicy lower R) pre positive chosen ↔
      FirstExitValidSelection (ordinaryRosserRetainedPolicy lower R) pre positive chosen := by
  induction chosen generalizing pre positive with
  | nil => rfl
  | cons q qs ih =>
      have hprime' : ∀ p ∈ qs.reverse ++ q :: pre, p.Prime := by
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hprime
      have hsort' : (qs.reverse ++ q :: pre).Pairwise (· < ·) := by
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hsort
      have hq : q.Prime := hprime' q (by simp)
      have htest := ordinaryParityRosserPolicy_eq_full_on_valid_prefix lower R pre positive q
        hpre hsign hq (fun hl => hlevel hl q (by simp)) (List.pairwise_append.mp hsort').2.1
      simp only [FirstExitValidSelection, htest]
      by_cases hnext : ordinaryRosserPrefixAdmissible lower R (q :: pre)
      · have hsign' : (!positive) = evenListLength (q :: pre) := by
          rw [hsign]
          rfl
        simp only [ordinaryRosserRetainedPolicy, decide_eq_true hnext, true_and]
        exact ih (q :: pre) (!positive) hnext hsign' hprime'
          (fun hl p hp => hlevel hl p (List.mem_cons_of_mem q hp)) hsort'
      · simp only [ordinaryRosserRetainedPolicy, decide_eq_false hnext,
          Bool.false_eq_true, false_and]

/-- The parity-safe policy has exactly the same natural modulus support as
the full-prefix policy. The lower first-prime cutoff is paid explicitly. -/
theorem ordinaryParityRosserRetainedModuli_eq
    (lower : Bool) (R : ℝ) (hR : 1 < R) (carrier : List ℕ)
    (hsort : carrier.Pairwise (· > ·)) (hprime : ∀ p ∈ carrier, p.Prime)
    (hlevel : lower = true → ∀ p ∈ carrier, (p : ℝ) < R) :
    firstExitRetainedModuli (ordinaryParityRosserPolicy lower R) carrier =
      firstExitRetainedModuli (ordinaryRosserRetainedPolicy lower R) carrier := by
  ext d
  rw [mem_firstExitRetainedModuli_iff_validSelection,
    mem_firstExitRetainedModuli_iff_validSelection]
  apply exists_congr
  intro chosen
  apply and_congr_right
  intro hsub
  have hcprime : ∀ p ∈ chosen.reverse ++ [], p.Prime := by
    simpa using (show ∀ p ∈ chosen, p.Prime from fun p hp => hprime p (hsub.subset hp))
  have hcsort : (chosen.reverse ++ []).Pairwise (· < ·) := by
    simpa only [List.append_nil, List.pairwise_reverse] using hsort.sublist hsub
  rw [firstExitValidSelection_ordinaryParityRosser_iff lower R chosen [] true
    (ordinaryRosserPrefixAdmissible_nil lower hR) (by simp [evenListLength])
    hcprime (fun hl p hp => hlevel hl p (hsub.subset hp)) hcsort]

theorem firstExitRetainedCoefficient_ordinaryParityRosser
    (lower : Bool) (R : ℝ) (hR : 1 < R) (carrier : List ℕ)
    (hsort : carrier.Pairwise (· > ·)) (hprime : ∀ p ∈ carrier, p.Prime)
    (hlevel : lower = true → ∀ p ∈ carrier, (p : ℝ) < R) (d : ℕ) :
    (firstExitRetainedCoefficient (ordinaryParityRosserPolicy lower R) carrier d : ℝ) =
      ordinaryRosserWeight lower carrier.prod R d := by
  rw [← firstExitRetainedCoefficient_ordinaryRosser lower R hR carrier hsort hprime d]
  simp only [firstExitRetainedCoefficient,
    ordinaryParityRosserRetainedModuli_eq lower R hR carrier hsort hprime hlevel]

theorem firstExitRetainedPolynomial_ordinaryParityRosser
    (lower : Bool) (R : ℝ) (hR : 1 < R) (carrier : List ℕ)
    (hsort : carrier.Pairwise (· > ·)) (hprime : ∀ p ∈ carrier, p.Prime)
    (hlevel : lower = true → ∀ p ∈ carrier, (p : ℝ) < R) (h : ℕ → ℝ) :
    firstExitRetainedPolynomial (ordinaryParityRosserPolicy lower R) h [] true 1 carrier =
      firstExitRetainedPolynomial (ordinaryRosserRetainedPolicy lower R) h [] true 1 carrier := by
  rw [firstExitRetainedPolynomial_eq_retainedModuli_sum _ _ _ hsort.nodup hprime,
    firstExitRetainedPolynomial_eq_retainedModuli_sum _ _ _ hsort.nodup hprime,
    ordinaryParityRosserRetainedModuli_eq lower R hR carrier hsort hprime hlevel]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [firstExitRetainedCoefficient_ordinaryParityRosser lower R hR carrier hsort hprime hlevel,
    firstExitRetainedCoefficient_ordinaryRosser lower R hR carrier hsort hprime]

/-- The parity-safe root tree is the actual ordinary density. Only the
lower policy needs the sifting cutoff at most the level. -/
theorem firstExitRetainedPolynomial_ordinaryParityRosser_eq_actualDensity
    (lower : Bool) (N cap : ℕ) (y R : ℝ) (hR : 1 < R)
    (hyR : lower = true → y ≤ R) :
    firstExitRetainedPolynomial (ordinaryParityRosserPolicy lower R)
        (fun p => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 y) =
      if lower then actualSmallRosserMinusDensity N cap y R
        else actualSmallRosserPlusDensity N cap y R := by
  rw [firstExitRetainedPolynomial_ordinaryParityRosser lower R hR _
    (roughPrimeUniverse_pairwise_gt N cap 0 y)
    (fun _ hp => mem_roughPrimeUniverse_prime hp)
    (fun hl _ hp => (mem_roughPrimeUniverse.mp hp).2.2.2.2.trans_le (hyR hl))]
  exact firstExitRetainedPolynomial_eq_actualSmallRosserDensity lower N cap y R hR

theorem firstExitRetainedCoefficient_ordinaryParityRosser_eq_actualPlus
    (N cap : ℕ) (y R : ℝ) (hR : 1 < R) (d : ℕ) :
    (firstExitRetainedCoefficient (ordinaryParityRosserPolicy false R)
      (roughPrimeUniverse N cap 0 y) d : ℝ) = actualSmallRosserPlus N cap y R d := by
  rw [firstExitRetainedCoefficient_ordinaryParityRosser false R hR _
    (roughPrimeUniverse_pairwise_gt N cap 0 y)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) (by simp)]
  simp only [ordinaryRosserWeight, Bool.false_eq_true, if_false, actualSmallRosserPlus,
    actualSmallPrimeProduct_eq_universe_prod]

theorem firstExitRetainedCoefficient_ordinaryParityRosser_eq_actualMinus
    (N cap : ℕ) (y R : ℝ) (hR : 1 < R) (hyR : y ≤ R) (d : ℕ) :
    (firstExitRetainedCoefficient (ordinaryParityRosserPolicy true R)
      (roughPrimeUniverse N cap 0 y) d : ℝ) = actualSmallRosserMinus N cap y R d := by
  rw [firstExitRetainedCoefficient_ordinaryParityRosser true R hR _
    (roughPrimeUniverse_pairwise_gt N cap 0 y)
    (fun _ hp => mem_roughPrimeUniverse_prime hp)
    (fun _ _ hp => (mem_roughPrimeUniverse.mp hp).2.2.2.2.trans_le hyR)]
  simp only [ordinaryRosserWeight, if_true, actualSmallRosserMinus,
    actualSmallPrimeProduct_eq_universe_prod]

end

end ImbalancedChen
