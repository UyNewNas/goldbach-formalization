import ImbalancedChen.OrdinaryRosserFirstExitPolicy

/-!
# Ordinary Rosser continuation below an actual prefix

All inherited cubic tests are required to hold at the displayed total
level. Splitting the actual prime filters then gives the literal residual
real level divided by the prefix product, and reverses upper/lower parity
exactly when the prefix rank is odd. No rounded integer level is divided.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical List BigOperators
open MathlibNt.SieveTheory

/-- Removing an odd number of selected primes reverses the Rosser parity. -/
def ordinaryRosserResidualLower (lower : Bool) (rank : ℕ) : Bool :=
  if Even rank then lower else !lower

/-- A filter at an inherited prime contains no smaller residual prime. -/
theorem ordinaryRosser_filter_at_old (pre suffix : Finset ℕ)
    (hsep : ∀ q ∈ suffix, ∀ p ∈ pre, q < p) {p : ℕ} (hp : p ∈ pre) :
    (suffix ∪ pre).filter (fun r => p ≤ r) = pre.filter (fun r => p ≤ r) := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hr | hr, hpr⟩
    · exact ((not_lt_of_ge hpr) (hsep r hr p hp)).elim
    · exact ⟨hr, hpr⟩
  · exact fun ⟨hr, hpr⟩ => ⟨Or.inr hr, hpr⟩

/-- A filter at a residual prime contains the entire inherited prefix. -/
theorem ordinaryRosser_filter_at_residual (pre suffix : Finset ℕ)
    (hsep : ∀ q ∈ suffix, ∀ p ∈ pre, q < p) {q : ℕ} (hq : q ∈ suffix) :
    (suffix ∪ pre).filter (fun r => q ≤ r) =
      pre ∪ suffix.filter (fun r => q ≤ r) := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hr | hr, hqr⟩
    · exact Or.inr ⟨hr, hqr⟩
    · exact Or.inl hr
  · rintro (hr | ⟨hr, hqr⟩)
    · exact ⟨Or.inr hr, (hsep q hq r hr).le⟩
    · exact ⟨Or.inl hr, hqr⟩

theorem ordinaryRosser_prefix_suffix_disjoint (pre suffix : Finset ℕ)
    (hsep : ∀ q ∈ suffix, ∀ p ∈ pre, q < p) : Disjoint pre suffix := by
  exact Finset.disjoint_left.mpr fun p hp hq => (lt_irrefl p) (hsep p hq p hp)

theorem ordinaryRosser_residual_filter_card (pre suffix : Finset ℕ)
    (hsep : ∀ q ∈ suffix, ∀ p ∈ pre, q < p) {q : ℕ} (hq : q ∈ suffix) :
    ((suffix ∪ pre).filter (fun r => q ≤ r)).card =
      pre.card + (suffix.filter (fun r => q ≤ r)).card := by
  rw [ordinaryRosser_filter_at_residual pre suffix hsep hq,
    Finset.card_union_of_disjoint]
  exact (ordinaryRosser_prefix_suffix_disjoint pre suffix hsep).mono_right
    (Finset.filter_subset _ _)

theorem ordinaryRosser_residual_filter_prod (pre suffix : Finset ℕ)
    (hsep : ∀ q ∈ suffix, ∀ p ∈ pre, q < p) {q : ℕ} (hq : q ∈ suffix) :
    ((suffix ∪ pre).filter (fun r => q ≤ r)).prod id =
      pre.prod id * (suffix.filter (fun r => q ≤ r)).prod id := by
  rw [ordinaryRosser_filter_at_residual pre suffix hsep hq,
    Finset.prod_union]
  exact (ordinaryRosser_prefix_suffix_disjoint pre suffix hsep).mono_right
    (Finset.filter_subset _ _)

private def rosserCardTest (lower : Bool) (rank : ℕ) : Prop :=
  if lower then Even rank else ¬Even rank

private theorem rosserCardTest_add (lower : Bool) (m n : ℕ) :
    rosserCardTest lower (m + n) ↔
      rosserCardTest (ordinaryRosserResidualLower lower m) n := by
  cases lower <;> by_cases hm : Even m <;>
    simp [rosserCardTest, ordinaryRosserResidualLower, Nat.even_add, hm]

private def rosserSetTests (lower : Bool) (Q : ℝ) (s : Finset ℕ) : Prop :=
  ∀ p ∈ s, rosserCardTest lower ((s.filter (fun r => p ≤ r)).card) →
    (((s.filter (fun r => p ≤ r)).prod id : ℕ) : ℝ) * (p : ℝ) ^ 2 < Q

private theorem rosserSetTests_iff (lower : Bool) (Q : ℝ) (s : Finset ℕ) :
    rosserSetTests lower Q s ↔
      if lower then LiLiuPrereqWF.SmallRosser.LowerAdmissibleSet Q s
      else LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet Q s := by
  cases lower <;> rfl

private theorem rosserSetTests_union_iff (lower : Bool) (Q : ℝ)
    (pre suffix : Finset ℕ)
    (hsep : ∀ q ∈ suffix, ∀ p ∈ pre, q < p)
    (hP : (0 : ℝ) < (pre.prod id : ℕ)) (hpre : rosserSetTests lower Q pre) :
    rosserSetTests lower Q (suffix ∪ pre) ↔
      rosserSetTests (ordinaryRosserResidualLower lower pre.card)
        (Q / ((pre.prod id : ℕ) : ℝ)) suffix := by
  have hscale (x : ℝ) : ((pre.prod id : ℕ) : ℝ) * x < Q ↔
      x < Q / ((pre.prod id : ℕ) : ℝ) := by
    rw [lt_div_iff₀ hP, mul_comm]
  constructor
  · intro hall q hq hcard
    have hc : rosserCardTest lower
        (((suffix ∪ pre).filter (fun r => q ≤ r)).card) := by
      rw [ordinaryRosser_residual_filter_card pre suffix hsep hq]
      exact (rosserCardTest_add lower _ _).mpr hcard
    have hh := hall q (Finset.mem_union_left _ hq) hc
    rw [ordinaryRosser_residual_filter_prod pre suffix hsep hq, Nat.cast_mul,
      mul_assoc] at hh
    exact (hscale _).mp hh
  · intro hlocal p hp hcard
    rcases Finset.mem_union.mp hp with hs | hp
    · rw [ordinaryRosser_residual_filter_card pre suffix hsep hs] at hcard
      have hh := hlocal p hs ((rosserCardTest_add lower _ _).mp hcard)
      rw [ordinaryRosser_residual_filter_prod pre suffix hsep hs, Nat.cast_mul,
        mul_assoc]
      exact (hscale _).mpr hh
    · rw [ordinaryRosser_filter_at_old pre suffix hsep hp] at hcard ⊢
      exact hpre p hp hcard

/-- The complete inherited history factors out exactly. Its old tests
remain an explicit hypothesis at `Q`; the residual tests use `Q / P`.
The suffix need not itself be admissible on either side of this iff. -/
theorem ordinaryRosserPrefixAdmissible_append_iff
    (lower : Bool) (Q : ℝ) (pre suffix : List ℕ)
    (hpre : ordinaryRosserPrefixAdmissible lower Q pre)
    (hnd : pre.Nodup) (hP : (0 : ℝ) < pre.prod)
    (hsep : ∀ q ∈ suffix, ∀ p ∈ pre, q < p) :
    ordinaryRosserPrefixAdmissible lower Q (suffix ++ pre) ↔
      ordinaryRosserPrefixAdmissible
        (ordinaryRosserResidualLower lower pre.length) (Q / (pre.prod : ℝ)) suffix := by
  have hprod : pre.toFinset.prod id = pre.prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p) hnd
  have hsep' : ∀ q ∈ suffix.toFinset, ∀ p ∈ pre.toFinset, q < p :=
    fun q hq p hp => hsep q (List.mem_toFinset.mp hq) p (List.mem_toFinset.mp hp)
  have htests := rosserSetTests_union_iff lower Q pre.toFinset suffix.toFinset hsep'
    (by simpa only [hprod] using hP)
    ((rosserSetTests_iff lower Q pre.toFinset).mpr hpre.2)
  rw [rosserSetTests_iff, rosserSetTests_iff, List.toFinset_card_of_nodup hnd, hprod]
    at htests
  unfold ordinaryRosserPrefixAdmissible
  rw [List.prod_append, Nat.cast_mul, List.toFinset_append, htests]
  exact and_congr (lt_div_iff₀ hP).symm Iff.rfl

theorem ordinaryRosser_residual_level_gt_one
    (lower : Bool) (Q : ℝ) (pre : List ℕ)
    (hpre : ordinaryRosserPrefixAdmissible lower Q pre)
    (hP : (0 : ℝ) < pre.prod) : 1 < Q / (pre.prod : ℝ) := by
  exact (one_lt_div hP).mpr hpre.1

private theorem ordinaryRosser_polynomial_append
    (lower : Bool) (Q : ℝ) (pre remaining : List ℕ)
    (hpre : ordinaryRosserPrefixAdmissible lower Q pre)
    (hnd : pre.Nodup) (hP : (0 : ℝ) < pre.prod)
    (hrem : ∀ q ∈ remaining, ∀ p ∈ pre, q < p)
    (h : ℕ → ℝ) (suffix : List ℕ) (positive : Bool) (mass : ℝ)
    (hsuffix : ∀ q ∈ suffix, ∀ p ∈ pre, q < p) :
    firstExitRetainedPolynomial (ordinaryRosserRetainedPolicy lower Q)
        h (suffix ++ pre) positive mass remaining =
      firstExitRetainedPolynomial
        (ordinaryRosserRetainedPolicy (ordinaryRosserResidualLower lower pre.length)
          (Q / (pre.prod : ℝ))) h suffix positive mass remaining := by
  induction remaining generalizing suffix positive mass with
  | nil => rfl
  | cons q qs ih =>
      have hqs : ∀ q ∈ qs, ∀ p ∈ pre, q < p :=
        fun q hq p hp => hrem q (List.mem_cons_of_mem _ hq) p hp
      have hnext : ∀ r ∈ q :: suffix, ∀ p ∈ pre, r < p := by
        intro r hr p hp
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hrem r (by simp) p hp
        · exact hsuffix r hr p hp
      have htest :
          ordinaryRosserRetainedPolicy lower Q (!positive) (q :: (suffix ++ pre)) =
            ordinaryRosserRetainedPolicy
              (ordinaryRosserResidualLower lower pre.length) (Q / (pre.prod : ℝ))
              (!positive) (q :: suffix) := by
        unfold ordinaryRosserRetainedPolicy
        change decide (ordinaryRosserPrefixAdmissible lower Q ((q :: suffix) ++ pre)) = _
        rw [ordinaryRosserPrefixAdmissible_append_iff lower Q pre (q :: suffix)
          hpre hnd hP hnext]
      simp only [firstExitRetainedPolynomial, htest]
      rw [ih hqs suffix positive mass hsuffix]
      by_cases ht : ordinaryRosserRetainedPolicy
          (ordinaryRosserResidualLower lower pre.length) (Q / (pre.prod : ℝ))
          (!positive) (q :: suffix) = true
      · simp only [if_pos ht]
        congr 1
        exact ih hqs (q :: suffix) (!positive) (mass * h q) hnext
      · simp only [if_neg ht]

private theorem signIndependent_polynomial_mul
    {α : Type*} (retained : List α → Bool) (h : α → ℝ)
    (remaining pre : List α) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial (fun _ => retained) h pre positive mass remaining =
      signedTreeCoefficient positive mass *
        firstExitRetainedPolynomial (fun _ => retained) h pre true 1 remaining := by
  induction remaining generalizing pre positive mass with
  | nil => simp [firstExitRetainedPolynomial]
  | cons p ps ih =>
      simp only [firstExitRetainedPolynomial]
      by_cases ht : retained (p :: pre) = true
      · simp only [if_pos ht, Bool.not_true]
        rw [ih pre positive mass, ih (p :: pre) (!positive) (mass * h p),
          ih (p :: pre) false (1 * h p)]
        rw [signedTreeCoefficient_not_mul]
        simp only [signedTreeCoefficient_false, one_mul]
        ring
      · simp only [if_neg ht, add_zero]
        exact ih pre positive mass

/-- Exact ordinary continuation, for arbitrary prime weights and incoming
signed mass. The inherited history is explicit; no continuation equality
or analytic estimate is assumed. -/
theorem firstExitRetainedPolynomial_ordinaryRosser_continuation
    (lower : Bool) (Q : ℝ) (pre carrier : List ℕ)
    (hpre : ordinaryRosserPrefixAdmissible lower Q pre)
    (hnd : pre.Nodup) (hP : (0 : ℝ) < pre.prod)
    (hsep : ∀ q ∈ carrier, ∀ p ∈ pre, q < p)
    (h : ℕ → ℝ) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial (ordinaryRosserRetainedPolicy lower Q)
        h pre positive mass carrier =
      signedTreeCoefficient positive mass *
        firstExitRetainedPolynomial
          (ordinaryRosserRetainedPolicy (ordinaryRosserResidualLower lower pre.length)
            (Q / (pre.prod : ℝ))) h [] true 1 carrier := by
  rw [← List.nil_append pre,
    ordinaryRosser_polynomial_append lower Q pre carrier hpre hnd hP hsep h []
      positive mass (by simp)]
  exact signIndependent_polynomial_mul _ h carrier [] positive mass

/-- On the actual carrier below `y`, a retained ordinary history has the
same literal small-prime residual density. The cutoff only needs to be
below every inherited prime; the enumeration cap may be arbitrary. -/
theorem firstExitRetainedPolynomial_ordinaryRosser_continuation_actualDensity
    (lower : Bool) (N cap : ℕ) (y Q : ℝ) (pre : List ℕ)
    (hpre : ordinaryRosserPrefixAdmissible lower Q pre)
    (hnd : pre.Nodup) (hP : (0 : ℝ) < pre.prod)
    (hcut : ∀ p ∈ pre, y ≤ (p : ℝ)) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial (ordinaryRosserRetainedPolicy lower Q)
        (fun p => 1 / ((p : ℝ) - 1)) pre positive mass
        (roughPrimeUniverse N cap 0 y) =
      signedTreeCoefficient positive mass *
        (if ordinaryRosserResidualLower lower pre.length then
          actualSmallRosserMinusDensity N cap y (Q / (pre.prod : ℝ))
        else actualSmallRosserPlusDensity N cap y (Q / (pre.prod : ℝ))) := by
  rw [firstExitRetainedPolynomial_ordinaryRosser_continuation lower Q pre _
    hpre hnd hP]
  · rw [firstExitRetainedPolynomial_eq_actualSmallRosserDensity _ N cap y _
      (ordinaryRosser_residual_level_gt_one lower Q pre hpre hP)]
  · intro q hq p hp
    exact_mod_cast (mem_roughPrimeUniverse.mp hq).2.2.2.2.trans_le (hcut p hp)

/-- Reachable valid histories allow the parity-safe policy to be replaced
by its full predicate throughout the actual continuation. The lower
first-prime level condition is explicit here. -/
theorem firstExitRetainedPolynomial_ordinaryParityRosser_eq_full_valid
    (lower : Bool) (Q : ℝ) (carrier pre : List ℕ)
    (positive : Bool) (mass : ℝ) (h : ℕ → ℝ)
    (hpre : ordinaryRosserPrefixAdmissible lower Q pre)
    (hsign : positive = evenListLength pre)
    (hprime : ∀ p ∈ carrier, p.Prime)
    (hlevel : lower = true → ∀ p ∈ carrier, (p : ℝ) < Q)
    (hsort : (carrier.reverse ++ pre).Pairwise (· < ·)) :
    firstExitRetainedPolynomial (ordinaryParityRosserPolicy lower Q)
        h pre positive mass carrier =
      firstExitRetainedPolynomial (ordinaryRosserRetainedPolicy lower Q)
        h pre positive mass carrier := by
  induction carrier generalizing pre positive mass with
  | nil => rfl
  | cons q qs ih =>
      have hsort' : (qs.reverse ++ q :: pre).Pairwise (· < ·) := by
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hsort
      have hskipSort : (qs.reverse ++ pre).Pairwise (· < ·) :=
        hsort'.sublist ((List.Sublist.refl qs.reverse).append ((List.Sublist.refl pre).cons q))
      have hqprime : q.Prime := hprime q (by simp)
      have hprime' : ∀ p ∈ qs, p.Prime :=
        fun p hp => hprime p (List.mem_cons_of_mem q hp)
      have hlevel' : lower = true → ∀ p ∈ qs, (p : ℝ) < Q :=
        fun hl p hp => hlevel hl p (List.mem_cons_of_mem q hp)
      have htest := ordinaryParityRosserPolicy_eq_full_on_valid_prefix lower Q pre positive q
        hpre hsign hqprime (fun hl => hlevel hl q (by simp))
        (List.pairwise_append.mp hsort').2.1
      simp only [firstExitRetainedPolynomial, htest]
      rw [ih pre positive mass hpre hsign hprime' hlevel' hskipSort]
      by_cases ht : ordinaryRosserRetainedPolicy lower Q (!positive) (q :: pre) = true
      · simp only [if_pos ht]
        congr 1
        have hn : ordinaryRosserPrefixAdmissible lower Q (q :: pre) := of_decide_eq_true ht
        have hsg : (!positive) = evenListLength (q :: pre) := by rw [hsign]; rfl
        exact ih (q :: pre) (!positive) (mass * h q) hn hsg hprime' hlevel' hsort'
      · simp only [if_neg ht]

/-- A nonempty actual inherited prefix pays the total-level first-prime
condition automatically. The remaining density is the literal ordinary
upper or lower weight, with parity determined by the inherited rank. -/
theorem firstExitRetainedPolynomial_ordinaryParityRosser_continuation_actualDensity
    (lower : Bool) (N cap : ℕ) (y Q : ℝ) (pre : List ℕ)
    (hpre : ordinaryRosserPrefixAdmissible lower Q pre)
    (hsort : pre.Pairwise (· < ·)) (hP : (0 : ℝ) < pre.prod) (hne : pre ≠ [])
    (hcut : ∀ p ∈ pre, y ≤ (p : ℝ)) (positive : Bool) (mass : ℝ)
    (hsign : positive = evenListLength pre) :
    firstExitRetainedPolynomial (ordinaryParityRosserPolicy lower Q)
        (fun p => 1 / ((p : ℝ) - 1)) pre positive mass
        (roughPrimeUniverse N cap 0 y) =
      signedTreeCoefficient positive mass *
        (if ordinaryRosserResidualLower lower pre.length then
          actualSmallRosserMinusDensity N cap y (Q / (pre.prod : ℝ))
        else actualSmallRosserPlusDensity N cap y (Q / (pre.prod : ℝ))) := by
  have hyQ : y < Q := by
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil pre hne
    have hPn : 0 < pre.prod := by exact_mod_cast hP
    have hpP : (p : ℝ) ≤ pre.prod := by
      exact_mod_cast Nat.le_of_dvd hPn (List.dvd_prod hp)
    exact (hcut p hp).trans_lt (hpP.trans_lt hpre.1)
  have hallSort : ((roughPrimeUniverse N cap 0 y).reverse ++ pre).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨?_, hsort, ?_⟩
    · simpa only [List.pairwise_reverse] using roughPrimeUniverse_pairwise_gt N cap 0 y
    · intro q hq p hp
      have hq' : q ∈ roughPrimeUniverse N cap 0 y := List.mem_reverse.mp hq
      exact_mod_cast (mem_roughPrimeUniverse.mp hq').2.2.2.2.trans_le (hcut p hp)
  rw [firstExitRetainedPolynomial_ordinaryParityRosser_eq_full_valid lower Q _ pre
    positive mass _ hpre hsign (fun _ hp => mem_roughPrimeUniverse_prime hp)
    (fun _ _ hp => (mem_roughPrimeUniverse.mp hp).2.2.2.2.trans hyQ) hallSort]
  exact firstExitRetainedPolynomial_ordinaryRosser_continuation_actualDensity
    lower N cap y Q pre hpre hsort.nodup hP hcut positive mass

end

end ImbalancedChen
