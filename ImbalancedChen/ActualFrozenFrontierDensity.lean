import ImbalancedChen.FrozenRosserPolicy
import ImbalancedChen.FirstExitFrontierInvariants

/-!
# Actual residual densities on an ancestor-frozen parent frontier

The parent recursion supplies every prefix, its sign and prime mass, and
the exact remaining strict prime carrier. A continuation whose level is
frozen at this selected rank is therefore the literal ordinary Rosser
density at the real quotient level. Only admissibility of the inherited
prefix at that level remains a hypothesis.

Both splice branches below use the same parent frontier. Their difference
is an exact finite sum of differences of actual densities, before any
asymptotic estimate or box integration. The splice is after the selected
rank; it does not replace that rank's own admission test.
-/

namespace ImbalancedChen

noncomputable section

/-- The actual signed reciprocal-prime mass times the ordinary residual
density below the last selected prime, at the ancestor's chosen level. -/
def actualFrozenFrontierDensityTerm
    (lower : Bool) (N cap : ℕ) (Q : List ℕ → ℝ) (pre : List ℕ) : ℝ :=
  signedTreeCoefficient (evenListLength pre)
      ((pre.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod) *
    (if ordinaryRosserResidualLower lower pre.length then
      actualSmallRosserMinusDensity N cap (pre.headD 0 : ℝ) (Q pre / (pre.prod : ℝ))
    else actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ) (Q pre / (pre.prod : ℝ)))

/-- All history, mass, sign and endpoint data come from the real root
frontier. The enumeration cap may truncate the original prime universe. -/
theorem actualPrimeFrontier_geometry
    (k : ℕ) (hk : 0 < k) (parent : Bool → List ℕ → Bool)
    (N cap : ℕ) (z : ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z)) :
    state.selectedPrefix.length = k ∧
      state.selectedPrefix.Pairwise (· < ·) ∧
      (0 : ℝ) < state.selectedPrefix.prod ∧
      (∀ p ∈ state.selectedPrefix, (state.selectedPrefix.headD 0 : ℝ) ≤ (p : ℝ)) ∧
      state.remaining = roughPrimeUniverse N cap 0 (state.selectedPrefix.headD 0 : ℝ) ∧
      state.positive = evenListLength state.selectedPrefix ∧
      state.mass = (state.selectedPrefix.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod := by
  have hlen := firstExitDepthFrontier_selected_length k parent
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] (roughPrimeUniverse N cap 0 z) true 1
    (by simp) state hstate
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist k parent
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap 0 z) state hstate
  have hsort : state.selectedPrefix.Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse] using
      (roughPrimeUniverse_pairwise_gt N cap 0 z).sublist hsub
  have hprime : ∀ p ∈ state.selectedPrefix, p.Prime := by
    intro p hp
    exact mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))
  have hPnat : 0 < state.selectedPrefix.prod :=
    List.prod_pos (fun p hp => (hprime p hp).pos)
  have hP : (0 : ℝ) < state.selectedPrefix.prod := by exact_mod_cast hPnat
  obtain ⟨q, tail, hsel, _hq, hrem⟩ :=
    mem_firstExitDepthFrontier_roughPrime_remaining k hk parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) N cap 0 z state hstate
  have hhead : state.selectedPrefix.headD 0 = q := by simp [hsel]
  have hcut : ∀ p ∈ state.selectedPrefix,
      (state.selectedPrefix.headD 0 : ℝ) ≤ (p : ℝ) := by
    rw [hhead, hsel]
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact le_rfl
    · have hqp : q < p := (List.pairwise_cons.mp (hsel ▸ hsort)).1 p hp
      exact_mod_cast hqp.le
  refine ⟨hlen, hsort, hP, hcut, ?_, ?_, ?_⟩
  · simpa only [hhead] using hrem
  · exact mem_firstExitDepthFrontier_positive_eq_evenListLength k parent _ _ state hstate
  · exact mem_firstExitDepthFrontier_mass_eq_selected_prod k parent _ _ state hstate

/-- A full-predicate frozen continuation on a real parent frontier has
the exact displayed actual residual density, with its inherited sign. -/
theorem firstExitRetainedPolynomial_frozenOrdinary_frontier_density
    (lower : Bool) (k : ℕ) (hk : 0 < k) (parent : Bool → List ℕ → Bool)
    (Q : List ℕ → ℝ) (N cap : ℕ) (z : ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z))
    (hpre : ordinaryRosserPrefixAdmissible lower (Q state.selectedPrefix) state.selectedPrefix) :
    firstExitRetainedPolynomial (frozenOrdinaryRosserPolicy lower k Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) state.selectedPrefix state.positive
        state.mass state.remaining =
      actualFrozenFrontierDensityTerm lower N cap Q state.selectedPrefix := by
  obtain ⟨hlen, hsort, hP, hcut, hrem, hsign, hmass⟩ :=
    actualPrimeFrontier_geometry k hk parent N cap z state hstate
  rw [firstExitRetainedPolynomial_frozenOrdinaryRosser_eq lower k Q _ _ _ _ _ hlen,
    hrem, firstExitRetainedPolynomial_ordinaryRosser_continuation_actualDensity
      lower N cap _ _ _ hpre hsort.nodup hP hcut, hsign, hmass]
  rfl

/-- The parity-safe frozen policy has the same actual frontier formula;
its sign, sorted history and nonempty prefix are not caller assumptions. -/
theorem firstExitRetainedPolynomial_frozenParity_frontier_density
    (lower : Bool) (k : ℕ) (hk : 0 < k) (parent : Bool → List ℕ → Bool)
    (Q : List ℕ → ℝ) (N cap : ℕ) (z : ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z))
    (hpre : ordinaryRosserPrefixAdmissible lower (Q state.selectedPrefix) state.selectedPrefix) :
    firstExitRetainedPolynomial (frozenParityRosserPolicy lower k Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) state.selectedPrefix state.positive
        state.mass state.remaining =
      actualFrozenFrontierDensityTerm lower N cap Q state.selectedPrefix := by
  obtain ⟨hlen, hsort, hP, hcut, hrem, hsign, hmass⟩ :=
    actualPrimeFrontier_geometry k hk parent N cap z state hstate
  have hne : state.selectedPrefix ≠ [] := by
    intro heq
    rw [heq] at hlen
    simp only [List.length_nil] at hlen
    omega
  rw [firstExitRetainedPolynomial_frozenParityRosser_eq lower k Q _ _ _ _ _ hlen,
    hrem, firstExitRetainedPolynomial_ordinaryParityRosser_continuation_actualDensity
      lower N cap _ _ _ hpre hsort hP hne hcut _ _ hsign, hsign, hmass]
  rfl

/-- The complete spliced polynomial is its untouched terminal part plus
the sum of actual residual-density terms on the original parent frontier. -/
theorem firstExitRetainedPolynomial_frozenParity_splice_eq_density_sum
    (lower : Bool) (k : ℕ) (hk : 0 < k) (parent : Bool → List ℕ → Bool)
    (Q : List ℕ → ℝ) (N cap : ℕ) (z : ℝ)
    (hpre : ∀ state ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
        ordinaryRosserPrefixAdmissible lower (Q state.selectedPrefix) state.selectedPrefix) :
    firstExitRetainedPolynomial
        (firstExitDepthSplicePolicy k parent (frozenParityRosserPolicy lower k Q))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      firstExitDepthTerminalPolynomial k parent
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) +
        ((firstExitDepthFrontier k parent (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N cap 0 z)).map
          (fun state => actualFrozenFrontierDensityTerm lower N cap Q state.selectedPrefix)).sum := by
  rw [firstExitRetainedPolynomial_depthSplice_eq_terminal_add_frontier]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hstate
  exact firstExitRetainedPolynomial_frozenParity_frontier_density
    lower k hk parent Q N cap z state hstate (hpre state hstate)

/-- Two frozen replacements are compared below the same actual parent
frontier. No continuation equality, frontier weights or prime cutoffs are
supplied as hypotheses; the only two obligations are prefix admissibility. -/
theorem firstExitRetainedPolynomial_frozenParity_splice_sub_eq_density_sum
    (lower : Bool) (k : ℕ) (hk : 0 < k) (parent : Bool → List ℕ → Bool)
    (Qold Qnew : List ℕ → ℝ) (N cap : ℕ) (z : ℝ)
    (hold : ∀ state ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
        ordinaryRosserPrefixAdmissible lower (Qold state.selectedPrefix) state.selectedPrefix)
    (hnew : ∀ state ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
        ordinaryRosserPrefixAdmissible lower (Qnew state.selectedPrefix) state.selectedPrefix) :
    firstExitRetainedPolynomial
        (firstExitDepthSplicePolicy k parent (frozenParityRosserPolicy lower k Qnew))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial
        (firstExitDepthSplicePolicy k parent (frozenParityRosserPolicy lower k Qold))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      ((firstExitDepthFrontier k parent (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap 0 z)).map (fun state =>
          actualFrozenFrontierDensityTerm lower N cap Qnew state.selectedPrefix -
            actualFrozenFrontierDensityTerm lower N cap Qold state.selectedPrefix)).sum := by
  rw [firstExitRetainedPolynomial_frozenParity_splice_eq_density_sum
      lower k hk parent Qnew N cap z hnew,
    firstExitRetainedPolynomial_frozenParity_splice_eq_density_sum
      lower k hk parent Qold N cap z hold, add_sub_add_left_eq_sub]
  generalize firstExitDepthFrontier k parent (fun p : ℕ => 1 / ((p : ℝ) - 1))
    [] true 1 (roughPrimeUniverse N cap 0 z) = states
  induction states with
  | nil => simp
  | cons state states ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      ring

end

end ImbalancedChen
