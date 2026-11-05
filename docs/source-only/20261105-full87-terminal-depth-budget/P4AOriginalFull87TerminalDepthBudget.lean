import ImbalancedChen.P4AOriginalFull87ActualTerminalFactors

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED / ZERO KERNEL CREDIT.

The previous real changed original87 eighth frontier is followed into BOTH
actual ordinary continuation leaf lists. The prime-factor correction is
now charged at the FULL terminal selected depth, never at depth eight.
The old own-sixth parent and the saved eighth cap are still the two
existing ordinary levels; the leaf sign, beta and full modulus are retained.

This is a finite proof candidate only: no asymptotic density, o(1) bound,
signed level monotonicity, numerical certificate or reserve is inferred.
-/

namespace ImbalancedChen.P4AOriginalFull87TerminalDepthBudget
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalFull87OwnedEighthSource
open P4AOriginalFull87EighthPrimeMeanLedger (densityTest receiverTest primeMass primitiveError)
open P4AOriginalFull87ChangedFrontierBudget
open P4AOriginalFull87PopulationVariation
open P4AOriginalFull87FactorPopulation
open P4AOriginalFull87ActualTerminalFactors

/-- A selected FULL terminal prime-history depth, plus the actual number
of distinct SMALL factors, weighted by that sign's original beta. -/
def depthAttached (N cap : ℕ) (w L : ℝ)
    (positive : Bool) (selected : List ℕ) : ℝ :=
  ∑ a ∈ actualSmallRosserSupport N cap w,
    |if positive then actualSmallRosserPlus N cap w L a
     else actualSmallRosserMinus N cap w L a| *
      (((a.primeFactors.card + selected.length : ℕ) : ℝ) *
        densityTest (a * selected.prod))

/-- The SMALL factor part remains an actual small-divisor sum;
it is not replaced by a constant or a different sieve density. -/
def smallFactorAttached (N cap : ℕ) (w L : ℝ)
    (positive : Bool) (selected : List ℕ) : ℝ :=
  ∑ a ∈ actualSmallRosserSupport N cap w,
    |if positive then actualSmallRosserPlus N cap w L a
     else actualSmallRosserMinus N cap w L a| *
      ((a.primeFactors.card : ℝ) * densityTest (a * selected.prod))

/-- Exact depth/small-population split at each signed terminal leaf.
The depth factor is extracted only after the true terminal history is fixed.
Nothing assumes the terminal length equals eight. -/
theorem depthAttached_split (N cap : ℕ) (w L : ℝ)
    (positive : Bool) (selected : List ℕ) :
    depthAttached N cap w L positive selected =
      smallFactorAttached N cap w L positive selected +
        (selected.length : ℝ) *
          absoluteAttached N cap w L densityTest positive selected := by
  unfold depthAttached smallFactorAttached absoluteAttached
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  push_cast
  ring

/-- Existing signed recursion expanded into its ACTUAL retained terminal
leaf list, with positive absolute leaf masses. This works for arbitrary
terminal tests, not just multiplicative tests. -/
theorem absoluteSignedTest_eq_leaves {α : Type*}
    (R : Bool → List α → Bool) (h : α → ℝ)
    (V : Bool → List α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    absoluteSignedTest R h V pre positive mass remaining =
      ((firstExitRetainedLeaves R h pre positive mass remaining).map
        (fun leaf => |leaf.value| * V leaf.positive leaf.selected)).sum := by
  induction remaining generalizing pre positive mass with
  | nil =>
      simp [absoluteSignedTest, firstExitRetainedLeaves, FirstExitLeaf.value]
  | cons p ps ih =>
      by_cases hr : R (!positive) (p :: pre) = true
      · simp only [absoluteSignedTest, firstExitRetainedLeaves, if_pos hr,
          List.map_append, List.sum_append]
        rw [ih, ih]
      · simp only [absoluteSignedTest, firstExitRetainedLeaves, if_neg hr,
          List.append_nil, add_zero]
        exact ih pre positive mass

/-- Occurrence-preserving list comparison: no conversion to a Finset
and therefore no loss of genuine repeated frontier occurrences. -/
private theorem sum_map_mono {α : Type*} (xs : List α)
    (f g : α → ℝ) (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : f x ≤ g x := h x (by simp)
      have ht : ∀ y ∈ xs, f y ≤ g y := by
        intro y hy
        exact h y (by simp [hy])
      simpa only [List.map_cons, List.sum_cons] using add_le_add hx (ih ht)

/-- On a TRUE ordinary terminal leaf below a changed original87
occurrence, the previously defined positive full-modulus factor
budget is bounded by this leaf's exact terminal-depth envelope. -/
theorem attached_factor_le_depth
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c)
    (R : Bool → List ℕ → Bool) (leaf : FirstExitLeaf ℕ)
    (hl : leaf ∈ firstExitRetainedLeaves R (fun _ => 1)
       s.selectedPrefix s.positive s.mass s.remaining) :
    absoluteAttached N cap w L (factorModulusBudgetTest N)
      leaf.positive leaf.selected ≤
        depthAttached N cap w L leaf.positive leaf.selected := by
  unfold absoluteAttached depthAttached
  apply Finset.sum_le_sum
  intro a ha
  have hfactor := actual_terminal_factor_budget
    delta n e q om N cap w z c s hs R leaf hl a ha
  exact mul_le_mul_of_nonneg_left hfactor (abs_nonneg _)

/-- A depth-weighted sum on exactly the retained leaves of the REAL
ordinary policy at this state, including their own masses and signs. -/
def terminalDepthVariation (R : Bool → List ℕ → Bool)
    (N cap : ℕ) (w L : ℝ) (s : FirstExitDepthState ℕ) : ℝ :=
  ((firstExitRetainedLeaves R (fun _ => 1)
      s.selectedPrefix s.positive s.mass s.remaining).map
    (fun leaf => |leaf.value| *
      depthAttached N cap w L leaf.positive leaf.selected)).sum

/-- Finite signed-beta factor variation bound, with no claim that an
ordinary exit-series or signed saving is monotone in its level. -/
theorem continuation_factor_le_terminal_depth
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c)
    (R : Bool → List ℕ → Bool) :
    continuationVariation R N cap w L (factorModulusBudgetTest N) s ≤
      terminalDepthVariation R N cap w L s := by
  unfold continuationVariation terminalDepthVariation
  rw [absoluteSignedTest_eq_leaves]
  apply sum_map_mono
  intro leaf hl
  have ht := attached_factor_le_depth
    delta n e q om N cap w z L c s hs R leaf hl
  exact mul_le_mul_of_nonneg_left ht (abs_nonneg leaf.value)

/-- One explicit budget over BOTH actual continuation policies for each
changed occurrence. The owner Cell and the real rank-eight state lists
are inherited; there is no independent artificial terminal supplier. -/
def full87TerminalDepthBudget
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) : ℝ :=
  ∑ c : Cell,
    ((changedStates delta n e q om N cap w z c).map
      (fun s =>
        terminalDepthVariation
          (ordinaryParityRosserPolicy false
            ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
          N cap w L s +
        terminalDepthVariation
          (ordinaryParityRosserPolicy false
            ((N : ℝ) ^
              (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
          N cap w L s)).sum

/-- The existing factor-population budget of the SAME physical coefficient
is bounded by this real terminal-depth budget on all 87 original owners.
The proof preserves duplicate occurrences and distinct old/new leaf lists. -/
theorem changed_factor_le_full87_terminal_depth
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    changedVariationBudget delta n e q om N cap w z L
      (factorModulusBudgetTest N) ≤
        full87TerminalDepthBudget delta n e q om N cap w z L := by
  unfold changedVariationBudget full87TerminalDepthBudget
  apply Finset.sum_le_sum
  intro c _
  let xs := changedStates delta n e q om N cap w z c
  change
    (xs.map (fun s =>
      continuationVariation
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
        N cap w L (factorModulusBudgetTest N) s +
      continuationVariation
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^
            (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
        N cap w L (factorModulusBudgetTest N) s)).sum ≤
    (xs.map (fun s =>
      terminalDepthVariation
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
        N cap w L s +
      terminalDepthVariation
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^
            (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
        N cap w L s)).sum
  apply sum_map_mono
  intro s hs
  have hstate : s ∈ changedStates delta n e q om N cap w z c := by
    simpa only [xs] using hs
  exact add_le_add
    (continuation_factor_le_terminal_depth delta n e q om
      N cap w z L c s hstate
      (ordinaryParityRosserPolicy false
        ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix)))
    (continuation_factor_le_terminal_depth delta n e q om
      N cap w z L c s hstate
      (ordinaryParityRosserPolicy false
        ((N : ℝ) ^
          (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ))))

/-- Actual receiver lower-bound error ledger after finite terminal-depth
transport. The primitive discrepancy and centre-prime term remain
explicit. This bound DOES NOT prove the terminal budget is small enough
after normalization to pay either of the two paper reserves. -/
theorem receiver_density_terminal_depth_bound
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    |gain delta n e q om N cap w z L (receiverTest N) -
       primeMass N * gain delta n e q om N cap w z L densityTest| ≤
      changedAbsBudget delta n e q om N cap w z L (primitiveError N) +
      full87TerminalDepthBudget delta n e q om N cap w z L +
      chenPrimeDivisorCount N N *
        changedVariationBudget delta n e q om N cap w z L (fun _ => 1) := by
  have hprevious := receiver_density_changed_factor_bound
    delta n e q om N cap w z L
  have hdepth := changed_factor_le_full87_terminal_depth
    delta n e q om N cap w z L
  linarith

end
end ImbalancedChen.P4AOriginalFull87TerminalDepthBudget
