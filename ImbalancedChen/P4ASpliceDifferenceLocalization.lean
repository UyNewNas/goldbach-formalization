import ImbalancedChen.P4ARetainedSupportDifferenceMass
import ImbalancedChen.FirstExitDepthSplice
import ImbalancedChen.ActualExtendedThirdCompactUpperRho

/-!
SOURCEONLY / UNCOMPILED. Agreement through selected rank k gives equality
of all terminal leaves of selected length at most k. The original rough
carrier is duplicate-free and prime, so the selected length of a retained
leaf is exactly the number of distinct prime factors of its modulus.
Consequently actual fixed coefficients agree on every modulus with at
most k prime factors. The exact compiler charge can only involve deeper
retained moduli. This is finite coefficient localization, not a mass bound.
-/

namespace ImbalancedChen.P4ASpliceDifferenceLocalization

noncomputable section
open scoped BigOperators symmDiff
open P4ARetainedSupportDifferenceMass

/-- Selection never decreases the incoming selected rank. -/
theorem incoming_length_le_leaf_length {α : Type*}
    (policy : Bool → List α → Bool) (weight : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    ∀ leaf ∈ firstExitRetainedLeaves policy weight pre positive mass remaining,
      pre.length ≤ leaf.selected.length := by
  induction remaining generalizing pre positive mass with
  | nil =>
      intro leaf hleaf
      simp only [firstExitRetainedLeaves, List.mem_singleton] at hleaf
      subst leaf
      exact le_rfl
  | cons p ps ih =>
      intro leaf hleaf
      by_cases hr : policy (!positive) (p :: pre) = true
      · rw [firstExitRetainedLeaves, if_pos hr, List.mem_append] at hleaf
        rcases hleaf with hskip | hselect
        · exact ih pre positive mass leaf hskip
        · have hnext := ih (p :: pre) (!positive) (mass * weight p) leaf hselect
          simpa only [List.length_cons] using (Nat.le_succ pre.length).trans hnext
      · rw [firstExitRetainedLeaves, if_neg hr, List.append_nil] at hleaf
        exact ih pre positive mass leaf hleaf

/-- A terminal leaf of rank at most k never needs a policy decision after
rank k. Its full selected list, sign and mass are unchanged. -/
theorem shallow_leaf_mem_iff {α : Type*} (k : ℕ)
    (policy₁ policy₂ : Bool → List α → Bool)
    (hagree : ∀ positive history, history.length ≤ k →
      policy₁ positive history = policy₂ positive history)
    (weight : α → ℝ) (pre remaining : List α) (positive : Bool) (mass : ℝ)
    (leaf : FirstExitLeaf α) (hlen : leaf.selected.length ≤ k) :
    leaf ∈ firstExitRetainedLeaves policy₁ weight pre positive mass remaining ↔
      leaf ∈ firstExitRetainedLeaves policy₂ weight pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
      by_cases hnext : (p :: pre).length ≤ k
      · have htest := hagree (!positive) (p :: pre) hnext
        by_cases hr : policy₂ (!positive) (p :: pre) = true
        · simp only [firstExitRetainedLeaves, htest, if_pos hr, List.mem_append]
          exact or_congr (ih pre positive mass) (ih (p :: pre) (!positive) (mass * weight p))
        · simp only [firstExitRetainedLeaves, htest, if_neg hr, List.append_nil]
          exact ih pre positive mass
      · have hnot₁ : leaf ∉ firstExitRetainedLeaves policy₁ weight (p :: pre)
            (!positive) (mass * weight p) ps := by
          intro hleaf
          exact hnext ((incoming_length_le_leaf_length policy₁ weight (p :: pre) ps
            (!positive) (mass * weight p) leaf hleaf).trans hlen)
        have hnot₂ : leaf ∉ firstExitRetainedLeaves policy₂ weight (p :: pre)
            (!positive) (mass * weight p) ps := by
          intro hleaf
          exact hnext ((incoming_length_le_leaf_length policy₂ weight (p :: pre) ps
            (!positive) (mass * weight p) leaf hleaf).trans hlen)
        by_cases hr₁ : policy₁ (!positive) (p :: pre) = true <;>
          by_cases hr₂ : policy₂ (!positive) (p :: pre) = true <;>
          simp only [firstExitRetainedLeaves, hr₁, hr₂, if_true, if_false,
            List.mem_append, List.not_mem_nil, hnot₁, hnot₂, or_false, List.append_nil] <;>
          exact ih pre positive mass

/-- Odd-policy agreement gives literal equality of shallow root leaf
membership; the always-admitted even ranks are preserved automatically. -/
theorem shallow_odd_leaf_mem_iff {α : Type*} (k : ℕ)
    (retainOdd₁ retainOdd₂ : List α → Bool)
    (hagree : ∀ history, history.length ≤ k → retainOdd₁ history = retainOdd₂ history)
    (weight : α → ℝ) (carrier : List α) (leaf : FirstExitLeaf α)
    (hlen : leaf.selected.length ≤ k) :
    leaf ∈ oddFirstExitRetainedLeaves retainOdd₁ weight carrier ↔
      leaf ∈ oddFirstExitRetainedLeaves retainOdd₂ weight carrier := by
  apply shallow_leaf_mem_iff k (oddFirstExitPolicy retainOdd₁)
    (oddFirstExitPolicy retainOdd₂) ?_ weight [] carrier true 1 leaf hlen
  intro positive history hhistory
  simp only [oddFirstExitPolicy, hagree history hhistory]

/-- A root leaf's rank is exactly its modulus' number of distinct prime
factors, using the actual duplicate-free rough prime carrier. -/
theorem actual_leaf_primeFactors_card_eq_length
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd (fun _ => 1)
      (roughPrimeUniverse N cap w z)) :
    leaf.selected.prod.primeFactors.card = leaf.selected.length := by
  rw [mem_oddFirstExitRetainedLeaves_primeFactors_selectedProd retainOdd (fun _ => 1)
    (roughPrimeUniverse N cap w z) (roughPrimeUniverse_nodup N cap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) leaf hleaf]
  exact List.toFinset_card_of_nodup (mem_oddFirstExitRetainedLeaves_selected_nodup
    retainOdd (fun _ => 1) (roughPrimeUniverse N cap w z)
    (roughPrimeUniverse_nodup N cap w z) leaf hleaf)

/-- Agreement through rank k transfers every retained modulus having at
most k prime factors, with its complete actual retained leaf as witness. -/
theorem shallow_support_mem_imp (k : ℕ)
    (retainOdd₁ retainOdd₂ : List ℕ → Bool)
    (hagree : ∀ history, history.length ≤ k → retainOdd₁ history = retainOdd₂ history)
    (N cap : ℕ) (w z : ℝ) (d : ℕ) (hcard : d.primeFactors.card ≤ k)
    (hd : d ∈ fixedRoughSupport retainOdd₁ N cap w z) :
    d ∈ fixedRoughSupport retainOdd₂ N cap w z := by
  change d ∈ oddFirstExitRetainedModuli retainOdd₁ (fun _ => 1)
    (roughPrimeUniverse N cap w z) at hd
  change d ∈ oddFirstExitRetainedModuli retainOdd₂ (fun _ => 1)
    (roughPrimeUniverse N cap w z)
  obtain ⟨leaf, hleaf, hprod⟩ :=
    (mem_oddFirstExitRetainedModuli retainOdd₁ (fun _ => 1)
      (roughPrimeUniverse N cap w z) d).mp hd
  have hlength := actual_leaf_primeFactors_card_eq_length retainOdd₁ N cap w z leaf hleaf
  have hlen : leaf.selected.length ≤ k := by
    rw [hprod] at hlength
    omega
  exact (mem_oddFirstExitRetainedModuli retainOdd₂ (fun _ => 1)
    (roughPrimeUniverse N cap w z) d).mpr
      ⟨leaf, (shallow_odd_leaf_mem_iff k retainOdd₁ retainOdd₂ hagree
        (fun _ => 1) _ leaf hlen).mp hleaf, hprod⟩

theorem shallow_support_mem_iff (k : ℕ)
    (retainOdd₁ retainOdd₂ : List ℕ → Bool)
    (hagree : ∀ history, history.length ≤ k → retainOdd₁ history = retainOdd₂ history)
    (N cap : ℕ) (w z : ℝ) (d : ℕ) (hcard : d.primeFactors.card ≤ k) :
    d ∈ fixedRoughSupport retainOdd₁ N cap w z ↔
      d ∈ fixedRoughSupport retainOdd₂ N cap w z := by
  constructor
  · exact shallow_support_mem_imp k retainOdd₁ retainOdd₂ hagree N cap w z d hcard
  · exact shallow_support_mem_imp k retainOdd₂ retainOdd₁
      (fun history hlen => (hagree history hlen).symm) N cap w z d hcard

/-- The actual signed coefficients, including their signs, agree on all
moduli of rank at most k; no membership premise for either policy is needed. -/
theorem shallow_coefficient_eq (k : ℕ)
    (retainOdd₁ retainOdd₂ : List ℕ → Bool)
    (hagree : ∀ history, history.length ≤ k → retainOdd₁ history = retainOdd₂ history)
    (N cap : ℕ) (w z : ℝ) (d : ℕ) (hcard : d.primeFactors.card ≤ k) :
    fixedRoughCoefficient retainOdd₁ N cap w z d =
      fixedRoughCoefficient retainOdd₂ N cap w z d := by
  have hmem := shallow_support_mem_iff k retainOdd₁ retainOdd₂ hagree N cap w z d hcard
  rw [coefficient_eq_moebius_indicator, coefficient_eq_moebius_indicator, hmem]

/-- Every modulus in the exact compiler charge comes from a descendant
strictly after the common depth. -/
theorem changed_support_has_more_primeFactors (k : ℕ)
    (retainOdd₁ retainOdd₂ : List ℕ → Bool)
    (hagree : ∀ history, history.length ≤ k → retainOdd₁ history = retainOdd₂ history)
    (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ fixedRoughSupport retainOdd₁ N cap w z ∆
      fixedRoughSupport retainOdd₂ N cap w z) :
    k < d.primeFactors.card := by
  by_contra hnot
  have hmem := shallow_support_mem_iff k retainOdd₁ retainOdd₂ hagree
    N cap w z d (Nat.le_of_not_gt hnot)
  rcases Finset.mem_symmDiff.mp hd with ⟨h₁, h₂⟩ | ⟨h₂, h₁⟩
  · exact h₂ (hmem.mp h₁)
  · exact h₁ (hmem.mpr h₂)

/-- Exact compiler mass localization, with the rank filter justified by
policy agreement rather than assumed as support geometry. -/
theorem compilerMass_eq_deeper_changed_moduli (k : ℕ)
    (retainOdd₁ retainOdd₂ : List ℕ → Bool)
    (hagree : ∀ history, history.length ≤ k → retainOdd₁ history = retainOdd₂ history)
    (N cap : ℕ) (w z : ℝ) :
    reciprocalTotientDensity
      (fixedRoughSupport retainOdd₁ N cap w z ∪ fixedRoughSupport retainOdd₂ N cap w z)
      (fun d => |fixedRoughCoefficient retainOdd₁ N cap w z d -
        fixedRoughCoefficient retainOdd₂ N cap w z d|) =
      reciprocalTotientDensity
        ((fixedRoughSupport retainOdd₁ N cap w z ∆ fixedRoughSupport retainOdd₂ N cap w z).filter
          (fun d => k < d.primeFactors.card)) (fun _ => 1) := by
  classical
  have hfilter :
      (fixedRoughSupport retainOdd₁ N cap w z ∆ fixedRoughSupport retainOdd₂ N cap w z).filter
        (fun d => k < d.primeFactors.card) =
      fixedRoughSupport retainOdd₁ N cap w z ∆ fixedRoughSupport retainOdd₂ N cap w z := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    exact changed_support_has_more_primeFactors k retainOdd₁ retainOdd₂ hagree N cap w z hd
  rw [hfilter, compilerMass_union_eq_symmDiff_unitMass]

/-- Two literal depth splices inherit the same early signed coefficients. -/
theorem depthSplice_shallow_coefficient_eq (k : ℕ)
    (parent replacement₁ replacement₂ : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) (d : ℕ) (hcard : d.primeFactors.card ≤ k) :
    fixedRoughCoefficient (firstExitDepthSplicePolicy k parent replacement₁ false) N cap w z d =
      fixedRoughCoefficient (firstExitDepthSplicePolicy k parent replacement₂ false) N cap w z d := by
  apply shallow_coefficient_eq k _ _ ?_ N cap w z d hcard
  intro history hlen
  simp only [firstExitDepthSplicePolicy, if_pos hlen]

/-- The actual compact third update cannot charge the unit, prime, or
two-prime moduli. Its original initial policy, including its first stop,
supplies exactly the same coefficient at each such modulus. -/
theorem actualThird_shallow_coefficient_eq (e h : ℝ) (m N cap : ℕ) (w z : ℝ)
    (d : ℕ) (hcard : d.primeFactors.card ≤ 2) :
    fixedRoughCoefficient (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z d =
      fixedRoughCoefficient (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z d := by
  exact shallow_coefficient_eq 2 _ _
    (fun history hlen => actualExtendedThirdCompactUpperPolicy_through_two
      e h m N false history hlen) N cap w z d hcard

/-- Original third-policy compiler charges are supported only at rank ≥3. -/
theorem actualThird_changed_support_has_at_least_three_primeFactors
    (e h : ℝ) (m N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ fixedRoughSupport (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z ∆
      fixedRoughSupport (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z) :
    3 ≤ d.primeFactors.card := by
  have hdeep := changed_support_has_more_primeFactors 2 _ _
    (fun history hlen => actualExtendedThirdCompactUpperPolicy_through_two
      e h m N false history hlen) N cap w z hd
  omega

/-- The literal original third-policy compiler mass, with all early-rank
moduli removed by proof. This equality leaves the changed descendant mass
visible; it does not supply a smallness estimate for that mass. -/
theorem actualThird_compilerMass_eq_deeper_changed_moduli
    (e h : ℝ) (m N cap : ℕ) (w z : ℝ) :
    reciprocalTotientDensity
      (fixedRoughSupport (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z ∪
        fixedRoughSupport (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z)
      (fun d => |fixedRoughCoefficient (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z d -
        fixedRoughCoefficient (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z d|) =
      reciprocalTotientDensity
        ((fixedRoughSupport (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z ∆
          fixedRoughSupport (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z).filter
            (fun d => 2 < d.primeFactors.card)) (fun _ => 1) := by
  exact compilerMass_eq_deeper_changed_moduli 2 _ _
    (fun history hlen => actualExtendedThirdCompactUpperPolicy_through_two
      e h m N false history hlen) N cap w z

end
end ImbalancedChen.P4ASpliceDifferenceLocalization
