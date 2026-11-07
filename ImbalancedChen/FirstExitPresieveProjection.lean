import ImbalancedChen.FirstExitTree

/-!
# Exact first-exit substitution and presieve projection

The carrier is processed in the order `rough ++ small`. Each retained
rough leaf is continued through the small carrier with its original history,
sign and unsigned mass. The full polynomial is exactly the rough polynomial
times the small Euler product, plus the sum of these continuation corrections.

If every even prefix is retained, each correction is nonnegative. If every
odd prefix is retained, each is nonpositive. These signs hold for either
incoming sign and a nonnegative incoming mass. In particular, no projection
inequality is multiplied by a possibly negative leaf coefficient.

The statements are finite algebra for arbitrary lists and policies. Actual
prime carriers, causal cap rules, and density asymptotics are separate inputs.
-/

namespace ImbalancedChen

noncomputable section

/-- Splitting the carrier preserves every retained leaf's entire incoming
history, sign and mass before continuing through the second carrier. -/
theorem firstExitRetainedLeaves_append
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (selectedPrefix rough small : List α) (positive : Bool) (mass : ℝ) :
    firstExitRetainedLeaves retained h selectedPrefix positive mass (rough ++ small) =
      (firstExitRetainedLeaves retained h selectedPrefix positive mass rough).flatMap
        (fun leaf => firstExitRetainedLeaves retained h leaf.selected
          leaf.positive leaf.mass small) := by
  induction rough generalizing selectedPrefix positive mass with
  | nil => simp [firstExitRetainedLeaves]
  | cons p ps ih =>
      by_cases hr : retained (Bool.not positive) (p :: selectedPrefix) = true
      · simp [firstExitRetainedLeaves, hr, ih, List.flatMap_append]
      · simp [firstExitRetainedLeaves, hr, ih]

/-- The full polynomial is the sum of the actual continued rough leaves. -/
theorem firstExitRetainedPolynomial_append_eq_leaves_sum
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (selectedPrefix rough small : List α) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial retained h selectedPrefix positive mass (rough ++ small) =
      ((firstExitRetainedLeaves retained h selectedPrefix positive mass rough).map
        (fun leaf => firstExitRetainedPolynomial retained h leaf.selected
          leaf.positive leaf.mass small)).sum := by
  induction rough generalizing selectedPrefix positive mass with
  | nil => simp [firstExitRetainedLeaves]
  | cons p ps ih =>
      by_cases hr : retained (Bool.not positive) (p :: selectedPrefix) = true
      · simp [firstExitRetainedPolynomial, firstExitRetainedLeaves, hr, ih]
      · simp [firstExitRetainedPolynomial, firstExitRetainedLeaves, hr, ih]

/-- Exact presieve decomposition. The remaining error is a sum of genuine
small-carrier corrections with the rough leaves' inherited histories. -/
theorem firstExitRetainedPolynomial_append_eq_mul_product_add_corrections
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (selectedPrefix rough small : List α) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial retained h selectedPrefix positive mass (rough ++ small) =
      firstExitRetainedPolynomial retained h selectedPrefix positive mass rough *
          (small.map fun p => 1 - h p).prod +
        ((firstExitRetainedLeaves retained h selectedPrefix positive mass rough).map
          (fun leaf => firstExitCorrection retained h leaf.selected
            leaf.positive leaf.mass small)).sum := by
  have hsum (leaves : List (FirstExitLeaf α)) :
      (leaves.map (fun leaf => firstExitRetainedPolynomial retained h leaf.selected
          leaf.positive leaf.mass small)).sum =
        (leaves.map FirstExitLeaf.value).sum * (small.map fun p => 1 - h p).prod +
          (leaves.map (fun leaf => firstExitCorrection retained h leaf.selected
            leaf.positive leaf.mass small)).sum := by
    induction leaves with
    | nil => simp
    | cons leaf leaves ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [firstExitRetainedPolynomial_eq_product_add_correction, ih]
        simp only [FirstExitLeaf.value]
        ring
  rw [firstExitRetainedPolynomial_append_eq_leaves_sum, hsum,
    ← firstExitRetainedPolynomial_eq_leaves_sum]

/-- Retention and sign changes do not change the nonnegativity of the
unsigned masses accumulated along the actual rough leaves. -/
theorem firstExitRetainedLeaves_mass_nonneg
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (selectedPrefix remaining : List α) (positive : Bool) (mass : ℝ)
    (hmass : 0 ≤ mass) (hh : ∀ p ∈ remaining, 0 ≤ h p) :
    ∀ leaf ∈ firstExitRetainedLeaves retained h selectedPrefix positive mass remaining,
      0 ≤ leaf.mass := by
  induction remaining generalizing selectedPrefix positive mass with
  | nil =>
      intro leaf hleaf
      simp only [firstExitRetainedLeaves, List.mem_singleton] at hleaf
      subst leaf
      exact hmass
  | cons p ps ih =>
      have hp := hh p List.mem_cons_self
      have hps : ∀ q ∈ ps, 0 ≤ h q := fun q hq => hh q (List.mem_cons_of_mem p hq)
      intro leaf hleaf
      by_cases hr : retained (Bool.not positive) (p :: selectedPrefix) = true
      · rw [firstExitRetainedLeaves, if_pos hr, List.mem_append] at hleaf
        rcases hleaf with hskip | hselect
        · exact ih selectedPrefix positive mass hmass hps leaf hskip
        · exact ih (p :: selectedPrefix) (Bool.not positive) (mass * h p)
            (mul_nonneg hmass hp) hps leaf hselect
      · rw [firstExitRetainedLeaves, if_neg hr, List.append_nil] at hleaf
        exact ih selectedPrefix positive mass hmass hps leaf hleaf

/-- Retaining every odd prefix forces every first-exit correction to be
nonpositive, even if the incoming prefix has negative sign. -/
theorem firstExitCorrection_nonpos_of_odd_retained
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (selectedPrefix remaining : List α) (positive : Bool) (mass : ℝ)
    (hodd : ∀ pre, retained false pre = true)
    (hmass : 0 ≤ mass)
    (hh : ∀ p ∈ remaining, 0 ≤ h p ∧ h p ≤ 1) :
    firstExitCorrection retained h selectedPrefix positive mass remaining ≤ 0 := by
  induction remaining generalizing selectedPrefix positive mass with
  | nil => simp [firstExitCorrection]
  | cons p ps ih =>
      have hp : 0 ≤ h p ∧ h p ≤ 1 := hh p List.mem_cons_self
      have hps : ∀ q ∈ ps, 0 ≤ h q ∧ h q ≤ 1 :=
        fun q hq => hh q (List.mem_cons_of_mem p hq)
      have hleft := ih selectedPrefix positive mass hmass hps
      have hright := ih (p :: selectedPrefix) (Bool.not positive) (mass * h p)
        (mul_nonneg hmass hp.1) hps
      have hprod : 0 ≤ (ps.map fun q => 1 - h q).prod :=
        list_prod_nonneg_of_mem (fun q => 1 - h q) ps
          (fun q hq => sub_nonneg.mpr (hps q hq).2)
      simp only [firstExitCorrection]
      by_cases hr : retained (Bool.not positive) (p :: selectedPrefix) = true
      · rw [if_pos hr]
        exact add_nonpos hleft hright
      · rw [if_neg hr]
        cases positive with
        | false =>
            exact add_nonpos hleft
              (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hmass hp.1))
                hprod)
        | true => exact False.elim (hr (hodd (p :: selectedPrefix)))

/-- The upper projection follows from nonnegative continuation corrections,
not from multiplying a local inequality by a signed rough coefficient. -/
theorem firstExitPresieveProjection_upper_of_even_retained
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (selectedPrefix rough small : List α) (positive : Bool) (mass : ℝ)
    (heven : ∀ pre, retained true pre = true) (hmass : 0 ≤ mass)
    (hrough : ∀ p ∈ rough, 0 ≤ h p)
    (hsmall : ∀ p ∈ small, 0 ≤ h p ∧ h p ≤ 1) :
    firstExitRetainedPolynomial retained h selectedPrefix positive mass rough *
        (small.map fun p => 1 - h p).prod ≤
      firstExitRetainedPolynomial retained h selectedPrefix positive mass (rough ++ small) := by
  rw [firstExitRetainedPolynomial_append_eq_mul_product_add_corrections]
  apply le_add_of_nonneg_right
  apply List.sum_nonneg
  intro x hx
  rcases List.mem_map.mp hx with ⟨leaf, hleaf, rfl⟩
  exact firstExitCorrection_nonneg_of_even_retained retained h leaf.selected small
    leaf.positive leaf.mass heven
    (firstExitRetainedLeaves_mass_nonneg retained h selectedPrefix rough positive mass
      hmass hrough leaf hleaf) hsmall

/-- The lower projection has the opposite direction because every
continuation correction is nonpositive. -/
theorem firstExitPresieveProjection_lower_of_odd_retained
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (selectedPrefix rough small : List α) (positive : Bool) (mass : ℝ)
    (hodd : ∀ pre, retained false pre = true) (hmass : 0 ≤ mass)
    (hrough : ∀ p ∈ rough, 0 ≤ h p)
    (hsmall : ∀ p ∈ small, 0 ≤ h p ∧ h p ≤ 1) :
    firstExitRetainedPolynomial retained h selectedPrefix positive mass (rough ++ small) ≤
      firstExitRetainedPolynomial retained h selectedPrefix positive mass rough *
        (small.map fun p => 1 - h p).prod := by
  rw [firstExitRetainedPolynomial_append_eq_mul_product_add_corrections]
  apply add_le_of_nonpos_right
  have hsum := List.sum_le_sum (g := fun _ : FirstExitLeaf α => (0 : ℝ))
    (fun leaf hleaf => firstExitCorrection_nonpos_of_odd_retained retained h
      leaf.selected small leaf.positive leaf.mass hodd
      (firstExitRetainedLeaves_mass_nonneg retained h selectedPrefix rough positive mass
        hmass hrough leaf hleaf) hsmall)
  simpa using hsum

/-- A policy with only even first exits; odd prefixes are always retained. -/
def evenFirstExitPolicy {α : Type*}
    (retainEven : List α → Bool) (positive : Bool) (selectedPrefix : List α) : Bool :=
  !positive || retainEven selectedPrefix

@[simp] theorem evenFirstExitPolicy_odd {α : Type*}
    (retainEven : List α → Bool) (selectedPrefix : List α) :
    evenFirstExitPolicy retainEven false selectedPrefix = true := by
  simp [evenFirstExitPolicy]

/-- Root polynomial of an even-first-exit tree. -/
def evenFirstExitRetainedPolynomial {α : Type*}
    (retainEven : List α → Bool) (h : α → ℝ) (carrier : List α) : ℝ :=
  firstExitRetainedPolynomial (evenFirstExitPolicy retainEven) h [] true 1 carrier

theorem oddFirstExitRetainedPolynomial_presieveProjection
    {α : Type*} (retainOdd : List α → Bool) (h : α → ℝ) (rough small : List α)
    (hrough : ∀ p ∈ rough, 0 ≤ h p)
    (hsmall : ∀ p ∈ small, 0 ≤ h p ∧ h p ≤ 1) :
    oddFirstExitRetainedPolynomial retainOdd h rough * (small.map fun p => 1 - h p).prod ≤
      oddFirstExitRetainedPolynomial retainOdd h (rough ++ small) := by
  exact firstExitPresieveProjection_upper_of_even_retained (oddFirstExitPolicy retainOdd)
    h [] rough small true 1 (oddFirstExitPolicy_even retainOdd) zero_le_one hrough hsmall

theorem evenFirstExitRetainedPolynomial_presieveProjection
    {α : Type*} (retainEven : List α → Bool) (h : α → ℝ) (rough small : List α)
    (hrough : ∀ p ∈ rough, 0 ≤ h p)
    (hsmall : ∀ p ∈ small, 0 ≤ h p ∧ h p ≤ 1) :
    evenFirstExitRetainedPolynomial retainEven h (rough ++ small) ≤
      evenFirstExitRetainedPolynomial retainEven h rough * (small.map fun p => 1 - h p).prod := by
  exact firstExitPresieveProjection_lower_of_odd_retained (evenFirstExitPolicy retainEven)
    h [] rough small true 1 (evenFirstExitPolicy_odd retainEven) zero_le_one hrough hsmall

end

end ImbalancedChen
