import ImbalancedChen.P2LowerFiniteCellRounding
import ImbalancedChen.ActualCompilerDensityReserve

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

The upper ALL/ANY constructor on the literal squarefree rough carrier.
The reused lower module supplies only its policy-independent prime carrier
and half-open logarithmic labels. No lower coefficient or lower estimate
is used. A supplied frozen tag is retained together with every fine label.

Outer membership is used for positive Mobius coefficients; inner membership
is used for negative ones. Both tests concern the complete retained support,
so they cannot reselect ancestor gates independently. The output is a new
coefficient, not a claim that rounded support is a first-exit tree.

All coefficient comparisons and the exact reciprocal-totient discrepancy
are proved from these finite definitions. No smallness of the crossing mass,
original full87 policy identity, support exponent, or density cap is asserted.
-/

namespace ImbalancedChen.P4AUpperTaggedParityCompiler

noncomputable section
open scoped Classical BigOperators

abbrev universe := P2LowerFiniteCellRounding.universe
abbrev primeLabel := P2LowerFiniteCellRounding.primeLabel
abbrev primeWordLabel := P2LowerFiniteCellRounding.label

def rawSupport (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  fixedRoughSupport retainOdd N cap w z

def raw (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) : ℕ → ℝ :=
  fixedRoughCoefficient retainOdd N cap w z

/-- A frozen finite historical tag accompanies the entire ordered prime word. -/
def label (tag : ℕ → List Bool) (N : ℕ) (tau : ℝ) (d : ℕ) :
    List Bool × List ℤ := (tag d, primeWordLabel N tau d)

def cell (tag : ℕ → List Bool) (N cap : ℕ) (w z tau : ℝ) (d : ℕ) : Finset ℕ :=
  (universe N cap w z).filter (fun e => label tag N tau e = label tag N tau d)

def inner (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) (d : ℕ) : Prop :=
  cell tag N cap w z tau d ⊆ rawSupport retainOdd N cap w z

def outer (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) (d : ℕ) : Prop :=
  (cell tag N cap w z tau d ∩ rawSupport retainOdd N cap w z).Nonempty

def coefficient (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) (d : ℕ) : ℝ :=
  if d ∈ universe N cap w z then
    if 0 ≤ (ArithmeticFunction.moebius d : ℝ) then
      if outer retainOdd tag N cap w z tau d then (ArithmeticFunction.moebius d : ℝ) else 0
    else if inner retainOdd tag N cap w z tau d then (ArithmeticFunction.moebius d : ℝ) else 0
  else 0

theorem rawSupport_subset_universe (retainOdd : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : rawSupport retainOdd N cap w z ⊆ universe N cap w z := by
  intro d hd
  obtain ⟨leaf, hleaf, hprod⟩ :=
    (mem_oddFirstExitRetainedModuli retainOdd (fun _ => 1)
      (roughPrimeUniverse N cap w z) d).mp hd
  have hsub := mem_oddFirstExitRetainedLeaves_selected_reverse_sublist
    retainOdd (fun _ => 1) (roughPrimeUniverse N cap w z) leaf hleaf
  apply Nat.mem_divisors.mpr
  refine ⟨?_, (P2LowerFiniteCellRounding.roughProduct_squarefree N cap w z).ne_zero⟩
  simpa only [List.prod_reverse, hprod] using hsub.prod_dvd_prod

theorem raw_value (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    raw retainOdd N cap w z d =
      if d ∈ rawSupport retainOdd N cap w z then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  unfold raw fixedRoughCoefficient oddFirstExitRetainedCoefficient rawSupport fixedRoughSupport
  split_ifs <;> rfl

theorem self_mem_cell (tag : ℕ → List Bool) (N cap : ℕ) (w z tau : ℝ)
    {d : ℕ} (hd : d ∈ universe N cap w z) : d ∈ cell tag N cap w z tau d :=
  Finset.mem_filter.mpr ⟨hd, rfl⟩

theorem cell_frozen_tag (tag : ℕ → List Bool) (N cap : ℕ) (w z tau : ℝ)
    {d e : ℕ} (he : e ∈ cell tag N cap w z tau d) : tag e = tag d :=
  congrArg Prod.fst (Finset.mem_filter.mp he).2

theorem cell_prime_labels (tag : ℕ → List Bool) (N cap : ℕ) (w z tau : ℝ)
    {d e : ℕ} (he : e ∈ cell tag N cap w z tau d) :
    primeWordLabel N tau e = primeWordLabel N tau d :=
  congrArg Prod.snd (Finset.mem_filter.mp he).2

theorem cell_rank_preserved (tag : ℕ → List Bool) (N cap : ℕ) (w z tau : ℝ)
    {d e : ℕ} (he : e ∈ cell tag N cap w z tau d) :
    e.primeFactorsList.length = d.primeFactorsList.length := by
  have h := congrArg List.length (cell_prime_labels tag N cap w z tau he)
  simpa only [primeWordLabel, P2LowerFiniteCellRounding.label,
    List.length_map, List.length_reverse] using h

/-- A bin crossing has width tau, including the lower endpoint convention. -/
theorem same_primeLabel_coordinate_distance_lt (N : ℕ) {tau : ℝ}
    (htau : 0 < tau) {p q : ℕ} (h : primeLabel N tau p = primeLabel N tau q) :
    |Real.log (p : ℝ) / Real.log N - Real.log (q : ℝ) / Real.log N| < tau := by
  have hp := P2LowerFiniteCellRounding.primeLabel_halfopen N htau p
  have hq := P2LowerFiniteCellRounding.primeLabel_halfopen N htau q
  rw [h] at hp
  apply abs_lt.mpr
  constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]

theorem cells_disjoint (tag : ℕ → List Bool) (N cap : ℕ) (w z tau : ℝ)
    {d e : ℕ} (h : label tag N tau d ≠ label tag N tau e) :
    Disjoint (cell tag N cap w z tau d) (cell tag N cap w z tau e) := by
  apply Finset.disjoint_left.mpr
  intro k hk hd
  exact h ((Finset.mem_filter.mp hk).2.symm.trans (Finset.mem_filter.mp hd).2)

theorem outer_of_raw (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) {d : ℕ}
    (hd : d ∈ rawSupport retainOdd N cap w z) : outer retainOdd tag N cap w z tau d :=
  ⟨d, Finset.mem_inter.mpr
    ⟨self_mem_cell tag N cap w z tau (rawSupport_subset_universe retainOdd N cap w z hd), hd⟩⟩

/-- Coefficientwise upper domination is a theorem of the literal outer/inner tests. -/
theorem raw_le_coefficient (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) (d : ℕ) :
    raw retainOdd N cap w z d ≤ coefficient retainOdd tag N cap w z tau d := by
  rw [raw_value]
  by_cases hd : d ∈ universe N cap w z
  · have hself := self_mem_cell tag N cap w z tau hd
    by_cases hsign : 0 ≤ (ArithmeticFunction.moebius d : ℝ)
    · by_cases hr : d ∈ rawSupport retainOdd N cap w z
      · have ho := outer_of_raw retainOdd tag N cap w z tau hr
        simp only [coefficient, if_pos hd, if_pos hsign, if_pos ho, if_pos hr, le_refl]
      · simp only [coefficient, if_pos hd, if_pos hsign, if_neg hr]
        split_ifs <;> linarith
    · by_cases hi : inner retainOdd tag N cap w z tau d
      · have hr := hi hself
        simp only [coefficient, if_pos hd, if_neg hsign, if_pos hi, if_pos hr, le_refl]
      · simp only [coefficient, if_pos hd, if_neg hsign, if_neg hi]
        split_ifs <;> linarith
  · have hr : d ∉ rawSupport retainOdd N cap w z :=
      fun hr => hd (rawSupport_subset_universe retainOdd N cap w z hr)
    simp only [coefficient, if_neg hd, if_neg hr, le_refl]

theorem coefficient_abs_le_one (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) (d : ℕ) :
    |coefficient retainOdd tag N cap w z tau d| ≤ 1 := by
  unfold coefficient
  split_ifs <;> try norm_num
  all_goals exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))

/-- An active rounded modulus has an original witness in its very same tagged cell. -/
theorem active_has_raw_witness (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) {d : ℕ}
    (hd : coefficient retainOdd tag N cap w z tau d ≠ 0) :
    ∃ e ∈ rawSupport retainOdd N cap w z,
      e ∈ cell tag N cap w z tau d ∧ tag e = tag d ∧
        primeWordLabel N tau e = primeWordLabel N tau d := by
  have hu : d ∈ universe N cap w z := by
    by_contra hu
    exact hd (by simp only [coefficient, if_neg hu])
  have ho : outer retainOdd tag N cap w z tau d := by
    by_cases hsign : 0 ≤ (ArithmeticFunction.moebius d : ℝ)
    · by_contra ho
      exact hd (by simp only [coefficient, if_pos hu, if_pos hsign, if_neg ho])
    · have hi : inner retainOdd tag N cap w z tau d := by
        by_contra hi
        exact hd (by simp only [coefficient, if_pos hu, if_neg hsign, if_neg hi])
      exact outer_of_raw retainOdd tag N cap w z tau
        (hi (self_mem_cell tag N cap w z tau hu))
  obtain ⟨e, he⟩ := ho
  have hc := (Finset.mem_inter.mp he).1
  exact ⟨e, (Finset.mem_inter.mp he).2, hc,
    cell_frozen_tag tag N cap w z tau hc, cell_prime_labels tag N cap w z tau hc⟩

/-- The two actual ways upper parity rounding changes a coefficient. -/
def changed (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) (d : ℕ) : Prop :=
  if 0 ≤ (ArithmeticFunction.moebius d : ℝ) then
    outer retainOdd tag N cap w z tau d ∧ d ∉ rawSupport retainOdd N cap w z
  else d ∈ rawSupport retainOdd N cap w z ∧ ¬inner retainOdd tag N cap w z tau d

/-- A crossing cell has both a retained witness and an unretained witness. -/
def crossing (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) (d : ℕ) : Prop :=
  outer retainOdd tag N cap w z tau d ∧ ¬inner retainOdd tag N cap w z tau d

/-- Crossing is a genuine pair of opposite support decisions in one tagged cube. -/
theorem crossing_has_opposite_witnesses (retainOdd : List ℕ → Bool)
    (tag : ℕ → List Bool) (N cap : ℕ) (w z tau : ℝ) {d : ℕ}
    (hc : crossing retainOdd tag N cap w z tau d) :
    ∃ a ∈ cell tag N cap w z tau d, ∃ b ∈ cell tag N cap w z tau d,
      a ∈ rawSupport retainOdd N cap w z ∧ b ∉ rawSupport retainOdd N cap w z := by
  obtain ⟨a, ha⟩ := hc.1
  have hb : ∃ b ∈ cell tag N cap w z tau d, b ∉ rawSupport retainOdd N cap w z := by
    by_contra hn
    apply hc.2
    intro b hb
    by_contra hbr
    exact hn ⟨b, hb, hbr⟩
  obtain ⟨b, hb, hbr⟩ := hb
  exact ⟨a, (Finset.mem_inter.mp ha).1, b, hb, (Finset.mem_inter.mp ha).2, hbr⟩

theorem changed_implies_crossing (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) {d : ℕ} (hd : d ∈ universe N cap w z)
    (hc : changed retainOdd tag N cap w z tau d) : crossing retainOdd tag N cap w z tau d := by
  by_cases hsign : 0 ≤ (ArithmeticFunction.moebius d : ℝ)
  · rw [changed, if_pos hsign] at hc
    exact ⟨hc.1, fun hi => hc.2 (hi (self_mem_cell tag N cap w z tau hd))⟩
  · rw [changed, if_neg hsign] at hc
    exact ⟨outer_of_raw retainOdd tag N cap w z tau hc.1, hc.2⟩

/-- There is no factor two: squarefree parity changes only between zero and one sign. -/
theorem abs_coefficient_sub_raw (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) {d : ℕ} (hd : d ∈ universe N cap w z) :
    |coefficient retainOdd tag N cap w z tau d - raw retainOdd N cap w z d| =
      if changed retainOdd tag N cap w z tau d then 1 else 0 := by
  have hmu : |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
      (P2LowerFiniteCellRounding.universe_squarefree N cap w z hd)
  rw [raw_value]
  by_cases hsign : 0 ≤ (ArithmeticFunction.moebius d : ℝ)
  · by_cases hr : d ∈ rawSupport retainOdd N cap w z
    · have ho := outer_of_raw retainOdd tag N cap w z tau hr
      simp only [coefficient, if_pos hd, if_pos hsign, if_pos ho, if_pos hr,
        changed, hr, not_true_eq_false, and_false, if_false, sub_self, abs_zero]
    · by_cases ho : outer retainOdd tag N cap w z tau d
      · simp only [coefficient, if_pos hd, if_pos hsign, if_pos ho, if_neg hr,
          changed, ho, hr, not_false_eq_true, and_self, if_true, sub_zero, hmu]
      · simp only [coefficient, if_pos hd, if_pos hsign, if_neg ho, if_neg hr,
          changed, ho, false_and, if_false, sub_self, abs_zero]
  · by_cases hr : d ∈ rawSupport retainOdd N cap w z
    · by_cases hi : inner retainOdd tag N cap w z tau d
      · simp only [coefficient, if_pos hd, if_neg hsign, if_pos hi, if_pos hr,
          changed, hr, hi, not_true_eq_false, and_false, if_false, sub_self, abs_zero]
      · simp only [coefficient, if_pos hd, if_neg hsign, if_neg hi, if_pos hr,
          changed, hr, hi, not_false_eq_true, and_self, if_true, zero_sub, abs_neg, hmu]
    · have hi : ¬inner retainOdd tag N cap w z tau d :=
        fun hi => hr (hi (self_mem_cell tag N cap w z tau hd))
      simp only [coefficient, if_pos hd, if_neg hsign, if_neg hi, if_neg hr,
        changed, hr, false_and, if_false, sub_self, abs_zero]

def changedMass (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) : ℝ :=
  ∑ d ∈ (universe N cap w z).filter (changed retainOdd tag N cap w z tau),
    1 / (Nat.totient d : ℝ)

def crossingMass (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) : ℝ :=
  ∑ d ∈ (universe N cap w z).filter (crossing retainOdd tag N cap w z tau),
    1 / (Nat.totient d : ℝ)

/-- Exact literal compiler norm; no wall estimate or compiler-error premise. -/
theorem coefficient_error_eq_changedMass (retainOdd : List ℕ → Bool)
    (tag : ℕ → List Bool) (N cap : ℕ) (w z tau : ℝ) :
    reciprocalTotientDensity (universe N cap w z)
      (fun d => |coefficient retainOdd tag N cap w z tau d - raw retainOdd N cap w z d|) =
        changedMass retainOdd tag N cap w z tau := by
  unfold reciprocalTotientDensity changedMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  rw [abs_coefficient_sub_raw retainOdd tag N cap w z tau hd]
  split_ifs <;> simp

theorem changedMass_le_crossingMass (retainOdd : List ℕ → Bool)
    (tag : ℕ → List Bool) (N cap : ℕ) (w z tau : ℝ) :
    changedMass retainOdd tag N cap w z tau ≤ crossingMass retainOdd tag N cap w z tau := by
  unfold changedMass crossingMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hd, hc⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨hd, changed_implies_crossing retainOdd tag N cap w z tau hd hc⟩
  · intro d _ _
    positivity

/-- Exact signed density increase equals the nonnegative literal compiler norm. -/
theorem rough_density_increase_eq_changedMass (retainOdd : List ℕ → Bool)
    (tag : ℕ → List Bool) (N cap : ℕ) (w z tau : ℝ) :
    reciprocalTotientDensity (universe N cap w z) (coefficient retainOdd tag N cap w z tau) -
      reciprocalTotientDensity (universe N cap w z) (raw retainOdd N cap w z) =
        changedMass retainOdd tag N cap w z tau := by
  rw [← coefficient_error_eq_changedMass]
  unfold reciprocalTotientDensity
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [abs_of_nonneg (sub_nonneg.mpr (raw_le_coefficient retainOdd tag N cap w z tau d))]
  ring

end
end ImbalancedChen.P4AUpperTaggedParityCompiler
