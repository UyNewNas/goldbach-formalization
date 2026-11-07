import ImbalancedChen.ActualSmallRoughAttachment

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A nonzero high physical q is traced all the way back to a literal
retained odd-first-exit leaf, rather than merely to a number in a
displayed rough support.  The original sign-sensitive beta and the
full small/rough modulus remain attached.  No PP admission, actual
87-domain rank bound, or analytic saving is inferred here.
-/

namespace ImbalancedChen.P4AOriginalFull87HighQCausalLeaf

noncomputable section
open scoped Classical BigOperators

/-- Elementary finite-product bound, with no sieve hypothesis. -/
private theorem list_prod_le_cap_pow_length
    (cap : ℕ) (xs : List ℕ)
    (hcap : ∀ p ∈ xs, p ≤ cap) :
    xs.prod ≤ cap ^ xs.length := by
  induction xs with
  | nil =>
      simp
  | cons p ps ih =>
      have hp : p ≤ cap := hcap p (by simp)
      have hps : ∀ x ∈ ps, x ≤ cap := by
        intro x hx
        exact hcap x (by simp [hx])
      have htail := ih hps
      calc
        (p :: ps).prod = p * ps.prod := rfl
        _ ≤ cap * cap ^ ps.length := Nat.mul_le_mul hp htail
        _ = cap ^ (p :: ps).length := by
          simp [pow_succ, mul_comm]

/-- Nonzero high-q terms have an ACTUAL retained rough leaf.  The
selected word is in the original descending rough-prime carrier, has
its original parity and unit local mass, and its actual sign-sensitive
small beta is unchanged.  This does not assert a numerical PP level. -/
theorem high_q_has_actual_retained_leaf
    (P : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (X q : ℕ)
    (hX : X < q)
    (hq : actualSmallRoughRho (P false) N cap w z L q ≠ 0) :
    ∃ a ∈ actualSmallRosserSupport N cap w,
      ∃ leaf ∈ oddFirstExitRetainedLeaves (P false)
          (fun _ : ℕ => (1 : ℝ)) (roughPrimeUniverse N cap w z),
        q = a * leaf.selected.prod ∧
        (a : ℝ) < L ∧
        fixedRoughCoefficient (P false) N cap w z
          leaf.selected.prod ≠ 0 ∧
        leaf.selected.reverse <+ roughPrimeUniverse N cap w z ∧
        leaf.positive = evenListLength leaf.selected ∧
        leaf.mass = 1 ∧
        (∀ p ∈ leaf.selected,
          p < cap ∧ p.Prime ∧ ¬p ∣ N ∧
            w ≤ (p : ℝ) ∧ (p : ℝ) < z) ∧
        (X : ℝ) < L * (leaf.selected.prod : ℝ) ∧
        actualSmallRoughRho (P false) N cap w z L q =
          signAttachedCoefficient
            (fixedRoughCoefficient (P false) N cap w z leaf.selected.prod)
            (actualSmallRosserMinus N cap w L a)
            (actualSmallRosserPlus N cap w L a) := by
  obtain ⟨a, ha, b, hb, hab, haL, hbne⟩ :=
    actualSmallRoughRho_ne_zero_factors (P false) N cap w z L hq
  change b ∈ oddFirstExitRetainedModuli (P false)
    (fun _ : ℕ => (1 : ℝ)) (roughPrimeUniverse N cap w z) at hb
  obtain ⟨leaf, hleaf, hleafProd⟩ :=
    (mem_oddFirstExitRetainedModuli (P false)
      (fun _ : ℕ => (1 : ℝ)) (roughPrimeUniverse N cap w z) b).mp hb
  subst b
  have hsub :=
    mem_oddFirstExitRetainedLeaves_selected_reverse_sublist
      (P false) (fun _ : ℕ => (1 : ℝ))
      (roughPrimeUniverse N cap w z) leaf hleaf
  have hpar :=
    mem_oddFirstExitRetainedLeaves_positive_eq_evenListLength
      (P false) (fun _ : ℕ => (1 : ℝ))
      (roughPrimeUniverse N cap w z) leaf hleaf
  have hmass : leaf.mass = 1 := by
    have hm := mem_oddFirstExitRetainedLeaves_mass_eq_selected_prod
      (P false) (fun _ : ℕ => (1 : ℝ))
      (roughPrimeUniverse N cap w z) leaf hleaf
    simpa using hm
  have hselected :
      ∀ p ∈ leaf.selected, p < cap ∧ p.Prime ∧ ¬p ∣ N ∧
        w ≤ (p : ℝ) ∧ (p : ℝ) < z := by
    intro p hp
    have hc : p ∈ roughPrimeUniverse N cap w z := by
      apply hsub.subset
      simpa using hp
    exact mem_roughPrimeUniverse.mp hc
  have hXreal : (X : ℝ) < (q : ℝ) := by exact_mod_cast hX
  have hthreshold : (X : ℝ) < L * (leaf.selected.prod : ℝ) := by
    calc
      (X : ℝ) < (q : ℝ) := hXreal
      _ = (a : ℝ) * (leaf.selected.prod : ℝ) := by exact_mod_cast hab
      _ ≤ L * (leaf.selected.prod : ℝ) :=
        mul_le_mul_of_nonneg_right haL.le (Nat.cast_nonneg _)
  have hcoeff :
      actualSmallRoughRho (P false) N cap w z L q =
        signAttachedCoefficient
          (fixedRoughCoefficient (P false) N cap w z leaf.selected.prod)
          (actualSmallRosserMinus N cap w L a)
          (actualSmallRosserPlus N cap w L a) := by
    rw [hab]
    change smallRoughRho (actualSmallRosserSupport N cap w)
      (fixedRoughSupport (P false) N cap w z)
      (fixedRoughCoefficient (P false) N cap w z)
      (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L)
      (a * leaf.selected.prod) =
      smallRoughPairCoefficient
        (fixedRoughCoefficient (P false) N cap w z)
        (actualSmallRosserMinus N cap w L)
        (actualSmallRosserPlus N cap w L)
        (a, leaf.selected.prod)
    exact smallRoughRho_mul
      (fun d hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
      (fun d hd => fixedRoughSupport_roughPrimeSupportedAt
        (P false) N cap w z hd)
      (fixedRoughCoefficient (P false) N cap w z)
      (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L) ha hb
  exact ⟨a, ha, leaf, hleaf, hab, haL, hbne,
    hsub, hpar, hmass, hselected, hthreshold, hcoeff⟩

/-- A precise, possibly weak, finite rank envelope for every ACTUAL
unlicensed coefficient: X < L * cap^length(selected).  The cap is the
original enumeration cap, not a claimed analytic rough-factor bound. -/
theorem high_q_actual_leaf_rank_envelope
    (P : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (X q : ℕ)
    (hX : X < q)
    (hq : actualSmallRoughRho (P false) N cap w z L q ≠ 0) :
    ∃ leaf ∈ oddFirstExitRetainedLeaves (P false)
        (fun _ : ℕ => (1 : ℝ)) (roughPrimeUniverse N cap w z),
      (X : ℝ) < L * (cap : ℝ) ^ leaf.selected.length ∧
      leaf.selected.reverse <+ roughPrimeUniverse N cap w z ∧
      leaf.positive = evenListLength leaf.selected := by
  obtain ⟨a, ha, leaf, hleaf, hab, haL, hbne,
    hsub, hpar, hmass, hselected, hthreshold, hcoeff⟩ :=
    high_q_has_actual_retained_leaf P N cap w z L X q hX hq
  have hcap : leaf.selected.prod ≤ cap ^ leaf.selected.length :=
    list_prod_le_cap_pow_length cap leaf.selected
      (fun p hp => Nat.le_of_lt (hselected p hp).1)
  have hcast : (leaf.selected.prod : ℝ) ≤
      (cap : ℝ) ^ leaf.selected.length := by
    exact_mod_cast hcap
  have hLnonneg : 0 ≤ L :=
    (Nat.cast_nonneg a).trans haL.le
  refine ⟨leaf, hleaf, ?_, hsub, hpar⟩
  exact hthreshold.trans_le
    (mul_le_mul_of_nonneg_left hcast hLnonneg)

/-- If the PP cutoff already exceeds the small beta level, a high-q
active coefficient must have at least one actual retained rough prime.
The empty inherited leaf cannot be charged as a high-q exception. -/
theorem high_q_actual_leaf_nonempty
    (P : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (X q : ℕ)
    (hLX : L ≤ (X : ℝ))
    (hX : X < q)
    (hq : actualSmallRoughRho (P false) N cap w z L q ≠ 0) :
    ∃ leaf ∈ oddFirstExitRetainedLeaves (P false)
        (fun _ : ℕ => (1 : ℝ)) (roughPrimeUniverse N cap w z),
      leaf.selected ≠ [] ∧
      leaf.selected.reverse <+ roughPrimeUniverse N cap w z := by
  obtain ⟨a, ha, leaf, hleaf, hab, haL, hbne,
    hsub, hpar, hmass, hselected, hthreshold, hcoeff⟩ :=
    high_q_has_actual_retained_leaf P N cap w z L X q hX hq
  refine ⟨leaf, hleaf, ?_, hsub⟩
  intro hempty
  have hbad : (X : ℝ) < L := by simpa [hempty] using hthreshold
  exact (not_lt_of_ge hLX) hbad

end
end ImbalancedChen.P4AOriginalFull87HighQCausalLeaf
