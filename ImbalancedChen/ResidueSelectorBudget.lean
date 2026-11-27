import ImbalancedChen.PrimeRectanglePrefixes

/-!
# Loss-free finite residue-selector budgets

A bound on the sum over moduli, uniform over primitive residue selectors,
also bounds the sum of the pointwise largest absolute errors. The selector
is chosen separately at each modulus before applying the single assumed
sum bound. Thus recentering about the reduced-residue average costs only
the factor two, with no factor counting the moduli or the residue classes.

The final specializations use the literal full prime-prefix pair counts
and their genuine coprime masses. The common main term may depend on the
modulus but never on its residue. Every distribution estimate remains an
explicit hypothesis; this file proves only finite algebra and selection.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Elementary finite maximization, stated without a supremum or an
analytic boundedness premise. -/
theorem exists_abs_max_on_finset (s : Finset ℕ) (f : ℕ → ℝ) :
    s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, |f b| ≤ |f a| := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rintro ⟨a, ha⟩
      simp at ha
  | @insert a s ha ih =>
      intro _
      by_cases hs : s.Nonempty
      · obtain ⟨b, hb, hmax⟩ := ih hs
        by_cases hab : |f a| ≤ |f b|
        · refine ⟨b, Finset.mem_insert_of_mem hb, ?_⟩
          intro c hc
          rcases Finset.mem_insert.mp hc with hca | hc
          · subst c
            exact hab
          · exact hmax c hc
        · refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
          intro c hc
          rcases Finset.mem_insert.mp hc with hca | hc
          · subst c
            exact le_rfl
          · exact (hmax c hc).trans (le_of_not_ge hab)
      · refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
        intro c hc
        rcases Finset.mem_insert.mp hc with hca | hc
        · subst c
          exact le_rfl
        · exact False.elim (hs ⟨c, hc⟩)

/-- Every positive modulus has a canonical primitive residue, including
the sole representative zero at modulus one. -/
theorem finiteReducedResidues_nonempty (d : ℕ) (hd : 0 < d) :
    (finiteReducedResidues d).Nonempty := by
  apply Finset.card_pos.mp
  rw [card_finiteReducedResidues]
  exact Nat.totient_pos.mpr hd

/-- One selector simultaneously attains the largest absolute error at
every positive modulus. Its value at zero is immaterial. -/
theorem exists_reducedResidue_abs_max_selector (E : ℕ → ℕ → ℝ) :
    ∃ a : ℕ → ℕ, ∀ d : ℕ, 0 < d →
      a d ∈ finiteReducedResidues d ∧
        ∀ b ∈ finiteReducedResidues d, |E d b| ≤ |E d (a d)| := by
  classical
  have hm : ∀ d : ℕ, ∃ a : ℕ, 0 < d →
      a ∈ finiteReducedResidues d ∧
        ∀ b ∈ finiteReducedResidues d, |E d b| ≤ |E d a| := by
    intro d
    by_cases hd : 0 < d
    · obtain ⟨a, ha, hmax⟩ := exists_abs_max_on_finset
        (finiteReducedResidues d) (E d) (finiteReducedResidues_nonempty d hd)
      exact ⟨a, fun _ => ⟨ha, hmax⟩⟩
    · exact ⟨0, fun hd' => False.elim (hd hd')⟩
  exact ⟨fun d => Classical.choose (hm d),
    fun d => Classical.choose_spec (hm d)⟩

/-- Finite sums commute with independent maximization: a single primitive
selector dominates every other selector's sum, term by term. -/
theorem exists_reducedResidue_selector_maximizing_sum
    (S : Finset ℕ) (E : ℕ → ℕ → ℝ)
    (hS : ∀ d ∈ S, 0 < d) :
    ∃ a : ℕ → ℕ, (∀ d ∈ S, a d ∈ finiteReducedResidues d) ∧
      ∀ b : ℕ → ℕ, (∀ d ∈ S, b d ∈ finiteReducedResidues d) →
        (∑ d ∈ S, |E d (b d)|) ≤ ∑ d ∈ S, |E d (a d)| := by
  obtain ⟨a, ha⟩ := exists_reducedResidue_abs_max_selector E
  refine ⟨a, fun d hd => (ha d (hS d hd)).1, ?_⟩
  intro b hb
  exact Finset.sum_le_sum fun d hd => (ha d (hS d hd)).2 (b d) (hb d hd)

/-- The reduced-residue average of any signed finite error array is at
most its common absolute-error bound. The divisor is exactly `φ(d)`. -/
theorem abs_reducedResidue_average_le
    (E : ℕ → ℝ) (ε : ℝ) (d : ℕ) (hd : 0 < d)
    (hE : ∀ a ∈ finiteReducedResidues d, |E a| ≤ ε) :
    |(∑ a ∈ finiteReducedResidues d, E a) / (Nat.totient d : ℝ)| ≤ ε := by
  have hphi : (0 : ℝ) < Nat.totient d := by
    exact_mod_cast Nat.totient_pos.mpr hd
  rw [abs_div, abs_of_pos hphi]
  calc
    |∑ a ∈ finiteReducedResidues d, E a| / (Nat.totient d : ℝ) ≤
        (∑ a ∈ finiteReducedResidues d, |E a|) / (Nat.totient d : ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hphi.le
    _ ≤ (∑ _a ∈ finiteReducedResidues d, ε) / (Nat.totient d : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum hE) hphi.le
    _ = ε := by
      rw [Finset.sum_const, nsmul_eq_mul, card_finiteReducedResidues]
      field_simp [hphi.ne']
      <;> ring

/-- A selected canonical primitive error costs at most twice a common
absolute bound after subtracting its actual reduced-residue average. -/
theorem abs_reducedResidue_recentered_le_two_mul
    (E : ℕ → ℝ) (ε : ℝ) (a d : ℕ) (hd : 0 < d)
    (ha : a ∈ finiteReducedResidues d)
    (hE : ∀ b ∈ finiteReducedResidues d, |E b| ≤ ε) :
    |E a - (∑ b ∈ finiteReducedResidues d, E b) / (Nat.totient d : ℝ)| ≤
      2 * ε := by
  calc
    |E a - (∑ b ∈ finiteReducedResidues d, E b) / (Nat.totient d : ℝ)| ≤
        |E a| + |(∑ b ∈ finiteReducedResidues d, E b) / (Nat.totient d : ℝ)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (E a) 0
          ((∑ b ∈ finiteReducedResidues d, E b) / (Nat.totient d : ℝ)))
    _ ≤ ε + ε := add_le_add (hE a ha)
      (abs_reducedResidue_average_le E ε d hd hE)
    _ = 2 * ε := by ring

/-- A selector-uniform bound for a SUM of raw errors yields twice that
same budget for the SUM of recentered errors. No cardinality factor is
introduced. The empty modulus set also follows from the stated premise. -/
theorem sum_abs_reducedResidue_recentered_le_two_mul_of_uniform_selector
    (S : Finset ℕ) (E : ℕ → ℕ → ℝ) (B : ℝ)
    (hS : ∀ d ∈ S, 0 < d)
    (hE : ∀ b : ℕ → ℕ, (∀ d ∈ S, b d ∈ finiteReducedResidues d) →
      (∑ d ∈ S, |E d (b d)|) ≤ B)
    (a : ℕ → ℕ) (ha : ∀ d ∈ S, a d ∈ finiteReducedResidues d) :
    (∑ d ∈ S, |E d (a d) -
      (∑ b ∈ finiteReducedResidues d, E d b) / (Nat.totient d : ℝ)|) ≤
      2 * B := by
  obtain ⟨b, hb⟩ := exists_reducedResidue_abs_max_selector E
  have hB := hE b (fun d hd => (hb d (hS d hd)).1)
  calc
    (∑ d ∈ S, |E d (a d) -
        (∑ c ∈ finiteReducedResidues d, E d c) / (Nat.totient d : ℝ)|) ≤
        ∑ d ∈ S, 2 * |E d (b d)| := by
      apply Finset.sum_le_sum
      intro d hd
      exact abs_reducedResidue_recentered_le_two_mul
        (E d) |E d (b d)| (a d) d (hS d hd) (ha d hd) (hb d (hS d hd)).2
    _ = 2 * (∑ d ∈ S, |E d (b d)|) := by rw [Finset.mul_sum]
    _ ≤ 2 * B := mul_le_mul_of_nonneg_left hB (by norm_num)

/-- Literal finite-source specialization, allowing signed weights and a
modulus-dependent, residue-independent main term. The selected target
residue need only be primitive; reduction modulo `d` is proved harmless. -/
theorem sum_abs_finitePrimitiveDiscrepancy_le_two_mul_of_uniform_selector
    (S T : Finset ℕ) (w : ℕ → ℝ) (M : ℕ → ℝ) (B : ℝ)
    (hS : ∀ d ∈ S, 0 < d)
    (hE : ∀ b : ℕ → ℕ, (∀ d ∈ S, b d ∈ finiteReducedResidues d) →
      (∑ d ∈ S, |finiteCongruenceMass T w (b d) d - M d|) ≤ B)
    (a : ℕ → ℕ) (ha : ∀ d ∈ S, Nat.Coprime (a d) d) :
    (∑ d ∈ S, |finitePrimitiveDiscrepancy T w (a d) d|) ≤ 2 * B := by
  have hmod : ∀ d ∈ S, a d % d ∈ finiteReducedResidues d := by
    intro d hd
    exact (mod_mem_finiteReducedResidues_iff (a d) d (hS d hd)).mpr (ha d hd)
  calc
    (∑ d ∈ S, |finitePrimitiveDiscrepancy T w (a d) d|) =
        ∑ d ∈ S, |finiteCommonMainError T w (M d) (a d % d) d -
          (∑ b ∈ finiteReducedResidues d, finiteCommonMainError T w (M d) b d) /
            (Nat.totient d : ℝ)| := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [finiteCommonMainError_sub_average T w (M d) (a d % d) d (hS d hd),
        finitePrimitiveDiscrepancy_residue_mod]
    _ ≤ 2 * B :=
      sum_abs_reducedResidue_recentered_le_two_mul_of_uniform_selector
        S (fun d b => finiteCommonMainError T w (M d) b d) B hS hE
        (fun d => a d % d) hmod

set_option maxHeartbeats 800000 in
/-- The actual ordered-prime prefix discrepancy satisfies the loss-free
selector transfer. The sole estimate is the explicit hypothesis on the
literal prefix AP count, uniformly over canonical primitive selectors. -/
theorem sum_abs_primeRectanglePrefixDiscrepancy_le_two_mul_of_uniform_selector
    (S : Finset ℕ) (L U V : ℕ) (M : ℕ → ℝ) (B : ℝ)
    (hS : ∀ d ∈ S, 0 < d)
    (hE : ∀ b : ℕ → ℕ, (∀ d ∈ S, b d < d ∧ Nat.Coprime (b d) d) →
      (∑ d ∈ S, |primeRectanglePrefixAPCount L U V (b d) d - M d|) ≤ B)
    (a : ℕ → ℕ) (ha : ∀ d ∈ S, Nat.Coprime (a d) d) :
    (∑ d ∈ S, |primeRectanglePrefixDiscrepancy L U V (a d) d|) ≤ 2 * B := by
  let T : Finset ℕ :=
    (primeRectanglePrefixPairs L U V).image (fun p => p.1 * p.2)
  let w : ℕ → ℝ := pairProductWeight (primeRectanglePrefixPairs L U V)
  have hAP (b d : ℕ) : finiteCongruenceMass T w b d =
      primeRectanglePrefixAPCount L U V b d :=
    finiteCongruenceMass_primeRectanglePrefixPairs L U V b d
  have hdisc (b d : ℕ) : finitePrimitiveDiscrepancy T w b d =
      primeRectanglePrefixDiscrepancy L U V b d :=
    finitePrimitiveDiscrepancy_primeRectanglePrefixPairs L U V b d
  have hraw : ∀ b : ℕ → ℕ, (∀ d ∈ S, b d ∈ finiteReducedResidues d) →
      (∑ d ∈ S, |finiteCongruenceMass T w (b d) d - M d|) ≤ B := by
    intro b hb
    calc
      (∑ d ∈ S, |finiteCongruenceMass T w (b d) d - M d|) =
          ∑ d ∈ S, |primeRectanglePrefixAPCount L U V (b d) d - M d| := by
        apply Finset.sum_congr rfl
        intro d _
        rw [hAP (b d) d]
      _ ≤ B := hE b
        (fun d hd => (mem_finiteReducedResidues (b d) d).mp (hb d hd))
  have hbound : (∑ d ∈ S, |finitePrimitiveDiscrepancy T w (a d) d|) ≤ 2 * B :=
    sum_abs_finitePrimitiveDiscrepancy_le_two_mul_of_uniform_selector
      S T w M B hS hraw a ha
  calc
    (∑ d ∈ S, |primeRectanglePrefixDiscrepancy L U V (a d) d|) =
        ∑ d ∈ S, |finitePrimitiveDiscrepancy T w (a d) d| := by
      apply Finset.sum_congr rfl
      intro d _
      rw [hdisc (a d) d]
    _ ≤ 2 * B := hbound

/-- The complete inclusive positive-modulus interval is allowed, including
`D = 0`. The budget is still `2 * B`, independent of its length. -/
theorem sum_abs_primeRectanglePrefixDiscrepancy_Icc_le_two_mul_of_uniform_selector
    (D L U V : ℕ) (M : ℕ → ℝ) (B : ℝ)
    (hE : ∀ b : ℕ → ℕ,
      (∀ d ∈ Finset.Icc 1 D, b d < d ∧ Nat.Coprime (b d) d) →
      (∑ d ∈ Finset.Icc 1 D, |primeRectanglePrefixAPCount L U V (b d) d - M d|) ≤ B)
    (a : ℕ → ℕ) (ha : ∀ d ∈ Finset.Icc 1 D, Nat.Coprime (a d) d) :
    (∑ d ∈ Finset.Icc 1 D, |primeRectanglePrefixDiscrepancy L U V (a d) d|) ≤
      2 * B := by
  apply sum_abs_primeRectanglePrefixDiscrepancy_le_two_mul_of_uniform_selector
    (Finset.Icc 1 D) L U V M B ?_ hE a ha
  intro d hd
  exact (Finset.mem_Icc.mp hd).1

/-- The empty positive-modulus interval contributes exactly zero. -/
@[simp] theorem sum_abs_primeRectanglePrefixDiscrepancy_Icc_zero
    (L U V : ℕ) (a : ℕ → ℕ) :
    (∑ d ∈ Finset.Icc 1 0, |primeRectanglePrefixDiscrepancy L U V (a d) d|) = 0 := by
  simp

/-- Modulus one contributes exactly zero for every selected residue. -/
@[simp] theorem primeRectanglePrefixDiscrepancy_modulus_one (L U V a : ℕ) :
    primeRectanglePrefixDiscrepancy L U V a 1 = 0 := by
  rw [← finitePrimitiveDiscrepancy_primeRectanglePrefixPairs]
  exact finitePrimitiveDiscrepancy_modulus_one _ _ _

end

end ImbalancedChen
