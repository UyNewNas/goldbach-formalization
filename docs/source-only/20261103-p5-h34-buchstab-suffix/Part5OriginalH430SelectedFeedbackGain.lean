import ImbalancedChen.Part5OriginalH430OwnedBuchstabLower
import ImbalancedChen.Part5OriginalH430SelectedBuchstabSupply

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The NEW selected closed-table value is now paid by the OLD literal
strict-prime profile plus epsilon times the SAME parent normalizer.
The integer suffix-to-real-profile inequality is proved, not supplied
as an interface field. This is a feedback-mass result, NOT the complete
original count induction or the eventual U3+U4 bound.
-/
namespace ImbalancedChen.Part5OriginalH430SelectedFeedbackGain

noncomputable section
open Set
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P2EnhancedLowerPrimeChildCarriers
open P2OriginalChildPhysicalNormalization
open P2OriginalPositiveSameQMassLift
open P5OriginalFeedbackTableKernels
open Part5OriginalH430ClosedOwner
open Part5OriginalH430SameQHistoryCells Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430ArithmeticParentMass
open Part5OriginalH430ImmutableBankProfiles
open Part5OriginalH430CutoffCoherence
open Part5OriginalH430SelectedBuchstabSupply
open Part5OriginalH430OwnedBuchstabLower

/-- The actual g+1 value at the closed owner, not a new ideal integral. -/
def selectedGain (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) : ℝ :=
  ∑ h ∈ selectedFamily N n mesh tau c g, sigma h *
    (thetaAtom N (cellQ N n c) (parentProduct (labelWord h)) *
      tableFunction (!(labelNode n tau h).upper)
        (iterate ((g h).val+1) (labelNode n tau h).upper)
        (labelNode n tau h).physical.argument)

/-- The original child-prime sum already supplied by the preceding
packet. The old table and the original strict carrier remain literal. -/
def selectedPrimeGain (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) : ℝ :=
  ∑ h ∈ selectedFamily N n mesh tau c g, sigma h * primeProfile tau c g h

theorem selected_theta_nonneg {N n mesh : ℕ} {tau : ℝ} {c : RootCode n}
    {g : Label N mesh → Fin 430} {h : Label N mesh}
    (hN : 4 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hh : h ∈ selectedFamily N n mesh tau c g) :
    0 ≤ thetaAtom N (cellQ N n c) (parentProduct (labelWord h)) := by
  have hw := (cell_history_support (by omega : 1 < N) htau htauhi hn
    (selectedFamily_subset hh)).1
  have hd : (0:ℝ) < (parentProduct (labelWord h):ℝ) := Nat.cast_pos.mpr hw.2.1
  have hR : 1 < cellQ N n c/(parentProduct (labelWord h):ℝ) := by
    apply (lt_div_iff₀ hd).mpr
    simpa only [one_mul] using hw.2.2.1
  exact P2OriginalPositiveSameQMassLift.thetaAtom_nonneg hN hw.2.1 hR

theorem selectedGain_nonneg {N n mesh : ℕ} {tau : ℝ} (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ)
    (hN : 4 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hsigma : ∀ h ∈ selectedFamily N n mesh tau c g, 0 ≤ sigma h) :
    0 ≤ selectedGain N n mesh tau c g sigma := by
  unfold selectedGain
  apply Finset.sum_nonneg
  intro h hh
  exact mul_nonneg (hsigma h hh)
    (mul_nonneg (selected_theta_nonneg hN htau htauhi hn hh)
      (iterate_lookup_nonneg _ _ _))

/-- Finite, oriented feedback comparison. Selection is restricted only
inside the already uniform positive-row theorem; no sharp count mother
inequality is filtered after it was proved. -/
theorem selectedGain_le_prime_add_error {N n mesh : ℕ} {tau : ℝ} (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ)
    (hN : 4 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hsigma : ∀ h ∈ selectedFamily N n mesh tau c g, 0 ≤ sigma h) :
    selectedGain N n mesh tau c g sigma ≤
      selectedPrimeGain N n mesh tau c g sigma + selectedProfileError N n mesh tau c g sigma := by
  calc
    _ ≤ ∑ h ∈ selectedFamily N n mesh tau c g, sigma h *
        (primeProfile tau c g h + |primeProfile tau c g h-originalMain tau c g h|) := by
      apply Finset.sum_le_sum
      intro h hh
      obtain ⟨b, hb, hc⟩ := (mem_selectedFamily.mp hh).2.2
      have hs := selected_lookup_le_original hb hc
      have ht := mul_le_mul_of_nonneg_left hs
        (selected_theta_nonneg hN htau htauhi hn hh)
      have hab := neg_abs_le (primeProfile tau c g h-originalMain tau c g h)
      have hp : originalMain tau c g h ≤
          primeProfile tau c g h + |primeProfile tau c g h-originalMain tau c g h| := by
        linarith
      exact mul_le_mul_of_nonneg_left (ht.trans hp) (hsigma h hh)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, selectedPrimeGain, selectedProfileError]

/-- No division by Theta, including on a zero-mass selected family. -/
theorem selectedGain_eq_zero_of_theta_zero {N n mesh : ℕ} {tau : ℝ} (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ)
    (hN : 4 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hsigma : ∀ h ∈ selectedFamily N n mesh tau c g, 0 ≤ sigma h)
    (hzero : selectedTheta N n mesh tau c g sigma = 0) :
    selectedGain N n mesh tau c g sigma = 0 := by
  have hpos (h : Label N mesh) (hh : h ∈ selectedFamily N n mesh tau c g) :
      0 ≤ sigma h*thetaAtom N (cellQ N n c) (parentProduct (labelWord h)) :=
    mul_nonneg (hsigma h hh) (selected_theta_nonneg hN htau htauhi hn hh)
  change (∑ h ∈ selectedFamily N n mesh tau c g,
    sigma h*thetaAtom N (cellQ N n c) (parentProduct (labelWord h))) = 0 at hzero
  unfold selectedGain
  apply Finset.sum_eq_zero
  intro h hh
  have hle := Finset.single_le_sum hpos hh
  rw [hzero] at hle
  have hz := le_antisymm hle (hpos h hh)
  rw [← mul_assoc, hz, zero_mul]

/-- One threshold before N, mesh, common-Q cell, selected generations
and nonnegative marks. These marks/generations are not yet identified
with all original count histories. No h34 conclusion is asserted. -/
theorem uniform_selected_feedback_gain {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ c : RootCode n, ∀ g : Label N mesh → Fin 430,
      ∀ sigma : Label N mesh → ℝ,
      (∀ h ∈ selectedFamily N n mesh tau c g, 0 ≤ sigma h) →
      0 ≤ selectedGain N n mesh tau c g sigma ∧
      selectedGain N n mesh tau c g sigma ≤
        selectedPrimeGain N n mesh tau c g sigma + epsilon*selectedTheta N n mesh tau c g sigma ∧
      (selectedTheta N n mesh tau c g sigma = 0 → selectedGain N n mesh tau c g sigma = 0) := by
  obtain ⟨T, hT⟩ := uniform_selected_buchstab he
  refine ⟨max 4 T, ?_⟩
  intro N hN n mesh tau htau htauhi hn c g sigma hsigma
  have hN4 : 4 ≤ N := by omega
  have hr := hT N (by omega) n mesh tau htau htauhi hn c g sigma hsigma
  refine ⟨selectedGain_nonneg c g sigma hN4 htau htauhi hn hsigma, ?_, ?_⟩
  · exact (selectedGain_le_prime_add_error c g sigma hN4 htau htauhi hn hsigma).trans
      (add_le_add_left hr.2.1 _)
  · exact selectedGain_eq_zero_of_theta_zero c g sigma hN4 htau htauhi hn hsigma

/-- Distinct root cells retain distinct Q values and are aggregated
only AFTER their same-Q estimates, with one threshold for all cells. -/
theorem uniform_selected_outer_feedback_gain {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ g : Label N mesh → Fin 430, ∀ sigma : Label N mesh → ℝ,
      (∀ h ∈ catalog N n mesh tau,
        SelectedBuchstab (g h) (labelNode n tau h).upper
          (labelNode n tau h).physical.argument → 0 ≤ sigma h) →
      (∑ c : RootCode n, selectedGain N n mesh tau c g sigma) ≤
        (∑ c : RootCode n, selectedPrimeGain N n mesh tau c g sigma) +
          epsilon*(∑ c : RootCode n, selectedTheta N n mesh tau c g sigma) := by
  obtain ⟨T, hT⟩ := uniform_selected_feedback_gain he
  refine ⟨T, ?_⟩
  intro N hN n mesh tau htau htauhi hn g sigma hsigma
  have hs (c : RootCode n) (h : Label N mesh)
      (hh : h ∈ selectedFamily N n mesh tau c g) : 0 ≤ sigma h := by
    have hm := mem_selectedFamily.mp hh
    exact hsigma h (mem_catalog.mpr hm.1) hm.2.2
  calc
    _ ≤ ∑ c : RootCode n,
        (selectedPrimeGain N n mesh tau c g sigma + epsilon*selectedTheta N n mesh tau c g sigma) :=
      Finset.sum_le_sum (fun c _ =>
        (hT N hN n mesh tau htau htauhi hn c g sigma (hs c)).2.1)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]

end
end ImbalancedChen.Part5OriginalH430SelectedFeedbackGain
