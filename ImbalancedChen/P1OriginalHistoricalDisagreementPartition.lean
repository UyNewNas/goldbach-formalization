import ImbalancedChen.P1OriginalHistoricalResidualCarrier

/-!
# Exact finite partition of the actual historical difference

The family is fixed by the original coefficients before an arithmetic test is
chosen. Each nonzero complete modulus is assigned to an actual common-tree
first disagreement supplied by the accepted historical bridge. The original
remaining-modulus filter and coefficient, including the small Rosser attachment,
are retained. No modulus is counted in two fibres.

This is a finite historical partition. It supplies neither a factorisation of
each fibre into analytic whole atoms nor a signed medium estimate.
-/

namespace ImbalancedChen.P1OriginalHistoricalDisagreementPartition

noncomputable section
open Classical
open scoped BigOperators
open P1Full87TrueDPolicyDelta (trueDDeltaSupport trueDDeltaRho)
open P1Full87HistoricalMiddleSmoothing (remainingModuli)
open P1OriginalHistoricalCoefficientDictionary (commonRoughSupport)

variable (B : ℝ) (old fresh : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)

/-- Remove only zero coefficients from the original full-modulus filter. -/
def activeModuli : Finset ℕ :=
  (remainingModuli B N (trueDDeltaSupport old fresh N cap w z)).filter
    (fun d => trueDDeltaRho old fresh N cap w z L d ≠ 0)

private theorem exists_owner (d : ℕ)
    (hd : d ∈ activeModuli B old fresh N cap w z L) :
    ∃ state : FirstExitDepthState ℕ,
      state ∈ p1SignedExitStates
        (p1CommonAdmissionPolicy (oddFirstExitPolicy old) (oddFirstExitPolicy fresh))
        (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z) ∧
      state.positive = false ∧ old state.selectedPrefix ≠ fresh state.selectedPrefix ∧
      List.Sublist state.selectedPrefix.reverse (roughPrimeUniverse N cap w z) ∧
      (∀ p ∈ state.selectedPrefix, p ∈ d.primeFactors) ∧
      ∃ a ∈ actualSmallRosserSupport N cap w,
        ∃ b ∈ commonRoughSupport old fresh N cap w z, a * b = d ∧
          ∃ tail : List ℕ, b = state.selectedPrefix.prod * tail.prod ∧
            List.Sublist tail state.remaining ∧
            ((old state.selectedPrefix = true ∧
              FirstExitValidSelection (oddFirstExitPolicy old)
                state.selectedPrefix state.positive tail) ∨
             (fresh state.selectedPrefix = true ∧
              FirstExitValidSelection (oddFirstExitPolicy fresh)
                state.selectedPrefix state.positive tail)) := by
  have hn := (Finset.mem_filter.mp hd).2
  obtain ⟨a, ha, b, hb, hab, hor⟩ :=
    P1OriginalHistoricalResidualCarrier.nonzero_has_realized_rough_continuation
      old fresh N cap d w z L hn
  have hw : ∃ state : FirstExitDepthState ℕ,
      state ∈ p1SignedExitStates
        (p1CommonAdmissionPolicy (oddFirstExitPolicy old) (oddFirstExitPolicy fresh))
        (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z) ∧
      state.positive = false ∧ old state.selectedPrefix ≠ fresh state.selectedPrefix ∧
      List.Sublist state.selectedPrefix.reverse (roughPrimeUniverse N cap w z) ∧
      ∃ tail : List ℕ, b = state.selectedPrefix.prod * tail.prod ∧
        List.Sublist tail state.remaining ∧
        ((old state.selectedPrefix = true ∧
          FirstExitValidSelection (oddFirstExitPolicy old)
            state.selectedPrefix state.positive tail) ∨
         (fresh state.selectedPrefix = true ∧
          FirstExitValidSelection (oddFirstExitPolicy fresh)
            state.selectedPrefix state.positive tail)) := by
    rcases hor with hf | ho
    · obtain ⟨state, hs, hodd, hf, ho, tail, hp, hpre, ht, hv⟩ := hf
      have hc : p1CommonAdmissionPolicy (oddFirstExitPolicy fresh) (oddFirstExitPolicy old) =
          p1CommonAdmissionPolicy (oddFirstExitPolicy old) (oddFirstExitPolicy fresh) := by
        funext positive pre
        simp only [p1CommonAdmissionPolicy, Bool.and_comm]
      rw [hc] at hs
      exact ⟨state, hs, hodd, by simp [hf, ho], hpre, tail, hp, ht, Or.inr ⟨hf, hv⟩⟩
    · obtain ⟨state, hs, hodd, ho, hf, tail, hp, hpre, ht, hv⟩ := ho
      exact ⟨state, hs, hodd, by simp [hf, ho], hpre, tail, hp, ht, Or.inl ⟨ho, hv⟩⟩
  obtain ⟨state, hs, ho, hc, hpre, tail, hp, ht, hv⟩ := hw
  have hmem : d ∈ trueDDeltaSupport old fresh N cap w z := by
    by_contra hnot
    exact hn (P1Full87TrueDPolicyDelta.trueDDeltaRho_zero_outside
      old fresh N cap w z L hnot)
  have hd0 := (P1Full87TrueDPolicyDelta.trueDDeltaSupport_squarefree
    old fresh N cap w z hmem).ne_zero
  refine ⟨state, hs, ho, hc, hpre, ?_, a, ha, b, hb, hab, tail, hp, ht, hv⟩
  intro p hps
  have hpc : p ∈ roughPrimeUniverse N cap w z :=
    hpre.subset (by simpa only [List.mem_reverse] using hps)
  have hpb : p ∣ b := (List.dvd_prod hps).trans ⟨tail.prod, hp⟩
  have hbd : b ∣ d := ⟨a, by simpa only [Nat.mul_comm] using hab.symm⟩
  exact Nat.mem_primeFactors.mpr ⟨mem_roughPrimeUniverse_prime hpc, hpb.trans hbd, hd0⟩

/-- One realised owner, chosen without reference to the later arithmetic test. -/
def owner (d : ℕ) : FirstExitDepthState ℕ :=
  if hd : d ∈ activeModuli B old fresh N cap w z L then
    (exists_owner B old fresh N cap w z L d hd).choose
  else { selectedPrefix := [], positive := true, mass := 1, remaining := [] }

/-- Finite image of the actual nonzero historical moduli. -/
def owners : Finset (FirstExitDepthState ℕ) :=
  (activeModuli B old fresh N cap w z L).image (owner B old fresh N cap w z L)

/-- A fibre keeps the original complete moduli, not products of free labels. -/
def fibre (state : FirstExitDepthState ℕ) : Finset ℕ :=
  (activeModuli B old fresh N cap w z L).filter
    (fun d => owner B old fresh N cap w z L d = state)

theorem owner_spec (d : ℕ) (hd : d ∈ activeModuli B old fresh N cap w z L) :
    owner B old fresh N cap w z L d ∈ p1SignedExitStates
        (p1CommonAdmissionPolicy (oddFirstExitPolicy old) (oddFirstExitPolicy fresh))
        (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z) ∧
      (owner B old fresh N cap w z L d).positive = false ∧
      old (owner B old fresh N cap w z L d).selectedPrefix ≠
        fresh (owner B old fresh N cap w z L d).selectedPrefix ∧
      List.Sublist (owner B old fresh N cap w z L d).selectedPrefix.reverse
        (roughPrimeUniverse N cap w z) ∧
      (∀ p ∈ (owner B old fresh N cap w z L d).selectedPrefix, p ∈ d.primeFactors) ∧
      ∃ a ∈ actualSmallRosserSupport N cap w,
        ∃ b ∈ commonRoughSupport old fresh N cap w z, a * b = d := by
  have h := (exists_owner B old fresh N cap w z L d hd).choose_spec
  obtain ⟨hs, ho, hc, hp, hf, a, ha, b, hb, hab, _⟩ := h
  simpa only [owner, dif_pos hd] using And.intro hs
    ⟨ho, hc, hp, hf, a, ha, b, hb, hab⟩

/-- The very owner used in the sum partition has a valid residual selection.
This is the same witness, not a separate existential first disagreement. -/
theorem owner_residual_spec (d : ℕ)
    (hd : d ∈ activeModuli B old fresh N cap w z L) :
    ∃ a ∈ actualSmallRosserSupport N cap w,
      ∃ b ∈ commonRoughSupport old fresh N cap w z, a * b = d ∧
        ∃ tail : List ℕ,
          b = (owner B old fresh N cap w z L d).selectedPrefix.prod * tail.prod ∧
          List.Sublist tail (owner B old fresh N cap w z L d).remaining ∧
          ((old (owner B old fresh N cap w z L d).selectedPrefix = true ∧
            FirstExitValidSelection (oddFirstExitPolicy old)
              (owner B old fresh N cap w z L d).selectedPrefix
              (owner B old fresh N cap w z L d).positive tail) ∨
           (fresh (owner B old fresh N cap w z L d).selectedPrefix = true ∧
            FirstExitValidSelection (oddFirstExitPolicy fresh)
              (owner B old fresh N cap w z L d).selectedPrefix
              (owner B old fresh N cap w z L d).positive tail)) := by
  have h := (exists_owner B old fresh N cap w z L d hd).choose_spec
  simpa only [owner, dif_pos hd] using h.2.2.2.2.2

theorem fibre_preserves_original_data (state : FirstExitDepthState ℕ) (d : ℕ)
    (hd : d ∈ fibre B old fresh N cap w z L state) :
    d ∈ remainingModuli B N (trueDDeltaSupport old fresh N cap w z) ∧
      trueDDeltaRho old fresh N cap w z L d ≠ 0 ∧
      (∀ p ∈ state.selectedPrefix, p ∈ d.primeFactors) ∧
      ∃ a ∈ actualSmallRosserSupport N cap w,
        ∃ b ∈ commonRoughSupport old fresh N cap w z, a * b = d := by
  obtain ⟨hd, heq⟩ := Finset.mem_filter.mp hd
  have hactive := Finset.mem_filter.mp hd
  have hs := owner_spec B old fresh N cap w z L d hd
  rw [heq] at hs
  exact ⟨hactive.1, hactive.2, hs.2.2.2.2.1, hs.2.2.2.2.2⟩

theorem fibres_disjoint {s t : FirstExitDepthState ℕ} (hst : s ≠ t) :
    Disjoint (fibre B old fresh N cap w z L s) (fibre B old fresh N cap w z L t) := by
  apply Finset.disjoint_left.mpr
  intro d hs ht
  exact hst ((Finset.mem_filter.mp hs).2.symm.trans (Finset.mem_filter.mp ht).2)

private theorem active_test_eq_remaining_test (G : ℕ → ℂ) :
    (∑ d ∈ activeModuli B old fresh N cap w z L,
      (trueDDeltaRho old fresh N cap w z L d : ℂ) * G d) =
    ∑ d ∈ remainingModuli B N (trueDDeltaSupport old fresh N cap w z),
      (trueDDeltaRho old fresh N cap w z L d : ℂ) * G d := by
  unfold activeModuli
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : trueDDeltaRho old fresh N cap w z L d = 0 <;> simp [hd]

/-- Exact signed arithmetic-test identity, with one fixed partition for all G. -/
theorem remaining_test_eq_owner_fibres (G : ℕ → ℂ) :
    (∑ d ∈ remainingModuli B N (trueDDeltaSupport old fresh N cap w z),
      (trueDDeltaRho old fresh N cap w z L d : ℂ) * G d) =
    ∑ state ∈ owners B old fresh N cap w z L,
      ∑ d ∈ fibre B old fresh N cap w z L state,
        (trueDDeltaRho old fresh N cap w z L d : ℂ) * G d := by
  rw [← active_test_eq_remaining_test B old fresh N cap w z L G]
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun d hd => Finset.mem_image_of_mem (owner B old fresh N cap w z L) hd)
    (fun d => (trueDDeltaRho old fresh N cap w z L d : ℂ) * G d)

/-- Each fibre retains the exact attached small/rough coefficient and tests the
COMPLETE modulus a*b against the original remaining filter. The mask is outside
the Rosser sign choice, including on deleted old-only rough moduli. -/
theorem fibre_test_eq_attached_pair_sum (state : FirstExitDepthState ℕ) (G : ℕ → ℂ) :
    (∑ d ∈ fibre B old fresh N cap w z L state,
      (trueDDeltaRho old fresh N cap w z L d : ℂ) * G d) =
      ∑ a ∈ actualSmallRosserSupport N cap w,
        ∑ b ∈ commonRoughSupport old fresh N cap w z,
          (P1OriginalHistoricalCoefficientDictionary.roughMaskDelta
            old fresh N cap w z b : ℂ) *
          (P1OriginalHistoricalCoefficientDictionary.attachedMobius N cap w L a b : ℂ) *
          (if a * b ∈ remainingModuli B N (trueDDeltaSupport old fresh N cap w z) then
            if owner B old fresh N cap w z L (a * b) = state then G (a * b) else 0
          else 0) := by
  calc
    _ = ∑ d ∈ activeModuli B old fresh N cap w z L,
        (trueDDeltaRho old fresh N cap w z L d : ℂ) *
          (if owner B old fresh N cap w z L d = state then G d else 0) := by
      unfold fibre
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : owner B old fresh N cap w z L d = state <;> simp [hd]
    _ = ∑ d ∈ remainingModuli B N (trueDDeltaSupport old fresh N cap w z),
        (trueDDeltaRho old fresh N cap w z L d : ℂ) *
          (if owner B old fresh N cap w z L d = state then G d else 0) :=
      active_test_eq_remaining_test B old fresh N cap w z L _
    _ = _ := P1OriginalHistoricalCoefficientDictionary.remaining_trueDDeltaRho_test_eq_pair_sum
      B old fresh N cap w z L _

theorem mem_owners_is_actual_first_disagreement (state : FirstExitDepthState ℕ)
    (hs : state ∈ owners B old fresh N cap w z L) :
    state ∈ p1SignedExitStates
        (p1CommonAdmissionPolicy (oddFirstExitPolicy old) (oddFirstExitPolicy fresh))
        (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z) ∧
      state.positive = false ∧ old state.selectedPrefix ≠ fresh state.selectedPrefix ∧
      List.Sublist state.selectedPrefix.reverse (roughPrimeUniverse N cap w z) := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hs
  have h := owner_spec B old fresh N cap w z L d hd
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

end
end ImbalancedChen.P1OriginalHistoricalDisagreementPartition
