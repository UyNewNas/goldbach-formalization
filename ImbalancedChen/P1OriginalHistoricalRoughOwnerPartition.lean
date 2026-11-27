import ImbalancedChen.P1OriginalHistoricalResidualCarrier

/-!
# A rough-only historical owner, fixed before the small attachment

The common-tree first disagreement is selected for each changed rough modulus
before the small factor, its Rosser attachment, the remaining-modulus cutoff,
and the later arithmetic test. All attachments therefore use the same actual
state and ordered residual carrier. This is an exact finite identity; it does
not assert analytic whole-atom factorization or a signed medium estimate.
-/

namespace ImbalancedChen.P1OriginalHistoricalRoughOwnerPartition

noncomputable section
open Classical
open scoped BigOperators
open P1OriginalHistoricalCoefficientDictionary
  (commonRoughSupport roughMaskDelta attachedMobius)
open P1OriginalHistoricalResidualCarrier (fixed_rough_modulus_realized_continuation)
open P1Full87TrueDPolicyDelta (trueDDeltaSupport trueDDeltaRho)
open P1Full87HistoricalMiddleSmoothing (remainingModuli)

variable (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)

def changedRough : Finset ℕ :=
  (commonRoughSupport old fresh N cap w z).filter
    (fun b => roughMaskDelta old fresh N cap w z b ≠ 0)

/-- An actual common-tree state with the original admitting continuation. -/
def Realizes (state : FirstExitDepthState ℕ) (b : ℕ) : Prop :=
  state ∈ p1SignedExitStates
      (p1CommonAdmissionPolicy (oddFirstExitPolicy old) (oddFirstExitPolicy fresh))
      (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z) ∧
    state.positive = false ∧ old state.selectedPrefix ≠ fresh state.selectedPrefix ∧
    roughMaskDelta old fresh N cap w z b =
      (if fresh state.selectedPrefix = true then 1 else -1) ∧
    List.Sublist state.selectedPrefix.reverse (roughPrimeUniverse N cap w z) ∧
    ∃ tail : List ℕ,
      b = state.selectedPrefix.prod * tail.prod ∧
      List.Sublist tail state.remaining ∧
      ((old state.selectedPrefix = true ∧
        FirstExitValidSelection (oddFirstExitPolicy old)
          state.selectedPrefix state.positive tail) ∨
       (fresh state.selectedPrefix = true ∧
        FirstExitValidSelection (oddFirstExitPolicy fresh)
          state.selectedPrefix state.positive tail))

private theorem exists_state (b : ℕ)
    (hb : b ∈ changedRough old fresh N cap w z) :
    ∃ state, Realizes old fresh N cap w z state b := by
  have hn := (Finset.mem_filter.mp hb).2
  by_cases hf : b ∈ fixedRoughSupport fresh N cap w z
  · have ho : b ∉ fixedRoughSupport old N cap w z := by
      intro ho
      exact hn (by simp [roughMaskDelta, hf, ho])
    obtain ⟨state, hs, hodd, hfa, hor, tail, hp, hpre, ht, hv⟩ :=
      fixed_rough_modulus_realized_continuation fresh old N cap b w z hf ho
    have hc : p1CommonAdmissionPolicy (oddFirstExitPolicy fresh) (oddFirstExitPolicy old) =
        p1CommonAdmissionPolicy (oddFirstExitPolicy old) (oddFirstExitPolicy fresh) := by
      funext positive pre
      simp only [p1CommonAdmissionPolicy, Bool.and_comm]
    rw [hc] at hs
    refine ⟨state, hs, hodd, by simp [hfa, hor], ?_, hpre, tail, hp, ht, Or.inr ⟨hfa, hv⟩⟩
    simp [roughMaskDelta, hf, ho, hfa]
  · have ho : b ∈ fixedRoughSupport old N cap w z := by
      by_contra ho
      exact hn (by simp [roughMaskDelta, hf, ho])
    obtain ⟨state, hs, hodd, hoa, hfr, tail, hp, hpre, ht, hv⟩ :=
      fixed_rough_modulus_realized_continuation old fresh N cap b w z ho hf
    refine ⟨state, hs, hodd, by simp [hoa, hfr], ?_, hpre, tail, hp, ht, Or.inl ⟨hoa, hv⟩⟩
    simp [roughMaskDelta, hf, ho, hfr]

/-- This choice has no B, L, small-factor, or arithmetic-test argument. -/
def owner (b : ℕ) : FirstExitDepthState ℕ :=
  if hb : b ∈ changedRough old fresh N cap w z then
    (exists_state old fresh N cap w z b hb).choose
  else {selectedPrefix := [], positive := true, mass := 1, remaining := []}

def owners : Finset (FirstExitDepthState ℕ) :=
  (changedRough old fresh N cap w z).image (owner old fresh N cap w z)

def fibre (state : FirstExitDepthState ℕ) : Finset ℕ :=
  (changedRough old fresh N cap w z).filter
    (fun b => owner old fresh N cap w z b = state)

theorem owner_spec (b : ℕ) (hb : b ∈ changedRough old fresh N cap w z) :
    Realizes old fresh N cap w z (owner old fresh N cap w z b) b := by
  simpa only [owner, dif_pos hb] using
    (exists_state old fresh N cap w z b hb).choose_spec

theorem fibre_realizes (state : FirstExitDepthState ℕ) (b : ℕ)
    (hb : b ∈ fibre old fresh N cap w z state) :
    Realizes old fresh N cap w z state b := by
  obtain ⟨hb, heq⟩ := Finset.mem_filter.mp hb
  simpa only [heq] using owner_spec old fresh N cap w z b hb

theorem fibres_disjoint (s t : FirstExitDepthState ℕ) (hst : s ≠ t) :
    Disjoint (fibre old fresh N cap w z s) (fibre old fresh N cap w z t) := by
  apply Finset.disjoint_left.mpr
  intro b hs ht
  exact hst ((Finset.mem_filter.mp hs).2.symm.trans (Finset.mem_filter.mp ht).2)

/-- The fresh-minus-old mask is one fixed external sign on each fibre.
It does not select the small Rosser member; the original Mobius sign does. -/
theorem fibre_mask (state : FirstExitDepthState ℕ) (b : ℕ)
    (hb : b ∈ fibre old fresh N cap w z state) :
    roughMaskDelta old fresh N cap w z b =
      (if fresh state.selectedPrefix = true then 1 else -1) :=
  (fibre_realizes old fresh N cap w z state b hb).2.2.2.1

/-- Reindex the signed physical sum without changing its small/rough
attachment or the original cutoff on the COMPLETE modulus a*b. -/
theorem remaining_test_eq_rough_owner_sum (B L : ℝ) (G : ℕ → ℂ) :
    (∑ d ∈ remainingModuli B N (trueDDeltaSupport old fresh N cap w z),
      (trueDDeltaRho old fresh N cap w z L d : ℂ) * G d) =
    ∑ state ∈ owners old fresh N cap w z,
      ∑ b ∈ fibre old fresh N cap w z state,
        (roughMaskDelta old fresh N cap w z b : ℂ) *
          ∑ a ∈ actualSmallRosserSupport N cap w,
            (attachedMobius N cap w L a b : ℂ) *
              (if a * b ∈ remainingModuli B N
                (trueDDeltaSupport old fresh N cap w z) then G (a * b) else 0) := by
  rw [P1OriginalHistoricalCoefficientDictionary.remaining_trueDDeltaRho_test_eq_pair_sum]
  rw [Finset.sum_comm]
  let F : ℕ → ℂ := fun b =>
    (roughMaskDelta old fresh N cap w z b : ℂ) *
      ∑ a ∈ actualSmallRosserSupport N cap w,
        (attachedMobius N cap w L a b : ℂ) *
          (if a * b ∈ remainingModuli B N
            (trueDDeltaSupport old fresh N cap w z) then G (a * b) else 0)
  have hgroup : (∑ b ∈ commonRoughSupport old fresh N cap w z,
      ∑ a ∈ actualSmallRosserSupport N cap w,
        (roughMaskDelta old fresh N cap w z b : ℂ) *
          (attachedMobius N cap w L a b : ℂ) *
            (if a * b ∈ remainingModuli B N
              (trueDDeltaSupport old fresh N cap w z) then G (a * b) else 0)) =
      ∑ b ∈ commonRoughSupport old fresh N cap w z, F b := by
    apply Finset.sum_congr rfl
    intro b _
    simp only [F, Finset.mul_sum, mul_assoc]
  rw [hgroup]
  have hfilter : (∑ b ∈ commonRoughSupport old fresh N cap w z, F b) =
      ∑ b ∈ changedRough old fresh N cap w z, F b := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b hb hout
    have hz : roughMaskDelta old fresh N cap w z b = 0 := by
      by_contra hn
      exact hout (Finset.mem_filter.mpr ⟨hb, hn⟩)
    simp [F, hz]
  rw [hfilter]
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun b hb => Finset.mem_image_of_mem (owner old fresh N cap w z) hb) F

/-- Each actual historical state has a fixed signed scalar outside both
the rough fibre and the original small Rosser attachment. -/
theorem remaining_test_eq_fixed_signed_owner_sum (B L : ℝ) (G : ℕ → ℂ) :
    (∑ d ∈ remainingModuli B N (trueDDeltaSupport old fresh N cap w z),
      (trueDDeltaRho old fresh N cap w z L d : ℂ) * G d) =
    ∑ state ∈ owners old fresh N cap w z,
      ((if fresh state.selectedPrefix = true then (1 : ℝ) else -1) : ℂ) *
        ∑ b ∈ fibre old fresh N cap w z state,
          ∑ a ∈ actualSmallRosserSupport N cap w,
            (attachedMobius N cap w L a b : ℂ) *
              (if a * b ∈ remainingModuli B N
                (trueDDeltaSupport old fresh N cap w z) then G (a * b) else 0) := by
  rw [remaining_test_eq_rough_owner_sum]
  apply Finset.sum_congr rfl
  intro state _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [fibre_mask old fresh N cap w z state b hb]
  by_cases hf : fresh state.selectedPrefix = true <;> simp [hf]

end
end ImbalancedChen.P1OriginalHistoricalRoughOwnerPartition
