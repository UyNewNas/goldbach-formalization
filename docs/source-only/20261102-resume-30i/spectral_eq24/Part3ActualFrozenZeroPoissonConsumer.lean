import ImbalancedChen.Part3ActualZeroPoissonSupport
import ImbalancedChen.Part3OriginalActualFrozenSmoothPackets

/-!
Source only; uncompiled; zero formal credit.

The lambda sequence below is literally the S coefficient in H's ordered
non-Hermitian frozen packet. Both original smooth labels stay independent.
Its physical reciprocal-square m=0 branch now has a proved bound. This
does NOT assert the still-missing positive-Cauchy/colored-source mapping
from the entire frozenUpperPacket to that reciprocal-square family.
-/

namespace ImbalancedChen.Part3.ActualFrozenZeroPoissonConsumer20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalActualThreePairPolarization20261102 OriginalActualPolarizedProductCaller20261102
open OriginalActualFrozenSmoothPackets20261102 OriginalMediumPhysicalE3Block
open OriginalMediumDoubleLambdaColorWindows20261028
open ActualZeroPoissonSupport20261102 ActualCountedSpectralPolynomial20261102
open ActualOriginalSpectralScales20261028 ActualOccupiedCountingScale20261102
open MediumGlobalDyadicOwnership20261028 OriginalSamePsiS1OwnedAtlas
open OriginalLambdaTrimPoissonFamily20261028 ActualMediumVarianceAtomBindingSourceOnly
open LichtmanSignedDifferenceMultiplicity

def frozenSSequence (atom : MediumAtom) (st st' : ℕ × ℕ) (e : Fin 4) : ℕ → ℂ :=
  diagonal (gamma2Slot atom st.1) (gamma2Slot atom st'.1) e

/-- Exact coefficient identity in the independently defined H source.
It neither transposes the kernel nor identifies the reverse cross term. -/
theorem frozenDiagonal_eq_frozenSSequence (atom : MediumAtom) (st st' : ℕ × ℕ)
    (t : Index) (p p' : Factor) (e f g : Fin 4) :
    frozenDiagonal atom st st' t p p' e f g =
      (frozenSSequence atom st st' e p.u*star (frozenSSequence atom st st' e p'.u))*
      (diagonal (gamma3Slot atom st.2) (gamma3Slot atom st'.2) f p.v*
        star (diagonal (gamma3Slot atom st.2) (gamma3Slot atom st'.2) f p'.v))*
      (diagonal (alphaSlot atom) (alphaSlot atom) g t.n1*
        star (diagonal (alphaSlot atom) (alphaSlot atom) g t.n2)) := rfl

theorem frozenSSequence_norm_le_one {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (st st' : ℕ × ℕ) (e : Fin 4) (s : ℕ) :
    ‖frozenSSequence atom st st' e s‖ ≤ 1 := by
  have hgamma := (actual_slots_one_bounded hA).1
  exact diagonal_norm_le_one _ _ e (hgamma st.1) (hgamma st'.1) s

/-- The exact S sequence in the frozen non-Hermitian source is consumed
by the genuine m=0 estimate, then by H's literal counted polynomial. -/
theorem frozen_zero_sq_le_countedPolynomial {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (ha : atom.residue ≠ 0) (z : ℝ) (k : Key) (hk : k ∈ originalNumericKeys atom z)
    (A : ℕ) (st st' : ℕ × ℕ) (e : Fin 4)
    (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ) (nus : Finset ℕ) :
    ‖occupiedZeroSource atom k A (frozenSSequence atom st st' e) omega eps‖^2 ≤
      zeroBranchCost atom k*
        countedPolynomial atom k A (frozenSSequence atom st st' e) omega eps nus :=
  occupiedZeroSource_sq_le_countedPolynomial hA ha z k hk A
    (frozenSSequence atom st st' e) omega eps nus

/-- The original threshold is uniform in both independent smooth labels
and all four polarization parameters. No SW is reapplied. Only omega and
the output alignment phase retain their original one-bounded hypotheses. -/
theorem exists_normalized_frozen_zero_threshold (sigma : ℝ) (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (kappa c0 : ℝ) (atom : MediumAtom),
      0 < c0 → MediumAdmissible B sigma kappa c0 atom → x0 ≤ atom.scale →
      ∀ z : ℝ, ∀ k ∈ originalNumericKeys atom z,
      ∀ (A : ℕ) (st st' : ℕ × ℕ) (e : Fin 4)
        (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ),
      (∀ h ∈ frequencyCarrier (keyRealH atom k), ‖omega h‖ ≤ 1) →
      (∀ zy, ‖eps zy‖ ≤ 1) →
      normalizingFactor atom k*
          ‖occupiedZeroSource atom k A (frozenSSequence atom st st' e) omega eps‖^2 ≤
        zeroBranchCost atom k*sourceDivisorCost atom k*(poissonLoss atom k)^2*D1 atom k := by
  obtain ⟨x0,hx0,hzero⟩ := exists_normalized_occupiedZeroSource_threshold sigma hsigma
  refine ⟨x0,hx0,?_⟩
  intro B kappa c0 atom hc0 hA hx z k hk A st st' e omega eps homega heps
  exact hzero B kappa c0 atom hc0 hA hx z k hk A
    (frozenSSequence atom st st' e) omega eps
    (fun s hs => frozenSSequence_norm_le_one hA st st' e s) homega heps

end
end ImbalancedChen.Part3.ActualFrozenZeroPoissonConsumer20261102
