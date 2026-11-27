import ImbalancedChen.Part3ActualNonzeroSourceCore
import ImbalancedChen.Part3PrimaryDyadicAssembly

/-! Exact short endpoints and dyadic beta energy for the installed actual source. -/

namespace ImbalancedChen.P3ZActualPrimaryShortEndpoint

noncomputable section

open Classical Finset
open scoped BigOperators

/-- Direct specialization to the installed actual nonzero source. Residue
sign and output-y sign are independent parameters. -/
abbrev actualDyadicBeta (e : ImbalancedChen.Part3.MediumAtom) (D delta g l : ℕ)
    (Z : ℝ) (residueNegative yNegative : Bool) (nu : ℕ) (U : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (y z : ℕ) : ℂ :=
  dyadicBeta
    (ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly.signedResidue residueNegative e.residue)
    (ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.actualNonzeroSource
      e D delta g l Z residueNegative) nu U yNegative lambda omega y z

theorem actual_nonempty_endpoint_bounds (e : ImbalancedChen.Part3.MediumAtom)
    (D delta g l : ℕ) (Z : ℝ) (residueNegative yNegative : Bool)
    (nu n z : ℕ) (U : ℝ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hU : 0 < U)
    (hb : actualDyadicBeta e D delta g l Z residueNegative yNegative nu U lambda omega (nu * n) z ≠ 0) :
    0 < nu ∧ 0 < n ∧ (nu : ℝ) ≤ 2 * U ∧ (1 : ℝ) / 2 ≤ U / (nu : ℝ) := by
  exact nonempty_endpoint_bounds hU hb

theorem actual_short_index_eq_one (e : ImbalancedChen.Part3.MediumAtom)
    (D delta g l : ℕ) (Z : ℝ) (residueNegative yNegative : Bool)
    (nu n z : ℕ) (U : ℝ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hU : 0 < U) (hshort : U / (nu : ℝ) < 1)
    (hb : actualDyadicBeta e D delta g l Z residueNegative yNegative nu U lambda omega (nu * n) z ≠ 0) :
    n = 1 := by
  exact short_nonzero_index_eq_one hU hshort hb

theorem actual_nonzero_coprime (e : ImbalancedChen.Part3.MediumAtom)
    (D delta g l : ℕ) (Z : ℝ) (residueNegative yNegative : Bool)
    (nu n z : ℕ) (U : ℝ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hb : actualDyadicBeta e D delta g l Z residueNegative yNegative nu U lambda omega (nu * n) z ≠ 0) :
    Nat.Coprime n e.residue.natAbs := by
  simpa only [ImbalancedChen.Part3.ActualM2FinitePoissonAdapterSourceOnly.signedResidue_natAbs] using
    dyadicBeta_coprime hb

end

end ImbalancedChen.P3ZActualPrimaryShortEndpoint

namespace ImbalancedChen.P3ZActualPrimaryDyadicAssembly

noncomputable section

open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly

/-- The complete installed actual nonzero-source beta energy, not a
new independent coefficient family or an assumed L2 budget. -/
theorem actual_beta_energy_assembly (e : ImbalancedChen.Part3.MediumAtom)
    (D delta g l : ℕ) (Z : ℝ) (negative : Bool)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (B : Finset Output) :
    let S := ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.actualNonzeroSource
      e D delta g l Z negative
    let rho := ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly.signedResidue negative e.residue
    (∑ zy ∈ B, ‖beta S lambda omega zy‖ ^ 2) =
      ∑ k ∈ keys rho S, ∑ zy ∈ B, ‖beta (block rho S k) lambda omega zy‖ ^ 2 := by
  dsimp only
  have h := finite_beta_energy_assembly
    (ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly.signedResidue negative e.residue)
    (ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.actualNonzeroSource
      e D delta g l Z negative) lambda omega B
  have heq : nonzeroSource
      (ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.actualNonzeroSource
        e D delta g l Z negative) =
      ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.actualNonzeroSource
        e D delta g l Z negative := by
    unfold ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.actualNonzeroSource
    exact nonzeroSource_idempotent _
  rw [heq] at h
  exact h

end

end ImbalancedChen.P3ZActualPrimaryDyadicAssembly
