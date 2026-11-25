import ImbalancedChen.Part3PrimaryDyadicAssembly
import ImbalancedChen.Part3ZActualPrimaryShortEndpoint
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# P3 exact finite primary/sign/output-dyadic assembly

Source-written, uncompiled. These keys partition the actual joint output y,
not the existing fKey decomposition of the original frequency f.
The sibling short-endpoint module must be staged on the source path.
-/

namespace ImbalancedChen.P3ZActualPrimaryDyadicAssembly

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3 (CommonCompletedVariable)
open ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
open ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly
open ImbalancedChen.P3ZActualPrimaryShortEndpoint

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

/-- Exact finite common-phase packet assembly on the actual source.
The same I.weight is present in every block, row and completed m. -/
theorem common_phase_source_assembly (rho : ℤ) (S : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (I : CommonCompletedVariable)
    (M : Finset ℕ) (K : ℕ → Output → ℂ) :
    (∑ m ∈ M, ∑ s ∈ nonzeroSource S, I.weight m * weight lambda omega s * K m (output s)) =
      ∑ k ∈ keys rho S, ∑ m ∈ M, ∑ s ∈ block rho S k,
        I.weight m * weight lambda omega s * K m (output s) := by
  have hs (m : ℕ) := finite_source_assembly rho S
    (fun s => I.weight m * weight lambda omega s * K m (output s))
  simp_rw [hs]
  rw [sum_comm]

theorem common_phase_beta_assembly (rho : ℤ) (S : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (I : CommonCompletedVariable)
    (M : Finset ℕ) (B : Finset Output) (K : ℕ → Output → ℂ) :
    (∑ m ∈ M, ∑ zy ∈ B, I.weight m * beta (nonzeroSource S) lambda omega zy * K m zy) =
      ∑ k ∈ keys rho S, ∑ m ∈ M, ∑ zy ∈ B,
        I.weight m * beta (block rho S k) lambda omega zy * K m zy := by
  calc
    _ = ∑ m ∈ M, ∑ zy ∈ B, ∑ k ∈ keys rho S,
        I.weight m * beta (block rho S k) lambda omega zy * K m zy := by
      apply sum_congr rfl
      intro m _
      apply sum_congr rfl
      intro zy _
      rw [finite_beta_assembly rho S lambda omega zy, mul_sum, sum_mul]
    _ = ∑ m ∈ M, ∑ k ∈ keys rho S, ∑ zy ∈ B,
        I.weight m * beta (block rho S k) lambda omega zy * K m zy := by
      apply sum_congr rfl
      intro m _
      exact sum_comm
    _ = _ := by rw [sum_comm]

end

end ImbalancedChen.P3ZActualPrimaryDyadicAssembly
