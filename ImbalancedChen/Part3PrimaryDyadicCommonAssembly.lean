import ImbalancedChen.Part3DistributionTargets
import ImbalancedChen.Part3PrimaryDyadicAssembly

/-! Integration adapter for the already accepted P3.4 source at 97d5de82.
Existing declaration owners are reused; retained theorem statements and proof bodies
are unchanged. Exact transformations are recorded in
`docs/part3-distribution/p31-actual-source-lanes-20261126/SUPPLIER_ADAPTERS.json`. -/


/-! Finite primary/sign/dyadic assembly with the original common completed-variable weight. -/

namespace ImbalancedChen.P3ZActualPrimaryShortEndpoint

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3 (CoprimePacket CommonCompletedVariable)
open ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
open ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)

/-- Literal packet reduction to n=1. The common completed-variable phase
is exactly the same object at every m and is never moved or discarded. -/
theorem short_common_phase_packet (rho : ℤ) (S : Finset Source) (nu z : ℕ)
    (U : ℝ) (negative : Bool) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hz : 0 < z) (hc : Nat.Coprime rho.natAbs z)
    (hU : 0 < U) (hshort : U / (nu : ℝ) < 1)
    (k : D4 → ℤ) (Z : ℝ) (I : CommonCompletedVariable)
    (M N : Finset ℕ) (K : ℕ → ℕ → ℂ) :
    (∑ m ∈ M, ∑ n ∈ N, I.weight m * signedCoefficient negative
      (modePacket (dyadicPacket rho S nu z U negative lambda omega hz hc) k U Z) n * K m n) =
      if 1 ∈ N then ∑ m ∈ M, I.weight m * signedCoefficient negative
        (modePacket (dyadicPacket rho S nu z U negative lambda omega hz hc) k U Z) 1 * K m 1 else 0 := by
  have hs (m : ℕ) := finite_singleton N
    (fun n => I.weight m * signedCoefficient negative
      (modePacket (dyadicPacket rho S nu z U negative lambda omega hz hc) k U Z) n * K m n)
    (fun n hn => by
      rw [short_modeCoefficient_zero rho S nu z U negative lambda omega hz hc hU hshort k Z hn]
      simp)
  simp_rw [hs]
  by_cases h1 : 1 ∈ N <;> simp only [h1, if_true, if_false, sum_const_zero]

end

end ImbalancedChen.P3ZActualPrimaryShortEndpoint

namespace ImbalancedChen.P3ZActualPrimaryDyadicAssembly

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3 (CommonCompletedVariable)
open ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
open ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly
open ImbalancedChen.P3ZActualPrimaryShortEndpoint

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
