import ImbalancedChen.Part3PrimaryDyadicShortEndpoint
import ImbalancedChen.Part3FixedRhoPrimarySignedFiniteDecomposition
import ImbalancedChen.Part3ActualLiteralPacketIntegral
import Mathlib.Tactic

/-!
# P3 actual finite beta at the short primary endpoint

Source-written, uncompiled. Dyadic support is obtained from an explicit
filter of the actual Source carrier, never attributed to arbitrary beta.
The original generic PacketData carrier only has a wider normalized box.
-/

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
