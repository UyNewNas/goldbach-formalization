import ImbalancedChen.Part3FourierModeIndex
import ImbalancedChen.Part3CoprimePacketCore
import ImbalancedChen.Part3CuspPhaseCore
import Mathlib.Tactic

namespace P3ActualLiteralPacketIntegralSourceOnly

noncomputable section

open ImbalancedChen.Part3 (CoprimePacket)
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (norm_e)
open scoped BigOperators

def signedCoefficient (negative : Bool) (d : CoprimePacket) (n : ℕ) : ℂ :=
  if Nat.Coprime n d.residue then
    d.beta (d.multiplier*n) d.level * cuspPhase negative d.level n
  else 0

theorem signedCoefficient_false_eq_actual (d : CoprimePacket) (n : ℕ) :
    signedCoefficient false d n = d.transformedCoefficient n := by
  by_cases hc : Nat.Coprime n d.residue
  · rw [signedCoefficient, if_pos hc, CoprimePacket.transformedCoefficient, if_pos hc]
    apply congrArg (fun z : ℂ => d.beta (d.multiplier*n) d.level*z)
    dsimp [cuspPhase, P3Period64NativeReconstructionSourceOnly.e]
    push_cast
    congr 1
    ring
  · simp only [signedCoefficient, CoprimePacket.transformedCoefficient, if_neg hc]

theorem signedCoefficient_true_eq_plus (d : CoprimePacket) (n : ℕ) :
    signedCoefficient true d n =
      if Nat.Coprime n d.residue then
        d.beta (d.multiplier*n) d.level * P3Period64NativeReconstructionSourceOnly.e ((n : ℝ)/(d.level : ℝ))
      else 0 := by
  simp [signedCoefficient, cuspPhase]

theorem norm_signedCoefficient (negative : Bool) (d : CoprimePacket) (n : ℕ) :
    ‖signedCoefficient negative d n‖ = ‖d.transformedCoefficient n‖ := by
  rw [← signedCoefficient_false_eq_actual d n]
  by_cases hc : Nat.Coprime n d.residue
  · simp only [signedCoefficient, if_pos hc, norm_mul, cuspPhase, norm_e, mul_one]
  · simp only [signedCoefficient, if_neg hc]

def modePacket (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) : CoprimePacket :=
  { d with
    beta := fun y z =>
      d.beta y z *
        P3Period64NativeReconstructionSourceOnly.e
          ((k 2 : ℝ)/64*((y : ℝ)/U) + (k 3 : ℝ)/64*((z : ℝ)/Z)) }

theorem modePacket_beta_norm (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) (y z : ℕ) :
    ‖(modePacket d k U Z).beta y z‖ = ‖d.beta y z‖ := by
  simp only [modePacket, norm_mul, norm_e, mul_one]

theorem modePacket_beta_finite_l2 (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ)
    (S : Finset (ℕ × ℕ)) :
    (∑ yz ∈ S, ‖(modePacket d k U Z).beta yz.1 yz.2‖^2) =
      ∑ yz ∈ S, ‖d.beta yz.1 yz.2‖^2 := by
  apply Finset.sum_congr rfl
  intro yz _hyz
  rw [modePacket_beta_norm]

theorem signedCoefficient_modePacket
    (negative : Bool) (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) (n : ℕ) :
    signedCoefficient negative (modePacket d k U Z) n =
      signedCoefficient negative d n *
        P3Period64NativeReconstructionSourceOnly.e ((k 2 : ℝ)/64*(((d.multiplier*n : ℕ) : ℝ)/U) +
           (k 3 : ℝ)/64*((d.level : ℝ)/Z)) := by
  dsimp only [signedCoefficient, modePacket]
  by_cases hc : Nat.Coprime n d.residue
  · simp only [if_pos hc]
    ring
  · simp only [if_neg hc, zero_mul]

theorem norm_signedCoefficient_modePacket
    (negative : Bool) (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) (n : ℕ) :
    ‖signedCoefficient negative (modePacket d k U Z) n‖ =
      ‖d.transformedCoefficient n‖ := by
  rw [signedCoefficient_modePacket, norm_mul, norm_e, mul_one, norm_signedCoefficient]

theorem modePacket_finite_fibre_l2
    (negative : Bool) (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) (N : Finset ℕ) :
    (∑ n ∈ N, ‖signedCoefficient negative (modePacket d k U Z) n‖^2) =
      ∑ n ∈ N, ‖d.transformedCoefficient n‖^2 := by
  apply Finset.sum_congr rfl
  intro n _hn
  rw [norm_signedCoefficient_modePacket]

end
end P3ActualLiteralPacketIntegralSourceOnly
