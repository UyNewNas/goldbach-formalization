import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson
import ImbalancedChen.Part3ActualIntervalGeometricSum
import Batteries.Tactic.OpenPrivate

/-! Opening the physical Kloosterman sum in Drappeau's initial estimate.
Both short sums retain their original, oppositely shifted real phases. -/
namespace ImbalancedChen.Part3.OriginalInverseShortSums20261113
noncomputable section
open Finset AddCircle
open scoped BigOperators
open OriginalSmoothPoissonTail ActualIntervalGeometricSumSourceOnly
open private phase_sum_length_bound from ImbalancedChen.Part3ActualIntervalGeometricSum

def shortSum (S : Finset ℕ) (ω : ℝ) : ℂ := ∑ m ∈ S, phaseAt ω m

def inverseShortMean (k : ℕ+) (S T : Finset ℕ) (ω : ℝ) : ℝ :=
  ∑ u ∈ (range k.val).filter (fun u => Nat.Coprime u k.val),
    ‖shortSum S ((u:ℝ)/(k.val:ℝ)+ω)‖ *
      ‖shortSum T ((inverseResidue k.val u:ℝ)/(k.val:ℝ)-ω)‖

private theorem shift (k : ℕ+) (m n u : ℕ) (ω : ℝ) :
    phaseAt ω m * phaseAt (-ω) n *
      fourier 1 ((((m:ℤ)*(u:ℤ)+(n:ℤ)*inverseResidue k.val u : ℤ) : ℝ) /
        (k.val : ℝ) : UnitAddCircle) =
      phaseAt ((u:ℝ)/(k.val:ℝ)+ω) m *
        phaseAt ((inverseResidue k.val u:ℝ)/(k.val:ℝ)-ω) n := by
  simp only [phaseAt,fourier_coe_apply,div_one]
  push_cast
  simp only [← Complex.exp_add]
  congr 1
  ring

private theorem opened_sum (k : ℕ+) (S T : Finset ℕ) (ω : ℝ) :
    (∑ m ∈ S, ∑ n ∈ T, phaseAt ω m*phaseAt (-ω) n*kloosterman k.val (m:ℤ) (n:ℤ)) =
      ∑ u ∈ (range k.val).filter (fun u => Nat.Coprime u k.val),
        shortSum S ((u:ℝ)/(k.val:ℝ)+ω) *
          shortSum T ((inverseResidue k.val u:ℝ)/(k.val:ℝ)-ω) := by
  classical
  let U := (range k.val).filter (fun u => Nat.Coprime u k.val)
  have hKL (m n : ℕ) : phaseAt ω m*phaseAt (-ω) n*kloosterman k.val (m:ℤ) (n:ℤ) =
      ∑ u ∈ U, phaseAt ((u:ℝ)/(k.val:ℝ)+ω) m *
        phaseAt ((inverseResidue k.val u:ℝ)/(k.val:ℝ)-ω) n := by
    rw [kloosterman,← sum_filter,mul_sum]
    exact sum_congr rfl (fun u _ => shift k m n u ω)
  simp_rw [hKL]
  simp_rw [sum_comm (s := T) (t := U)]
  rw [sum_comm (s := S) (t := U)]
  apply sum_congr rfl
  intro u hu
  simp only [shortSum,sum_mul,mul_sum]

/-- The U1-to-U2 step holds for every modulus, every real twist, and
independent truncations of the two finite index sets. -/
theorem inverse_short_bound (k : ℕ+) (S T : Finset ℕ) (ω : ℝ) :
    ‖∑ m ∈ S, ∑ n ∈ T, phaseAt ω m*phaseAt (-ω) n*kloosterman k.val (m:ℤ) (n:ℤ)‖ ≤
      inverseShortMean k S T ω := by
  rw [opened_sum]
  exact (norm_sum_le _ _).trans_eq (by simp only [inverseShortMean,norm_mul])

/-- The two geometric sums over the actual prefix intervals, including
both resonances. -/
def shortMajorant (lo hi : ℕ) (ω : ℝ) : ℝ :=
  if phaseBase ω = 1 then ((hi-lo : ℕ) : ℝ)
  else min ((hi-lo : ℕ) : ℝ) (2/‖1-phaseBase ω‖)

private theorem short_bound (ω : ℝ) {lo hi : ℕ} (hl : lo ≤ hi) :
    ‖shortSum (Ico lo hi) ω‖ ≤ shortMajorant lo hi ω := by
  by_cases h : phaseBase ω = 1
  · rw [shortMajorant,if_pos h]
    exact phase_sum_length_bound ω hl
  · simpa only [shortSum,shortMajorant,if_neg h] using phase_sum_norm_le_min ω hl h

theorem prefix_bound (k : ℕ+) (ω : ℝ) {a b c d : ℕ} (hab : a≤b) (hcd : c≤d) :
    inverseShortMean k (Ico a b) (Ico c d) ω ≤
      ∑ u ∈ (range k.val).filter (fun u => Nat.Coprime u k.val),
        shortMajorant a b ((u:ℝ)/(k.val:ℝ)+ω) *
          shortMajorant c d ((inverseResidue k.val u:ℝ)/(k.val:ℝ)-ω) := by
  apply sum_le_sum
  intro u hu
  exact mul_le_mul (short_bound _ hab) (short_bound _ hcd) (norm_nonneg _)
    ((norm_nonneg _).trans (short_bound _ hab))

end
end ImbalancedChen.Part3.OriginalInverseShortSums20261113
