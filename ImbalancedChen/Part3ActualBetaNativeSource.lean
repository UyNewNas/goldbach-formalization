import ImbalancedChen.Part3ActualCompletedPairSharpL2
import ImbalancedChen.Part3ActualCompletedSquarePushforward
import ImbalancedChen.Part3ActualCompletedZeroDifferencePayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26, phase 9.
Exact connection of the new fixed-level beta_z to the OWNED original
joint beta. Physical support and positive level are derived from that
native source; no new factor-pair count is made. The y=0/nonzero split is
coefficientwise exact. The existing zeroPiece payment remains the native
zero contribution: nonzero y may also alias residue zero, so no orthogonal
residue-energy split is claimed. Full spectral 7/32 remains OPEN.
-/

namespace ImbalancedChen.Part3.ActualBetaNativeSource20261026b
noncomputable section
open Classical Finset ActualReciprocalSquarePoissonSourceOnly
open ActualCompletedPairYFibres20261026b ActualCompletedSquarePushforwardSourceOnly
open scoped BigOperators

theorem actualBetaZ_eq_owned_joint_beta
    (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ) (F : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (z : ℕ) (y : ℤ) :
    actualBetaZ A a T H F lambda omega z y =
      beta (carrier A a T H (originalFWindow F)) lambda omega (z,y) := by
  unfold actualBetaZ originalFibreWeight beta fiber carrier
  simp only [Finset.sum_filter,originalFuvCarrier,rawCarrier]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hf : s.1 ≠ 0 <;> by_cases hu : fixedUnit A a s.2.1.1 <;>
    by_cases hv : fixedUnit A a s.2.2.1 <;>
    by_cases hz : originalZ s = z <;> by_cases hy : originalY s = y <;>
    simp [output,weight,originalZ,originalY,Prod.mk.injEq,hf,hu,hv,hz,hy]

/-- Genuine native physical bounds, including the closed endpoints. -/
theorem actualBetaZ_nonzero_physical_support
    {A : ℕ} {a : ℤ} {T : Finset ℕ} {H : ℕ} {F S : ℝ}
    {lambda : ℕ → ℂ} {omega : ℤ → ℂ} {z : ℕ} {y : ℤ}
    (hS : 0 < S) (hF : 0 ≤ F) (hT : T ⊆ factorCarrier S)
    (hb : actualBetaZ A a T H F lambda omega z y ≠ 0) :
    0 < z ∧ S^2 ≤ (z : ℝ) ∧ (z : ℝ) ≤ 4*S^2 ∧ |(y : ℝ)| ≤ 4*F*(H : ℝ)*S := by
  rw [actualBetaZ_eq_owned_joint_beta] at hb
  have hout := beta_ne_zero_mem_image hb
  obtain ⟨s,hs,heq⟩ := Finset.mem_image.mp hout
  have hbound := output_support hS hF hT (fun f hf => actual_f_window_bound F hf) hs
  simpa only [heq,Prod.fst,Prod.snd] using hbound

theorem actualBetaZ_level_zero
    {A : ℕ} {a : ℤ} {T : Finset ℕ} {H : ℕ} {F S : ℝ}
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (y : ℤ)
    (hS : 0 < S) (hF : 0 ≤ F) (hT : T ⊆ factorCarrier S) :
    actualBetaZ A a T H F lambda omega 0 y = 0 := by
  by_contra hb
  have hh := (actualBetaZ_nonzero_physical_support hS hF hT hb).1
  omega

/-- Exact native split before any residue reduction. -/
theorem owned_beta_zero_nonzero (U : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (zy : Output) :
    beta U lambda omega zy = beta (zeroSource U) lambda omega zy +
      beta (nonzeroSource U) lambda omega zy := by
  unfold beta fiber zeroSource nonzeroSource
  simp only [Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hy : (output s).2 = 0 <;> simp [hy]

theorem owned_beta_nonzero_formula (U : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (zy : Output) :
    beta (nonzeroSource U) lambda omega zy =
      if zy.2 = 0 then 0 else beta U lambda omega zy := by
  unfold beta fiber nonzeroSource
  simp only [Finset.sum_filter]
  by_cases hy : zy.2 = 0
  · rw [if_pos hy]
    apply Finset.sum_eq_zero
    intro s hs
    by_cases hout : output s = zy
    · have hz : (output s).2 = 0 := (congrArg Prod.snd hout).trans hy
      simp [hout,hz]
    · simp [hout]
  · rw [if_neg hy]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hout : output s = zy
    · have hz : (output s).2 ≠ 0 := by simpa only [hout] using hy
      simp [hout,hz]
    · simp [hout]

end
end ImbalancedChen.Part3.ActualBetaNativeSource20261026b
