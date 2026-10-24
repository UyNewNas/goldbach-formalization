import ImbalancedChen.Part3ActualLiteralPacketIntegral
import ImbalancedChen.Part3ActualModeJointBetaPositiveCount
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / NOT ACCEPTED -- 20261024z P3.
The mask acts on the actual signedCoefficient, whose beta is evaluated at
(d.multiplier*n,d.level). Every complex identity retains its cusp phase.
The mass on the right is the finite beta(nu*n,z) mass, not a spectral
estimate. This file supplies no Parseval, Gram, Kuznetsov or ABL premise.
No Lean/lake/typechecker/runtime/audit/numerical replay was executed.
-/

namespace ImbalancedChen.Part3.ActualCoefficientMaskContraction_20261024z
noncomputable section
open Classical
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (e norm_e)

/-- The finite carrier is an actual Set indicator on the coefficient. -/
def carrierMask (N : Finset ℕ) (f : ℕ → ℂ) : ℕ → ℂ :=
  (N : Set ℕ).indicator f

/-- This gate is exactly the one in the installed signedCoefficient. -/
def coprimeMask (a : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if Nat.Coprime n a then f n else 0

def maskedSignedCoefficient (N : Finset ℕ) (negative : Bool)
    (d : CoprimePacket) : ℕ → ℂ :=
  carrierMask N (signedCoefficient negative d)

theorem carrierMask_apply (N : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) :
    carrierMask N f n = if n ∈ N then f n else 0 := by
  by_cases hn : n ∈ N <;> simp [carrierMask, hn]

theorem carrierMask_idempotent (N : Finset ℕ) (f : ℕ → ℂ) :
    carrierMask N (carrierMask N f) = carrierMask N f := by
  funext n
  by_cases hn : n ∈ N <;> simp [carrierMask_apply, hn]

theorem coprimeMask_idempotent (a : ℕ) (f : ℕ → ℂ) :
    coprimeMask a (coprimeMask a f) = coprimeMask a f := by
  funext n
  by_cases hn : Nat.Coprime n a <;> simp [coprimeMask, hn]

/-- No unit-modulus assumption is needed for this complex equality. -/
theorem carrierMask_modulation_commute (N : Finset ℕ) (f phase : ℕ → ℂ) :
    carrierMask N (fun n => f n * phase n) =
      fun n => carrierMask N f n * phase n := by
  funext n
  by_cases hn : n ∈ N <;> simp [carrierMask_apply, hn]

theorem coprimeMask_modulation_commute (a : ℕ) (f phase : ℕ → ℂ) :
    coprimeMask a (fun n => f n * phase n) =
      fun n => coprimeMask a f n * phase n := by
  funext n
  by_cases hn : Nat.Coprime n a <;> simp [coprimeMask, hn]

theorem carrierMask_coprimeMask_commute (N : Finset ℕ) (a : ℕ) (f : ℕ → ℂ) :
    carrierMask N (coprimeMask a f) = coprimeMask a (carrierMask N f) := by
  funext n
  by_cases hn : n ∈ N <;> by_cases hc : Nat.Coprime n a <;>
    simp [carrierMask_apply, coprimeMask, hn, hc]

theorem signedCoefficient_eq_coprimeMask (negative : Bool) (d : CoprimePacket) :
    signedCoefficient negative d = coprimeMask d.residue
      (fun n => d.beta (d.multiplier*n) d.level * cuspPhase negative d.level n) := by
  funext n
  rfl

theorem coprimeMask_signedCoefficient (negative : Bool) (d : CoprimePacket) :
    coprimeMask d.residue (signedCoefficient negative d) =
      signedCoefficient negative d := by
  funext n
  by_cases hc : Nat.Coprime n d.residue <;>
    simp [coprimeMask, signedCoefficient, hc]

/-- The mask preserves the full amplitude times original complex cusp phase. -/
theorem maskedSignedCoefficient_eq_literal (N : Finset ℕ) (negative : Bool)
    (d : CoprimePacket) (n : ℕ) :
    maskedSignedCoefficient N negative d n =
      if n ∈ N ∧ Nat.Coprime n d.residue then
        d.beta (d.multiplier*n) d.level * cuspPhase negative d.level n else 0 := by
  by_cases hn : n ∈ N <;> by_cases hc : Nat.Coprime n d.residue <;>
    simp [maskedSignedCoefficient, carrierMask_apply, signedCoefficient, hn, hc]

theorem norm_maskedSignedCoefficient (N : Finset ℕ) (negative : Bool)
    (d : CoprimePacket) (n : ℕ) :
    ‖maskedSignedCoefficient N negative d n‖ =
      if n ∈ N ∧ Nat.Coprime n d.residue then
        ‖d.beta (d.multiplier*n) d.level‖ else 0 := by
  rw [maskedSignedCoefficient_eq_literal]
  by_cases h : n ∈ N ∧ Nat.Coprime n d.residue <;>
    simp [h, norm_mul, cuspPhase, norm_e]

/-- Finite weighted L2 is exactly the filtered beta fibre, for arbitrary w. -/
theorem masked_finite_weighted_l2_eq (C N : Finset ℕ) (w : ℕ → ℝ)
    (negative : Bool) (d : CoprimePacket) :
    (∑ n ∈ C, w n * ‖maskedSignedCoefficient N negative d n‖^2) =
      ∑ n ∈ C.filter (fun n => n ∈ N ∧ Nat.Coprime n d.residue),
        w n * ‖d.beta (d.multiplier*n) d.level‖^2 := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases h : n ∈ N ∧ Nat.Coprime n d.residue <;>
    simp [norm_maskedSignedCoefficient, h]

theorem masked_finite_l2_eq (C N : Finset ℕ) (negative : Bool)
    (d : CoprimePacket) :
    (∑ n ∈ C, ‖maskedSignedCoefficient N negative d n‖^2) =
      ∑ n ∈ C.filter (fun n => n ∈ N ∧ Nat.Coprime n d.residue),
        ‖d.beta (d.multiplier*n) d.level‖^2 := by
  simpa only [one_mul] using masked_finite_weighted_l2_eq C N (fun _ => 1) negative d

/-- A [0,1] real energy weight contracts on the original finite carrier. -/
theorem masked_finite_weighted_l2_le (C N : Finset ℕ) (w : ℕ → ℝ)
    (hw0 : ∀ n ∈ C, 0 ≤ w n) (hw1 : ∀ n ∈ C, w n ≤ 1)
    (negative : Bool) (d : CoprimePacket) :
    (∑ n ∈ C, w n * ‖maskedSignedCoefficient N negative d n‖^2) ≤
      ∑ n ∈ C, ‖signedCoefficient negative d n‖^2 := by
  apply Finset.sum_le_sum
  intro n hn
  by_cases hm : n ∈ N
  · simp only [maskedSignedCoefficient, carrierMask_apply, if_pos hm]
    exact (mul_le_mul_of_nonneg_right (hw1 n hn) (sq_nonneg _)).trans_eq (one_mul _)
  · simp only [maskedSignedCoefficient, carrierMask_apply, if_neg hm, norm_zero,
      zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact sq_nonneg _

/-- Scaling the actual complex coefficient by a [0,1] real weight also contracts. -/
theorem soft_masked_finite_l2_le (C N : Finset ℕ) (w : ℕ → ℝ)
    (hw0 : ∀ n ∈ C, 0 ≤ w n) (hw1 : ∀ n ∈ C, w n ≤ 1)
    (negative : Bool) (d : CoprimePacket) :
    (∑ n ∈ C, ‖(w n : ℂ) * maskedSignedCoefficient N negative d n‖^2) ≤
      ∑ n ∈ C, ‖signedCoefficient negative d n‖^2 := by
  apply Finset.sum_le_sum
  intro n hn
  by_cases hm : n ∈ N
  · simp only [maskedSignedCoefficient, carrierMask_apply, if_pos hm, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 n hn)]
    exact pow_le_pow_left₀ (mul_nonneg (hw0 n hn) (norm_nonneg _))
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hw1 n hn)
          (norm_nonneg (signedCoefficient negative d n))) 2
  · simp only [maskedSignedCoefficient, carrierMask_apply, if_neg hm, mul_zero,
      norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _

/-- This is a complex identity, before taking a norm or a finite mass. -/
theorem maskedSignedCoefficient_modePacket (N : Finset ℕ) (negative : Bool)
    (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) (n : ℕ) :
    maskedSignedCoefficient N negative (modePacket d k U Z) n =
      maskedSignedCoefficient N negative d n *
        e ((k 2 : ℝ)/64*(((d.multiplier*n : ℕ) : ℝ)/U) +
          (k 3 : ℝ)/64*((d.level : ℝ)/Z)) := by
  by_cases hn : n ∈ N
  · simp only [maskedSignedCoefficient, carrierMask_apply, if_pos hn]
    exact signedCoefficient_modePacket negative d k U Z n
  · simp [maskedSignedCoefficient, carrierMask_apply, hn]

theorem norm_maskedSignedCoefficient_modePacket (N : Finset ℕ) (negative : Bool)
    (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) (n : ℕ) :
    ‖maskedSignedCoefficient N negative (modePacket d k U Z) n‖ =
      ‖maskedSignedCoefficient N negative d n‖ := by
  rw [maskedSignedCoefficient_modePacket, norm_mul, norm_e, mul_one]

/-- Same-mask exact finite mass preservation for the actual modePacket. -/
theorem modePacket_masked_finite_weighted_l2 (C N : Finset ℕ) (w : ℕ → ℝ)
    (negative : Bool) (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) :
    (∑ n ∈ C, w n * ‖maskedSignedCoefficient N negative (modePacket d k U Z) n‖^2) =
      ∑ n ∈ C, w n * ‖maskedSignedCoefficient N negative d n‖^2 := by
  apply Finset.sum_congr rfl
  intro n _hn
  rw [norm_maskedSignedCoefficient_modePacket]

/-- The actual unmasked fibre L2 theorem is the terminal contraction budget. -/
theorem modePacket_masked_finite_weighted_l2_le (C N : Finset ℕ) (w : ℕ → ℝ)
    (hw0 : ∀ n ∈ C, 0 ≤ w n) (hw1 : ∀ n ∈ C, w n ≤ 1)
    (negative : Bool) (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) :
    (∑ n ∈ C, w n * ‖maskedSignedCoefficient N negative (modePacket d k U Z) n‖^2) ≤
      ∑ n ∈ C, ‖d.transformedCoefficient n‖^2 := by
  calc
    _ ≤ ∑ n ∈ C, ‖signedCoefficient negative (modePacket d k U Z) n‖^2 :=
      masked_finite_weighted_l2_le C N w hw0 hw1 negative (modePacket d k U Z)
    _ = _ := modePacket_finite_fibre_l2 negative d k U Z C

/-- Literal finite B_nu mass, with the packet's original beta and level. -/
def finiteBetaNuMass (d : CoprimePacket) (C : Finset ℕ) : ℝ :=
  ∑ n ∈ C, ‖d.beta (d.multiplier*n) d.level‖^2

theorem masked_finite_l2_le_finiteBetaNuMass (C N : Finset ℕ)
    (negative : Bool) (d : CoprimePacket) :
    (∑ n ∈ C, ‖maskedSignedCoefficient N negative d n‖^2) ≤
      finiteBetaNuMass d C := by
  unfold finiteBetaNuMass
  apply Finset.sum_le_sum
  intro n _hn
  rw [norm_maskedSignedCoefficient]
  by_cases h : n ∈ N ∧ Nat.Coprime n d.residue
  · simp only [if_pos h, le_refl]
  · simp only [if_neg h, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _

theorem modePacket_masked_weighted_l2_le_finiteBetaNuMass
    (C N : Finset ℕ) (w : ℕ → ℝ)
    (hw0 : ∀ n ∈ C, 0 ≤ w n) (hw1 : ∀ n ∈ C, w n ≤ 1)
    (negative : Bool) (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) :
    (∑ n ∈ C, w n * ‖maskedSignedCoefficient N negative (modePacket d k U Z) n‖^2) ≤
      finiteBetaNuMass d C := by
  rw [modePacket_masked_finite_weighted_l2]
  calc
    _ ≤ ∑ n ∈ C, ‖maskedSignedCoefficient N negative d n‖^2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact (mul_le_mul_of_nonneg_right (hw1 n hn) (sq_nonneg _)).trans_eq (one_mul _)
    _ ≤ _ := masked_finite_l2_le_finiteBetaNuMass C N negative d

/-- The exact coprime/finite-mask loss is explicit; no beta norm premise. -/
theorem finiteBetaNuMass_split (C N : Finset ℕ) (negative : Bool)
    (d : CoprimePacket) :
    finiteBetaNuMass d C =
      (∑ n ∈ C, ‖maskedSignedCoefficient N negative d n‖^2) +
      ∑ n ∈ C.filter (fun n => ¬ (n ∈ N ∧ Nat.Coprime n d.residue)),
        ‖d.beta (d.multiplier*n) d.level‖^2 := by
  rw [masked_finite_l2_eq]
  unfold finiteBetaNuMass
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases h : n ∈ N ∧ Nat.Coprime n d.residue <;> simp [h]

end
end ImbalancedChen.Part3.ActualCoefficientMaskContraction_20261024z

namespace ImbalancedChen.Part3.ActualJointBetaMaskMass_20261024z
noncomputable section
open Classical
open scoped BigOperators
open ActualCompletedSquarePushforwardSourceOnly
open ActualModeBetaPositiveCountSourceOnly
open ActualM2FinitePoissonAdapterSourceOnly

/-- A mask on the final complex output coefficient, after its source sum.
No monotonicity under deletion inside a complex source sum is asserted. -/
def jointMaskedNuEnergy (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (nu : ℕ) (M : Finset Output) (w : Output → ℝ) : ℝ :=
  ∑ zy ∈ U.image output, if (nu : ℤ) ∣ zy.2 then
    w zy * ‖(M : Set Output).indicator (beta U lambda omega) zy‖^2 else 0

/-- Exact original joint-output and nu-divisibility filters, with signed y. -/
theorem jointMaskedNuEnergy_eq_filter (U : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (nu : ℕ)
    (M : Finset Output) (w : Output → ℝ) :
    jointMaskedNuEnergy U lambda omega nu M w =
      ∑ zy ∈ (U.image output).filter (fun zy => zy ∈ M ∧ (nu : ℤ) ∣ zy.2),
        w zy * ‖beta U lambda omega zy‖^2 := by
  unfold jointMaskedNuEnergy
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro zy _hzy
  by_cases hm : zy ∈ M <;> by_cases hd : (nu : ℤ) ∣ zy.2 <;>
    simp [hm, hd]

theorem jointMaskedNuEnergy_le_original (U : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (nu : ℕ)
    (M : Finset Output) (w : Output → ℝ)
    (_hw0 : ∀ zy ∈ U.image output, 0 ≤ w zy)
    (hw1 : ∀ zy ∈ U.image output, w zy ≤ 1) :
    jointMaskedNuEnergy U lambda omega nu M w ≤
      ∑ zy ∈ U.image output, if (nu : ℤ) ∣ zy.2 then
        ‖beta U lambda omega zy‖^2 else 0 := by
  unfold jointMaskedNuEnergy
  apply Finset.sum_le_sum
  intro zy hzy
  by_cases hd : (nu : ℤ) ∣ zy.2
  · simp only [if_pos hd]
    by_cases hm : zy ∈ M
    · simp only [Set.indicator_of_mem (show zy ∈ (M : Set Output) from hm)]
      exact (mul_le_mul_of_nonneg_right (hw1 zy hzy) (sq_nonneg _)).trans_eq
        (one_mul _)
    · simp only [Set.indicator_of_notMem (show zy ∉ (M : Set Output) from hm),
        norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
      exact sq_nonneg _
  · simp only [if_neg hd, le_refl]

/-- Direct actual supplier: original signed y, original complex mode beta,
and the existing finite positive count. In particular nu is not replaced
by an absolute-value carrier, and no B_nu estimate is an input. -/
theorem actual_masked_beta_energy_le_positive_count
    {B : ℕ} {sigma kappa c0 : ℝ} {a : MediumAtom}
    (ha : MediumAdmissible B sigma kappa c0 a)
    (D delta g l : ℕ) [NeZero (g*l)] (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (nu : ℕ)
    (M : Finset Output) (w : Output → ℝ)
    (hw0 : ∀ zy ∈ (actualNonzeroSource a D delta g l Z negative).image output,
      0 ≤ w zy)
    (hw1 : ∀ zy ∈ (actualNonzeroSource a D delta g l Z negative).image output,
      w zy ≤ 1) :
    jointMaskedNuEnergy (actualNonzeroSource a D delta g l Z negative)
      (actualModeLambda a D delta g l m negative u k)
      (actualModeOmega a D g l Z tag m negative k) nu M w ≤
        actualCountEnergy a D delta g l Z negative nu := by
  exact (jointMaskedNuEnergy_le_original
    (actualNonzeroSource a D delta g l Z negative)
    (actualModeLambda a D delta g l m negative u k)
    (actualModeOmega a D g l Z tag m negative k) nu M w hw0 hw1).trans
      (actual_beta_energy_le_positive_count ha D delta g l Z tag m negative u k nu)

end
end ImbalancedChen.Part3.ActualJointBetaMaskMass_20261024z
