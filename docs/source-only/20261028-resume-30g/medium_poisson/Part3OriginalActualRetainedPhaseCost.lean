import ImbalancedChen.Part3OriginalActualPoissonTightH
import Mathlib.Tactic

/-!
Source only; uncompiled; zero formal credit.
The actual fixed-block Q/q0 and D/d licences quantify the Poisson and
retained phase amplitudes. This bounds the real common jet scale of
the existing complete-W proof, without treating that algebraic charge
as an already proved finite weight5 variation or spectral estimate.
-/

noncomputable section
open Classical Finset Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumPhysicalFiveJets
open ImbalancedChen.Part3.OriginalMediumSmoothWeightInput
open ImbalancedChen.Part3.OriginalMediumCompleteWDegreeBound
open ImbalancedChen.Part3.OriginalActualPoissonTightH20261028
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028

namespace ImbalancedChen.Part3.OriginalActualRetainedPhaseCost20261028

theorem actual_block_scale_pos (B : FixedBlock) : 0 < B.x := by
  unfold FixedBlock.x MediumAtom.scale
  exact mul_pos B.U_pos B.V_pos

theorem actual_Q_ratio_le_two (B : FixedBlock) : B.atom.Q1 / B.q0 ≤ 2 := by
  apply (div_le_iff₀ B.q0_pos).mpr
  linarith [B.q0_from_Q_lo]

theorem actual_D_ratio_le_one (B : FixedBlock) : B.D / (B.d : ℝ) ≤ 1 := by
  have hd : (0 : ℝ) < B.d := by exact_mod_cast B.d_pos
  apply (div_le_iff₀ hd).mpr
  simpa using B.d_window_lo

theorem actual_poissonAmplitude_nonneg (B : FixedBlock) (hx : 1 ≤ B.x) :
    0 ≤ poissonAmplitude B := by
  have hlog := Real.log_nonneg hx
  have hd : (0 : ℝ) < B.d := by exact_mod_cast B.d_pos
  have hQ := B.Q_pos
  have hq0 := B.q0_pos
  have hD := B.D_pos
  unfold poissonAmplitude
  positivity

theorem actual_poissonAmplitude_le (B : FixedBlock) (hx : 1 ≤ B.x) :
    poissonAmplitude B ≤ 2 * Real.log B.x ^ 5 := by
  have hQ : 0 ≤ B.atom.Q1 / B.q0 := (div_pos B.Q_pos B.q0_pos).le
  have hlog := pow_nonneg (Real.log_nonneg hx) 5
  have hratio : (B.atom.Q1 / B.q0) * (B.D / (B.d : ℝ)) ≤ 2 := by
    calc
      _ ≤ (B.atom.Q1 / B.q0) * 1 :=
        mul_le_mul_of_nonneg_left (actual_D_ratio_le_one B) hQ
      _ ≤ 2 := by simpa using actual_Q_ratio_le_two B
  exact mul_le_mul_of_nonneg_right hratio hlog

theorem actual_phaseAmplitude_abs (B : FixedBlock) (hx : 1 ≤ B.x) :
    |phaseAmplitude B| =
      (2 * Real.pi * |(B.atom.residue : ℝ)| / B.x) * poissonAmplitude B := by
  have hform : phaseAmplitude B =
      (2 * Real.pi * (B.atom.residue : ℝ) / B.x) * poissonAmplitude B := by
    unfold phaseAmplitude poissonAmplitude
    ring
  rw [hform]
  simp only [abs_mul, abs_div, abs_ofNat, abs_of_pos Real.pi_pos,
    abs_of_pos (actual_block_scale_pos B),
    abs_of_nonneg (actual_poissonAmplitude_nonneg B hx)]

theorem actual_phaseAmplitude_abs_le (B : FixedBlock) (hx : 1 ≤ B.x) :
    |phaseAmplitude B| ≤
      4 * Real.pi * (|(B.atom.residue : ℝ)| / B.x) * Real.log B.x ^ 5 := by
  rw [actual_phaseAmplitude_abs B hx]
  have hxp := actual_block_scale_pos B
  have hc : 0 ≤ 2 * Real.pi * |(B.atom.residue : ℝ)| / B.x := by
    positivity
  calc
    _ ≤ (2 * Real.pi * |(B.atom.residue : ℝ)| / B.x) *
        (2 * Real.log B.x ^ 5) :=
      mul_le_mul_of_nonneg_left (actual_poissonAmplitude_le B hx) hc
    _ = _ := by ring

theorem admissible_residue_ratio_le {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) :
    |(atom.residue : ℝ)| / atom.scale ≤ atom.scale ^ κ := by
  have hx : 0 < atom.scale := lt_of_lt_of_le zero_lt_one (admissible_scale_gt_one hA).le
  have hc : (atom.residue.natAbs : ℝ) = |(atom.residue : ℝ)| := by
    exact_mod_cast Int.natCast_natAbs atom.residue
  have ha : |(atom.residue : ℝ)| ≤ atom.scale ^ (1 + κ) := by
    rw [← hc]
    exact hA.2.2.2.2.2.2.2.1
  have hp : atom.scale ^ (1 + κ) = atom.scale * atom.scale ^ κ := by
    rw [Real.rpow_add hx, Real.rpow_one]
  apply (div_le_iff₀ hx).mpr
  simpa only [hp, mul_comm] using ha

/-- Exact commonScale charge for the constructed actual tight block.
The parameter is the source residue range, not a five-Abel conclusion. -/
theorem actual_tight_commonScale_le
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (hκ : 0 ≤ κ) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) :
    let B := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
    commonScale (poissonAmplitude B) (phaseAmplitude B) ≤
      (52 * (3 + 4 * Real.pi)) * atom.scale ^ κ * Real.log atom.scale ^ 5 := by
  dsimp only
  let B := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
  have hx : 1 < B.x := admissible_scale_gt_one hA
  have hlog1 : 1 ≤ Real.log B.x := by
    have hexp : Real.exp 1 < Real.exp (Real.exp 1) :=
      Real.exp_lt_exp.mpr (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1))
    have hl : 1 < Real.log B.x :=
      (Real.lt_log_iff_exp_lt (actual_block_scale_pos B)).mpr
        (hexp.trans hA.2.2.2.2.2.1)
    exact hl.le
  have hp : 1 ≤ B.x ^ κ := Real.one_le_rpow hx.le hκ
  have hlog5 : 1 ≤ Real.log B.x ^ 5 := one_le_pow₀ hlog1
  have hL := actual_poissonAmplitude_le B hx.le
  have hAamp := actual_phaseAmplitude_abs_le B hx.le
  have hratio : |(B.atom.residue : ℝ)| / B.x ≤ B.x ^ κ :=
    admissible_residue_ratio_le hA
  have hphase : |phaseAmplitude B| ≤
      4 * Real.pi * (B.x ^ κ * Real.log B.x ^ 5) := by
    apply hAamp.trans
    have hlog0 : 0 ≤ Real.log B.x := zero_le_one.trans hlog1
    have hc : 0 ≤ 4 * Real.pi * Real.log B.x ^ 5 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hratio hc]
  have hLscaled : poissonAmplitude B ≤ 2 * (B.x ^ κ * Real.log B.x ^ 5) := by
    nlinarith [mul_le_mul_of_nonneg_right hp (pow_nonneg hlog1.le 5)]
  have hbase : 1 ≤ B.x ^ κ * Real.log B.x ^ 5 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hlog5)]
  change commonScale (poissonAmplitude B) (phaseAmplitude B) ≤
    (52 * (3 + 4 * Real.pi)) * B.x ^ κ * Real.log B.x ^ 5
  unfold commonScale
  rw [abs_of_nonneg (actual_poissonAmplitude_nonneg B hx.le)]
  nlinarith

/-- The original fifth-degree charge is paid once in this amplitude
envelope. Its use as a weight5 variation bound is a separate obligation. -/
theorem actual_tight_commonScale_fifth_le
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (hκ : 0 ≤ κ) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) :
    let B := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
    commonScale (poissonAmplitude B) (phaseAmplitude B) ^ 5 ≤
      (52 * (3 + 4 * Real.pi)) ^ 5 * atom.scale ^ (5 * κ) *
        Real.log atom.scale ^ 25 := by
  dsimp only
  have hb := actual_tight_commonScale_le atom z y k hA hκ Csep j small hd negative
  dsimp only at hb
  have hx : 0 < atom.scale := lt_of_lt_of_le zero_lt_one (admissible_scale_gt_one hA).le
  have hp : (atom.scale ^ κ) ^ 5 = atom.scale ^ (5 * κ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    ring
  calc
    _ ≤ ((52 * (3 + 4 * Real.pi)) * atom.scale ^ κ *
        Real.log atom.scale ^ 5) ^ 5 := by
      apply pow_le_pow_left₀
      · unfold commonScale
        positivity
      · exact hb
    _ = _ := by simp only [mul_pow, hp, ← pow_mul]; norm_num

end ImbalancedChen.Part3.OriginalActualRetainedPhaseCost20261028
