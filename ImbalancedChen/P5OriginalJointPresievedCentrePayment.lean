import ImbalancedChen.P5OriginalJointPresievedArithmeticSupport
import ImbalancedChen.PowerErrorBudget
import ImbalancedChen.ChenInitialCorrectionBudget

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The centre correction is paid for the ACTUAL constructed ALL16 presieved
coefficient. Unit amplitude and its proved153/256 physical support bound
the complete signed centre sum by N^(153/256)logN/log2. The original
positive normalization then absorbs it uniformly before all selected
banks, common beta pairs and same-E masks. No AP saving is assumed.
-/

namespace ImbalancedChen.P5Z.OriginalJointPresievedCentrePayment

noncomputable section
open Filter Topology
open scoped BigOperators
open Classical
open U1011OriginalSixteenArithmeticProducts
open OriginalCommonBetaActualParameters OriginalJointPresievedCompiler
open OriginalJointCommonBetaModel OriginalJointPresievedArithmeticSupport
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

def activeSupport (n N:ℕ) (eta:ℚ) (w B:ℝ) (E:ℕ×ℕ→Prop) : Finset ℕ :=
  (jointSupport n N eta w E).filter (fun q=>jointPresievedSigma n N eta w B E q≠0)

theorem jointCentre_eq_active (n N:ℕ) (eta:ℚ) (w B:ℝ) (E:ℕ×ℕ→Prop) :
    jointCentre n N eta w B E =
      ∑q∈activeSupport n N eta w B E,jointPresievedSigma n N eta w B E q*
        chenCentrePrimeAPCount N N q := by
  unfold jointCentre activeSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h:jointPresievedSigma n N eta w B E q=0 <;> simp [h]

/-- The bound counts only the actual nonzero physical support. Zero
rows in the full displayed carrier cost nothing. -/
theorem abs_jointCentre_le_power_log {n N:ℕ} {eta:ℚ} {nu epsilon:ℝ}
    (hN:1<N) (heta:0<eta) (hnu:0<nu) (he:0<epsilon)
    (heBudget:epsilon<epsilonBudget n eta nu) (E:ℕ×ℕ→Prop) :
    |jointCentre n N eta ((N:ℝ)^(nu*epsilon^2)) ((N:ℝ)^(nu*epsilon)) E| ≤
      (N:ℝ)^(153/256:ℝ)*(Real.log (N:ℝ)/Real.log 2) := by
  let w:=(N:ℝ)^(nu*epsilon^2)
  let B:=(N:ℝ)^(nu*epsilon)
  have hsub : activeSupport n N eta w B E ⊆ Finset.Icc 1 (Nat.floor ((N:ℝ)^(153/256:ℝ))) := by
    intro q hq
    have hnz := (Finset.mem_filter.mp hq).2
    have ha := actual_joint_arithmetic_support hN heta hnu he heBudget E hnz
    exact Finset.mem_Icc.mpr ⟨ha.1,Nat.le_floor ha.2.2.2.2.le⟩
  have hcard : ((activeSupport n N eta w B E).card:ℝ)≤(N:ℝ)^(153/256:ℝ) := by
    calc
      ((activeSupport n N eta w B E).card:ℝ) ≤
          ((Finset.Icc 1 (Nat.floor ((N:ℝ)^(153/256:ℝ)))).card:ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ = (Nat.floor ((N:ℝ)^(153/256:ℝ)):ℝ) := by simp
      _ ≤ (N:ℝ)^(153/256:ℝ) := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hNpos : 0<N := by omega
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hlog : 0≤Real.log (N:ℝ)/Real.log 2 :=
    div_nonneg (Real.log_pos hn).le (Real.log_pos (by norm_num)).le
  have hpoint (q:ℕ) (hq:q∈activeSupport n N eta w B E) :
      |jointPresievedSigma n N eta w B E q*chenCentrePrimeAPCount N N q|≤
        Real.log (N:ℝ)/Real.log 2 := by
    have hnz := (Finset.mem_filter.mp hq).2
    have ha := actual_joint_arithmetic_support hN heta hnu he heBudget E hnz
    have hc := (chenCentrePrimeAPCount_le_divisorCount N N q).trans
      (chenPrimeDivisorCount_le_log N hNpos)
    calc
      |jointPresievedSigma n N eta w B E q*chenCentrePrimeAPCount N N q| =
          |jointPresievedSigma n N eta w B E q|*chenCentrePrimeAPCount N N q := by
        rw [abs_mul,abs_of_nonneg (chenCentrePrimeAPCount_nonneg N N q)]
      _ ≤ 1*(Real.log (N:ℝ)/Real.log 2) :=
        mul_le_mul ha.2.2.2.1 hc (chenCentrePrimeAPCount_nonneg N N q) (by norm_num)
      _ = Real.log (N:ℝ)/Real.log 2 := one_mul _
  calc
    |jointCentre n N eta w B E| =
        |∑q∈activeSupport n N eta w B E,jointPresievedSigma n N eta w B E q*
          chenCentrePrimeAPCount N N q| := by rw [jointCentre_eq_active]
    _ ≤ ∑q∈activeSupport n N eta w B E,
        |jointPresievedSigma n N eta w B E q*chenCentrePrimeAPCount N N q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑q∈activeSupport n N eta w B E,Real.log (N:ℝ)/Real.log 2 :=
      Finset.sum_le_sum hpoint
    _ = ((activeSupport n N eta w B E).card:ℝ)*(Real.log (N:ℝ)/Real.log 2) := by simp
    _ ≤ (N:ℝ)^(153/256:ℝ)*(Real.log (N:ℝ)/Real.log 2) :=
      mul_le_mul_of_nonneg_right hcard hlog

/-- One threshold precedes every actual finite bank, physical precision,
admissible common beta pair and same-E mask. -/
theorem eventually_jointCentre_paid (reserve:ℝ) (hreserve:0<reserve) :
    ∀ᶠ N:ℕ in atTop,∀n:ℕ,∀eta:ℚ,0<eta → ∀nu epsilon:ℝ,0<nu → 0<epsilon →
      epsilon<epsilonBudget n eta nu → ∀E:ℕ×ℕ→Prop,
        |jointCentre n N eta ((N:ℝ)^(nu*epsilon^2)) ((N:ℝ)^(nu*epsilon)) E|≤
          reserve*singularNormalization N := by
  have hp := eventually_powerLog_le_singularNormalization (1/Real.log 2) (153/256:ℝ) 1
    (by norm_num) reserve hreserve
  filter_upwards [hp,eventually_ge_atTop (2:ℕ)] with N hpower hN
  intro n eta heta nu epsilon hnu he heBudget E
  have hN1 : 1<N := by omega
  exact (abs_jointCentre_le_power_log hN1 heta hnu he heBudget E).trans (by
    simpa only [pow_one,mul_div_assoc,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hpower)

/-- The original complete source now keeps only its SAME actual
presieved density and signed AP error, with the centre genuinely paid. -/
theorem eventually_original_joint_upper_centre_paid (reserve:ℝ) (hreserve:0<reserve) :
    ∀ᶠ N:ℕ in atTop,∀n:ℕ,∀eta:ℚ,0<eta → ∀nu epsilon:ℝ,0<nu → 0<epsilon →
      epsilon<epsilonBudget n eta nu → ∀E:ℕ×ℕ→Prop,
        let w:=(N:ℝ)^(nu*epsilon^2)
        let B:=(N:ℝ)^(nu*epsilon)
        currentChenUpsilon10 N+currentChenUpsilon11 N E≤
          (∑t∈U1011OriginalSixteenJointNearCapCompiler.fallbackTuples n N E,U11Adaptive.weight N t)+
          trueLogarithmicIntegral N*jointDensity n N eta w B E+
            jointAP n N eta w B E+reserve*singularNormalization N := by
  filter_upwards [eventually_jointCentre_paid reserve hreserve,eventually_ge_atTop (2:ℕ)]
    with N hpaid hN
  intro n eta heta nu epsilon hnu he heBudget E
  have hN1 : 1<N := by omega
  have hn : (1:ℝ)<N := by exact_mod_cast hN1
  have he8 : epsilon≤1/8 := heBudget.le.trans (min_le_left _ _)
  have heSquare : epsilon^2≤epsilon := by nlinarith
  have hB := Real.one_lt_rpow hn (mul_pos hnu he)
  have hwB := Real.rpow_le_rpow_of_exponent_le hn.le
    (mul_le_mul_of_nonneg_left heSquare hnu.le)
  have hw (t:Four) (ht:t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E) :=
    (parameters_on_joint_row hN1 heta hnu he heBudget ht).1
  have hu := original_joint_source_upper hN1 heta hB hwB E hw
  have hc := hpaid n eta heta nu epsilon hnu he heBudget E
  dsimp only
  have hneg := neg_le_abs_self
    (jointCentre n N eta ((N:ℝ)^(nu*epsilon^2)) ((N:ℝ)^(nu*epsilon)) E)
  linarith

end
end ImbalancedChen.P5Z.OriginalJointPresievedCentrePayment
