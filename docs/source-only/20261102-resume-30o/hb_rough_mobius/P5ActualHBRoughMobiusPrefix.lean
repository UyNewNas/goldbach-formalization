import ImbalancedChen.P5ActualRoughMobiusSmallSW
import ImbalancedChen.P5ActualHBRoughBrunRates
import ImbalancedChen.P5ActualHBRolePrefixReduction

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Composition with the ACTUAL O/hb_rough_one source theorem.  The Brun
comparison, factorial gap and support rate are not new hypotheses.  The
only named analytic premise is ClassicalUnroughMobiusSW from the preceding
module.  All positive moduli, real endpoints and the computed prefix
maximum are retained.  This is a source candidate, not kernel closure of
the complete PP theorem or of the broad task.
-/
namespace ImbalancedChen.P5Z.ActualHBRoughMobiusPrefix
noncomputable section
open Classical Filter Finset
open scoped Topology BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.ActualRoughContourParameters20261026b
open ActualRoughMobiusRankin ActualRoughMobiusInner ActualRoughMobiusSmallSW
open ActualHBRoughBrunFinite ActualHBRoughBrunRates
open ActualHBGroupLogAbelPrefix ActualHBRolePrefixReduction OriginalBetaPrimeSource

theorem log_fourth_envelope {U : ℝ} (hL : 1 ≤ Real.log U) :
    (1+Real.log U)^4 ≤ 16*(Real.log U)^4 := by
  have hh := pow_le_pow_left₀ (by linarith : (0:ℝ)≤1+Real.log U)
    (by linarith : 1+Real.log U≤2*Real.log U) 4
  norm_num [mul_pow] at hh
  exact hh

theorem log_power_add_four {U A : ℝ} (hL : 0 < Real.log U) :
    (Real.log U)^(A+4) = (Real.log U)^A*(Real.log U)^4 := by
  rw [Real.rpow_add hL]
  norm_num

/-- The exponent 29/32 pays the fixed fourth divisor moment.  Both
polynomial remainders are bounded before choosing the original chart. -/
theorem eventually_brunMobiusPolynomial_logU (hSW : ClassicalUnroughMobiusSW)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      ∀ a b : ℝ, U ≤ a → a ≤ b → b ≤ 2*U →
        ∀ (S : Finset ℕ) (c : ℕ → ℂ),
          S ⊆ Icc 1 (Nat.floor (U^(1/4 : ℝ))) →
          (∀ ell ∈ S, Squarefree ell) → (∀ ell ∈ S, ‖c ell‖ ≤ 1) →
          ∀ q r : ℕ, 0 < q → (q : ℝ) ≤ (Real.log U)^A → r.Coprime q →
          ‖∑ ell ∈ S,c ell*divisibleMobiusAtom ell a b q r‖ ≤
            C*U/(Real.log U)^A := by
  obtain ⟨C,U0,hC,hU0,hpoly⟩ := uniform_brunMobiusPolynomial hSW
    (A+4) A (by linarith) hA
  refine ⟨16*C+32,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop U0,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_logPower_le_power (A+4) (3/32 : ℝ) (by norm_num)]
    with U hU hL hpower
  intro a b ha hab hb S c hS hsq hc q r hq hqlog hr
  have hUp : 0 < U := zero_lt_one.trans hpower.1
  have hLp : 0 < Real.log U := zero_lt_one.trans_le hL
  have hden : 0 < (Real.log U)^A := Real.rpow_pos_of_pos hLp _
  have hden4 : 0 < (Real.log U)^4 := pow_pos hLp 4
  have hsmall : C*U*(1+Real.log U)^4/(Real.log U)^(A+4) ≤
      16*C*U/(Real.log U)^A := by
    calc
      _ ≤ C*U*(16*(Real.log U)^4)/(Real.log U)^(A+4) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (log_fourth_envelope hL) (by positivity))
          (Real.rpow_nonneg hLp.le _)
      _ = _ := by
        rw [log_power_add_four hLp]
        field_simp [hden.ne',hden4.ne']
        <;> ring
  have hlarge : 2*U^(29/32 : ℝ)*(1+Real.log U)^4 ≤
      32*U/(Real.log U)^A := by
    apply (le_div_iff₀ hden).mpr
    have hlogpow : (Real.log U)^4*(Real.log U)^A ≤ U^(3/32 : ℝ) := by
      rw [mul_comm,← log_power_add_four hLp]
      exact hpower.2
    calc
      (2*U^(29/32 : ℝ)*(1+Real.log U)^4)*(Real.log U)^A ≤
          (2*U^(29/32 : ℝ)*(16*(Real.log U)^4))*(Real.log U)^A :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (log_fourth_envelope hL) (by positivity)) hden.le
      _ = 32*U^(29/32 : ℝ)*((Real.log U)^4*(Real.log U)^A) := by ring
      _ ≤ 32*U^(29/32 : ℝ)*U^(3/32 : ℝ) :=
        mul_le_mul_of_nonneg_left hlogpow (by positivity)
      _ = 32*U := by
        rw [mul_assoc,← Real.rpow_add hUp]
        norm_num
  calc
    _ ≤ C*U*(1+Real.log U)^4/(Real.log U)^(A+4) +
        2*U^(29/32 : ℝ)*(1+Real.log U)^4 :=
      hpoly U a b hU ha hab hb S c hS hsq hc q r hq hqlog hr
    _ ≤ 16*C*U/(Real.log U)^A+32*U/(Real.log U)^A := add_le_add hsmall hlarge
    _ = _ := by ring

theorem Ico_succ_eq_Ioc (L H : ℕ) : Ico (L+1) (H+1) = Ioc L H := by
  ext n
  simp only [Finset.mem_Ico,Finset.mem_Ioc]
  omega

theorem divisorError_mu_eq_atom (ell q r H : ℕ) (u : ℝ) :
    divisorError (Nat.floor u+1) (H+1) q r ell muCoefficient =
      divisibleMobiusAtom ell u (H : ℝ) q r := by
  rw [divisorError,Ico_succ_eq_Ioc,error_eq_kernel]
  simp only [divisibleMobiusAtom,interval,Nat.floor_natCast]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp

theorem brunSupport_subset_quarter {U z : ℝ} (hU : 0 ≤ U) (hz : 1 ≤ z)
    (j : ℕ) (hcap : z^(2*j+1) ≤ U^(1/4 : ℝ)) :
    brunSupport z j ⊆ Icc 1 (Nat.floor (U^(1/4 : ℝ))) := by
  intro d hd
  have hh := (brun_support_bounds hz j).1 d hd
  exact Finset.mem_Icc.mpr ⟨hh.1,
    (Nat.le_floor_iff (Real.rpow_nonneg hU _)).mpr (hh.2.trans hcap)⟩

/-- Small q uses the proved polynomial cancellation; large q uses the
peer's exact universal interval count.  No upper bound on U or q occurs. -/
theorem eventually_roughMobius_prefix_with_gap (hSW : ClassicalUnroughMobiusSW)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      2 ≤ U ∧ ∀ z : ℝ, 1 ≤ z → ∀ j : ℕ, z^(2*j+1) ≤ U^(1/4 : ℝ) →
        ∀ u v : ℝ, U ≤ u → u ≤ v → v ≤ 2*U →
          ∀ q r : ℕ, 0 < q → r.Coprime q →
          prefixNorm (roughMoebiusSlot z) u v q r ≤
            C*U/(Real.log U)^A + 4*gapDensity z j*U + 10*z^(2*j+1) := by
  obtain ⟨C,hC,hpoly⟩ := eventually_brunMobiusPolynomial_logU hSW A hA
  refine ⟨C+10,by positivity,?_⟩
  filter_upwards [hpoly,eventually_ge_atTop (2 : ℝ),
    eventually_logPower_le_power A 1 zero_lt_one] with U hpolyU hU2 hpower
  refine ⟨hU2,?_⟩
  intro z hz j hcap u v hUu huv hvU q r hq hr
  have hU : 0 < U := lt_of_lt_of_le (by norm_num) hU2
  have hlogU : 0 < Real.log U := Real.log_pos (lt_of_lt_of_le (by norm_num) hU2)
  have hden : 0 < (Real.log U)^A := Real.rpow_pos_of_pos hlogU _
  have hpow : (Real.log U)^A ≤ U := by simpa using hpower.2
  have heps := gapDensity_nonneg z j
  have hY : 0 ≤ z^(2*j+1) := pow_nonneg (zero_le_one.trans hz) _
  have hu0 : 0 ≤ u := hU.le.trans hUu
  have hv0 : 0 ≤ v := hu0.trans huv
  apply Finset.sup'_le
  intro H hH
  by_cases hlow : H ≤ Nat.floor u
  · simp only [prefix,Finset.Ioc_eq_empty_of_le hlow,Finset.sum_empty,norm_zero]
    positivity
  have hLH : Nat.floor u ≤ H := by omega
  have huH : u ≤ (H : ℝ) := ((Nat.floor_lt hu0).mp (Nat.lt_of_not_ge hlow)).le
  have hHv : (H : ℝ) ≤ v := (Nat.le_floor_iff hv0).mp
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hH))
  have hHU : (H : ℝ) ≤ 2*U := hHv.trans hvU
  have hlen : ((H-Nat.floor u : ℕ) : ℝ) ≤ 2*U :=
    (show ((H-Nat.floor u : ℕ) : ℝ) ≤ H by exact_mod_cast Nat.sub_le H _).trans hHU
  have hprefix : prefix (roughMoebiusSlot z) u q r H =
      auxiliarySWError (Ico (Nat.floor u+1) (H+1)) (roughMoebiusSlot z) 1 q r := by
    rw [Ico_succ_eq_Ioc,error_eq_kernel]
    rfl
  rw [hprefix]
  by_cases hqsmall : (q : ℝ) ≤ (Real.log U)^A
  · have hbrun := signed_rough_brun_comparison hz j (Nat.floor u+1) (H+1)
      q r muCoefficient (by omega) hq hr (fun n _ => muCoefficient_norm_le n)
    change ‖auxiliarySWError (Ico (Nat.floor u+1) (H+1)) (roughMoebiusSlot z) 1 q r‖ ≤ _ at hbrun
    simp only [Nat.add_sub_add_right,divisorError_mu_eq_atom] at hbrun
    have hpol := hpolyU u (H : ℝ) hUu huH hHU
      (brunSupport z j) (fun d => (upperWeight z j d : ℂ))
      (brunSupport_subset_quarter hU.le hz j hcap)
      (fun d hd => brun_support_squarefree hd)
      (fun d _ => by simpa only [Complex.norm_real,Real.norm_eq_abs] using (brun_weights z j d).1)
      q r hq hqsmall hr
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hgap : 2*gapDensity z j*((H-Nat.floor u : ℕ) : ℝ)/(q : ℝ) ≤
        4*gapDensity z j*U := by
      calc
        _ ≤ 2*gapDensity z j*((H-Nat.floor u : ℕ) : ℝ) := div_le_self (by positivity) hq1
        _ ≤ 2*gapDensity z j*(2*U) := mul_le_mul_of_nonneg_left hlen (by positivity)
        _ = _ := by ring
    have hCpay : C*U/(Real.log U)^A ≤ (C+10)*U/(Real.log U)^A := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : C≤C+10) hU.le) hden.le
    linarith
  · have hlarge := oneBounded_interval_large_modulus (Nat.floor u+1) (H+1) q r
      (roughMoebiusSlot z) (by omega) hq (fun n _ => roughMoebiusSlot_norm_le z n)
    simp only [Nat.add_sub_add_right] at hlarge
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hcount : 2*((H-Nat.floor u : ℕ) : ℝ)/(q : ℝ) ≤ 4*U/(Real.log U)^A := by
      calc
        _ ≤ (4*U)/(q : ℝ) := div_le_div_of_nonneg_right (by linarith) hqR.le
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hden (le_of_not_ge hqsmall)
    have hend : (6 : ℝ) ≤ 6*U/(Real.log U)^A := by
      apply (le_div_iff₀ hden).mpr
      nlinarith [hpow]
    have hCpay : 10*U/(Real.log U)^A ≤ (C+10)*U/(Real.log U)^A := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : 10≤C+10) hU.le) hden.le
    have htotal : ‖auxiliarySWError (Ico (Nat.floor u+1) (H+1))
        (roughMoebiusSlot z) 1 q r‖ ≤ 10*U/(Real.log U)^A := by
      calc
        _ ≤ 2*((H-Nat.floor u : ℕ) : ℝ)/(q : ℝ)+6 := hlarge
        _ ≤ 4*U/(Real.log U)^A+6*U/(Real.log U)^A := add_le_add hcount hend
        _ = _ := by ring
    have hgap0 : 0 ≤ 4*gapDensity z j*U := by positivity
    have hY0 : 0 ≤ 10*z^(2*j+1) := by positivity
    linarith

/-- The literal base rough-Mobius prefix cancellation at the actual
chart cutoff, with one threshold before ALL U,u,v,q,r.  No upper bound
on U is required; no modulus-dependent mask is introduced. -/
theorem eventually_roughMobius_prefix_log_saving (hSW : ClassicalUnroughMobiusSW)
    (xi A : ℝ) (hxi : 0 < xi) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ U u v : ℝ, ∀ q r : ℕ,
        x^xi ≤ U → U ≤ u → u ≤ v → v ≤ 2*U → 0 < q → r.Coprime q →
        prefixNorm (roughMoebiusSlot (roughZ x)) u v q r ≤ C*U/(Real.log x)^A := by
  obtain ⟨C,hC,hUevent⟩ := eventually_roughMobius_prefix_with_gap hSW A hA
  obtain ⟨U0,hU0⟩ := Filter.eventually_atTop.mp hUevent
  refine ⟨C/(xi^A)+14,by positivity,?_⟩
  filter_upwards [eventually_actual_brun_payments xi A hxi,
    (tendsto_rpow_atTop hxi).eventually (eventually_ge_atTop U0)] with x hx hscale0
  intro U u v q r hscale hUu huv hvU hq hr
  have hdata := hU0 U (hscale0.trans hscale)
  have hU2 : 2 ≤ U := hdata.1
  have hUp : 0 < U := lt_of_lt_of_le (by norm_num) hU2
  have hxp : 0 < x := zero_lt_one.trans hx.1
  have hLx : 0 < Real.log x := hx.2.2.1
  have hLU : 0 < Real.log U := Real.log_pos (lt_of_lt_of_le (by norm_num) hU2)
  have hdenx : 0 < (Real.log x)^A := Real.rpow_pos_of_pos hLx _
  have hdenU : 0 < (Real.log U)^A := Real.rpow_pos_of_pos hLU _
  have hxiA : 0 < xi^A := Real.rpow_pos_of_pos hxi _
  have hlog : xi*Real.log x ≤ Real.log U := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hxp xi) hscale
    rwa [Real.log_rpow hxp] at hh
  have hp : xi^A*(Real.log x)^A ≤ (Real.log U)^A := by
    have hh := Real.rpow_le_rpow (mul_nonneg hxi.le hLx.le) hlog hA
    rwa [Real.mul_rpow hxi.le hLx.le] at hh
  have hmain : C*U/(Real.log U)^A ≤ (C/(xi^A))*U/(Real.log x)^A := by
    calc
      _ ≤ C*U/(xi^A*(Real.log x)^A) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hxiA hdenx) hp
      _ = _ := by ring
  have hY : supportSize x ≤ U/(Real.log x)^A :=
    hx.2.2.2.1.trans (div_le_div_of_nonneg_right hscale hdenx.le)
  have heps := hx.2.2.2.2.1
  have hcap : (roughZ x)^(2*halfOrder x+1) ≤ U^(1/4 : ℝ) :=
    (hx.2.2.2.2.2 U hscale).le
  have hbound := hdata.2 (roughZ x) hx.2.1 (halfOrder x) hcap
    u v hUu huv hvU q r hq hr
  change prefixNorm (roughMoebiusSlot (roughZ x)) u v q r ≤
    C*U/(Real.log U)^A+4*epsilon x*U+10*supportSize x at hbound
  calc
    _ ≤ C*U/(Real.log U)^A+4*epsilon x*U+10*supportSize x := hbound
    _ ≤ (C/(xi^A))*U/(Real.log x)^A + 4*(1/(Real.log x)^A)*U +
        10*(U/(Real.log x)^A) := add_le_add
      (add_le_add hmain (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left heps (by norm_num)) hUp.le))
      (mul_le_mul_of_nonneg_left hY (by norm_num))
    _ = _ := by ring

/-- The k=1 interval conclusion is stated with the same exact mean. -/
theorem eventually_roughMobius_interval_log_saving (hSW : ClassicalUnroughMobiusSW)
    (xi A : ℝ) (hxi : 0 < xi) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ U u v : ℝ, ∀ q r : ℕ,
        x^xi ≤ U → U ≤ u → u ≤ v → v ≤ 2*U → 0 < q → r.Coprime q →
        ‖auxiliarySWError (Ioc (Nat.floor u) (Nat.floor v))
          (roughMoebiusSlot (roughZ x)) 1 q r‖ ≤ C*U/(Real.log x)^A := by
  obtain ⟨C,hC,hprefix⟩ := eventually_roughMobius_prefix_log_saving hSW xi A hxi hA
  refine ⟨C,hC,?_⟩
  filter_upwards [hprefix] with x hx
  intro U u v q r hscale hUu huv hvU hq hr
  rw [error_eq_kernel]
  exact (prefix_le (roughMoebiusSlot (roughZ x)) u v q r le_rfl).trans
    (hx U u v q r hscale hUu huv hvU hq hr)

/-- The ORIGINAL real truncation y is retained through the frozen M
prefix reduction; the threshold is chosen before y varies. -/
theorem eventually_actual_mobius_prefix_log_saving (hSW : ClassicalUnroughMobiusSW)
    (xi A : ℝ) (hxi : 0 < xi) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ U u v y : ℝ, ∀ q r : ℕ,
        x^xi ≤ U → U ≤ u → u ≤ v → v ≤ 2*U →
        0 < q → r.Coprime q →
        prefixNorm (ActualRoughHeathBrownWords.actual (roughZ x) y .mobius) u v q r ≤
          C*U/(Real.log x)^A := by
  obtain ⟨C,hC,hprefix⟩ := eventually_roughMobius_prefix_log_saving hSW xi A hxi hA
  refine ⟨C,hC,?_⟩
  filter_upwards [hprefix,eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro U u v y q r hscale hUu huv hvU hq hr
  have hU : 0 < U := (Real.rpow_pos_of_pos (zero_lt_one.trans hx1) xi).trans_le hscale
  have hu1 : 1 ≤ u := (Real.one_le_rpow hx1.le hxi.le).trans (hscale.trans hUu)
  have hred := actual_prefixNorm_le_base (roughZ x) y .mobius hU hu1 hUu huv hvU q r
  simp only [baseRole,numeratorCost,mul_one] at hred
  exact hred.trans (hx U u v q r hscale hUu huv hvU hq hr)

end
end ImbalancedChen.P5Z.ActualHBRoughMobiusPrefix
