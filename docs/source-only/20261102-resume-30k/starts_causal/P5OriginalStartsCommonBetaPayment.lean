import ImbalancedChen.P5OriginalStartsRoundedBetaReserve
import ImbalancedChen.P5OriginalStartsCommonBetaCount

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A single beta parameter pays the actual rounded loss of BOTH original
starts, at the actual nu=249/448 level and common cap ceil(N^h).
The complete 3+1 multiplier is paid before either policy or mesh is read.
The resulting count theorem still displays the real raw-density minus
rounding cost and the sharp errors of the SAME compiled physical rho.
It does not assume the final causal coefficient or hstarts.
-/

namespace ImbalancedChen.P5OriginalStartsCommonBetaPayment

noncomputable section
open Filter Topology
open P5OriginalStartsCommonBetaCount P5OriginalStartsRoundedBetaReserve

/-- No beta error remains in this main term. The actual full raw source
and the exact ALL/ANY rounding loss are retained separately. -/
def roundingMain (epsilon : ℝ) (N : ℕ) (z tau : ℝ)
    (retainEven : List ℕ → Bool) : ℝ :=
  reciprocalTotientDensity
      (fixedEvenRoughSupport retainEven N (commonCap N) 0 z)
      (fixedEvenRoughCoefficient retainEven N (commonCap N) 0 z) -
    actualSmallEulerProduct N (commonCap N) (commonPresieve epsilon N)*
      P2LowerFiniteCellRounding.roundingLoss retainEven N (commonCap N)
        (commonPresieve epsilon N) z tau

theorem rawMain_eq_roundingMain_sub_betaLoss
    (C K epsilon : ℝ) (N : ℕ) (z tau : ℝ) (retainEven : List ℕ → Bool) :
    rawMain C K epsilon N z tau retainEven =
      roundingMain epsilon N z tau retainEven -
        betaLoss C K (rootLevel N) epsilon retainEven N (commonCap N) z tau := rfl

/-- A quantitative payment on the literal C_N/log N scale at nu=249/448.
The top h cutoff pays both original starts; no second beta pair is chosen.
The threshold is uniform in both retained histories and their shared mesh. -/
theorem exists_original_grouped_beta_reserve
    (C K eta epsilonMax : ℝ) (hC : 0<C) (heta : 0<eta)
    (hepsilonMax : 0<epsilonMax) :
    ∃ epsilon : ℝ, 0<epsilon ∧ epsilon<1/8 ∧ epsilon<epsilonMax ∧
      ∃ N0 : ℕ, 2≤N0 ∧ ∀ N : ℕ, N0≤N → Even N →
        ∀ (ra rh : List ℕ → Bool) (tau : ℝ),
          3*betaLoss C K (rootLevel N) epsilon ra N (commonCap N) (cutoffA N) tau +
            betaLoss C K (rootLevel N) epsilon rh N (commonCap N) (cutoffH N) tau ≤
              eta*singularSeries N/Real.log (N:ℝ) := by
  have hnu : 0<ordinaryNu := by norm_num [ordinaryNu]
  obtain ⟨epsilon,he,he8,hemax,_her,D0,_hD0,hbound⟩ :=
    exists_betaLoss_le_normalized_reserve C K ((19/125:ℝ)/ordinaryNu)
      (eta*ordinaryNu/4) epsilonMax hC (by positivity) (by positivity) hepsilonMax
  have hpower : Tendsto rootLevel atTop atTop :=
    (tendsto_rpow_atTop hnu).comp tendsto_natCast_atTop_atTop
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (hpower.eventually (eventually_ge_atTop D0))
  refine ⟨epsilon,he,he8,hemax,max 2 T,le_max_left _ _,?_⟩
  intro N hN hEven ra rh tau
  have hN2 : 2≤N := (le_max_left _ _).trans hN
  have hNT : T≤N := (le_max_right _ _).trans hN
  have hNpos : 0<N := by omega
  have hNposR : (0:ℝ)<N := by exact_mod_cast hNpos
  have hN1 : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hlogN : 0<Real.log (N:ℝ) := Real.log_pos hN1
  obtain ⟨_hL,_hwL,hwA,hwH,_haCap,hhCap⟩ := original_common_gates he he8 hN2
  have htop : (rootLevel N)^((19/125:ℝ)/ordinaryNu)=cutoffH N := by
    dsimp only [rootLevel,cutoffH]
    rw [← Real.rpow_mul hNposR.le]
    congr 1
    field_simp [hnu.ne']
  have hAH : cutoffA N≤cutoffH N :=
    Real.rpow_le_rpow_of_exponent_le hN1.le (by norm_num)
  have hcap : (rootLevel N)^(epsilon^2)≤(commonCap N:ℝ) := hwH.trans hhCap
  have ha := hbound (rootLevel N) (hT N hNT) N (commonCap N) hNpos hEven
    hcap (cutoffA N) tau hwA (by rw [htop]; exact hAH) ra
  have hh := hbound (rootLevel N) (hT N hNT) N (commonCap N) hNpos hEven
    hcap (cutoffH N) tau hwH (by rw [htop]) rh
  have hnorm : (eta*ordinaryNu/4)*singularSeries N/Real.log (rootLevel N) =
      (eta/4)*singularSeries N/Real.log (N:ℝ) := by
    rw [rootLevel,Real.log_rpow hNposR]
    field_simp [hnu.ne',hlogN.ne']
    <;> ring
  rw [hnorm] at ha hh
  nlinarith only [ha,hh]

/-- The actual original source/count entrance with its entire beta loss
paid. For any requested eta, epsilon can respect an earlier fixed margin.
The source remains exactly 3*U1+U2, and both sharp errors use the same
rounded coefficients as the physical minorants. No PP estimate is hidden. -/
theorem exists_original_grouped_count_beta_paid
    (eta delta epsilonMax : ℝ) (heta : 0<eta) (hdelta : 0<delta)
    (hepsilonMax : 0<epsilonMax) :
    ∃ epsilon : ℝ, 0<epsilon ∧ epsilon<1/8 ∧ epsilon<epsilonMax ∧
      ∃ N0 : ℕ, 2≤N0 ∧ ∀ N : ℕ, N0≤N → Even N →
        ∀ (ra rh : List ℕ → Bool) (tau : ℝ),
          ((chenPrimePrefix N).card:ℝ)*
              (3*roundingMain epsilon N (cutoffA N) tau ra +
                roundingMain epsilon N (cutoffH N) tau rh -
                eta*singularSeries N/Real.log (N:ℝ)) +
            3*sharpError epsilon N (cutoffA N) tau ra +
              sharpError epsilon N (cutoffH N) tau rh -
              delta*singularNormalization N ≤
                3*currentChenUpsilon1 N+currentChenUpsilon2 N := by
  obtain ⟨C,K,hC,_hK,hcount⟩ := exists_original_common_beta_grouped_count
  obtain ⟨epsilon,he,he8,hemax,Nbeta,hNbeta,hbeta⟩ :=
    exists_original_grouped_beta_reserve C K eta epsilonMax hC heta hepsilonMax
  obtain ⟨Ncount,_hNcount,hcount⟩ := hcount epsilon he he8 delta hdelta
  refine ⟨epsilon,he,he8,hemax,max Nbeta Ncount,
    hNbeta.trans (le_max_left _ _),?_⟩
  intro N hN hEven ra rh tau
  have hb := hbeta N ((le_max_left _ _).trans hN) hEven ra rh tau
  have hc := hcount N ((le_max_right _ _).trans hN) hEven ra rh tau
  have hmain :
      3*roundingMain epsilon N (cutoffA N) tau ra +
        roundingMain epsilon N (cutoffH N) tau rh -
        eta*singularSeries N/Real.log (N:ℝ) ≤
      3*rawMain C K epsilon N (cutoffA N) tau ra +
        rawMain C K epsilon N (cutoffH N) tau rh := by
    rw [rawMain_eq_roundingMain_sub_betaLoss,rawMain_eq_roundingMain_sub_betaLoss]
    linarith only [hb]
  have hmul := mul_le_mul_of_nonneg_left hmain
    (Nat.cast_nonneg (chenPrimePrefix N).card : (0:ℝ)≤(chenPrimePrefix N).card)
  linarith only [hmul,hc]

end
end ImbalancedChen.P5OriginalStartsCommonBetaPayment
