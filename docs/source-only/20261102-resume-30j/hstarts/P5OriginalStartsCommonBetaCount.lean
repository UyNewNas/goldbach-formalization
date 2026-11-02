import ImbalancedChen.P5OriginalStartsOneSidedCentre

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Original ordinary starts at a=417/5000, h=19/125 and nu=249/448.
One actual small Rosser pair and one enumeration cap serve both starts.
The prime-count entrance below is proved for the independently constructed
finite-cell compiler, with its literal full-policy raw density, its actual
rounding loss, its actual absolute beta loss, and its same-rho sharp error.
No scalar originalGroupedStarts inequality or enhanced-table licence is
an input. Paying the remaining raw/integral, rounding and PP ports is open.
-/

namespace ImbalancedChen.P5OriginalStartsCommonBetaCount

noncomputable section
open Filter Topology
open P5OriginalStartsOneSidedCentre

def ordinaryNu : ℝ := 249/448
def cutoffA (N : ℕ) : ℝ := (N:ℝ)^(417/5000:ℝ)
def cutoffH (N : ℕ) : ℝ := (N:ℝ)^(19/125:ℝ)
def rootLevel (N : ℕ) : ℝ := (N:ℝ)^ordinaryNu
def commonCap (N : ℕ) : ℕ := Nat.ceil (cutoffH N)
def commonPresieve (epsilon : ℝ) (N : ℕ) : ℝ := rootLevel N^(epsilon^2)
def commonBetaLevel (epsilon : ℝ) (N : ℕ) : ℝ := rootLevel N^epsilon

/-- This is a derived arithmetic expression, not a caller's density
certificate. Every loss is the actual finite compiler's own function. -/
def rawMain (C K epsilon : ℝ) (N : ℕ) (z tau : ℝ)
    (retainEven : List ℕ → Bool) : ℝ :=
  reciprocalTotientDensity (fixedEvenRoughSupport retainEven N (commonCap N) 0 z)
    (fixedEvenRoughCoefficient retainEven N (commonCap N) 0 z) -
  actualSmallEulerProduct N (commonCap N) (commonPresieve epsilon N) *
    P2LowerFiniteCellRounding.roundingLoss retainEven N (commonCap N)
      (commonPresieve epsilon N) z tau -
  (actualSmallEulerProduct N (commonCap N) (commonPresieve epsilon N) *
    actualSmallRosserDensityError C K (rootLevel N) epsilon) *
    reciprocalTotientDensity
      (P2LowerFiniteCellRounding.universe N (commonCap N) (commonPresieve epsilon N) z)
      (fun d => |P2LowerFiniteCellRounding.coefficient retainEven N (commonCap N)
        (commonPresieve epsilon N) z tau d|)

def sharpError (epsilon : ℝ) (N : ℕ) (z tau : ℝ)
    (retainEven : List ℕ → Bool) : ℝ :=
  compiledSharpError N (commonCap N) (commonPresieve epsilon N) z tau
    (commonBetaLevel epsilon N) retainEven

/-- The common small-beta choices fit BOTH literal original starts.
No support/physical-level claim about the arbitrary rough policy occurs. -/
theorem original_common_gates {epsilon : ℝ} (he : 0<epsilon) (he8 : epsilon<1/8)
    {N : ℕ} (hN : 2≤N) :
    1<commonBetaLevel epsilon N ∧
      commonPresieve epsilon N≤commonBetaLevel epsilon N ∧
      commonPresieve epsilon N≤cutoffA N ∧ commonPresieve epsilon N≤cutoffH N ∧
      cutoffA N≤(commonCap N:ℝ) ∧ cutoffH N≤(commonCap N:ℝ) := by
  have hN1 : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hnu : 0<ordinaryNu := by norm_num [ordinaryNu]
  have hD : 1<rootLevel N := Real.one_lt_rpow hN1 hnu
  have hesq : epsilon^2≤epsilon := by
    nlinarith [mul_pos he (sub_pos.mpr he8)]
  have hesq8 : epsilon^2<(1/8:ℝ)^2 := by
    nlinarith [mul_pos he (sub_pos.mpr he8)]
  have hsmall : ordinaryNu*epsilon^2≤(417/5000:ℝ) := by
    dsimp [ordinaryNu]
    nlinarith only [hesq8]
  have hwA : commonPresieve epsilon N≤cutoffA N := by
    dsimp [commonPresieve,rootLevel,cutoffA]
    rw [←Real.rpow_mul (zero_lt_one.trans hN1).le]
    exact Real.rpow_le_rpow_of_exponent_le hN1.le hsmall
  have hAH : cutoffA N≤cutoffH N :=
    Real.rpow_le_rpow_of_exponent_le hN1.le (by norm_num)
  have hhCap : cutoffH N≤(commonCap N:ℝ) := Nat.le_ceil _
  exact ⟨Real.one_lt_rpow hD he,
    Real.rpow_le_rpow_of_exponent_le hD.le hesq,
    hwA,hwA.trans hAH,hAH.trans hhCap,hhCap⟩

/-- Real source/count/mean entrance for the original grouped starts.
C,K come from the proved ordinary beta sandwich. One N threshold is
chosen before BOTH policies and the common finite partition tau. There
is no error-smallness assumption: the signed errors and actual rounding
and beta losses remain displayed. The complete excluded-prime loss is
already paid in the original H_N normalization. -/
theorem exists_original_common_beta_grouped_count :
    ∃ C K : ℝ, 0<C ∧ 1<K ∧
      ∀ epsilon : ℝ, 0<epsilon → epsilon<1/8 →
      ∀ eta : ℝ, 0<eta → ∃ N0 : ℕ, 2≤N0 ∧
      ∀ N : ℕ, N0≤N → Even N →
      ∀ (ra rh : List ℕ → Bool) (tau : ℝ),
        ((chenPrimePrefix N).card:ℝ) *
            (3*rawMain C K epsilon N (cutoffA N) tau ra +
              rawMain C K epsilon N (cutoffH N) tau rh) +
          3*sharpError epsilon N (cutoffA N) tau ra +
            sharpError epsilon N (cutoffH N) tau rh -
          eta*singularNormalization N ≤ 3*currentChenUpsilon1 N + currentChenUpsilon2 N := by
  obtain ⟨C,K,hC,hK,hsupply⟩ :=
    P2LowerFiniteCellRawDensityReserve.exists_actual_compiled_raw_density_reserve
  refine ⟨C,K,hC,hK,?_⟩
  intro epsilon he he8 eta heta
  obtain ⟨D0,hD0,hdensity⟩ := hsupply epsilon he he8
  have hnu : 0<ordinaryNu := by norm_num [ordinaryNu]
  have hpower : Tendsto rootLevel atTop atTop :=
    (tendsto_rpow_atTop hnu).comp tendsto_natCast_atTop_atTop
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp
    ((hpower.eventually (eventually_ge_atTop D0)).and
      ((eventually_actual_grouped_starts_total_pi_lower_paid eta heta).and
        (eventually_ge_atTop (2:ℕ))))
  refine ⟨max 2 N0,le_max_left _ _,?_⟩
  intro N hN hEven ra rh tau
  have hN0' : N0≤N := (le_max_right _ _).trans hN
  obtain ⟨hlevel,hcount,hN2⟩ := hN0 N hN0'
  obtain ⟨hL,hwL,hwA,hwH,haCap,hhCap⟩ := original_common_gates he he8 hN2
  have hrawA := hdensity (rootLevel N) hlevel N (commonCap N) hEven
    ra (cutoffA N) tau hwA
  have hrawH := hdensity (rootLevel N) hlevel N (commonCap N) hEven
    rh (cutoffH N) tau hwH
  change rawMain C K epsilon N (cutoffA N) tau ra ≤
    compiledDensity N (commonCap N) (commonPresieve epsilon N) (cutoffA N) tau
      (commonBetaLevel epsilon N) ra at hrawA
  change rawMain C K epsilon N (cutoffH N) tau rh ≤
    compiledDensity N (commonCap N) (commonPresieve epsilon N) (cutoffH N) tau
      (commonBetaLevel epsilon N) rh at hrawH
  have hmain := mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left hrawA (by norm_num : (0:ℝ)≤3)) hrawH)
    (Nat.cast_nonneg (chenPrimePrefix N).card : (0:ℝ)≤(chenPrimePrefix N).card)
  have hactual := hcount (commonCap N) (commonPresieve epsilon N) tau
    (commonBetaLevel epsilon N) ra rh hEven hL hwL hwA hwH haCap hhCap
  change ((chenPrimePrefix N).card:ℝ) *
      (3*compiledDensity N (commonCap N) (commonPresieve epsilon N) (cutoffA N) tau
          (commonBetaLevel epsilon N) ra +
        compiledDensity N (commonCap N) (commonPresieve epsilon N) (cutoffH N) tau
          (commonBetaLevel epsilon N) rh) +
    3*sharpError epsilon N (cutoffA N) tau ra + sharpError epsilon N (cutoffH N) tau rh -
    eta*singularNormalization N ≤ _ at hactual
  linarith only [hmain,hactual]

end
end ImbalancedChen.P5OriginalStartsCommonBetaCount
