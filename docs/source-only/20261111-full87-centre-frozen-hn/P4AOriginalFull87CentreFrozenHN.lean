import ImbalancedChen.P4AOriginalFull87CentreSqrtEnvelope
import MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Normalization bridge for the SAME original87 centre-prime bill, not a new
signed coefficient or another reserve. The genuine odd-prime infinite
product from the PINNED native library is used, not the finite sieve proxy
singularSeries, which differs by a factor of two and a truncation tail.

The frozen manuscript's C_N is exactly liuSingularSeries N:
liuUniversalProduct times the finite correction on odd prime divisors.
The work below combines the existing ACTUAL centre envelope with this
exact H_N and the fixed mathlib logarithm-versus-power asymptotics.
-/

namespace ImbalancedChen.P4AOriginalFull87CentreFrozenHN
noncomputable section
open Filter Topology Real
open scoped Classical BigOperators
open MathlibNt.SieveTheory.SingularSeries
open P4AOriginalFull87CentreCoprimeDivisors (centreCoprimeDivisorBudget)
open P4AOriginalFull87CentreSqrtEnvelope
  (centreSqrtLogBudget original87_centre_coprime_budget_le_sqrt_log)

/-- Literal frozen normalization C_N*N/log(N)^2.  The native
liuSingularSeries is the genuine infinite odd-prime C_2 times the
exact finite odd-prime-divisor correction (NOT the finite proxy). -/
def frozenHN (N : ℕ) : ℝ :=
  liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2

theorem frozenHN_source_formula (N : ℕ) :
    frozenHN N =
      (liuUniversalProduct * liuCorrection N) *
        (N : ℝ) / Real.log (N : ℝ) ^ 2 := by
  unfold frozenHN liuSingularSeries
  ring

theorem frozenHN_pos (N : ℕ) (hN : 2 ≤ N) : 0 < frozenHN N := by
  have hx : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  unfold frozenHN
  exact div_pos (mul_pos (liuSingularSeries_pos N) hx) (pow_pos hl _)

/-- The actual frozen C_N has a uniform positive lower factor C_2,
supplied by the exact native infinite product proof. -/
theorem frozenHN_lower (N : ℕ) :
    liuUniversalProduct * (N : ℝ) / Real.log (N : ℝ) ^ 2 ≤
      frozenHN N := by
  unfold frozenHN
  apply div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_right
    (liuUniversalProduct_le_liuSingularSeries N) (by positivity)

/-- Literal integer log_2 cannot be replaced by natural real log
without this explicit change of base. -/
private theorem natLogTwo_le_log_div_logTwo
    (N : ℕ) (hN : 2 ≤ N) :
    ((Nat.log 2 N : ℕ) : ℝ) ≤
      Real.log (N : ℝ) / Real.log (2 : ℝ) := by
  have hp : 2 ^ Nat.log 2 N ≤ N :=
    Nat.pow_log_le_self 2 (by omega)
  have hpR : (2 : ℝ) ^ Nat.log 2 N ≤ (N : ℝ) := by
    exact_mod_cast hp
  have hlog : Real.log ((2 : ℝ) ^ Nat.log 2 N) ≤
      Real.log (N : ℝ) :=
    Real.log_le_log (pow_pos (by norm_num) _) hpR
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    (by simpa only [mul_comm] using hlog)

/-- Pointwise real majorant for the ACTUAL centre invoice.  The factor
eight comes from sqrt_int(N)+2 ≤ 2*sqrt_real(N) for N≥4. -/
theorem original87_centre_budget_le_real_sqrt_log
    (N : ℕ) (hN : 4 ≤ N) :
    centreCoprimeDivisorBudget N ≤
      (8 / Real.log (2 : ℝ)) *
        Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
  have hrootNatSq : (((Nat.sqrt N : ℕ) : ℝ) ^ 2) ≤ (N : ℝ) := by
    exact_mod_cast Nat.sqrt_le' N
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hsquare : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt hN0
  have hrootNat : ((Nat.sqrt N : ℕ) : ℝ) ≤
      Real.sqrt (N : ℝ) := by
    have hnat : (0 : ℝ) ≤ (Nat.sqrt N : ℕ) := by positivity
    have hreal := Real.sqrt_nonneg (N : ℝ)
    nlinarith
  have hroot2 : (2 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have hreal := Real.sqrt_nonneg (N : ℝ)
    nlinarith
  calc
    centreCoprimeDivisorBudget N ≤ centreSqrtLogBudget N :=
      original87_centre_coprime_budget_le_sqrt_log N (by omega)
    _ = 4 * (((Nat.sqrt N : ℕ) : ℝ) + 2) *
          ((Nat.log 2 N : ℕ) : ℝ) := by
      simp [centreSqrtLogBudget, Nat.cast_add]
    _ ≤ 4 * (2 * Real.sqrt (N : ℝ)) *
          (Real.log (N : ℝ) / Real.log (2 : ℝ)) := by
      gcongr
      · linarith
      · exact natLogTwo_le_log_div_logTwo N (by omega)
    _ = (8 / Real.log (2 : ℝ)) *
          Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by ring

/-- Explicit pointwise ratio bound on the frozen manuscript scale.
This consumes the already proved finite centre invoice ONCE.
No PP hypothesis or new arithmetic coefficient enters this lemma. -/
theorem original87_centre_budget_div_frozenHN_le
    (N : ℕ) (hN : 4 ≤ N) :
    centreCoprimeDivisorBudget N / frozenHN N ≤
      (8 / (liuUniversalProduct * Real.log (2 : ℝ))) *
        (Real.log (N : ℝ) ^ 3 / Real.sqrt (N : ℝ)) := by
  have hx : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hlog2 : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hC2 : 0 < liuUniversalProduct := liuUniversalProduct_pos
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hx
  have hHN : 0 < frozenHN N := frozenHN_pos N (by omega)
  have hHlow : 0 <
      liuUniversalProduct * (N : ℝ) / Real.log (N : ℝ) ^ 2 :=
    div_pos (mul_pos hC2 hx) (pow_pos hl _)
  have hE : 0 ≤
      (8 / Real.log (2 : ℝ)) *
        Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by positivity
  calc
    centreCoprimeDivisorBudget N / frozenHN N ≤
        ((8 / Real.log (2 : ℝ)) *
          Real.sqrt (N : ℝ) * Real.log (N : ℝ)) / frozenHN N := by
      exact div_le_div_of_nonneg_right
        (original87_centre_budget_le_real_sqrt_log N hN) hHN.le
    _ ≤ ((8 / Real.log (2 : ℝ)) *
          Real.sqrt (N : ℝ) * Real.log (N : ℝ)) /
          (liuUniversalProduct * (N : ℝ) /
            Real.log (N : ℝ) ^ 2) := by
      exact div_le_div_of_nonneg_left hE hHlow
        (frozenHN_lower N)
    _ = (8 / (liuUniversalProduct * Real.log (2 : ℝ))) *
          (Real.log (N : ℝ) ^ 3 / Real.sqrt (N : ℝ)) := by
      have hs : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
        Real.sq_sqrt hx.le
      have hn : (N : ℝ) ≠ 0 := hx.ne'
      field_simp [hlog2.ne', hC2.ne', hl.ne', hroot.ne', hn]
      nlinarith [hs]

/-- The genuine frozen-normalization ratio tends to zero.  The only
asymptotic lemma used is PINNED mathlib's log^3=o(x^(1/2)).
The result is for all N→∞, hence in particular even N. -/
theorem tendsto_original87_centre_budget_div_frozenHN_zero :
    Tendsto (fun N : ℕ =>
      centreCoprimeDivisorBudget N / frozenHN N) atTop (𝓝 0) := by
  have hlogSmall : Tendsto
      (fun N : ℕ => Real.log (N : ℝ) ^ 3 / Real.sqrt (N : ℝ))
      atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (3 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    simpa only [Real.rpow_natCast, Real.sqrt_eq_rpow, Function.comp_def]
      using h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound : Tendsto
      (fun N : ℕ =>
        (8 / (liuUniversalProduct * Real.log (2 : ℝ))) *
          (Real.log (N : ℝ) ^ 3 / Real.sqrt (N : ℝ)))
      atTop (𝓝 0) := by
    simpa using hlogSmall.const_mul
      (8 / (liuUniversalProduct * Real.log (2 : ℝ)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    hbound
  · filter_upwards [eventually_ge_atTop (4 : ℕ)] with N hN
    apply div_nonneg
    · unfold centreCoprimeDivisorBudget
      positivity
    · exact (frozenHN_pos N (by omega)).le
  · filter_upwards [eventually_ge_atTop (4 : ℕ)] with N hN
    exact original87_centre_budget_div_frozenHN_le N hN

end
end ImbalancedChen.P4AOriginalFull87CentreFrozenHN
