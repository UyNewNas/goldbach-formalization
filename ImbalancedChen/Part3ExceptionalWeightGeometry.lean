import ImbalancedChen.Part3ExceptionalWeightExtension

/-!
# The physical exceptional spectral weight

These are the actual `Y₀ = 4π√(AVU)/(C√Z)` and `L = U/ν` identities used
in `ana:spectral-polynomial` of the 2026-11-06 manuscript. The elementary
scale and ratio proofs are extracted from the archived
`Part3ActualPoissonNormalizedFScalar.lean` and
`Part3ZExceptionalThresholdGeometry.lean` at
`fa22a56829ee880404516a36d498ce27dcb32f92`; no old analytic dependency is
imported. The final bound connects them to the existing common-interval
quadratic form. The full-block spectral estimate and eigenvalue lower
bound remain explicit classical inputs.
-/

namespace ImbalancedChen.Part3.ExceptionalWeightGeometry

noncomputable section

open ExceptionalWeightExtension CommonIntervalFourier ActualIntervalGeometricSumSourceOnly
open scoped BigOperators

def spectralScale (A V U Z C : ℝ) : ℝ :=
  4*Real.pi*Real.sqrt (A*V*U)/(C*Real.sqrt Z)

/-- Quadratic scale, with the full 16*pi^2 retained. -/
theorem spectralScale_sq {A V U Z C : ℝ} (hA : 0<A) (hV : 0<V)
    (hU : 0<U) (hZ : 0<Z) (hC : 0<C) :
    (spectralScale A V U Z C)^2 = 16*Real.pi^2*A*V*U/(C^2*Z) := by
  have _ := hC
  simp only [spectralScale, div_pow, mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ A*V*U), Real.sq_sqrt hZ.le]
  ring

def weight (X Z L : ℝ) : ℝ := (1 + X / Real.sqrt (1 + Z / L)) ^ 2

def spectralWeight (A V U Z C L : ℝ) : ℝ :=
  weight (1 / spectralScale A V U Z C) Z L

def ratioBound (A nu L V Z C : ℝ) : ℝ :=
  2 / threshold V Z +
    8 * (C ^ 2 * Z / (16 * Real.pi ^ 2 * A * nu * (L + Z) * (V + Z) ^ 2))

theorem actual_spectralScale_pos {A V U Z C : ℝ}
    (hA : 0 < A) (hV : 0 < V) (hU : 0 < U) (hZ : 0 < Z) (hC : 0 < C) :
    0 < spectralScale A V U Z C := by
  unfold spectralScale
  positivity

/-- Exact positive-scale identity with U=nu*L. The 16*pi^2 in the actual
spectralScale square is retained. -/
theorem inverse_scale_ratio {A V nu L Z C : ℝ}
    (hA : 0 < A) (hV : 0 < V) (hnu : 0 < nu) (hL : 0 < L)
    (hZ : 0 < Z) (hC : 0 < C) :
    (1 / spectralScale
        A V (nu * L) Z C) ^ 2 / (1 + Z / L) / comparisonThreshold V Z =
      C ^ 2 * Z / (16 * Real.pi ^ 2 * A * nu * (L + Z) * (V + Z) ^ 2) := by
  have hnormalizer : 1 + Z / L ≠ 0 := (show 0 < 1 + Z / L by positivity).ne'
  have hLZ : L + Z ≠ 0 := (add_pos hL hZ).ne'
  have hVZ : V + Z ≠ 0 := (add_pos hV hZ).ne'
  rw [div_pow, one_pow,
    spectralScale_sq
      hA hV (mul_pos hnu hL) hZ hC]
  unfold comparisonThreshold
  field_simp [hA.ne', hV.ne', hnu.ne', hL.ne', hZ.ne', hC.ne',
    Real.pi_ne_zero, hnormalizer, hLZ, hVZ]

/-- The same identity in the literal dictionary L=U/nu. -/
theorem inverse_scale_ratio_divisor {A V U nu Z C : ℝ}
    (hA : 0 < A) (hV : 0 < V) (hU : 0 < U) (hnu : 0 < nu)
    (hZ : 0 < Z) (hC : 0 < C) :
    (1 / spectralScale A V U Z C) ^ 2 /
        (1 + Z / (U / nu)) / comparisonThreshold V Z =
      C ^ 2 * Z / (16 * Real.pi ^ 2 * A * nu * (U / nu + Z) * (V + Z) ^ 2) := by
  have hcancel : nu * (U / nu) = U := by field_simp [hnu.ne']
  simpa only [hcancel] using inverse_scale_ratio hA hV hnu (div_pos hU hnu) hZ hC

theorem weight_pos {X Z L : ℝ} (hX : 0 ≤ X) (hZ : 0 < Z) (hL : 0 < L) :
    0 < weight X Z L := by
  have hroot : 0 < Real.sqrt (1 + Z / L) := Real.sqrt_pos.mpr (by positivity)
  unfold weight
  exact sq_pos_of_pos (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hX hroot.le))

/-- The only estimate on the enlarged weight is (1+q)^2<=2+2*q^2.
Threshold comparability then supplies the factor 8 in the second term. -/
theorem weight_ratio_le {X V Z L : ℝ}
    (hV : 0 < V) (hZ : 0 < Z) (hL : 0 < L) :
    weight X Z L / threshold V Z ≤
      2 / threshold V Z + 8 * (X ^ 2 / (1 + Z / L) / comparisonThreshold V Z) := by
  have hT : 0 < threshold V Z := threshold_pos hV
  have hQ : 0 < comparisonThreshold V Z := comparisonThreshold_pos hV hZ
  have hK : 0 < 1 + Z / L := by positivity
  have hsqrt : Real.sqrt (1 + Z / L) ^ 2 = 1 + Z / L := Real.sq_sqrt hK.le
  have hweight : weight X Z L ≤ 2 + 2 * (X ^ 2 / (1 + Z / L)) := by
    have hsq := sq_nonneg (1 - X / Real.sqrt (1 + Z / L))
    have hquot : (X / Real.sqrt (1 + Z / L)) ^ 2 = X ^ 2 / (1 + Z / L) := by
      rw [div_pow, hsqrt]
    unfold weight
    nlinarith only [hsq, hquot]
  have hcomp := comparison_le_four_threshold hV hZ
  have hB : 0 ≤ X ^ 2 / (1 + Z / L) := div_nonneg (sq_nonneg X) hK.le
  have hterm : (2 * (X ^ 2 / (1 + Z / L))) / threshold V Z ≤
      (8 * (X ^ 2 / (1 + Z / L))) / comparisonThreshold V Z := by
    apply (div_le_div_iff₀ hT hQ).mpr
    have h := mul_le_mul_of_nonneg_left hcomp (mul_nonneg (show 0 ≤ (2 : ℝ) by norm_num) hB)
    nlinarith only [h]
  calc
    weight X Z L / threshold V Z ≤ (2 + 2 * (X ^ 2 / (1 + Z / L))) / threshold V Z := by
      exact (div_le_div_iff₀ hT hT).mpr
        (mul_le_mul_of_nonneg_right hweight hT.le)
    _ = 2 / threshold V Z + (2 * (X ^ 2 / (1 + Z / L))) / threshold V Z := by ring
    _ ≤ 2 / threshold V Z + (8 * (X ^ 2 / (1 + Z / L))) / comparisonThreshold V Z :=
      add_le_add le_rfl hterm
    _ = 2 / threshold V Z + 8 * (X ^ 2 / (1 + Z / L) / comparisonThreshold V Z) := by ring

/-- Explicit actual-geometry bound. There is no suppressed pi constant. -/
theorem spectral_weight_ratio_le {A V nu L Z C : ℝ}
    (hA : 0 < A) (hV : 0 < V) (hnu : 0 < nu) (hL : 0 < L)
    (hZ : 0 < Z) (hC : 0 < C) :
    spectralWeight A V (nu * L) Z C L / threshold V Z ≤ ratioBound A nu L V Z C := by
  have h := weight_ratio_le
    (X := 1 / spectralScale
      A V (nu * L) Z C) hV hZ hL
  rw [inverse_scale_ratio hA hV hnu hL hZ hC] at h
  exact h

/-- The actual physical weight in the common clipped positive quadratic
form. In particular, the residue/divisor factor is still present in
`ratioBound`, ready to cancel only after multiplying the two norms. -/
theorem commonBlock_physical_tauEnergy_le {ι : Type*} [Fintype ι]
    (J j : ℕ) (ω bound : ℝ) {A V nu L Z C : ℝ}
    (hA : 0 < A) (hV : 0 < V) (hnu : 0 < nu) (hL : 0 < L)
    (hZ : 0 < Z) (hC : 0 < C)
    (lambda : ι → ℝ) (hlambda : ∀ i, (975 : ℝ) / 4096 ≤ lambda i)
    (a : ι → ℕ → ℂ)
    (full_uniform : ∀ ρ : ℝ,
      weightedEnergy (fullBlock j) ρ (threshold V Z) (fun i => tau (lambda i)) a ≤ bound) :
    weightedEnergy (commonBlock J j) ω (spectralWeight A V (nu * L) Z C L)
        (fun i => tau (lambda i)) a ≤
      (2 + Real.log (period j)) ^ 2 *
        max 1 (ratioBound A nu L V Z C ^ (7 / 32 : ℝ)) * bound := by
  have hscale := actual_spectralScale_pos hA hV (mul_pos hnu hL) hZ hC
  have hW : 0 < spectralWeight A V (nu * L) Z C L :=
    weight_pos (div_nonneg (by norm_num) hscale.le) hZ hL
  have hT : 0 < threshold V Z := threshold_pos hV
  have hbound : 0 ≤ bound :=
    (weightedEnergy_nonneg (fullBlock j) 0 hT.le (fun i => tau (lambda i)) a).trans
      (full_uniform 0)
  have hratio := spectral_weight_ratio_le hA hV hnu hL hZ hC
  have hmono :
      max 1 ((spectralWeight A V (nu * L) Z C L / threshold V Z) ^ (7 / 32 : ℝ)) ≤
        max 1 (ratioBound A nu L V Z C ^ (7 / 32 : ℝ)) := by
    apply max_le_max le_rfl
    exact Real.rpow_le_rpow (div_nonneg hW.le hT.le) hratio (by norm_num)
  refine (commonBlock_weightedEnergy_le J j ω bound hW hT
    (fun i => tau (lambda i)) (fun i => tau_nonneg _)
    (fun i => tau_le_seven_thirtyseconds (hlambda i)) a full_uniform).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmono (sq_nonneg _)) hbound

/-- The `A*ν` factor cancels in the second exceptional term after its
power is multiplied by the geometric ratio. The complete `16π²` remains. -/
theorem packet_power_cancellation {A V nu L Z C cap : ℝ}
    (hA : 0 < A) (hV : 0 < V) (hnu : 0 < nu) (hL : 0 < L)
    (hZ : 0 < Z) :
    (A * nu) ^ cap *
        (C ^ 2 * Z / (16 * Real.pi ^ 2 * A * nu * (L + Z) * (V + Z) ^ 2)) ^ cap =
      (C ^ 2 * Z / (16 * Real.pi ^ 2 * (L + Z) * (V + Z) ^ 2)) ^ cap := by
  rw [← Real.mul_rpow (mul_nonneg hA.le hnu.le) (by positivity)]
  congr 1
  field_simp [hA.ne', hnu.ne', (add_pos hL hZ).ne', (add_pos hV hZ).ne', Real.pi_ne_zero]

/-- The endpoint-corrected classical length. The original integer block
and its common additive phase are retained. -/
def classicalMScale (j : ℕ) : ℝ := ((2 : ℕ) ^ j : ℝ) - 1 / 2

theorem classicalMScale_bounds (j : ℕ) :
    (1 : ℝ) / 2 ≤ classicalMScale j ∧
      ((2 : ℕ) ^ j : ℝ) / 2 ≤ classicalMScale j ∧
      classicalMScale j ≤ ((2 : ℕ) ^ j : ℝ) := by
  have hvN : 1 ≤ (2 : ℕ) ^ j :=
    Nat.succ_le_iff.mpr (pow_pos (by norm_num : 0 < (2 : ℕ)) j)
  have hv : (1 : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hvN
  simp only [classicalMScale, Nat.cast_ofNat]
  constructor
  · linarith only [hv]
  constructor <;> linarith only [hv]

/-- The existing exact Fourier support identity, with the classical
length made explicit. It includes `j = 0` and the integer `m = 1`. -/
theorem fullBlock_classical_support (j m : ℕ) :
    m ∈ fullBlock j ↔ (m : ℝ) ∈ Set.Ioc (classicalMScale j) (2 * classicalMScale j) := by
  simpa [classicalMScale] using mem_fullBlock_iff_classical_interval j m

/-- Two fixed level scales cover the closed physical plateau. -/
def classicalLevelScale (Z : ℝ) (lower : Bool) : ℝ := if lower then Z / 2 else Z

theorem classicalLevelScale_bounds {Z : ℝ} (hZ : 1 ≤ Z) (lower : Bool) :
    (1 : ℝ) / 2 ≤ classicalLevelScale Z lower ∧
      Z / 2 ≤ classicalLevelScale Z lower ∧ classicalLevelScale Z lower ≤ Z := by
  cases lower <;> simp only [classicalLevelScale, Bool.false_eq_true, if_false, if_true]
  · constructor
    · linarith
    exact ⟨by linarith, le_rfl⟩
  · exact ⟨by linarith, le_rfl, by linarith⟩

theorem level_plateau_classical_cover {z Z : ℝ} (hZ : 0 < Z)
    (hz : z ∈ Set.Icc Z (2 * Z)) :
    z ∈ Set.Ioc (Z / 2) Z ∨ z ∈ Set.Ioc Z (2 * Z) := by
  by_cases he : z = Z
  · exact Or.inl ⟨by rw [he]; linarith, he.le⟩
  · exact Or.inr ⟨lt_of_le_of_ne hz.1 (Ne.symm he), hz.2⟩

/-- The endpoint comparison is extracted from archived
`Part3OriginalClassicalSpectralSupports.lean`, without its old packet imports. -/
theorem physical_threshold_le_four_classical (j : ℕ) (Z : ℝ) (lower : Bool) :
    threshold ((2 : ℕ) ^ j : ℝ) Z ≤
      4 * threshold (classicalMScale j) (classicalLevelScale Z lower) := by
  let V : ℝ := ((2 : ℕ) ^ j : ℝ)
  let M : ℝ := classicalMScale j
  let Q : ℝ := classicalLevelScale Z lower
  change max V (Z ^ 2 / V) ≤ 4 * max M (Q ^ 2 / M)
  have hmb := classicalMScale_bounds j
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) hmb.1
  have hV : 0 < V := hM.trans_le hmb.2.2
  have hMV : M ≤ V := hmb.2.2
  have hhalf : V / 2 ≤ M := hmb.2.1
  have hVM : V ≤ 2 * M := by linarith only [hhalf]
  have hZQ : Z ^ 2 ≤ 4 * Q ^ 2 := by
    cases lower
    · change Z ^ 2 ≤ 4 * Z ^ 2
      nlinarith only [sq_nonneg Z]
    · change Z ^ 2 ≤ 4 * (Z / 2) ^ 2
      nlinarith only []
  have hratio : Z ^ 2 / V ≤ 4 * (Q ^ 2 / M) := by
    have hnum : Z ^ 2 * M ≤ (4 * Q ^ 2) * V :=
      (mul_le_mul_of_nonneg_right hZQ hM.le).trans
        (mul_le_mul_of_nonneg_left hMV (by positivity))
    have hh : Z ^ 2 / V ≤ (4 * Q ^ 2) / M := (div_le_div_iff₀ hV hM).mpr hnum
    exact hh.trans_eq (by ring)
  have hmaxM : M ≤ max M (Q ^ 2 / M) := le_max_left _ _
  have hmaxQ : Q ^ 2 / M ≤ max M (Q ^ 2 / M) := le_max_right _ _
  apply max_le
  · linarith only [hVM, hmaxM, hM]
  · linarith only [hratio, hmaxQ]

/-- The continuation factor with both the integer-block endpoint and
either classical level interval accounted for explicitly. -/
theorem classical_threshold_multiplier_le (j : ℕ) (lower : Bool)
    {Z W cap : ℝ} (hZ : 0 < Z) (hW : 0 < W) (hcap : 0 ≤ cap) :
    max 1 ((W / threshold (classicalMScale j) (classicalLevelScale Z lower)) ^ cap) ≤
      (16 : ℝ) ^ cap *
        (1 + (((2 : ℕ) ^ j : ℝ) * W / (((2 : ℕ) ^ j : ℝ) + Z) ^ 2) ^ cap) := by
  let V : ℝ := ((2 : ℕ) ^ j : ℝ)
  let T := threshold (classicalMScale j) (classicalLevelScale Z lower)
  have hV : 0 < V := by dsimp [V]; positivity
  have hM : 0 < classicalMScale j :=
    lt_of_lt_of_le (by norm_num) (classicalMScale_bounds j).1
  have hT : 0 < T := threshold_pos hM
  have hQ : 0 < comparisonThreshold V Z := comparisonThreshold_pos hV hZ
  have hcomparison : comparisonThreshold V Z ≤ 16 * T := by
    calc
      _ ≤ 4 * threshold V Z := comparison_le_four_threshold hV hZ
      _ ≤ 4 * (4 * T) :=
        mul_le_mul_of_nonneg_left (physical_threshold_le_four_classical j Z lower) (by norm_num)
      _ = _ := by ring
  have hratio : W / T ≤ 16 * (W / comparisonThreshold V Z) := by
    calc
      _ ≤ (16 * W) / comparisonThreshold V Z :=
        (div_le_div_iff₀ hT hQ).mpr (by
          nlinarith only [mul_le_mul_of_nonneg_left hcomparison hW.le])
      _ = _ := by ring
  have hid : W / comparisonThreshold V Z = V * W / (V + Z) ^ 2 := by
    unfold comparisonThreshold
    field_simp [hV.ne', (add_pos hV hZ).ne']
  have hconstant : 1 ≤ (16 : ℝ) ^ cap := Real.one_le_rpow (by norm_num) hcap
  have hpower := Real.rpow_nonneg (div_nonneg hW.le hQ.le) cap
  change max 1 ((W / T) ^ cap) ≤ (16 : ℝ) ^ cap * (1 + (V * W / (V + Z) ^ 2) ^ cap)
  rw [← hid]
  apply max_le
  · nlinarith only [hconstant, hpower,
      mul_nonneg (le_trans zero_le_one hconstant) hpower]
  · calc
      _ ≤ (16 * (W / comparisonThreshold V Z)) ^ cap :=
        Real.rpow_le_rpow (div_nonneg hW.le hT.le) hratio hcap
      _ = (16 : ℝ) ^ cap * (W / comparisonThreshold V Z) ^ cap :=
        Real.mul_rpow (by norm_num) (div_nonneg hW.le hQ.le)
      _ ≤ _ := by nlinarith only [hconstant]

/-- One of the two classical level intervals yields the physical common
interval bound, including the endpoint constants. The other interval uses
the same theorem with the other Boolean value and the same common phase. -/
theorem commonBlock_classical_tauEnergy_le {ι : Type*} [Fintype ι]
    (J j : ℕ) (lower : Bool) (ω bound : ℝ) {Z W : ℝ}
    (hZ : 0 < Z) (hW : 0 < W)
    (lambda : ι → ℝ) (hlambda : ∀ i, (975 : ℝ) / 4096 ≤ lambda i)
    (a : ι → ℕ → ℂ)
    (full_uniform : ∀ ρ : ℝ,
      weightedEnergy (fullBlock j) ρ
        (threshold (classicalMScale j) (classicalLevelScale Z lower))
        (fun i => tau (lambda i)) a ≤ bound) :
    weightedEnergy (commonBlock J j) ω W (fun i => tau (lambda i)) a ≤
      (2 + Real.log (period j)) ^ 2 * (16 : ℝ) ^ (7 / 32 : ℝ) *
        (1 + (((2 : ℕ) ^ j : ℝ) * W / (((2 : ℕ) ^ j : ℝ) + Z) ^ 2) ^ (7 / 32 : ℝ)) *
        bound := by
  have hM : 0 < classicalMScale j :=
    lt_of_lt_of_le (by norm_num) (classicalMScale_bounds j).1
  have hT := threshold_pos (Z := classicalLevelScale Z lower) hM
  have hbound : 0 ≤ bound :=
    (weightedEnergy_nonneg (fullBlock j) 0 hT.le (fun i => tau (lambda i)) a).trans
      (full_uniform 0)
  refine (commonBlock_weightedEnergy_le J j ω bound hW hT
    (fun i => tau (lambda i)) (fun i => tau_nonneg _)
    (fun i => tau_le_seven_thirtyseconds (hlambda i)) a full_uniform).trans ?_
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (classical_threshold_multiplier_le j lower hZ hW (show (0 : ℝ) ≤ 7 / 32 by norm_num))
      (sq_nonneg (2 + Real.log (period j)))) hbound
  simpa only [mul_assoc] using h

/-- Restriction of the actual level map to one printed classical interval. -/
def levelCoefficients {ι : Type*} (level : ι → ℕ) (Q : ℝ)
    (a : ι → ℕ → ℂ) : ι → ℕ → ℂ := by
  classical
  exact fun i m => if (level i : ℝ) ∈ Set.Ioc Q (2 * Q) then a i m else 0

def levelEnergy {ι : Type*} [Fintype ι] (S : Finset ℕ) (ω W : ℝ)
    (exponent : ι → ℝ) (a : ι → ℕ → ℂ) (level : ι → ℕ) (Q : ℝ) : ℝ := by
  classical
  exact ∑ i, if (level i : ℝ) ∈ Set.Ioc Q (2 * Q) then
    W ^ exponent i * ‖∑ m ∈ S, phaseAt ω m * a i m‖ ^ 2 else 0

theorem weightedEnergy_levelCoefficients {ι : Type*} [Fintype ι]
    (S : Finset ℕ) (ω W : ℝ) (exponent : ι → ℝ) (a : ι → ℕ → ℂ)
    (level : ι → ℕ) (Q : ℝ) :
    weightedEnergy S ω W exponent (levelCoefficients level Q a) =
      levelEnergy S ω W exponent a level Q := by
  classical
  unfold weightedEnergy levelEnergy
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (level i : ℝ) ∈ Set.Ioc Q (2 * Q)
  · simp [levelCoefficients, hi]
  · simp [levelCoefficients, hi]

/-- The closed physical level plateau is partitioned exactly into the
two classical intervals. The boundary level `Z` belongs to the lower one. -/
theorem levelEnergy_plateau_partition {ι : Type*} [Fintype ι]
    (S : Finset ℕ) (ω W : ℝ) (exponent : ι → ℝ) (a : ι → ℕ → ℂ)
    (level : ι → ℕ) {Z : ℝ} (hZ : 0 < Z)
    (hlevel : ∀ i, (level i : ℝ) ∈ Set.Icc Z (2 * Z)) :
    weightedEnergy S ω W exponent a =
      levelEnergy S ω W exponent a level (Z / 2) + levelEnergy S ω W exponent a level Z := by
  classical
  unfold weightedEnergy levelEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hid : 2 * (Z / 2) = Z := by ring
  simp only [hid]
  rcases level_plateau_classical_cover hZ (hlevel i) with hlo | hhi
  · have hn : ¬ (level i : ℝ) ∈ Set.Ioc Z (2 * Z) := fun hh => not_lt_of_ge hlo.2 hh.1
    simp [hlo, hn]
  · have hn : ¬ (level i : ℝ) ∈ Set.Ioc (Z / 2) Z := fun hh => not_lt_of_ge hh.2 hhi.1
    simp [hhi, hn]

/-- Both classical level inputs now supply the original closed-plateau
energy. The two windows retain the same interval and additive phase, and
their exact positive energies add before the common bound is applied. -/
theorem commonBlock_plateau_tauEnergy_le {ι : Type*} [Fintype ι]
    (J j : ℕ) (ω bound : ℝ) {Z W : ℝ} (hZ : 1 ≤ Z) (hW : 0 < W)
    (level : ι → ℕ) (hlevel : ∀ i, (level i : ℝ) ∈ Set.Icc Z (2 * Z))
    (lambda : ι → ℝ) (hlambda : ∀ i, (975 : ℝ) / 4096 ≤ lambda i)
    (a : ι → ℕ → ℂ)
    (full_uniform : ∀ (lower : Bool) (ρ : ℝ),
      levelEnergy (fullBlock j) ρ
        (threshold (classicalMScale j) (classicalLevelScale Z lower))
        (fun i => tau (lambda i)) a level (classicalLevelScale Z lower) ≤ bound) :
    weightedEnergy (commonBlock J j) ω W (fun i => tau (lambda i)) a ≤
      2 * ((2 + Real.log (period j)) ^ 2 * (16 : ℝ) ^ (7 / 32 : ℝ) *
        (1 + (((2 : ℕ) ^ j : ℝ) * W / (((2 : ℕ) ^ j : ℝ) + Z) ^ 2) ^ (7 / 32 : ℝ)) *
        bound) := by
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hwindow (lower : Bool) :
      levelEnergy (commonBlock J j) ω W (fun i => tau (lambda i)) a level
          (classicalLevelScale Z lower) ≤
        (2 + Real.log (period j)) ^ 2 * (16 : ℝ) ^ (7 / 32 : ℝ) *
          (1 + (((2 : ℕ) ^ j : ℝ) * W / (((2 : ℕ) ^ j : ℝ) + Z) ^ 2) ^ (7 / 32 : ℝ)) *
          bound := by
    have hfull (ρ : ℝ) :
        weightedEnergy (fullBlock j) ρ
          (threshold (classicalMScale j) (classicalLevelScale Z lower))
          (fun i => tau (lambda i)) (levelCoefficients level (classicalLevelScale Z lower) a) ≤
            bound := by
      rw [weightedEnergy_levelCoefficients]
      exact full_uniform lower ρ
    have h := commonBlock_classical_tauEnergy_le J j lower ω bound hZpos hW lambda hlambda
      (levelCoefficients level (classicalLevelScale Z lower) a) hfull
    rwa [weightedEnergy_levelCoefficients] at h
  rw [levelEnergy_plateau_partition (commonBlock J j) ω W (fun i => tau (lambda i)) a
    level hZpos hlevel]
  have hlo := hwindow true
  have hhi := hwindow false
  simp only [classicalLevelScale, if_true, Bool.false_eq_true, if_false] at hlo hhi
  linarith

/-- An arbitrary common `Ioc` interval, with both classical level windows
and the two-prefix cost included. -/
theorem commonIoc_plateau_tauEnergy_le {ι : Type*} [Fintype ι]
    {lo hi : ℕ} (h : lo ≤ hi) (j : ℕ) (ω bound : ℝ)
    {Z W : ℝ} (hZ : 1 ≤ Z) (hW : 0 < W)
    (level : ι → ℕ) (hlevel : ∀ i, (level i : ℝ) ∈ Set.Icc Z (2 * Z))
    (lambda : ι → ℝ) (hlambda : ∀ i, (975 : ℝ) / 4096 ≤ lambda i)
    (a : ι → ℕ → ℂ)
    (full_uniform : ∀ (lower : Bool) (ρ : ℝ),
      levelEnergy (fullBlock j) ρ
        (threshold (classicalMScale j) (classicalLevelScale Z lower))
        (fun i => tau (lambda i)) a level (classicalLevelScale Z lower) ≤ bound) :
    weightedEnergy (commonIoc lo hi j) ω W (fun i => tau (lambda i)) a ≤
      8 * ((2 + Real.log (period j)) ^ 2 * (16 : ℝ) ^ (7 / 32 : ℝ) *
        (1 + (((2 : ℕ) ^ j : ℝ) * W / (((2 : ℕ) ^ j : ℝ) + Z) ^ 2) ^ (7 / 32 : ℝ)) *
        bound) := by
  have hlo := commonBlock_plateau_tauEnergy_le lo j ω bound hZ hW level hlevel lambda hlambda
    a full_uniform
  have hhi := commonBlock_plateau_tauEnergy_le hi j ω bound hZ hW level hlevel lambda hlambda
    a full_uniform
  have hinterval := commonIoc_weightedEnergy_le_prefixes h j ω hW.le
    (fun i => tau (lambda i)) a
  linarith

end

end ImbalancedChen.Part3.ExceptionalWeightGeometry
