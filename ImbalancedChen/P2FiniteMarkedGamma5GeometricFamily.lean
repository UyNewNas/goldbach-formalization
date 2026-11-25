import ImbalancedChen.P2Gamma5AdmissibleFamilyCore
import ImbalancedChen.P2FiniteMarkedGamma5IntegerSupport
import ImbalancedChen.P2FiniteMarkedGamma5AllRankEulerBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

A constructed instance of the original admissible geometric Family, with
its unchanged fully qualified structure and the accepted Gamma5 physical
profile. The old, two fresh, and rough slots retain their original Fin
numbering. One fixed old/tail split is active at its exact total rank;
other ranks are zero. Below the existing scaleThreshold the whole
function is zero, and above it the function is exactly finPhysicalProfile
with the positive cutoff T^a. No cutoff in the physical coordinates is
added to that profile.

The positive exponent and width are fixed for a Family. The natural
mixed-Euler constant is selected before the scale, logQ function, old/tail
split, active rank, Euler word and physical point. Its logarithmic
exponent is zero. The hypotheses are only the stated numerical parameter
conditions; no Family, source licence, support bound or derivative target
is assumed.

This sparse geometric Family does not identify all actual arithmetic
histories with its profile, prove the actual source plateau, pay a collar,
or supply a prime-product estimate. Those source and distribution
obligations remain separate.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5GeometricFamily

noncomputable section
open Finset Real
open P2FiniteMarkedGamma5EulerWordBudget
open P2FiniteMarkedGamma5AllRankEulerBudget
open P2FiniteMarkedGamma5IntegerSupport
open P5Z.AdmissibleAllRankIntegerGeometricFamily
open scoped Classical BigOperators ContDiff

/-- The original physical profile at its own total rank and above the
existing scale threshold. The rank cast is only transport of the same
Fin coordinates along equality, with no permutation or lost slot. -/
def ambient (a width : ℝ) (logQ : ℕ → ℝ) (k r T d : ℕ) :
    (Fin d → ℝ) → ℝ :=
  if hd : d = k + (2 + r) then
    if scaleThreshold a ≤ (T : ℝ) then
      fun v => finPhysicalProfile (k := k) (r := r)
        (logQ T) (T : ℝ) width ((T : ℝ) ^ a)
        (fun i => v (Fin.cast hd.symm i))
    else 0
  else 0

/-- Exact function equality at the intended rank, not only equality on
prime tuples or on a restricted support. -/
theorem ambient_at_rank (a width : ℝ) (logQ : ℕ → ℝ) (k r T : ℕ)
    (hT : scaleThreshold a ≤ (T : ℝ)) :
    ambient a width logQ k r T (k + (2 + r)) =
      finPhysicalProfile (k := k) (r := r)
        (logQ T) (T : ℝ) width ((T : ℝ) ^ a) := by
  simp [ambient, hT]

theorem ambient_zero_of_rank_ne (a width : ℝ) (logQ : ℕ → ℝ) (k r T d : ℕ)
    (hd : d ≠ k + (2 + r)) : ambient a width logQ k r T d = 0 := by
  simp [ambient, hd]

/-- The only scale truncation is below the explicit original threshold. -/
theorem ambient_zero_below_threshold (a width : ℝ) (logQ : ℕ → ℝ)
    (k r T d : ℕ) (hT : (T : ℝ) < scaleThreshold a) :
    ambient a width logQ k r T d = 0 := by
  simp [ambient, not_le.mpr hT]

/-- The scale truncation changes only a finite initial set of natural
scales. No whole-scale equality to the original profile is asserted. -/
theorem finite_below_threshold (a : ℝ) :
    Set.Finite {T : ℕ | (T : ℝ) < scaleThreshold a} := by
  apply (Set.finite_Iic (Nat.ceil (scaleThreshold a))).subset
  intro T hT
  change T ≤ Nat.ceil (scaleThreshold a)
  exact_mod_cast hT.le.trans (Nat.le_ceil (scaleThreshold a))

theorem ambient_smooth {a width : ℝ} (ha : 0 < a) (logQ : ℕ → ℝ)
    (k r T d : ℕ) : ContDiff ℝ ∞ (ambient a width logQ k r T d) := by
  by_cases hd : d = k + (2 + r)
  · subst d
    by_cases hT : scaleThreshold a ≤ (T : ℝ)
    · rw [ambient_at_rank a width logQ k r T hT]
      have hT0 : 0 < (T : ℝ) := zero_lt_one.trans (scaleThreshold_bounds ha hT).1
      exact contDiff_finPhysicalProfile (logQ T) (T : ℝ) width
        (rpow_pos_of_pos hT0 a)
    · rw [ambient_zero_below_threshold a width logQ k r T _ (lt_of_not_ge hT)]
      exact contDiff_const
  · rw [ambient_zero_of_rank_ne a width logQ k r T d hd]
    exact contDiff_const

/-- The original positive floor and complete-product gate discharge the
unchanged Family support field, with constants 1/2 and exp(1). -/
theorem ambient_support {a width : ℝ} (ha : 0 < a) (hw : 0 < width)
    (hw1 : width ≤ 1) (logQ : ℕ → ℝ) (k r T d : ℕ)
    {v : Fin d → ℝ} (hne : ambient a width logQ k r T d v ≠ 0) :
    (∀ i, (1 / 2 : ℝ) * (T : ℝ) ^ a ≤ v i) ∧
      (∏ i, v i) ≤ exp 1 * (T : ℝ) := by
  by_cases hd : d = k + (2 + r)
  · subst d
    by_cases hT : scaleThreshold a ≤ (T : ℝ)
    · rw [ambient_at_rank a width logQ k r T hT] at hne
      have hT0 : 0 < (T : ℝ) := zero_lt_one.trans (scaleThreshold_bounds ha hT).1
      obtain ⟨hfloor, hproduct⟩ := finPhysicalProfile_nonzero_support
        (rpow_pos_of_pos hT0 a) hT0 hw hne
      refine ⟨?_, ?_⟩
      · intro i
        linarith only [(hfloor i).le]
      · exact hproduct.le.trans
          (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hw1) hT0.le)
    · exact (hne (congrFun
        (ambient_zero_below_threshold a width logQ k r T _ (lt_of_not_ge hT)) v)).elim
  · exact (hne (congrFun (ambient_zero_of_rank_ne a width logQ k r T d hd) v)).elim

/-- Finite prime support is inherited from the proved finite support on
all natural tuples; the original Family weight has no new prime filter. -/
theorem ambient_finite_prime_support {a width : ℝ} (ha : 0 < a)
    (hw : 0 < width) (logQ : ℕ → ℝ) (k r T d : ℕ) :
    Set.Finite {u : Fin d → ℕ | (∀ i, (u i).Prime) ∧
      ambient a width logQ k r T d (fun i => (u i : ℝ)) ≠ 0} := by
  by_cases hd : d = k + (2 + r)
  · subst d
    by_cases hT : scaleThreshold a ≤ (T : ℝ)
    · rw [ambient_at_rank a width logQ k r T hT]
      have hT0 : 0 < (T : ℝ) := zero_lt_one.trans (scaleThreshold_bounds ha hT).1
      exact finite_prime_support k r (logQ T) (rpow_pos_of_pos hT0 a) hT0 hw
    · rw [ambient_zero_below_threshold a width logQ k r T _ (lt_of_not_ge hT)]
      simp
  · rw [ambient_zero_of_rank_ne a width logQ k r T d hd]
    simp

/-- The natural constant precedes every moving scale, logQ, old/tail
split and rank. Width is fixed before the constant is chosen. This is
the accepted bounded-rank budget with a natural ceiling, not a new
derivative hypothesis. -/
theorem ambient_mixedEuler_budget (K : ℕ) (width : ℝ) (hw : 0 < width)
    (m : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (a : ℝ), 0 < a → ∀ (logQ : ℕ → ℝ) (k r : ℕ),
      k + 2 + r ≤ K → ∀ (T d : ℕ) (w : List (Fin d)) (v : Fin d → ℝ),
      w.length ≤ m →
      |eulerWord w (ambient a width logQ k r T d) v| ≤ (C : ℝ) := by
  obtain ⟨C0, _hC0, H⟩ := finPhysicalProfile_boundedRank_mixedEuler_budget K m
  let C : ℕ := Nat.ceil (C0 * (1 + width⁻¹) ^ m) + 1
  have hC : 0 < C := by dsimp [C]; omega
  have hround : C0 * (1 + width⁻¹) ^ m ≤ (C : ℝ) := by
    calc
      _ ≤ (Nat.ceil (C0 * (1 + width⁻¹) ^ m) : ℝ) := Nat.le_ceil _
      _ ≤ (C : ℝ) := by
        dsimp [C]
        exact_mod_cast Nat.le_succ (Nat.ceil (C0 * (1 + width⁻¹) ^ m))
  refine ⟨C, hC, ?_⟩
  intro a ha logQ k r hkr T d w v hwm
  by_cases hd : d = k + (2 + r)
  · subst d
    by_cases hT : scaleThreshold a ≤ (T : ℝ)
    · rw [ambient_at_rank a width logQ k r T hT]
      have hT0 : 0 < (T : ℝ) := zero_lt_one.trans (scaleThreshold_bounds ha hT).1
      exact (H k r hkr (logQ T) (T : ℝ) ((T : ℝ) ^ a) width
        (rpow_pos_of_pos hT0 a) hw w hwm v).trans hround
    · rw [ambient_zero_below_threshold a width logQ k r T _ (lt_of_not_ge hT),
        eulerWord_zero_eq]
      simpa only [Pi.zero_apply, abs_zero] using (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
  · rw [ambient_zero_of_rank_ne a width logQ k r T d hd, eulerWord_zero_eq]
    simpa only [Pi.zero_apply, abs_zero] using (Nat.cast_nonneg C : (0 : ℝ) ≤ C)

/-- An actual inhabitant of the original Family structure. The chosen
old/tail split has its exact rank inside Fin (K+1); all other ranks are
zero. No Family or licence is supplied as an input. -/
def geometricFamily (K k r : ℕ) (a width : ℝ) (logQ : ℕ → ℝ)
    (ha : 0 < a) (hw : 0 < width) (hw1 : width ≤ 1)
    (hkr : k + 2 + r ≤ K) : Family K where
  aStar := a
  aStar_pos := ha
  lower := 1 / 2
  lower_pos := by norm_num
  upper := exp 1
  upper_pos := exp_pos 1
  ambient := fun T d => ambient a width logQ k r T d.val
  smooth := fun T d => ambient_smooth (width := width) ha logQ k r T d.val
  support := fun T d _ hne => ambient_support ha hw hw1 logQ k r T d.val hne
  finitePrimeSupport := fun T d => ambient_finite_prime_support ha hw logQ k r T d.val
  mixedEuler := by
    intro m
    obtain ⟨C, hC, H⟩ := ambient_mixedEuler_budget K width hw m
    refine ⟨C, 0, hC, ?_⟩
    intro T d w v hwm
    simpa only [pow_zero, mul_one] using H a ha logQ k r hkr T d.val w v hwm

/-- At the intended rank and every admitted scale, the constructed
Family is exactly the original physical profile on the whole real
coordinate space. -/
theorem geometricFamily_at_rank (K k r : ℕ) (a width : ℝ) (logQ : ℕ → ℝ)
    (ha : 0 < a) (hw : 0 < width) (hw1 : width ≤ 1) (hkr : k + 2 + r ≤ K)
    (T : ℕ) (hT : scaleThreshold a ≤ (T : ℝ)) :
    (geometricFamily K k r a width logQ ha hw hw1 hkr).ambient T
        ⟨k + (2 + r), by omega⟩ =
      finPhysicalProfile (k := k) (r := r)
        (logQ T) (T : ℝ) width ((T : ℝ) ^ a) :=
  ambient_at_rank a width logQ k r T hT

theorem geometricFamily_zero_below_threshold (K k r : ℕ) (a width : ℝ)
    (logQ : ℕ → ℝ) (ha : 0 < a) (hw : 0 < width) (hw1 : width ≤ 1)
    (hkr : k + 2 + r ≤ K) (T : ℕ) (d : Fin (K + 1))
    (hT : (T : ℝ) < scaleThreshold a) :
    (geometricFamily K k r a width logQ ha hw hw1 hkr).ambient T d = 0 :=
  ambient_zero_below_threshold a width logQ k r T d.val hT

theorem geometricFamily_zero_of_rank_ne (K k r : ℕ) (a width : ℝ)
    (logQ : ℕ → ℝ) (ha : 0 < a) (hw : 0 < width) (hw1 : width ≤ 1)
    (hkr : k + 2 + r ≤ K) (T : ℕ) (d : Fin (K + 1))
    (hd : d.val ≠ k + (2 + r)) :
    (geometricFamily K k r a width logQ ha hw hw1 hkr).ambient T d = 0 :=
  ambient_zero_of_rank_ne a width logQ k r T d.val hd

end
end ImbalancedChen.P2FiniteMarkedGamma5GeometricFamily
