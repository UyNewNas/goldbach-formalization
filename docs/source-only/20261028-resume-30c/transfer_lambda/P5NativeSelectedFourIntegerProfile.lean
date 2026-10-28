import ImbalancedChen.P5PositiveFourProfileLocalZeroSmooth
import ImbalancedChen.P5ActualFourNativeBoxFullNorm
import ImbalancedChen.P5OriginalFourSelectedSmoothWBindingGap
import ImbalancedChen.P5LicensedOriginalIntegerProfile

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
This constructs the ORIGINAL retained-mask smooth cover from its native
state, native owner cell, selected row set, and actual smoothing mesh.
The independent test tuple u is never identified with a physical mark t.
The construction is rank FOUR. No zero-padding of the other ranks is
used to claim an all-rank native Family.
-/
namespace ImbalancedChen.P5Z.NativeSelectedFourIntegerProfile

noncomputable section
open Classical Set
open scoped BigOperators
open U11Integral U1011OriginalFifteenNativeGridCells
open U1011OriginalMaskSmoothBoxRealization
open ActualFourSmoothProfileEvaluation
open PositiveFourCandidateSupport PositiveFourProfileLocalZeroSmooth
open ActualFourNativeBoxFullNorm ActualFourSignedCoverJetPayment
open LicensedOriginalIntegerProfile
open OriginalFourSelectedSmoothWBindingGap

-- Every entry is native finite source data. There is no arbitrary W,
-- ambient, assumed support conclusion, or assumed derivative bound.
structure Data where
  rows : Finset FullMask.Row
  state : U1011OriginalSixteenAffineState.State
  ownerMesh : ℕ
  owner : Grid ownerMesh
  smoothMesh : ℕ
  width : ℝ
  width_pos : 0 < width
  width_lt_lower : width < (lower : ℝ)
  complete_margin : 4 * ((upper : ℝ) + width) ≤ 1

-- A concrete positive admissible width is available independently of N.
-- A later common refinement may choose another Data.width with the same
-- two explicitly recorded geometric constraints.
def defaultData (S : Finset FullMask.Row)
    (s : U1011OriginalSixteenAffineState.State)
    (m : ℕ) (owner : Grid m) (n : ℕ) : Data where
  rows := S
  state := s
  ownerMesh := m
  owner := owner
  smoothMesh := n
  width := 1 / 1000
  width_pos := by norm_num
  width_lt_lower := by norm_num [lower]
  complete_margin := by norm_num [upper]

def profile (D : Data) (lowerSide : Bool) (N : ℕ) : (Fin 4 → ℝ) → ℝ :=
  if 2 ≤ N then
    positiveFourProfile lowerSide D.rows D.state D.ownerMesh D.owner
      D.smoothMesh N D.width else fun _ => 0

def integerWeight (D : Data) (lowerSide : Bool) (N : ℕ)
    (u : Fin 4 → ℕ) : ℝ := profile D lowerSide N (fun i => (u i : ℝ))

def primeWeight (D : Data) (lowerSide : Bool) (N : ℕ)
    (u : Fin 4 → Fin (N + 1)) : ℝ :=
  profile D lowerSide N (fun i => ((u i).val : ℝ))

theorem profile_global_smooth (D : Data) (lowerSide : Bool) (N : ℕ) :
    ContDiff ℝ ∞ (profile D lowerSide N) := by
  by_cases hN : 2 ≤ N
  · simpa only [profile, if_pos hN] using
      positiveFourProfile_global_contDiff hN lowerSide D.rows D.state
        D.ownerMesh D.owner D.smoothMesh D.width_pos D.complete_margin
  · simp only [profile, if_neg hN]
    exact contDiff_const

theorem exponent_pos (D : Data) : 0 < (lower : ℝ) - D.width :=
  sub_pos.mpr D.width_lt_lower

theorem profile_support (D : Data) (lowerSide : Bool) {N : ℕ}
    {p : Fin 4 → ℝ} (hp : profile D lowerSide N p ≠ 0) :
    2 ≤ N ∧ (∀ i, (N : ℝ)^((lower : ℝ)-D.width) < p i) ∧
      (∏ i, p i) ≤ (N : ℝ) := by
  have hN : 2 ≤ N := by
    by_contra h
    exact hp (by simp [profile, h])
  have hs := positiveFourProfile_real_support hN lowerSide D.rows D.state
    D.ownerMesh D.owner D.smoothMesh D.width_pos D.complete_margin p
      (by simpa only [profile, if_pos hN] using hp)
  exact ⟨hN, hs⟩

-- Integer-bank finiteness is proved from the actual REAL support. It is
-- not a prime-only hypothesis on the extension Licence.
theorem profile_support_coordinate_le (D : Data) (lowerSide : Bool)
    {N : ℕ} {p : Fin 4 → ℝ} (hp : profile D lowerSide N p ≠ 0) :
    ∀ i, (1 : ℝ) ≤ p i ∧ p i ≤ (N : ℝ) := by
  obtain ⟨hN, hlo, hprod⟩ := profile_support D lowerSide hp
  have hbase : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow : (1 : ℝ) ≤ (N : ℝ)^((lower : ℝ)-D.width) :=
    Real.one_le_rpow hbase (exponent_pos D).le
  have hone (i : Fin 4) : (1 : ℝ) ≤ p i := hpow.trans (hlo i).le
  intro i
  refine ⟨hone i, ?_⟩
  have hrest : (1 : ℝ) ≤
      ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, p j :=
    Finset.one_le_prod (fun j hj => hone j)
  have heq := Finset.prod_erase_mul (Finset.univ : Finset (Fin 4)) p
    (Finset.mem_univ i)
  have hmul := mul_le_mul_of_nonneg_right hrest (zero_le_one.trans (hone i))
  calc
    p i = 1 * p i := (one_mul _).symm
    _ ≤ (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, p j) * p i := hmul
    _ = ∏ j : Fin 4, p j := heq
    _ ≤ (N : ℝ) := hprod

def integerBank (N : ℕ) : Finset (Fin 4 → ℕ) :=
  Fintype.piFinset (fun _ => Finset.Icc 1 N)

theorem integerWeight_mem_bank (D : Data) (lowerSide : Bool) (N : ℕ)
    (u : Fin 4 → ℕ) (hu : integerWeight D lowerSide N u ≠ 0) :
    u ∈ integerBank N := by
  apply Finset.mem_piFinset.mpr
  intro i
  obtain ⟨hlo, hhi⟩ := profile_support_coordinate_le D lowerSide hu i
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

theorem finite_integer_support (D : Data) (lowerSide : Bool) (N : ℕ) :
    Set.Finite {u : Fin 4 → ℕ | integerWeight D lowerSide N u ≠ 0} := by
  apply (integerBank N).finite_toSet.subset
  intro u hu
  exact integerWeight_mem_bank D lowerSide N u hu

theorem finite_prime_support (D : Data) (lowerSide : Bool) (N : ℕ) :
    Set.Finite {u : Fin 4 → ℕ |
      (∀ i, (u i).Prime) ∧ integerWeight D lowerSide N u ≠ 0} :=
  (finite_integer_support D lowerSide N).subset (fun u hu => hu.2)

def nativeLicence (D : Data) (lowerSide : Bool) (N : ℕ) :
    Licence 4 (integerWeight D lowerSide N) where
  ambient := profile D lowerSide N
  smooth := profile_global_smooth D lowerSide N
  agrees_on_primes := by intro u hu; rfl

theorem exact_native_prime_evaluation (D : Data) (lowerSide : Bool)
    {N : ℕ} (hN : 2 ≤ N) (u : Fin 4 → Fin (N+1))
    (hu : u ∈ Part3.labelledPrimeTuples 4 N) :
    primeWeight D lowerSide N u = currentMaskFourWeight lowerSide
      D.rows D.state D.ownerMesh D.owner D.smoothMesh N D.width u := by
  simpa only [primeWeight, profile, if_pos hN] using
    positiveFourProfile_eq_on_positive_primes lowerSide D.rows D.state
      D.ownerMesh D.owner D.smoothMesh N D.width u hu

-- This is the original same-mask approximation relation, not equality of
-- a sharp source indicator with a globally smooth real-variable function.
theorem native_prime_mask_sandwich (D : Data) {N : ℕ} (hN : 2 ≤ N)
    (u : Fin 4 → Fin (N+1)) (hu : u ∈ Part3.labelledPrimeTuples 4 N)
    (hlog : actualPrimeTupleLog N (fun i => (u i).val) ∈ cube) :
    primeWeight D true N u ≤
        retainedIndicator D.rows D.state D.ownerMesh D.owner
          (actualPrimeTupleLog N (fun i => (u i).val)) ∧
      retainedIndicator D.rows D.state D.ownerMesh D.owner
          (actualPrimeTupleLog N (fun i => (u i).val)) ≤
        primeWeight D false N u := by
  rw [exact_native_prime_evaluation D true hN u hu,
    exact_native_prime_evaluation D false hN u hu]
  exact original_mask_smooth_sandwich D.rows D.state D.ownerMesh D.owner
    D.smoothMesh D.width_pos hlog

-- A genuine constructor for the explicit native smooth cover's binding.
-- It does not identify an unrelated sharp/retrofitted selected W with it.
theorem native_cover_binding (D : Data) (lowerSide : Bool)
    {N : ℕ} (hN : 2 ≤ N) :
    OriginalFourSelectedSmoothWBinding N lowerSide D.rows D.state
      D.ownerMesh D.owner D.smoothMesh D.width
      (primeWeight D lowerSide N) (profile D lowerSide N) := by
  constructor
  · intro u hu
    rfl
  · intro p hp
    simp only [profile, if_pos hN, positiveFourProfile, if_pos hp]

-- The all-order native Fréchet supplier is attached to THIS selected
-- family, with its exact finite signed-row box count. Ordered eulerWord
-- identification is still a separate mathematical implementation step.
theorem native_mixed_chart_tensor (D : Data) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lowerSide : Bool) (N : ℕ), 2 ≤ N →
      ∀ p z : Fin 4 → ℝ, (∀ i, 0 < p i) →
      ‖iteratedFDeriv ℝ r
        (fun y => profile D lowerSide N (fun i => p i * Real.exp (y i))) z‖ ≤
        (Real.log (N : ℝ))⁻¹ ^ r *
          ((signedCoverBoxCount lowerSide D.rows D.state D.ownerMesh D.owner
            D.smoothMesh : ℝ) * (C / D.width ^ r)) := by
  obtain ⟨C, hC, hbound⟩ := exists_currentMaskFourProfile_euler_tensor_budget r
  refine ⟨C, hC, ?_⟩
  intro lowerSide N hN p z hp
  have heq :
      (fun y => profile D lowerSide N (fun i => p i * Real.exp (y i))) =
        fun y => currentMaskFourProfile lowerSide D.rows D.state D.ownerMesh
          D.owner D.smoothMesh N D.width (fun i => p i * Real.exp (y i)) := by
    funext y
    have hpos : ∀ i, 0 < p i * Real.exp (y i) :=
      fun i => mul_pos (hp i) (Real.exp_pos _)
    simp only [profile, if_pos hN, positiveFourProfile, if_pos hpos]
  rw [heq]
  exact hbound lowerSide D.rows D.state D.ownerMesh D.owner D.smoothMesh
    N D.width hN D.width_pos p z hp

def totalBoxCount (D : Data) : ℕ :=
  signedCoverBoxCount true D.rows D.state D.ownerMesh D.owner D.smoothMesh +
    signedCoverBoxCount false D.rows D.state D.ownerMesh D.owner D.smoothMesh

theorem side_boxCount_le (D : Data) (lowerSide : Bool) :
    signedCoverBoxCount lowerSide D.rows D.state D.ownerMesh D.owner
      D.smoothMesh ≤ totalBoxCount D := by
  cases lowerSide <;> simp only [totalBoxCount] <;> omega

-- Even the amplitude is derived for the explicit native cover, uniformly
-- before N and both orientations. There is no unconstrained Wnorm input.
theorem native_uniform_real_amplitude (D : Data) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (lowerSide : Bool) (N : ℕ) (p : Fin 4 → ℝ),
      |profile D lowerSide N p| ≤ M := by
  obtain ⟨C, hC, hbound⟩ := native_mixed_chart_tensor D 0
  refine ⟨(totalBoxCount D : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC, ?_⟩
  intro lowerSide N p
  by_cases hp : profile D lowerSide N p = 0
  · rw [hp, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hC
  · obtain ⟨hN, hlo, hprod⟩ := profile_support D lowerSide hp
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hpos : ∀ i, 0 < p i := fun i =>
      (Real.rpow_pos_of_pos hNpos _).trans (hlo i)
    have hm := hbound lowerSide N hN p 0 hpos
    have hvalue : |profile D lowerSide N p| ≤
        (signedCoverBoxCount lowerSide D.rows D.state D.ownerMesh D.owner
          D.smoothMesh : ℝ) * C := by
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero,
        div_one, one_mul, Pi.zero_apply, Real.exp_zero, mul_one] using hm
    exact hvalue.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast side_boxCount_le D lowerSide) hC)

theorem native_uniform_integer_amplitude (D : Data) :
    ∃ C : ℕ, 0 < C ∧ ∀ (lowerSide : Bool) (N : ℕ) (p : Fin 4 → ℝ),
      |profile D lowerSide N p| ≤ (C : ℝ) := by
  obtain ⟨M, hM, hbound⟩ := native_uniform_real_amplitude D
  refine ⟨Nat.ceil M + 1, by omega, ?_⟩
  intro lowerSide N p
  have hceil : M ≤ (Nat.ceil M : ℝ) := Nat.le_ceil M
  have hcast : (Nat.ceil M : ℝ) ≤ ((Nat.ceil M + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact (hbound lowerSide N p).trans (hceil.trans hcast)

end
end ImbalancedChen.P5Z.NativeSelectedFourIntegerProfile
