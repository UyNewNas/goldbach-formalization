import ImbalancedChen.P5NativeSelectedFourIntegerProfile
import ImbalancedChen.P5OccurrenceWordFourFactorLeibniz
import Mathlib

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
Dictionary from the actual ordered Family.eulerWord to the multiplicative
chart tensor, specialized to the native original247 selected rank-four
profile. The native tensor budget is already proved in batch 30c; it is not
silently identified with the syntactic Family Euler-word hypothesis.
Repeated coordinates and outer-to-inner word order are retained exactly.
-/
namespace ImbalancedChen.P5Z.NativeSelectedFourOrderedEuler
noncomputable section
open Classical Set Filter Topology
open scoped BigOperators
open AllWordAmbientOccurrenceBound OccurrenceWordFourFactorLeibniz
open AdmissibleAllRankIntegerGeometricFamily GroupedOccurrenceLogShift
open NativeSelectedFourIntegerProfile

/-- The tensor receives the head of the word as its outermost direction. -/
def wordDirections {m : ℕ} : (w : List (Fin m)) → Fin w.length → (Fin m → ℝ)
  | [] => Fin.elim0
  | a :: w => Fin.cons (Pi.single a 1) (wordDirections w)

theorem coordinate_norm_le {m : ℕ} (a : Fin m) :
    ‖(Pi.single a 1 : Fin m → ℝ)‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  by_cases hi : i = a <;> simp [Pi.single_apply, hi]

theorem wordDirections_norm_le {m : ℕ} (w : List (Fin m))
    (j : Fin w.length) : ‖wordDirections w j‖ ≤ 1 := by
  induction w with
  | nil => exact Fin.elim0 j
  | cons a w ih =>
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa [wordDirections] using coordinate_norm_le a
      · simpa [wordDirections] using ih j

/-- This is a true tensor identity, from Mathlib's derivative recursion and
constant multilinear evaluation, not a new definition of occWord. -/
theorem occWord_eq_tensor {m : ℕ} (f : (Fin m → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (w : List (Fin m)) (z : Fin m → ℝ) :
    occWord w f z = iteratedFDeriv ℝ w.length f z (wordDirections w) := by
  induction w generalizing z with
  | nil => simp [occWord, wordDirections]
  | cons a w ih =>
      have heq : occWord w f =
          fun y => iteratedFDeriv ℝ w.length f y (wordDirections w) := funext ih
      have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ w.length f) z :=
        hf.contDiffAt.differentiableAt_iteratedFDeriv (by simp)
      have heval : DifferentiableAt ℝ
          (fun y => iteratedFDeriv ℝ w.length f y (wordDirections w)) z :=
        hd.continuousMultilinear_apply_const (wordDirections w)
      change occOne a (occWord w f) z = _
      rw [heq, occOne_eq_fderiv a _ z heval]
      symm
      simpa [wordDirections] using
        (hd.iteratedFDeriv_succ_apply_left'
          (m := Fin.cons (Pi.single a 1) (wordDirections w)))

theorem abs_occWord_le_tensor_norm {m : ℕ} (f : (Fin m → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (w : List (Fin m)) (z : Fin m → ℝ) :
    |occWord w f z| ≤ ‖iteratedFDeriv ℝ w.length f z‖ := by
  rw [occWord_eq_tensor f hf w z]
  have hproduct : (∏ j, ‖wordDirections w j‖) ≤ (1 : ℝ) := by
    calc
      (∏ j, ‖wordDirections w j‖) ≤ ∏ _j : Fin w.length, (1 : ℝ) :=
        Finset.prod_le_prod (fun j hj => norm_nonneg _) (fun j hj => wordDirections_norm_le w j)
      _ = 1 := by simp
  calc
    |iteratedFDeriv ℝ w.length f z (wordDirections w)| =
        ‖iteratedFDeriv ℝ w.length f z (wordDirections w)‖ := Real.norm_eq_abs.symm
    _ ≤ ‖iteratedFDeriv ℝ w.length f z‖ * ∏ j, ‖wordDirections w j‖ :=
      (iteratedFDeriv ℝ w.length f z).le_opNorm (wordDirections w)
    _ ≤ ‖iteratedFDeriv ℝ w.length f z‖ * 1 :=
      mul_le_mul_of_nonneg_left hproduct (norm_nonneg _)
    _ = _ := mul_one _

def multiplicativeChart {m : ℕ} (p : Fin m → ℝ) (z : Fin m → ℝ) : Fin m → ℝ :=
  fun i => p i * Real.exp (z i)

theorem groupProduct_identity {m : ℕ} (p z : Fin m → ℝ) (i : Fin m) :
    groupProduct (id : Fin m → Fin m) p i z = multiplicativeChart p z i := by
  simp [groupProduct, groupBase, groupLog, multiplicativeChart]

theorem multiplicativeChart_smooth {m : ℕ} (p : Fin m → ℝ) :
    ContDiff ℝ ∞ (multiplicativeChart p) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_const.mul (contDiff_apply ℝ ℝ i).exp

@[simp] theorem multiplicativeChart_zero {m : ℕ} (p : Fin m → ℝ) :
    multiplicativeChart p 0 = p := by
  funext i
  simp [multiplicativeChart]

/-- Existing original-owner grouped chain, with identity owner, gives the
ordered Euler word at the actual multiplicative chart point. -/
theorem orderedEuler_occurrence_dictionary {m : ℕ} (f : (Fin m → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (w : List (Fin m)) (p z : Fin m → ℝ) :
    eulerWord w f (multiplicativeChart p z) =
      occWord w (fun y => f (multiplicativeChart p y)) z := by
  simpa only [groupProduct_identity, List.map_id] using
    (occWord_ambient (id : Fin m → Fin m) p f hf w z).symm

theorem orderedEuler_tensor_dictionary {m : ℕ} (f : (Fin m → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (w : List (Fin m)) (p z : Fin m → ℝ) :
    eulerWord w f (multiplicativeChart p z) =
      iteratedFDeriv ℝ w.length (fun y => f (multiplicativeChart p y)) z
        (wordDirections w) := by
  rw [orderedEuler_occurrence_dictionary f hf w p z]
  exact occWord_eq_tensor _ (hf.comp (multiplicativeChart_smooth p)) w z

/-- The exact native original247/owner/mask profile is used here. -/
theorem native_orderedEuler_tensor (D : Data) (side : Bool) (N : ℕ)
    (w : List (Fin 4)) (p z : Fin 4 → ℝ) :
    eulerWord w (profile D side N) (multiplicativeChart p z) =
      iteratedFDeriv ℝ w.length
        (fun y => profile D side N (fun i => p i * Real.exp (y i))) z
        (wordDirections w) :=
  orderedEuler_tensor_dictionary (profile D side N) (profile_global_smooth D side N) w p z

/-- Coordinate owner maps, repeated HB roles and every occurrence count
reuse precisely the same ordered original-word dictionary. -/
theorem native_grouped_occurrence_dictionary {m : ℕ} (D : Data) (side : Bool)
    (N : ℕ) (owner : Fin m → Fin 4) (U : Fin m → ℝ)
    (w : List (Fin m)) (z : Fin m → ℝ) :
    occWord w (fun z => profile D side N (fun i => groupProduct owner U i z)) z =
      eulerWord (w.map owner) (profile D side N)
        (fun i => groupProduct owner U i z) :=
  occWord_ambient owner U (profile D side N) (profile_global_smooth D side N) w z

/-- A function locally zero has every ordered Euler word locally zero,
including on the nonpositive axes of the native zero extension. -/
theorem eulerOne_eventually_zero {m : ℕ} (i : Fin m)
    (f : (Fin m → ℝ) → ℝ) (p : Fin m → ℝ) (h : f =ᶠ[𝓝 p] 0) :
    eulerOne i f =ᶠ[𝓝 p] 0 := by
  filter_upwards [h.iteratedFDeriv ℝ 1] with y hy
  have hdf : fderiv ℝ f y = 0 := by
    ext v
    have hv := congrArg (fun L => L (fun _ : Fin 1 => v)) hy
    simpa using hv
  simp [eulerOne, hdf]

theorem eulerWord_eventually_zero {m : ℕ} (w : List (Fin m))
    (f : (Fin m → ℝ) → ℝ) (p : Fin m → ℝ) (h : f =ᶠ[𝓝 p] 0) :
    eulerWord w f =ᶠ[𝓝 p] 0 := by
  induction w with
  | nil => simpa [eulerWord] using h
  | cons i w ih => simpa [eulerWord] using eulerOne_eventually_zero i (eulerWord w f) p ih

theorem native_profile_eventually_zero_nonpositive (D : Data) (side : Bool)
    (N : ℕ) (p : Fin 4 → ℝ) (hnp : ∃ i, p i ≤ 0) :
    profile D side N =ᶠ[𝓝 p] 0 := by
  by_cases hN : 2 ≤ N
  · obtain ⟨i, hi⟩ := hnp
    have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    let L := (N : ℝ) ^ ((U1011OriginalFifteenNativeGridCells.lower : ℝ) - D.width)
    have hL : 0 < L := Real.rpow_pos_of_pos hNp _
    have hopen : IsOpen {x : Fin 4 → ℝ | x i < L} :=
      isOpen_lt (continuous_apply i) continuous_const
    filter_upwards [hopen.mem_nhds (hi.trans_lt hL)] with x hx
    change profile D side N x = 0
    by_contra hn
    have hs := (profile_support D side hn).2.1 i
    exact (not_lt_of_ge hx.le) hs
  · simp only [profile, if_neg hN]
    exact Filter.Eventually.of_forall (fun _ => rfl)

theorem native_eulerWord_zero_nonpositive (D : Data) (side : Bool) (N : ℕ)
    (w : List (Fin 4)) (p : Fin 4 → ℝ) (hnp : ∃ i, p i ≤ 0) :
    eulerWord w (profile D side N) p = 0 :=
  (eulerWord_eventually_zero w (profile D side N) p
    (native_profile_eventually_zero_nonpositive D side N p hnp)).eq_of_nhds

/-- Fixed-order uniform size now follows from the TRUE native tensor
supplier, rather than assuming a syntactic Euler-word budget. -/
theorem native_fixed_order_bound (D : Data) (r : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (side : Bool) (N : ℕ)
      (w : List (Fin 4)) (p : Fin 4 → ℝ), w.length = r →
        |eulerWord w (profile D side N) p| ≤ M := by
  obtain ⟨C, hC, hbound⟩ := native_mixed_chart_tensor D r
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let M : ℝ := (Real.log 2)⁻¹ ^ r * ((totalBoxCount D : ℝ) * (C / D.width ^ r))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro side N w p hw
  by_cases hN : 2 ≤ N
  · by_cases hp : ∀ i, 0 < p i
    · have hlog : Real.log (2 : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hN)
      have hinv : (Real.log (N : ℝ))⁻¹ ≤ (Real.log (2 : ℝ))⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hlog2 hlog
      have hscale : (Real.log (N : ℝ))⁻¹ ^ r ≤ (Real.log (2 : ℝ))⁻¹ ^ r :=
        pow_le_pow_left₀ (inv_nonneg.mpr (hlog2.le.trans hlog)) hinv
      have hchart : ContDiff ℝ ∞ (fun y => profile D side N (multiplicativeChart p y)) :=
        (profile_global_smooth D side N).comp (multiplicativeChart_smooth p)
      have heq := orderedEuler_occurrence_dictionary (profile D side N)
        (profile_global_smooth D side N) w p 0
      have hword := abs_occWord_le_tensor_norm
        (fun y => profile D side N (multiplicativeChart p y)) hchart w 0
      have hten := hbound side N hN p 0 hp
      have hcount :
          (ActualFourSignedCoverJetPayment.signedCoverBoxCount side D.rows D.state
            D.ownerMesh D.owner D.smoothMesh : ℝ) ≤ (totalBoxCount D : ℝ) := by
        exact_mod_cast side_boxCount_le D side
      rw [hw] at hword
      calc
        |eulerWord w (profile D side N) p| =
            |occWord w (fun y => profile D side N (multiplicativeChart p y)) 0| := by
              simpa using congrArg abs heq
        _ ≤ ‖iteratedFDeriv ℝ r
            (fun y => profile D side N (multiplicativeChart p y)) 0‖ := hword
        _ ≤ (Real.log (N : ℝ))⁻¹ ^ r *
            ((ActualFourSignedCoverJetPayment.signedCoverBoxCount side D.rows D.state
              D.ownerMesh D.owner D.smoothMesh : ℝ) * (C / D.width ^ r)) := hten
        _ ≤ M := by
          dsimp [M]
          exact mul_le_mul hscale
            (mul_le_mul_of_nonneg_right hcount (div_nonneg hC (pow_nonneg D.width_pos.le r)))
            (by positivity) (by positivity)
    · push_neg at hp
      rw [native_eulerWord_zero_nonpositive D side N w p hp, abs_zero]
      exact hM
  · have hz : profile D side N = 0 := by simp [profile, hN]
    have hez : eulerWord w (profile D side N) p = 0 :=
      (eulerWord_eventually_zero w (profile D side N) p
        (Filter.Eventually.of_forall (fun y => congrFun hz y))).eq_of_nhds
    rw [hez, abs_zero]
    exact hM

/-- This is the exact missing finite-order field, for the actual rank-four
native test. The exponent can be zero since all smoothing data D are fixed.
It supplies no absent ranks and no arithmetic CapPlan-to-u identification. -/
theorem native_mixedEuler (D : Data) (r : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (side : Bool) (N : ℕ)
      (w : List (Fin 4)) (p : Fin 4 → ℝ), w.length ≤ r →
        |eulerWord w (profile D side N) p| ≤ (C : ℝ) := by
  choose M hM hb using (fun n : Fin (r + 1) => native_fixed_order_bound D n.val)
  let B : ℝ := ∑ n : Fin (r + 1), M n
  have hB : 0 ≤ B := Finset.sum_nonneg (fun n hn => hM n)
  refine ⟨Nat.ceil B + 1, by omega, ?_⟩
  intro side N w p hw
  let i : Fin (r + 1) := ⟨w.length, by omega⟩
  have hi : |eulerWord w (profile D side N) p| ≤ M i := hb i side N w p rfl
  have his : M i ≤ B := Finset.single_le_sum (fun n hn => hM n) (Finset.mem_univ i)
  have hceil : B ≤ ((Nat.ceil B + 1 : ℕ) : ℝ) := by
    have hc := Nat.le_ceil B
    push_cast
    linarith
  exact hi.trans (his.trans hceil)

/-- The same native constant works before arbitrary occurrence rank, owner
multiplicity and dyadic scales. No factor depending on m or repeated owners
is introduced: mapping a word to its owners preserves its exact length. -/
theorem native_grouped_occurrence_budget (D : Data) (r : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (side : Bool) (N m : ℕ)
      (owner : Fin m → Fin 4) (U : Fin m → ℝ)
      (w : List (Fin m)) (z : Fin m → ℝ), w.length ≤ r →
        |occWord w (fun z => profile D side N
          (fun i => groupProduct owner U i z)) z| ≤ (C : ℝ) := by
  obtain ⟨C, hC, hb⟩ := native_mixedEuler D r
  refine ⟨C, hC, ?_⟩
  intro side N m owner U w z hw
  rw [native_grouped_occurrence_dictionary]
  apply hb
  simpa using hw

end
end ImbalancedChen.P5Z.NativeSelectedFourOrderedEuler
