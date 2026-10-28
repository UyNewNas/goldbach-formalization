import ImbalancedChen.P5NativeSelectedFourOrderedEuler
import ImbalancedChen.P5PresievedRoughSmoothBoxAtoms
import Mathlib

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
Every member is the EXISTING production separated log-box atom, at its
actual residual rank. It is not the zero function inserted at an absent
rank. The association of a physical residual rank with an independent
original-prime PP caller must still be supplied by that source owner.
The present file proves derivatives of these genuine atoms without making
that absent caller association a coverage claim.
-/
namespace ImbalancedChen.P5Z.ActualRankLogAtomEuler
noncomputable section
open Classical Set Filter Topology
open scoped BigOperators
open PresievedRoughGateMeshReserve PresievedRoughSmoothBoxAtoms
open U1011CompactLogIntervalSmoothing
open NativeSelectedFourOrderedEuler
open AdmissibleAllRankIntegerGeometricFamily

/-- Actual existing log atom evaluated at real prime coordinates, with the
necessary real smooth zero extension. Both reserves and all cells remain. -/
def profile {r : ℕ} (inner : Bool) (δ a b : ℝ) (n : ℕ) (j : Grid r n)
    (N : ℕ) (p : Fin r → ℝ) : ℝ :=
  if 2 ≤ N then
    if ∀ i, 0 < p i then
      atom inner δ a b n j (fun i => Real.log (p i) / Real.log (N : ℝ))
    else 0
  else 0

/-- Exact evaluation on the existing production original-prime log atom.
There is no identification with a physical mark tuple in this equality. -/
theorem profile_integer_atom {r n : ℕ} (inner : Bool) (δ a b : ℝ)
    (j : Grid r n) {N : ℕ} (hN : 2 ≤ N) (p : Fin r → ℕ)
    (hp : ∀ i, 0 < p i) :
    profile inner δ a b n j N (fun i => (p i : ℝ)) =
      atom inner δ a b n j (actualPrimeTupleLog N p) := by
  have hpos : ∀ i, 0 < (p i : ℝ) := fun i => by exact_mod_cast hp i
  simp only [profile, if_pos hN, if_pos hpos, actualPrimeTupleLog]

theorem atom_nonzero_lower {r n : ℕ} {δ a b : ℝ} (hδ : 0 < δ)
    (inner : Bool) (j : Grid r n) (v : Fin r → ℝ)
    (hv : atom inner δ a b n j v ≠ 0) (i : Fin r) :
    logPrimeMeshLo a b n j i - δ < v i := by
  have hfac : weight inner δ (logPrimeMeshLo a b n j i)
      (logPrimeMeshHi a b n j i) (v i) ≠ 0 := by
    intro hz
    exact hv (Finset.prod_eq_zero (Finset.mem_univ i) hz)
  have hs : 0 ≤ shift inner δ := by cases inner <;> simp [shift, hδ.le]
  have hl := P4B.smoothGateUpperStep_nonzero_support hδ (mul_ne_zero_iff.mp hfac).1
  change -δ < v i - logPrimeMeshLo a b n j i - shift inner δ at hl
  linarith

/-- The exact positive floor is derived from the original atom endpoints. -/
theorem profile_zero_below_floor {r n : ℕ} {δ a b : ℝ} (hδ : 0 < δ)
    (inner : Bool) (j : Grid r n) {N : ℕ} (hN : 2 ≤ N)
    (p : Fin r → ℝ) (i : Fin r)
    (hi : p i ≤ Real.exp (Real.log (N : ℝ) * (logPrimeMeshLo a b n j i - δ))) :
    profile inner δ a b n j N p = 0 := by
  by_cases hp : ∀ i, 0 < p i
  · simp only [profile, if_pos hN, if_pos hp]
    by_contra hn
    have hl := atom_nonzero_lower hδ inner j _ hn i
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hiLog := Real.log_le_log (hp i) hi
    rw [Real.log_exp] at hiLog
    have hsmall : Real.log (p i) / Real.log (N : ℝ) ≤ logPrimeMeshLo a b n j i - δ :=
      (div_le_iff₀ hlog).mpr (by simpa only [mul_comm] using hiLog)
    exact (not_lt_of_ge hsmall) hl
  · simp [profile, hN, hp]

theorem profile_eventually_zero_nonpositive {r n : ℕ} {δ a b : ℝ} (hδ : 0 < δ)
    (inner : Bool) (j : Grid r n) (N : ℕ) (p : Fin r → ℝ)
    (hnp : ∃ i, p i ≤ 0) : profile inner δ a b n j N =ᶠ[𝓝 p] 0 := by
  by_cases hN : 2 ≤ N
  · obtain ⟨i, hi⟩ := hnp
    let L := Real.exp (Real.log (N : ℝ) * (logPrimeMeshLo a b n j i - δ))
    have hL : 0 < L := Real.exp_pos _
    have hopen : IsOpen {x : Fin r → ℝ | x i < L} :=
      isOpen_lt (continuous_apply i) continuous_const
    filter_upwards [hopen.mem_nhds (hi.trans_lt hL)] with x hx
    exact profile_zero_below_floor hδ inner j hN x i hx.le
  · simp only [profile, if_neg hN]
    exact Filter.Eventually.of_forall (fun _ => rfl)

theorem positive_orthant_open (r : ℕ) :
    IsOpen {p : Fin r → ℝ | ∀ i, 0 < p i} := by
  have heq : {p : Fin r → ℝ | ∀ i, 0 < p i} =
      ⋂ i : Fin r, {p : Fin r → ℝ | 0 < p i} := by ext p; simp
  rw [heq]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))

theorem profile_global_smooth {r n : ℕ} {δ a b : ℝ} (hδ : 0 < δ)
    (inner : Bool) (j : Grid r n) (N : ℕ) :
    ContDiff ℝ ∞ (profile inner δ a b n j N) := by
  by_cases hN : 2 ≤ N
  · apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : ∀ i, 0 < p i
    · have hcoord (i : Fin r) : ContDiffAt ℝ ∞
          (fun x : Fin r → ℝ => Real.log (x i) / Real.log (N : ℝ)) p :=
        ((Real.contDiffAt_log (hp i).ne').comp p
          (contDiff_apply ℝ ℝ i).contDiffAt).div_const _
      have hraw := (contDiff_atom inner δ a b n j).contDiffAt.comp p
        (contDiffAt_pi.mpr hcoord)
      have heq : profile inner δ a b n j N =ᶠ[𝓝 p]
          (fun x => atom inner δ a b n j (fun i => Real.log (x i) / Real.log (N : ℝ))) := by
        filter_upwards [(positive_orthant_open r).mem_nhds hp] with x hx
        simp [profile, hN, hx]
      exact hraw.congr_of_eventuallyEq heq
    · obtain ⟨i, hi⟩ := not_forall.mp hp
      exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Fin r → ℝ => (0 : ℝ)) p).
        congr_of_eventuallyEq (profile_eventually_zero_nonpositive hδ inner j N p
          ⟨i, le_of_not_gt hi⟩)
  · simp only [profile, if_neg hN]
    exact contDiff_const

/-- On the real positive multiplicative chart this is exactly the native
log atom after an affine map of slope 1/log N, not a new test definition. -/
theorem profile_multiplicative_identity {r n : ℕ} {δ a b : ℝ}
    (inner : Bool) (j : Grid r n) {N : ℕ} (hN : 2 ≤ N)
    (p : Fin r → ℝ) (hp : ∀ i, 0 < p i) :
    (fun z => profile inner δ a b n j N (multiplicativeChart p z)) =
      fun z => atom inner δ a b n j
        (fun i => (Real.log (p i) + z i) / Real.log (N : ℝ)) := by
  funext z
  have hz : ∀ i, 0 < multiplicativeChart p z i :=
    fun i => mul_pos (hp i) (Real.exp_pos _)
  simp only [profile, if_pos hN, if_pos hz]
  congr 1
  funext i
  rw [multiplicativeChart, Real.log_mul (hp i).ne' (Real.exp_pos _).ne', Real.log_exp]

theorem profile_orderedEuler_tensor {r n : ℕ} {δ a b : ℝ} (hδ : 0 < δ)
    (inner : Bool) (j : Grid r n) (N : ℕ) (w : List (Fin r)) (p z : Fin r → ℝ) :
    eulerWord w (profile inner δ a b n j N) (multiplicativeChart p z) =
      iteratedFDeriv ℝ w.length
        (fun y => profile inner δ a b n j N (multiplicativeChart p y)) z
          (wordDirections w) :=
  orderedEuler_tensor_dictionary _ (profile_global_smooth hδ inner j N) w p z

/-- The actual affine log scaling pays only log(2)^(-order), uniformly
before N, base point and chart point. The underlying atom tensor bound is
obtained from its existing smooth compact support, not assumed. -/
theorem exists_chart_tensor_budget {r n : ℕ} {δ a b : ℝ} (hδ : 0 < δ)
    (inner : Bool) (j : Grid r n) (q : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (N : ℕ), 2 ≤ N →
      ∀ p z : Fin r → ℝ, (∀ i, 0 < p i) →
        ‖iteratedFDeriv ℝ q
          (fun y => profile inner δ a b n j N (multiplicativeChart p y)) z‖ ≤ M := by
  obtain ⟨B, hB, hb⟩ := exists_atom_derivative_budget hδ inner a b n j q
  let K : ℝ := (Real.log 2)⁻¹
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hK : 0 ≤ K := (inv_pos.mpr hlog2).le
  refine ⟨B * K ^ q, mul_nonneg hB (pow_nonneg hK q), ?_⟩
  intro N hN p z hp
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlog : Real.log (2 : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hinv : (Real.log (N : ℝ))⁻¹ ≤ K := by
    simpa [K, one_div] using one_div_le_one_div_of_le hlog2 hlog
  let L : (Fin r → ℝ) →L[ℝ] (Fin r → ℝ) :=
    (Real.log (N : ℝ))⁻¹ • ContinuousLinearMap.id ℝ (Fin r → ℝ)
  let base : Fin r → ℝ := fun i => Real.log (p i) / Real.log (N : ℝ)
  let F : (Fin r → ℝ) → ℝ := fun x => atom inner δ a b n j (base + x)
  have hF : ContDiff ℝ ∞ F :=
    (contDiff_atom inner δ a b n j).comp (contDiff_const.add contDiff_id)
  have hL : ‖L‖ ≤ K := by
    apply ContinuousLinearMap.opNorm_le_bound L hK
    intro y
    change ‖(Real.log (N : ℝ))⁻¹ • y‖ ≤ K * ‖y‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlogN)]
    exact mul_le_mul_of_nonneg_right hinv (norm_nonneg y)
  have heq : (fun y => profile inner δ a b n j N (multiplicativeChart p y)) = F ∘ L := by
    rw [profile_multiplicative_identity inner j hN p hp]
    funext y
    dsimp [F, base, L, Function.comp_def]
    congr 1
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.id_apply]
    ring
  rw [heq, L.iteratedFDeriv_comp_right hF z (by simp)]
  have hn := (iteratedFDeriv ℝ q F (L z)).norm_compContinuousLinearMap_le
    (fun _ : Fin q => L)
  have hbase : ‖iteratedFDeriv ℝ q F (L z)‖ ≤ B := by
    dsimp only [F]
    rw [iteratedFDeriv_comp_add_left]
    exact hb _
  calc
    ‖(iteratedFDeriv ℝ q F (L z)).compContinuousLinearMap (fun _ : Fin q => L)‖ ≤
        ‖iteratedFDeriv ℝ q F (L z)‖ * ∏ _s : Fin q, ‖L‖ := hn
    _ ≤ B * K ^ q := by
      simpa using mul_le_mul hbase
        (by simpa using pow_le_pow_left₀ (norm_nonneg L) hL q)
        (by positivity) hB

theorem exists_fixed_order_euler_budget {r n : ℕ} {δ a b : ℝ} (hδ : 0 < δ)
    (inner : Bool) (j : Grid r n) (q : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (N : ℕ) (w : List (Fin r)) (p : Fin r → ℝ),
      w.length = q → |eulerWord w (profile inner δ a b n j N) p| ≤ M := by
  obtain ⟨M, hM, hb⟩ := exists_chart_tensor_budget hδ inner j q
  refine ⟨M, hM, ?_⟩
  intro N w p hw
  by_cases hN : 2 ≤ N
  · by_cases hp : ∀ i, 0 < p i
    · have heq := orderedEuler_occurrence_dictionary _ (profile_global_smooth hδ inner j N) w p 0
      have hn := abs_occWord_le_tensor_norm _
        ((profile_global_smooth hδ inner j N).comp (multiplicativeChart_smooth p)) w 0
      have hten := hb N hN p 0 hp
      rw [hw] at hn
      have hid : |eulerWord w (profile inner δ a b n j N) p| =
          |AllWordAmbientOccurrenceBound.occWord w
            (fun y => profile inner δ a b n j N (multiplicativeChart p y)) 0| := by
        simpa using congrArg abs heq
      rw [hid]
      exact hn.trans hten
    · push_neg at hp
      have hez := (eulerWord_eventually_zero w _ p
        (profile_eventually_zero_nonpositive hδ inner j N p hp)).eq_of_nhds
      rw [hez, abs_zero]
      exact hM
  · have hz : profile inner δ a b n j N = 0 := by simp [profile, hN]
    have hez := (eulerWord_eventually_zero w _ p
      (Filter.Eventually.of_forall (fun y => congrFun hz y))).eq_of_nhds
    rw [hez, abs_zero]
    exact hM

/-- Every actual atom key has a complete syntactic mixedEuler field at
its own genuine rank. No absent-rank zero profile is introduced. -/
theorem atom_mixedEuler {r n : ℕ} {δ a b : ℝ} (hδ : 0 < δ)
    (inner : Bool) (j : Grid r n) (q : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ N (w : List (Fin r)) p, w.length ≤ q →
      |eulerWord w (profile inner δ a b n j N) p| ≤ (C : ℝ) := by
  choose M hM hb using (fun d : Fin (q + 1) => exists_fixed_order_euler_budget hδ inner j d.val)
  let B : ℝ := ∑ d : Fin (q + 1), M d
  refine ⟨Nat.ceil B + 1, by omega, ?_⟩
  intro N w p hw
  let i : Fin (q + 1) := ⟨w.length, by omega⟩
  have h := hb i N w p rfl
  have hs : M i ≤ B := Finset.single_le_sum (fun d hd => hM d) (Finset.mem_univ i)
  have hc : B ≤ ((Nat.ceil B + 1 : ℕ) : ℝ) := by
    have hceil := Nat.le_ceil B
    push_cast
    linarith
  exact h.trans (hs.trans hc)

/-- This is a finite index for genuine existing atoms, not an asserted list
of all independent original-prime callers. That arithmetic association is
still owned by the exact source/caller module. -/
abbrev AtomKey (rMax n : ℕ) := Bool × (Σ r : Fin (rMax + 1), Grid r.val n)

theorem finite_rank_bank_mixedEuler {δ a b : ℝ} (hδ : 0 < δ)
    (rMax n q : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ key : AtomKey rMax n,
      ∀ N (w : List (Fin key.2.1.val)) p, w.length ≤ q →
        |eulerWord w (profile key.1 δ a b n key.2.2 N) p| ≤ (C : ℝ) := by
  choose B hB hb using (fun key : AtomKey rMax n => atom_mixedEuler hδ key.1 key.2.2 q)
  let C : ℕ := 1 + ∑ key : AtomKey rMax n, B key
  refine ⟨C, by dsimp [C]; omega, ?_⟩
  intro key N w p hw
  apply (hb key N w p hw).trans
  exact_mod_cast (show B key ≤ C from
    (Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finset.mem_univ key)).trans (by dsimp [C]; omega))

/-- Exact same finite bank constant before every HB occurrence count and
owner map; word order and repeated original coordinates are unchanged. -/
theorem finite_rank_bank_occurrence_budget {δ a b : ℝ} (hδ : 0 < δ)
    (rMax n q : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ key : AtomKey rMax n,
      ∀ (N m : ℕ) (owner : Fin m → Fin key.2.1.val) (U : Fin m → ℝ)
        (w : List (Fin m)) (z : Fin m → ℝ), w.length ≤ q →
        |AllWordAmbientOccurrenceBound.occWord w (fun z => profile key.1 δ a b n key.2.2 N
          (fun i => GroupedOccurrenceLogShift.groupProduct owner U i z)) z| ≤ (C : ℝ) := by
  obtain ⟨C, hC, hb⟩ := finite_rank_bank_mixedEuler hδ rMax n q
  refine ⟨C, hC, ?_⟩
  intro key N m owner U w z hw
  rw [AllWordAmbientOccurrenceBound.occWord_ambient owner U _
    (profile_global_smooth hδ key.1 key.2.2 N)]
  apply hb
  simpa using hw

end
end ImbalancedChen.P5Z.ActualRankLogAtomEuler
