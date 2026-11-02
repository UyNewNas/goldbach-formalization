import ImbalancedChen.Part5OriginalH430FrozenPerturbation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The real physical prime-density factor and its exact insertion/Jacobian
identities. This does not assert a prime-sum limit or a count licence.
The root error is absolute. Descendant bounds retain the actual physical
prefix factor, rather than dividing by the mass of a selected cell.
-/

namespace ImbalancedChen.Part5OriginalH430PhysicalMassPerturbation

noncomputable section
open Set Filter Topology MeasureTheory
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenPerturbation
open Part5UpperTables Part5UpperTables.OriginalU34
open Part5OriginalUpsilon5CausalDictionary (a)
open P5OriginalActionMassBound

/-- The continuous reciprocal-prime factor at the complete marked word.
No arithmetic singular-series or repeated-prime law is asserted here. -/
def physicalWeight (p : PhysicalNode) : ℝ := 4 / ((word p).prod * residual p)

def physicalSingletonKernel (L x : ℝ) : ℝ := L / (x*(L-x))
def physicalPairKernel (L x y : ℝ) : ℝ := L / (x*y*(L-x-y))

theorem root_physicalWeight (k : Root) (tau t : ℝ) :
    physicalWeight (sourceRoot k tau t).physical = branchWeight (sourceResidual k tau) t := by
  simp [physicalWeight, word, sourceRoot, residual, branchWeight, mul_comm]

theorem physicalWeight_singleton (p : PhysicalNode) (x s : ℝ)
    (hP : (word p).prod ≠ 0) (hL : residual p ≠ 0)
    (hx : x ≠ 0) (hnew : residual p-x ≠ 0) :
    physicalWeight (appendOne p x s) =
      physicalWeight p * physicalSingletonKernel (residual p) x := by
  unfold physicalWeight physicalSingletonKernel
  rw [word_appendOne, residual_appendOne]
  simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one]
  field_simp [hP, hL, hx, hnew]
  <;> ring

theorem physicalWeight_pair (p : PhysicalNode) (x y s : ℝ)
    (hP : (word p).prod ≠ 0) (hL : residual p ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) (hnew : residual p-x-y ≠ 0) :
    physicalWeight (appendPair p x y s) =
      physicalWeight p * physicalPairKernel (residual p) x y := by
  have hnew' : residual p-y-x ≠ 0 := by
    convert hnew using 1 <;> ring
  unfold physicalWeight physicalPairKernel
  rw [word_appendPair, residual_appendPair]
  simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one]
  field_simp [hP, hL, hx, hy, hnew, hnew']
  <;> ring

/-- Includes the Jacobian dx=L du, so this is precisely the original
singleton measure, not a pointwise density re-identification. -/
theorem singleton_Jacobian {L u : ℝ} (hL : 0 < L) (hu : u ∈ singletonAmbient) :
    L * physicalSingletonKernel L (L*u) = singletonKernel u := by
  have hu0 : 0 < u := (by norm_num : (0 : ℝ) < 1/5).trans_le hu.1
  have hu1 : 0 < 1-u := by linarith [hu.2]
  have hLu : L-L*u ≠ 0 := by nlinarith [mul_pos hL hu1]
  rw [singletonKernel_eq_raw hu]
  unfold physicalSingletonKernel
  field_simp [hL.ne', hu0.ne', hu1.ne', hLu]
  <;> ring

/-- Includes dx dy=L² du dv. The old total Q is unchanged. -/
theorem pair_Jacobian {L : ℝ} {u : Point} (hL : 0 < L)
    (hu : u ∈ pairAmbient) (hr : (1/5 : ℝ) ≤ 1-u 0-u 1) :
    L^2 * physicalPairKernel L (L*u 0) (L*u 1) = pairKernel u := by
  have hu0 : 0 < u 0 := (by norm_num : (0 : ℝ) < 1/5).trans_le (hu.1 0)
  have hu1 : 0 < u 1 := (by norm_num : (0 : ℝ) < 1/5).trans_le (hu.1 1)
  have hres : 0 < 1-u 0-u 1 := (by norm_num : (0 : ℝ) < 1/5).trans_le hr
  have hLres : L-L*u 0-L*u 1 ≠ 0 := by nlinarith [mul_pos hL hres]
  rw [pairKernel_eq_raw hu hr]
  unfold physicalPairKernel
  field_simp [hL.ne', hu0.ne', hu1.ne', hres.ne', hLres]
  <;> ring

/-- The positive absolute Jacobian for x=L/(w+1) gives dw/w. -/
theorem buchstab_Jacobian {L w : ℝ} (hL : 0 < L) (hw : w ∈ buchstabAmbient) :
    (L/(w+1)^2) * physicalSingletonKernel L (L/(w+1)) = buchstabKernel w := by
  have hw0 : 0 < w := zero_lt_one.trans_le hw.1
  have hw1 : w+1 ≠ 0 := by linarith
  have hres : L-L/(w+1) ≠ 0 := by
    have he : L-L/(w+1) = L*w/(w+1) := by field_simp [hw1]; ring
    rw [he]
    exact div_ne_zero (mul_ne_zero hL.ne' hw0.ne') hw1
  rw [buchstabKernel_eq_raw hw]
  unfold physicalSingletonKernel
  field_simp [hL.ne', hw0.ne', hw1, hres]
  <;> ring

/-- Exact prefix factor times the already derived residual error.
This statement is meaningful even for a zero-mass integration domain. -/
theorem descendant_physicalWeight_error {n : ℕ} {k : Root} {tau t lo hi : ℝ}
    {mesh depth : ℕ} (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (ht : t ∈ rootBand k) (hn : meshError n ≤ 11/384)
    (hd : depth ≤ 440) {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (frozenRoot n k tau t) code z) :
    |physicalWeight (realize depth (sourceRoot k 0 t) code z).physical -
        physicalWeight (realize depth (frozenRoot n k tau t) code z).physical| ≤
      |4/(word (realize depth (sourceRoot k 0 t) code z).physical).prod| *
        levelError n tau / (frozenResidualFloor*frozenResidualFloor) := by
  have hw : word (realize depth (sourceRoot k 0 t) code z).physical =
      word (realize depth (frozenRoot n k tau t) code z).physical :=
    congrArg (List.map Slot.exponent) (realize_slots_eq rfl code z)
  have he := actual_descendant_reciprocal_error htau htauhi ht hn hd hz
  unfold physicalWeight
  rw [← hw]
  have hid (P L M : ℝ) : 4/(P*L)-4/(P*M) = (4/P)*(1/L-1/M) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hid, abs_mul]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left he (abs_nonneg _)

def frozenRootWeight (n : ℕ) (k : Root) (tau t : ℝ) : ℝ :=
  physicalWeight (frozenRoot n k tau t).physical

theorem frozenRootWeight_eq (n : ℕ) (k : Root) (tau t : ℝ) :
    frozenRootWeight n k tau t = 4/(t*residual (frozenRoot n k tau t).physical) := by
  unfold frozenRootWeight physicalWeight
  have hw : word (frozenRoot n k tau t).physical = [t] := rfl
  rw [hw]
  simp only [List.prod_cons, List.prod_nil, mul_one]

def rootWeightConstant : ℝ := 4 / (a * ((11/384 : ℝ)*(11/384)))

theorem rootWeightConstant_pos : 0 < rootWeightConstant := by
  unfold rootWeightConstant
  norm_num [a]

theorem rootWeight_error {n : ℕ} {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (ht : t ∈ rootBand k)
    (hn : meshError n ≤ 11/384) :
    |branchWeight (sourceResidual k 0) t - frozenRootWeight n k tau t| ≤
      rootWeightConstant * levelError n tau := by
  have ht0 : 0 < t := (by norm_num [a] : (0 : ℝ) < a).trans_le (rootBand_subset k ht).1
  have hf := frozenRoot_residual_bounds htau htauhi ht hn
  have ho := sourceResidual_bounds (k := k) (tau := 0) (by norm_num) (by norm_num) ht
  have hl := rootLoss_bounds htau htauhi ht
  have heq : sourceResidual k 0 t-residual (frozenRoot n k tau t).physical =
      rootLoss n k tau t := by
    rw [frozenRoot_residual]
    unfold rootLoss
    change sourceResidual k 0 t-(frozenLevel n (t+sourceResidual k tau t)-t) =
      t+sourceResidual k 0 t-frozenLevel n (t+sourceResidual k tau t)
    ring
  have he : |1/sourceResidual k 0 t-1/residual (frozenRoot n k tau t).physical| ≤
      levelError n tau/((11/384 : ℝ)*(11/384)) := by
    apply reciprocal_difference (by norm_num) (by linarith [ho.1]) hf.1
    rw [heq, abs_of_nonneg hl.1]
    exact hl.2
  have hc : 4/t ≤ 4/a := div_le_div_of_nonneg_left (by norm_num)
    (by norm_num [a]) (rootBand_subset k ht).1
  have hleft : branchWeight (sourceResidual k 0) t-frozenRootWeight n k tau t =
      (4/t)*(1/sourceResidual k 0 t-1/residual (frozenRoot n k tau t).physical) := by
    simp only [branchWeight, frozenRootWeight, physicalWeight]
    have hw : word (frozenRoot n k tau t).physical = [t] := rfl
    rw [hw]
    simp only [List.prod_cons, List.prod_nil, mul_one, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hleft, abs_mul, abs_of_pos (div_pos (by norm_num) ht0)]
  calc
    _ ≤ (4/t)*(levelError n tau/((11/384 : ℝ)*(11/384))) :=
      mul_le_mul_of_nonneg_left he (div_pos (by norm_num) ht0).le
    _ ≤ (4/a)*(levelError n tau/((11/384 : ℝ)*(11/384))) :=
      mul_le_mul_of_nonneg_right hc (by
        unfold levelError
        exact div_nonneg (add_nonneg htau (meshError_pos n).le) (by norm_num))
    _ = rootWeightConstant*levelError n tau := by unfold rootWeightConstant; ring

/-- An actual absolute root integral. Its bound has no table or mass
licence hypothesis. Measurability/integrability are supplied separately
before using this to compare two individual mass integrals. -/
def rootAbsoluteError (n : ℕ) (k : Root) (tau : ℝ) : ℝ :=
  ∫ t in rootBand k, |branchWeight (sourceResidual k 0) t-frozenRootWeight n k tau t|

theorem rootBand_volume_lt_top (k : Root) : volume (rootBand k) < ⊤ := by
  cases k <;> simp [rootBand, Real.volume_Icc]

theorem rootBand_volume_le_one (k : Root) : volume.real (rootBand k) ≤ 1 := by
  cases k <;> norm_num [rootBand, Real.volume_real_Icc, a]

theorem rootAbsoluteError_bound {n : ℕ} (k : Root) {tau : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (hn : meshError n ≤ 11/384) :
    0 ≤ rootAbsoluteError n k tau ∧
      rootAbsoluteError n k tau ≤ rootWeightConstant*levelError n tau := by
  have hC : 0 ≤ rootWeightConstant*levelError n tau :=
    mul_nonneg rootWeightConstant_pos.le (add_nonneg htau (meshError_pos n).le)
  have he := norm_setIntegral_le_of_norm_le_const (rootBand_volume_lt_top k)
    (f := fun t => |branchWeight (sourceResidual k 0) t-frozenRootWeight n k tau t|)
    (C := rootWeightConstant*levelError n tau) (fun t ht => by
      simpa only [Real.norm_eq_abs, abs_abs] using rootWeight_error htau htauhi ht hn)
  have h0 : 0 ≤ rootAbsoluteError n k tau := integral_nonneg (fun _ => abs_nonneg _)
  refine ⟨h0, ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg h0] at he
  exact he.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (rootBand_volume_le_one k) hC)

/-- One concrete simultaneous choice for both primitive root bands;
finite tau is positive and is fixed before an arithmetic N is introduced. -/
theorem exists_frozen_root_mass_precision {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1/12 ∧ ∃ n : ℕ,
      meshError n ≤ 11/384 ∧
      ∀ k : Root, rootAbsoluteError n k tau < epsilon := by
  let tau : ℝ := min (1/12) (epsilon/(4*rootWeightConstant))
  have htau : 0 < tau := lt_min (by norm_num)
    (div_pos he (mul_pos (by norm_num) rootWeightConstant_pos))
  have htauhi : tau ≤ 1/12 := min_le_left _ _
  have hsmall : tau ≤ epsilon/(4*rootWeightConstant) := min_le_right _ _
  have hmesh : ∀ᶠ n : ℕ in atTop, meshError n < min tau (11/384 : ℝ) := by
    exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (eventually_lt_nhds (lt_min htau (by norm_num)))
  obtain ⟨n, hn⟩ := hmesh.exists
  have hnt : meshError n < tau := hn.trans_le (min_le_left _ _)
  have hnf : meshError n ≤ 11/384 := (hn.trans_le (min_le_right _ _)).le
  refine ⟨tau, htau, htauhi, n, hnf, fun k => ?_⟩
  have hb := (rootAbsoluteError_bound k htau.le htauhi hnf).2
  have hs := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4)
    rootWeightConstant_pos)).mp hsmall
  have hh := mul_lt_mul_of_pos_left hnt rootWeightConstant_pos
  unfold levelError at hb
  nlinarith [rootWeightConstant_pos]

end
end ImbalancedChen.Part5OriginalH430PhysicalMassPerturbation
