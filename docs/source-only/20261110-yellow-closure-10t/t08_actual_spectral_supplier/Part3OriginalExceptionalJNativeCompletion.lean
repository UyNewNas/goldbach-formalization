import ImbalancedChen.Part3OriginalNativeCuspFunctionals
import ImbalancedChen.Part3OriginalClassicalSpectralSupports
import ImbalancedChen.Part3ActualCuspBasisIndexCounting
import ImbalancedChen.Part3ActualAllFrameZeroEnergyRigidity
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
The common-interval extension in Classical §3 on the original full native
cuspidal eigenspaces. The complete dyadic interval and a single shifted
phase appear on the right, after summing the squared norms over levels
and all exceptional multiplicity slots. The external full-interval bound
and the Kim--Sarnak estimate are separate obligations.
-/
namespace ImbalancedChen.Part3.OriginalExceptionalJNativeCompletion20261110

noncomputable section
open Classical Finset
open scoped BigOperators MatrixGroups
open ActualFullCuspEigenbasis20261026b ActualCuspEigenbasisNativeLabels20261026b
open ActualCuspBasisIndexCounting20261026b ActualAllFrameZeroEnergyRigidity20261026b
open GammaFriedrichsKernelConstantRigidity20261026a
open Gamma0ActualSmoothQuotientCore20261025a
open ActualCuspBasisWhittakerCoefficients20261102 OriginalNativeCuspFunctionals20261102
open OriginalCompletedReciprocalSource20261102 OriginalPrimaryPacketRows20261102
open OriginalCommonPoissonLanes20261102 OriginalTwoZSourceAssembly20261102
open OriginalClassicalSpectralSupports20261102 OriginalSimultaneousPrefixCompletion20261102
open ActualCommonIntervalCompletionSourceOnly ActualCommonIntervalCompletionL1SourceOnly
open ActualIntervalGeometricSumSourceOnly MediumGlobalDyadicOwnership20261028
open P3NativePeriod64SamplingSourceOnly (D4)

attribute [local instance] Classical.propDecidable

/-- The zero eigenfunction of the scalar space does not occur in the actual
cuspidal ONB. This proves strict positivity without assuming a numerical gap. -/
theorem native_cusp_eigenvalue_pos (N : ℕ) [NeZero N] (hN : 0 < N)
    (i : actualCuspBasisIndex N hN) : 0 < actualCuspNativeEigenvalue N hN i := by
  apply lt_of_le_of_ne (actualCuspNativeEigenvalue_nonneg N hN i)
  intro hzero
  have hg := actualCuspHilbertBasis_original_friedrichs_graph N hN i
  rw [← hzero, Complex.ofReal_zero, zero_smul] at hg
  obtain ⟨u, hu, hAu⟩ := LinearPMap.mem_graph_iff.mp hg
  obtain ⟨c, hc⟩ := native_friedrichs_kernel_eq_scalar_constant N u hAu
  have he := hu.symm.trans hc
  have hm := (actualCuspHilbertBasis N hN i).property
  rw [he] at hm
  have hz := (scalar_constant_mem_allFrame_iff_zero N hN c).mp hm
  rw [hz, zero_smul] at he
  exact actualCuspHilbertBasis_original_ne_zero N hN i he

local instance (z : ℕ+) : NeZero (z : ℕ) := ⟨z.property.ne'⟩

/-- The strict exceptional range, with the original resolvent multiplicities. -/
def exceptional (z : ℕ+) : Finset (actualCuspBasisIndex z z.property) :=
  ((actualCuspIndexSublevel_finite z z.property (1/4)).toFinset).filter
    (fun i => actualCuspNativeEigenvalue z z.property i < 1/4)

theorem mem_exceptional (z : ℕ+) (i : actualCuspBasisIndex z z.property) :
    i ∈ exceptional z ↔
      0 < actualCuspNativeEigenvalue z z.property i ∧
        actualCuspNativeEigenvalue z z.property i < 1/4 := by
  rw [exceptional, mem_filter, Set.Finite.mem_toFinset]
  change (_ ≤ _ ∧ _ < _) ↔ (0 < _ ∧ _ < _)
  exact ⟨fun h => ⟨native_cusp_eigenvalue_pos z z.property i, h.2⟩,
    fun h => ⟨h.2.le, h.2⟩⟩

def tau (z : ℕ+) (i : actualCuspBasisIndex z z.property) : ℝ :=
  2 * Real.sqrt (1/4 - actualCuspNativeEigenvalue z z.property i)

private def maskKey (D : OriginalData) (j : ℕ) : Key :=
  { D.key with u := j+2 }

theorem maskPeriod_eq (D : OriginalData) (j : ℕ) :
    prefixPeriod (maskKey D j) = 4 * 2^j + 1 := by
  simp only [prefixPeriod, maskKey, pow_add]
  ring

private def frequency (ell : D4 → ℤ) (j : ℕ) : ℝ :=
  -((ell 1 : ℝ) / (64 * ((2^j : ℕ) : ℝ)))

/-- Both endpoints are the exact integer endpoints of Pascadi's (M,2M],
with M=2^j-1/2. The block at j=0 contains 1. -/
theorem mem_full_classical_block (j m : ℕ) :
    m ∈ dyadicWindow j ↔
      (m : ℝ) ∈ Set.Ioc (classicalMScale j) (2 * classicalMScale j) := by
  rw [dyadicWindow, mem_Ico, Set.mem_Ioc, classicalMScale, pow_succ]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hl : ((2^j : ℕ) : ℝ) ≤ m := by exact_mod_cast hlo
    have hu : (m : ℝ)+1 ≤ ((2^j : ℕ) : ℝ)*2 := by
      exact_mod_cast (show m+1 ≤ 2^j*2 by omega)
    constructor <;> linarith
  · rintro ⟨hlo, hhi⟩
    constructor
    · by_contra h
      have hn : m+1 ≤ 2^j := by omega
      have hr : (m : ℝ)+1 ≤ ((2^j : ℕ) : ℝ) := by exact_mod_cast hn
      linarith
    · by_contra h
      have hn : 2^j*2 ≤ m := by omega
      have hr : ((2^j : ℕ) : ℝ)*2 ≤ m := by exact_mod_cast hn
      linarith

private theorem source_weight (J j : ℕ) (ell : D4 → ℤ) {m : ℕ}
    (hm : m ∈ commonMBlock J j) :
    starRingEnd ℂ ((commonPoissonCompleted J j (ell 1)).weight m) =
      phaseAt (frequency ell j) m := by
  rw [commonPoissonCompleted_weight J j (ell 1) m hm]
  unfold phaseAt frequency
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_natCast, map_ofNat, Complex.conj_I, Complex.conj_ofReal,
    Complex.ofReal_neg]
  ring

private theorem mask_inversion (D : OriginalData) (J j m : ℕ)
    (hm : m ∈ dyadicWindow j) :
    (if m < J+1 then (1 : ℂ) else 0) =
      ∑ r : ZMod (prefixPeriod (maskKey D j)), prefixCoefficient (maskKey D j) J r *
        ZMod.stdAddChar (r * (m : ZMod (prefixPeriod (maskKey D j)))) := by
  let k := maskKey D j
  have hb : m < 2^k.u := by
    have h := (mem_Ico.mp hm).2
    change m < 2^(j+2)
    exact h.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hmem : m ∈ commonInterval (prefixGeometry k) 0 (J+1) ↔ m < J+1 := by
    simp [commonInterval, prefixGeometry_carrier, hb]
  have h := commonInterval_indicator_inversion (prefixGeometry k) 0 (J+1)
    (prefixPeriod k) (prefixGeometry_lt_period k) m hb
  rw [hmem] at h
  simpa only [k, prefixCoefficient, normalizedFourierCoeff, mul_sum, mul_assoc,
    cyclicCharacter_eq_exp] using h

private theorem phase_shift (P : ℕ) [NeZero P] (r : ZMod P) (m : ℕ) (ω : ℝ) :
    ZMod.stdAddChar (r * (m : ZMod P)) * phaseAt ω m =
      phaseAt (ω + (r.val : ℝ)/P) m := by
  rw [cyclicCharacter_eq_exp, phaseAt, phaseAt, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Unclipped full-block functional of the actual basis at the identity scaling. -/
def fullM (j : ℕ) (ω : ℝ) (z : ℕ+) (i : actualCuspBasisIndex z z.property) : ℂ :=
  ∑ m ∈ dyadicWindow j, phaseAt ω m * basisR z z.property i (1 : SL(2, ℤ)) (m : ℤ)

theorem original_M_eq_shifted_full (D : OriginalData) (J j : ℕ) (ell : D4 → ℤ)
    (z : ℕ+) (i : actualCuspBasisIndex z z.property) :
    originalMFunctional J j ell z z.property i =
      ∑ r : ZMod (prefixPeriod (maskKey D j)), prefixCoefficient (maskKey D j) J r *
        fullM j (frequency ell j + (r.val : ℝ)/prefixPeriod (maskKey D j)) z i := by
  let R := fun m : ℕ => basisR z z.property i (1 : SL(2, ℤ)) (m : ℤ)
  have hfilter : (dyadicWindow j).filter (fun m => m < J+1) = commonMBlock J j := by
    ext m
    simp only [dyadicWindow, commonMBlock, mem_filter, mem_Ico, lt_min_iff]
    tauto
  calc
    originalMFunctional J j ell z z.property i =
        ∑ m ∈ commonMBlock J j, phaseAt (frequency ell j) m * R m :=
      sum_congr rfl (fun m hm => by rw [← source_weight J j ell hm])
    _ = ∑ m ∈ dyadicWindow j,
        (if m < J+1 then (1 : ℂ) else 0) * (phaseAt (frequency ell j) m * R m) := by
      rw [← hfilter, sum_filter]
      simp only [ite_mul, one_mul, zero_mul]
    _ = ∑ m ∈ dyadicWindow j, (∑ r : ZMod (prefixPeriod (maskKey D j)),
        prefixCoefficient (maskKey D j) J r *
          ZMod.stdAddChar (r * (m : ZMod (prefixPeriod (maskKey D j))))) *
          (phaseAt (frequency ell j) m * R m) := by
      exact sum_congr rfl (fun m hm => by rw [mask_inversion D J j m hm])
    _ = _ := by
      simp only [fullM, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro r _
      rw [mul_sum]
      apply sum_congr rfl
      intro m _
      rw [← phase_shift]
      dsimp [R]
      ring

private abbrev NativeIndex (S : Finset ℕ+) := Σ z : S, ↥(exceptional z.val)

private def energyVector (S : Finset ℕ+) (X : ℝ)
    (F : (z : ℕ+) → actualCuspBasisIndex z z.property → ℂ) :
    EuclideanSpace ℂ (NativeIndex S) :=
  WithLp.toLp 2 fun a =>
    (Real.sqrt (X ^ tau a.1.val a.2.val) : ℂ) * F a.1.val a.2.val

private theorem vector_energy (S : Finset ℕ+) {X : ℝ} (hX : 0 < X)
    (F : (z : ℕ+) → actualCuspBasisIndex z z.property → ℂ) :
    ‖energyVector S X F‖^2 =
      ∑ z ∈ S, ∑ i : ↥(exceptional z), X ^ tau z i.val * ‖F z i.val‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sigma]
  simp only [energyVector, PiLp.toLp_apply, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (Real.rpow_nonneg hX.le _), Finset.univ_eq_attach, Finset.sum_attach]

def fullJ (S : Finset ℕ+) (X : ℝ) (j : ℕ) (ω : ℝ) : ℝ :=
  ∑ z ∈ S, ∑ i : ↥(exceptional z), X ^ tau z i.val * ‖fullM j ω z i.val‖^2

/-- The coefficient of sqrt(y) K in Pascadi (3.15) on this same native
basis, at every level of the printed sum. -/
def pascadiJ (S : Finset ℕ+) (X : ℝ) (j : ℕ) (ω : ℝ) : ℝ :=
  ∑ z ∈ S, ∑ i : ↥(exceptional z), X ^ tau z i.val *
    ‖∑ m ∈ dyadicWindow j,
      phaseAt ω m * basisRhoK z z.property i.val (1 : SL(2, ℤ)) (m : ℤ)‖^2

theorem pascadiJ_eq_four_mul (S : Finset ℕ+) (X : ℝ) (j : ℕ) (ω : ℝ) :
    pascadiJ S X j ω = 4 * fullJ S X j ω := by
  unfold pascadiJ fullJ
  rw [mul_sum]
  apply sum_congr rfl
  intro z _
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  have hsum : (∑ m ∈ dyadicWindow j,
      phaseAt ω m * basisRhoK z z.property i.val (1 : SL(2, ℤ)) (m : ℤ)) =
      2 * fullM j ω z i.val := by
    rw [fullM, mul_sum]
    apply sum_congr rfl
    intro m hm
    have hp : 0 < m := lt_of_lt_of_le (pow_pos (by norm_num : 0 < (2 : ℕ)) j)
      (mem_Ico.mp hm).1
    have hn : (m : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
    rw [basisR_eq_half_native z z.property i.val (1 : SL(2, ℤ)) hn]
    ring
  rw [hsum, norm_mul]
  norm_num <;> ring

def clippedJ (S : Finset ℕ+) (X : ℝ) (J j : ℕ) (ell : D4 → ℤ) : ℝ :=
  ∑ z ∈ S, ∑ i : ↥(exceptional z), X ^ tau z i.val *
    ‖originalMFunctional J j ell z z.property i.val‖^2

/-- One frequency serves the entire (level,index) Hilbert sum. The proof
uses the original cyclic mask only for its scalar Fourier inversion. -/
theorem native_common_interval_completion (D : OriginalData) (S : Finset ℕ+)
    {X : ℝ} (hX : 0 < X) (J j : ℕ) (ell : D4 → ℤ) :
    ∃ ω : ℝ, clippedJ S X J j ell ≤
      (2 + Real.log (4 * ((2^j : ℕ) : ℝ) + 1))^2 * fullJ S X j ω := by
  let k := maskKey D j
  let ω := fun r : ZMod (prefixPeriod k) => frequency ell j + (r.val : ℝ)/prefixPeriod k
  let V := fun r : ZMod (prefixPeriod k) => energyVector S X (fullM j (ω r))
  let U := energyVector S X (fun z i => originalMFunctional J j ell z z.property i)
  have hsum : U = ∑ r : ZMod (prefixPeriod k), prefixCoefficient k J r • V r := by
    apply PiLp.ext
    intro a
    let ev : EuclideanSpace ℂ (NativeIndex S) →ₗ[ℂ] ℂ :=
      PiLp.projₗ 2 (fun _ : NativeIndex S => ℂ) a
    change _ = ev (∑ r : ZMod (prefixPeriod k), prefixCoefficient k J r • V r)
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    change (Real.sqrt (X ^ tau a.1.val a.2.val) : ℂ) *
        originalMFunctional J j ell a.1.val a.1.val.property a.2.val =
      ∑ r : ZMod (prefixPeriod k), prefixCoefficient k J r *
        ((Real.sqrt (X ^ tau a.1.val a.2.val) : ℂ) * fullM j (ω r) a.1.val a.2.val)
    rw [original_M_eq_shifted_full D J j ell a.1.val a.2.val, mul_sum]
    exact sum_congr rfl (fun r _ => by dsimp [k, ω]; ring)
  obtain ⟨r, _, hr⟩ := Finset.exists_mem_eq_sup'
    (univ_nonempty : (univ : Finset (ZMod (prefixPeriod k))).Nonempty) (fun s => ‖V s‖)
  have hmax (s : ZMod (prefixPeriod k)) : ‖V s‖ ≤ ‖V r‖ := by
    rw [← hr]
    exact le_sup' (fun v => ‖V v‖) (mem_univ s)
  have hnorm : ‖U‖ ≤ (2 + Real.log (prefixPeriod k)) * ‖V r‖ := by
    calc
      ‖U‖ ≤ ∑ s : ZMod (prefixPeriod k), ‖prefixCoefficient k J s • V s‖ := by
        rw [hsum]
        exact norm_sum_le _ _
      _ ≤ ∑ s : ZMod (prefixPeriod k), endpointMajorant (prefixPeriod k) s * ‖V r‖ := by
        apply sum_le_sum
        intro s _
        rw [norm_smul]
        exact mul_le_mul (prefixCoefficient_le_majorant k J s) (hmax s)
          (norm_nonneg _) (endpointMajorant_nonneg _ s)
      _ ≤ _ := by
        rw [← sum_mul]
        exact mul_le_mul_of_nonneg_right
          (endpointMajorant_sum_le _ (prefixPeriod_two_le k)) (norm_nonneg _)
  have hs := pow_le_pow_left₀ (norm_nonneg U) hnorm 2
  rw [mul_pow] at hs
  dsimp only [U, V] at hs
  rw [vector_energy S hX, vector_energy S hX] at hs
  refine ⟨ω r, ?_⟩
  change _ ≤ _ * fullJ S X j (ω r)
  have hP : (prefixPeriod k : ℝ) = 4 * ((2^j : ℕ) : ℝ) + 1 := by
    exact_mod_cast maskPeriod_eq D j
  simpa only [clippedJ, fullJ, hP] using hs

/-- Finite levels of a classical interval. The guard retains Q<z≤2Q
literally, including Q=1/2. -/
def classicalLevels (Q : ℝ) : Finset ℕ+ :=
  (Icc (1 : ℕ+) (⟨⌊2*Q⌋₊+1, Nat.succ_pos _⟩ : ℕ+)).filter
    (fun z => (z.val : ℝ) ∈ Set.Ioc Q (2*Q))

theorem mem_classicalLevels (Q : ℝ) (z : ℕ+) :
    z ∈ classicalLevels Q ↔ (z.val : ℝ) ∈ Set.Ioc Q (2*Q) := by
  rw [classicalLevels, mem_filter]
  refine ⟨And.right, fun hz => ⟨mem_Icc.mpr ⟨?_, ?_⟩, hz⟩⟩
  · exact z.property
  · change z.val ≤ ⌊2*Q⌋₊+1
    exact (Nat.le_floor hz.2).trans (Nat.le_succ _)

/-- The original occupied levels on this fixed Z chart and classical
subinterval. The two endpoint-corrected subintervals are disjoint. -/
def originalLevels (D : OriginalData) (k : BlockKey) (upper lower : Bool) : Finset ℕ+ :=
  (classicalLevels (classicalLevelScale (fixedZ D upper) lower)).filter
    (fun z => z.val ∈ chartLevels D k upper)

theorem original_level_occurs (D : OriginalData) (k : BlockKey) (upper : Bool)
    {z : ℕ} (hz : z ∈ chartLevels D k upper) :
    let p : ℕ+ := ⟨z, (levelCarrier_licensed D k (chartLevels_subset D k upper hz)).1⟩
    p ∈ originalLevels D k upper true ∨ p ∈ originalLevels D k upper false := by
  obtain h | h := original_level_classical_cover D k ⟨z, chartLevels_subset D k upper hz⟩
  · left
    apply mem_filter.mpr
    exact ⟨(mem_classicalLevels _ _).mpr (by
      simpa [classicalLevelScale, levelChart_eq_fixedZ D k upper hz] using h), hz⟩
  · right
    apply mem_filter.mpr
    exact ⟨(mem_classicalLevels _ _).mpr (by
      simpa [classicalLevelScale, levelChart_eq_fixedZ D k upper hz] using h), hz⟩

/-- Direct original-row endpoint. The right side contains every actual
exceptional cusp eigenvector at every legal level in the printed J range. -/
theorem original_chart_J_completion (D : OriginalData) (k : BlockKey)
    (upper lower : Bool) {X : ℝ} (hX : 0 < X) (J j : ℕ) (ell : D4 → ℤ) :
    ∃ ω : ℝ, clippedJ (originalLevels D k upper lower) X J j ell ≤
      (2 + Real.log (4 * ((2^j : ℕ) : ℝ) + 1))^2 *
        fullJ (classicalLevels (classicalLevelScale (fixedZ D upper) lower)) X j ω := by
  obtain ⟨ω, h⟩ := native_common_interval_completion D (originalLevels D k upper lower)
    hX J j ell
  refine ⟨ω, h.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))⟩
  unfold fullJ
  apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
  intro z _ _
  exact sum_nonneg (fun i _ => mul_nonneg (Real.rpow_nonneg hX.le _) (sq_nonneg _))

/-- The norm on the right now uses the literal sqrt(y) K amplitudes in
Pascadi's theorem. Its factor 1/4 is independent of the cusp, level and mode. -/
theorem original_chart_J_completion_pascadi (D : OriginalData) (k : BlockKey)
    (upper lower : Bool) {X : ℝ} (hX : 0 < X) (J j : ℕ) (ell : D4 → ℤ) :
    ∃ ω : ℝ, clippedJ (originalLevels D k upper lower) X J j ell ≤
      (2 + Real.log (4 * ((2^j : ℕ) : ℝ) + 1))^2 *
        (pascadiJ (classicalLevels (classicalLevelScale (fixedZ D upper) lower)) X j ω / 4) := by
  obtain ⟨ω, hω⟩ := original_chart_J_completion D k upper lower hX J j ell
  refine ⟨ω, ?_⟩
  rw [pascadiJ_eq_four_mul]
  simpa only [mul_div_cancel_left₀ _ (by norm_num : (4 : ℝ) ≠ 0)] using hω

/-- Even when the original row meets the lower endpoint z=Z, the same
phase works for the two disjoint printed (Q,2Q] ranges together. -/
theorem original_chart_J_one_phase (D : OriginalData) (k : BlockKey)
    (upper : Bool) {X : ℝ} (hX : 0 < X) (J j : ℕ) (ell : D4 → ℤ) :
    let Z := fixedZ D upper
    ∃ ω : ℝ,
      clippedJ (originalLevels D k upper true ∪ originalLevels D k upper false) X J j ell ≤
        (2 + Real.log (4 * ((2^j : ℕ) : ℝ) + 1))^2 *
          ((pascadiJ (classicalLevels (Z/2)) X j ω +
            pascadiJ (classicalLevels Z) X j ω) / 4) := by
  let Z := fixedZ D upper
  let S := originalLevels D k upper true ∪ originalLevels D k upper false
  have hsub : S ⊆ classicalLevels (Z/2) ∪ classicalLevels Z :=
    union_subset_union (filter_subset _ _) (filter_subset _ _)
  have hd : Disjoint (classicalLevels (Z/2)) (classicalLevels Z) := by
    apply disjoint_left.mpr
    intro z ha hb
    have hp := ((mem_classicalLevels (Z/2) z).mp ha).2
    have hq := ((mem_classicalLevels Z z).mp hb).1
    linarith
  obtain ⟨ω, hω⟩ := native_common_interval_completion D S hX J j ell
  have hle : fullJ S X j ω ≤
      fullJ (classicalLevels (Z/2) ∪ classicalLevels Z) X j ω := by
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro z _ _
    exact sum_nonneg (fun i _ => mul_nonneg (Real.rpow_nonneg hX.le _) (sq_nonneg _))
  refine ⟨ω, hω.trans (mul_le_mul_of_nonneg_left (hle.trans_eq ?_) (sq_nonneg _))⟩
  rw [pascadiJ_eq_four_mul, pascadiJ_eq_four_mul]
  unfold fullJ
  rw [sum_union hd]
  ring

end
end ImbalancedChen.Part3.OriginalExceptionalJNativeCompletion20261110
