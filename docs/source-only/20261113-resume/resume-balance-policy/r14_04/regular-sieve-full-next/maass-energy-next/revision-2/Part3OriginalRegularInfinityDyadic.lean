import ImbalancedChen.Part3OriginalRegularGaussianSpectralWindow

/-! The genuine dyadic regular Maass and full incoming Eisenstein bounds
at the positive infinity observation, before summing spectral heights. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularInfinityDyadic20261113
open Real Set Filter MeasureTheory Finset
open scoped MatrixGroups Topology
open ActualUnitBandSpectralMass20261112 (exceptional height order_regular)
open ActualFullCuspEigenbasis20261026b
open ActualCuspBasisWhittakerCoefficients20261102
open ActualContinuousPoincarePairing20261110 (originalFrame)
open OriginalContinuousPoincarePackets20261110 (orderProbe)
open OriginalContinuousClassRemoval20261110 (markedRow)
open OriginalRegularCompactCoordinates20261113
open OriginalRegularCompactEnergy20261113 (limitEnergy energy_limit energy_bound)
open OriginalRegularCompactGram20261113 (vector)
open OriginalRegularCutoffPlane20261113 (compact)
open OriginalRegularCutoffOrder20261113 (coordinate)
open OriginalRegularGaussianSpectralWindow20261113
open OriginalRegularPreKuznetsovGaussian20261113 (weight weight_nonnegative)
open OriginalAllParameterKloosterman20261113 (dyadEnergy)
open OriginalRegularGaussianOffDiagonal20261113 (cost)

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩
private abbrev Idx (q : ℕ+) := actualCuspBasisIndex q.val q.property

def D (q : ℕ+) (M : ℕ) (a : ℕ→ℂ) (i : Idx q) :=
  markedRow (block M) (row M a) (index M) (basisR q.val q.property i (originalFrame false))
def L (q : ℕ+) (M : ℕ) (a : ℕ→ℂ) := native q false (block M) (row M a) (index M)

private theorem discrete_mass {K : ℝ} (kp : 0<K) (q : ℕ+) {M : ℕ} (hM : 0<M)
    (a : ℕ→ℂ) (J : Finset (Idx q)) (regular : ∀ i∈J,¬exceptional q.val i) :
    (∑ i∈J,(∫ r : ℝ,discreteDensity K none (height q.val i) r)*‖D q M a i‖^2)≤
      limitEnergy q M a K := by
  let d := fun (j : Option ℕ) (i : Idx q) r => discreteDensity K j (height q.val i) r*‖D q M a i‖^2
  have regi (j : Option ℕ) (i : Idx q) : Integrable (d j i) :=
    ((discrete_integral kp (height q.val i)).1 j).mul_const _
  have cap (j : ℕ) (r : ℝ) : (∑ i∈J,d (some j) i r)≤OriginalRegularCompactEnergy20261113.mass q M a K j r := by
    have h := (spectral_squares q false (block M) (row M a) (index M) (nonzero hM) (compact r j)).1 J
    rw [positive_vector q hM a] at h
    have b := mul_le_mul_of_nonneg_left h (weight_nonnegative K r)
    dsimp only [OriginalRegularCompactEnergy20261113.mass]
    apply le_trans _ b
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [order_regular q.val (regular i hi),norm_mul,mul_pow]
    dsimp only [d,D,discreteDensity,OriginalRegularCutoffOrder20261113.value,coordinate]
    exact (mul_assoc _ _ _).le
  have H (j : ℕ) : (∑ i∈J,(∫ r : ℝ,discreteDensity K (some j) (height q.val i) r)*‖D q M a i‖^2)≤
      ∫ r : ℝ,OriginalRegularCompactEnergy20261113.mass q M a K j r := by
    have h := integral_mono (integrable_finsetSum J (fun i _ => regi (some j) i))
      ((energy_limit kp q hM a).1 j) (cap j)
    rw [integral_finsetSum J (fun i _ => regi (some j) i)] at h
    simpa only [d,integral_mul_const] using h
  exact le_of_tendsto_of_tendsto' (tendsto_finsetSum J (fun i _ =>
    ((discrete_integral kp (height q.val i)).2).mul_const _)) (energy_limit kp q hM a).2 H

private theorem continuous_mass {K : ℝ} (kp : 0<K) (q : ℕ+) {M : ℕ} (hM : 0<M) (a : ℕ→ℂ) :
    (∫ z,lineDensity K none (L q M a) z ∂volume.prod (windowMeasure K))≤limitEnergy q M a K := by
  let g := L q M a
  have g0 : ∀ t,0≤g t := native_nonnegative q false (block M) (row M a) (index M)
  have reg := integral_window kp (L:=g) (native_continuous q false (block M) (row M a) (index M)) g0
  have cap (j : ℕ) (r : ℝ) : (∫ t,lineDensity K (some j) g (r,t) ∂windowMeasure K)≤
      OriginalRegularCompactEnergy20261113.mass q M a K j r := by
    obtain ⟨_,int,T⟩ := spectral_squares q false (block M) (row M a) (index M) (nonzero hM) (compact r j)
    rw [positive_vector q hM a] at T
    let F := fun t => ‖coordinate j r t‖^2*g t
    have I : Integrable F := int
    have tr := setIntegral_le_integral (s:=window K) I (ae_of_all _ (fun t => mul_nonneg (sq_nonneg _) (g0 t)))
    have b := mul_le_mul_of_nonneg_left (tr.trans T) (weight_nonnegative K r)
    rw [show (fun t => lineDensity K (some j) g (r,t))=(fun t => weight K r*F t) by
      funext t; dsimp only [lineDensity,OriginalRegularCutoffOrder20261113.value,F];ring,integral_const_mul]
    exact b
  have C (j : ℕ) : (∫ z,lineDensity K (some j) g z ∂volume.prod (windowMeasure K))≤
      ∫ r : ℝ,OriginalRegularCompactEnergy20261113.mass q M a K j r := by
    rw [integral_prod _ (reg.1 (some j))]
    exact integral_mono (reg.1 (some j)).integral_prod_left ((energy_limit kp q hM a).1 j) (cap j)
  exact le_of_tendsto_of_tendsto' reg.2 (energy_limit kp q hM a).2 C

/-- Both positive measures with the same uniform constant; finite Maass
subsets are arbitrary and the native continuous measure includes every
incoming parameter, the two signs of t and its own 1/(4π). -/
theorem positive_shell : ∃ C : ℝ,0<C ∧ ∀ {e K : ℝ},0<e → 2≤K → ∀ (q : ℕ+) {M : ℕ},0<M →
    ∀ a : ℕ→ℂ,
      (∀ J : Finset (Idx q),
        (∀ i∈J,¬exceptional q.val i ∧ height q.val i∈window K) →
        (∑ i∈J,‖D q M a i‖^2/cosh (π*height q.val i))≤
          C*((π*sqrt π/8)*K^2+cost e*((M:ℝ)^(1+e)/q.val))*dyadEnergy M a) ∧
      (∫ t,L q M a t/cosh (π*t) ∂windowMeasure K)≤
          C*((π*sqrt π/8)*K^2+cost e*((M:ℝ)^(1+e)/q.val))*dyadEnergy M a := by
  obtain ⟨C,Cp,floor⟩ := shell_floor
  refine ⟨C,Cp,?_⟩
  intro e K he hK q M hM a
  have kp : 0<K := by linarith only [hK]
  have H := energy_bound he hK q hM a
  have pay {v : ℝ} (h : K*v≤C*limitEnergy q M a K) :
      v≤C*((π*sqrt π/8)*K^2+cost e*((M:ℝ)^(1+e)/q.val))*dyadEnergy M a := by
    apply (mul_le_mul_iff_right₀ kp).mp
    have b := mul_le_mul_of_nonneg_left H Cp.le
    nlinarith only [h,b]
  constructor
  · intro J hJ
    have per (i : Idx q) (hi : i∈J) :
        K*(‖D q M a i‖^2/cosh (π*height q.val i))≤
          C*((∫ r : ℝ,discreteDensity K none (height q.val i) r)*‖D q M a i‖^2) := by
      have b := mul_le_mul_of_nonneg_right (floor hK (hJ i hi).2) (sq_nonneg ‖D q M a i‖)
      convert b using 1 <;> ring
    apply pay
    rw [Finset.mul_sum]
    apply (Finset.sum_le_sum per).trans
    rw [←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (discrete_mass kp q hM a J (fun i hi => (hJ i hi).1)) Cp.le
  · let g := L q M a
    let mu := windowMeasure K
    let f := fun t r => lineDensity K none g (r,t)
    have g0 : ∀ t,0≤g t := native_nonnegative q false (block M) (row M a) (index M)
    have gc : Continuous g := native_continuous q false (block M) (row M a) (index M)
    have I := (integral_window kp gc g0).1 none
    have A : Integrable (fun t => g t/cosh (π*t)) mu :=
      ((gc.div (Real.continuous_cosh.comp (continuous_const.mul continuous_id)) (fun _ => (cosh_pos _).ne')).continuousOn.integrableOn_compact
        (isCompact_Icc (a:=-K) (b:=K))).mono_set (fun t h => abs_le.mp h.2.2)
    have bound : ∀ᵐ t ∂mu,K*(g t/cosh (π*t))≤C*(∫ r : ℝ,f t r) := by
      filter_upwards [ae_restrict_mem (μ:=volume) (window_measurable K)] with t ht
      have v := mul_le_mul_of_nonneg_right (floor hK ht) (g0 t)
      dsimp only [f,lineDensity]
      rw [integral_mul_const]
      convert v using 1 <;> dsimp only [discreteDensity] <;> ring
    have h := integral_mono_ae (A.const_mul K) (I.integral_prod_right.const_mul C) bound
    rw [integral_const_mul,integral_const_mul] at h
    have F : (∫ t,∫ r : ℝ,f t r ∂volume ∂mu)=∫ z,lineDensity K none g z ∂volume.prod mu := by
      change (∫ t,∫ r : ℝ,lineDensity K none g (r,t) ∂volume ∂mu)=_
      calc
        _=∫ r : ℝ,∫ t,lineDensity K none g (r,t) ∂mu := (integral_integral_swap I).symm
        _=_ := (integral_prod _ I).symm
    rw [F] at h
    exact pay (h.trans (mul_le_mul_of_nonneg_left (continuous_mass kp q hM a) Cp.le))

end ImbalancedChen.Part3.OriginalRegularInfinityDyadic20261113
end

