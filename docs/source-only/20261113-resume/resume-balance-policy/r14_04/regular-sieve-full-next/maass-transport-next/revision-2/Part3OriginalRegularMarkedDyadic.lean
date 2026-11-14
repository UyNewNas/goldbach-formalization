import ImbalancedChen.Part3OriginalRegularMarkedEnergy

/-! Actual regular spectral shell at both observing cusps and both
frequency signs, on the manuscript's finite coefficient set. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularMarkedDyadic20261113
open Real Set Filter MeasureTheory Finset
open scoped MatrixGroups Topology
open ActualUnitBandSpectralMass20261112 (exceptional height order_regular)
open ActualFullCuspEigenbasis20261026b
open OriginalRegularCompactCoordinates20261113 (spectral_squares native_nonnegative)
open OriginalRegularMarkedEnergy20261113 (limit mass energy_limit energy_bound)
open OriginalRegularPacketTest20261113 (mark mark_ne Dyadic energy discreteRow lineMass)
open OriginalHolomorphicInfinityPacket20261113 (start)
open OriginalRegularCutoffPlane20261113 (compact)
open OriginalRegularCutoffOrder20261113 (coordinate)
open OriginalRegularGaussianSpectralWindow20261113
open OriginalRegularPreKuznetsovGaussian20261113 (weight weight_nonnegative)
open OriginalRegularGaussianOffDiagonal20261113 (cost)

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩
private abbrev Idx (q : ℕ+) := actualCuspBasisIndex q.val q.property

private theorem discrete_mass {K : ℝ} (kp : 0<K) (q : ℕ+) (one neg : Bool) {L : ℝ} (hL : 1/2≤L)
    (S : Finset ℕ) (a : ℕ→ℂ) (bd : Dyadic L S) (J : Finset (Idx q)) (regular : ∀ i∈J,¬exceptional q.val i) :
    (∑ i∈J,(∫ r : ℝ,discreteDensity K none (height q.val i) r)*‖discreteRow q.val one neg S a i‖^2)≤
      limit q one neg L S a K := by
  let d := fun (j : Option ℕ) (i : Idx q) r => discreteDensity K j (height q.val i) r*‖discreteRow q.val one neg S a i‖^2
  have regi (j : Option ℕ) (i : Idx q) : Integrable (d j i) :=
    ((discrete_integral kp (height q.val i)).1 j).mul_const _
  have cap (j : ℕ) (r : ℝ) : (∑ i∈J,d (some j) i r)≤mass q one neg hL S a bd K j r := by
    have h := (spectral_squares q one S a (mark neg) (mark_ne (by linarith only [hL]) S bd neg) (compact r j)).1 J
    have b := mul_le_mul_of_nonneg_left h (weight_nonnegative K r)
    dsimp only [mass]
    apply le_trans _ b
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [order_regular q.val (regular i hi),norm_mul,mul_pow]
    dsimp only [d,discreteRow,discreteDensity,OriginalRegularCutoffOrder20261113.value,coordinate]
    exact (mul_assoc _ _ _).le
  have H (j : ℕ) : (∑ i∈J,(∫ r : ℝ,discreteDensity K (some j) (height q.val i) r)*‖discreteRow q.val one neg S a i‖^2)≤
      ∫ r : ℝ,mass q one neg hL S a bd K j r := by
    have h := integral_mono (integrable_finsetSum J (fun i _ => regi (some j) i))
      ((energy_limit kp q one neg hL S a bd).1 j) (cap j)
    rw [integral_finsetSum J (fun i _ => regi (some j) i)] at h
    simpa only [d,integral_mul_const] using h
  exact le_of_tendsto_of_tendsto' (tendsto_finsetSum J (fun i _ =>
    ((discrete_integral kp (height q.val i)).2).mul_const _)) (energy_limit kp q one neg hL S a bd).2 H

private theorem continuous_mass {K : ℝ} (kp : 0<K) (q : ℕ+) (one neg : Bool) {L : ℝ} (hL : 1/2≤L) (S : Finset ℕ) (a : ℕ→ℂ) (bd : Dyadic L S) :
    (∫ z,lineDensity K none (lineMass q.val one neg S a) z ∂volume.prod (windowMeasure K))≤limit q one neg L S a K := by
  let g := lineMass q.val one neg S a
  have g0 : ∀ t,0≤g t := native_nonnegative q one S a (mark neg)
  have reg := integral_window kp (L:=g) (native_continuous q one S a (mark neg)) g0
  have cap (j : ℕ) (r : ℝ) : (∫ t,lineDensity K (some j) g (r,t) ∂windowMeasure K)≤
      mass q one neg hL S a bd K j r := by
    obtain ⟨_,int,T⟩ := spectral_squares q one S a (mark neg) (mark_ne (by linarith only [hL]) S bd neg) (compact r j)
    let F := fun t => ‖coordinate j r t‖^2*g t
    have I : Integrable F := int
    have tr := setIntegral_le_integral (s:=window K) I (ae_of_all _ (fun t => mul_nonneg (sq_nonneg _) (g0 t)))
    have b := mul_le_mul_of_nonneg_left (tr.trans T) (weight_nonnegative K r)
    rw [show (fun t => lineDensity K (some j) g (r,t))=(fun t => weight K r*F t) by
      funext t; dsimp only [lineDensity,OriginalRegularCutoffOrder20261113.value,F];ring,integral_const_mul]
    exact b
  have C (j : ℕ) : (∫ z,lineDensity K (some j) g z ∂volume.prod (windowMeasure K))≤
      ∫ r : ℝ,mass q one neg hL S a bd K j r := by
    rw [integral_prod _ (reg.1 (some j))]
    exact integral_mono (reg.1 (some j)).integral_prod_left ((energy_limit kp q one neg hL S a bd).1 j) (cap j)
  exact le_of_tendsto_of_tendsto' reg.2 (energy_limit kp q one neg hL S a bd).2 C

/-- Both positive measures with the same uniform constant; finite Maass
subsets are arbitrary and the native continuous measure includes every
incoming parameter, the two signs of t and its own 1/(4π). -/
theorem marked_shell : ∃ C : ℝ,0<C ∧ ∀ {e K : ℝ},0<e → 2≤K → ∀ (q : ℕ+) (one neg : Bool) {L : ℝ},1/2≤L →
    ∀ (S : Finset ℕ) (a : ℕ→ℂ),Dyadic L S →
      (∀ J : Finset (Idx q),
        (∀ i∈J,¬exceptional q.val i ∧ height q.val i∈window K) →
        (∑ i∈J,‖discreteRow q.val one neg S a i‖^2/cosh (π*height q.val i))≤
          C*((π*sqrt π/8)*K^2+cost e*((start L:ℝ)^(1+e)/q.val))*energy S a) ∧
      (∫ t,lineMass q.val one neg S a t/cosh (π*t) ∂windowMeasure K)≤
          C*((π*sqrt π/8)*K^2+cost e*((start L:ℝ)^(1+e)/q.val))*energy S a := by
  obtain ⟨C,Cp,floor⟩ := shell_floor
  refine ⟨C,Cp,?_⟩
  intro e K he hK q one neg L hL S a bd
  have kp : 0<K := by linarith only [hK]
  have H := energy_bound he hK q one neg hL S a bd
  have pay {v : ℝ} (h : K*v≤C*limit q one neg L S a K) :
      v≤C*((π*sqrt π/8)*K^2+cost e*((start L:ℝ)^(1+e)/q.val))*energy S a := by
    apply (mul_le_mul_iff_right₀ kp).mp
    have b := mul_le_mul_of_nonneg_left H Cp.le
    nlinarith only [h,b]
  constructor
  · intro J hJ
    have per (i : Idx q) (hi : i∈J) :
        K*(‖discreteRow q.val one neg S a i‖^2/cosh (π*height q.val i))≤
          C*((∫ r : ℝ,discreteDensity K none (height q.val i) r)*‖discreteRow q.val one neg S a i‖^2) := by
      have b := mul_le_mul_of_nonneg_right (floor hK (hJ i hi).2) (sq_nonneg ‖discreteRow q.val one neg S a i‖)
      convert b using 1 <;> ring
    apply pay
    rw [Finset.mul_sum]
    apply (Finset.sum_le_sum per).trans
    rw [←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (discrete_mass kp q one neg hL S a bd J (fun i hi => (hJ i hi).1)) Cp.le
  · let g := lineMass q.val one neg S a
    let mu := windowMeasure K
    let f := fun t r => lineDensity K none g (r,t)
    have g0 : ∀ t,0≤g t := native_nonnegative q one S a (mark neg)
    have gc : Continuous g := native_continuous q one S a (mark neg)
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
    exact pay (h.trans (mul_le_mul_of_nonneg_left (continuous_mass kp q one neg hL S a bd) Cp.le))

end ImbalancedChen.Part3.OriginalRegularMarkedDyadic20261113
end
