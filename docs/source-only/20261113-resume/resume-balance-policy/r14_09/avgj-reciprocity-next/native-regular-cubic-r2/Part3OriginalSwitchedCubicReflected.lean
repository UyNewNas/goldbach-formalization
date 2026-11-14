import ImbalancedChen.Part3OriginalSwitchedCubicRows
import ImbalancedChen.Part3OriginalSwitchedRegularBlockExchange

/-! Cauchy on the two actual shifted rows of each Fourier mode, followed by
the complete mode and spectral sums of the returned trace. -/
namespace ImbalancedChen.Part3.OriginalSwitchedCubicReflected20261113
noncomputable section
open Finset MeasureTheory Complex
open scoped BigOperators Classical MatrixGroups
open OriginalSwitchedCubicRows20261113 (Idx X Z Dterm Eterm cross)
open OriginalSwitchedRegularBlockExchange20261113 (principalBlock incomingBlock principal_fourier incoming_fourier)
open OriginalSwitchedRegularFourierBudget20261113 (scaled term uniform_majorant)
open OriginalSwitchedRegularRows20261113 (D E)
open OriginalSwitchedSeparatedBlocks20261113 (multiplier)
open OriginalSwitchedSeparatedNativeSlots20261113 (legs)
open OriginalSwitchedFourCoordinateRows20261113 (ratio norm_phase)
open OriginalSwitchedSeparatedTransforms20261113 (factor)
open OriginalSwitchedCutoffModes20261113 (mode)
open P3Period64NativeReconstructionSourceOnly (spectralTest norm_e)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open ActualMarkedCubicPrice20261112 (linePrice)
open OriginalRegularPacketTest20261113 (energy energy_nonneg)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open ActualPrescribedPositiveJ20261112 (positiveWeight regular_transform weightSchwartz)
open P3NativePeriod64SamplingSourceOnly (D4)

local instance (d : ℕ+) : NeZero d.val := ⟨d.property.ne'⟩

def W (j : ℕ) (Y Q : ℝ) (d : ℕ+) (k : D4→ℤ) (t : ℝ) :=
  multiplier k (ratio (j:=j) Y Q d)*scaled (spectralTest (mode (k 0)) Y⁻¹) t

private theorem weighted (j : ℕ) (Y Q : ℝ) (d : ℕ+) (k : D4→ℤ) (t : ℝ) :
    ‖W j Y Q d k t‖=‖term d j Y Q 0 0 k t‖ := by
  unfold W term factor multiplier
  split_ifs <;> simp only [norm_mul,norm_phase,norm_e,mul_one]

theorem mode_cont {Y : ℝ} (yp : 0<Y) (l : ℤ) :
    Continuous (scaled (spectralTest (mode l) Y⁻¹)) := by
  let vp := inv_pos.mpr yp
  change Continuous (fun t => positiveWeight (spectralTest (mode l) Y⁻¹) t/(Real.cosh (Real.pi*t):ℂ))
  simp_rw [show ∀ t,positiveWeight (spectralTest (mode l) Y⁻¹) t=weightSchwartz (mode l) vp t from
    fun t => (regular_transform _ vp t).2]
  exact (weightSchwartz _ _).continuous.div (by fun_prop) (fun t => Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne')

theorem reflected {ε : ℝ} (ep : 0<ε) :
    ∃ C : ℝ,0≤C ∧ ∀ (d : ℕ+) (j : ℕ) (u : ℕ→ℂ) (Y Q ω : ℝ),1≤Y → 0<Q →
      let B := C*(1+Real.log (2*Y)^2)*(1+(classicalMScale j)^(1+ε)/(d.val:ℝ))*energy (dyadicWindow j) u
      ‖principalBlock d j Y Q ω u‖≤B ∧ ‖incomingBlock d j Y Q ω u‖≤B := by
  obtain ⟨C,cp,R⟩ := cross ep
  obtain ⟨A,an,sa,H⟩ := uniform_majorant
  let K := (∑' k,A k)*C
  refine ⟨K,mul_nonneg (tsum_nonneg an) cp.le,fun d j u Y Q ω y1 qp => ?_⟩
  let P := 1+Real.log (2*Y)^2
  let V := C*(1+(classicalMScale j)^(1+ε)/(d.val:ℝ))*energy (dyadicWindow j) u
  let v := fun k : D4→ℤ => ω-(k 1:ℝ)/(64*classicalMScale j)
  let w := fun k : D4→ℤ => ω+(k 2:ℝ)/(64*classicalMScale j)
  let g := W j Y Q d
  have dr (k : D4→ℤ) (i : Idx d) :
      D d j Y Q ω u k i=Dterm d j u (v k) (w k) (g k) i := by
    unfold D Dterm
    split_ifs <;> first | rfl | dsimp only [g,W,v,w,legs,X];ring
  have er (k : D4→ℤ) (t : ℝ) :
      E d j Y Q ω u k t=Eterm d j u (v k) (w k) (g k) t := by
    unfold E Eterm
    apply sum_congr rfl
    intro a _
    dsimp only [g,W,v,w,legs,Z];ring
  have per (k : D4→ℤ) :
      Summable (fun i => ‖D d j Y Q ω u k i‖) ∧
      (∑' i,‖D d j Y Q ω u k i‖)≤A k*P*V ∧
      Integrable (E d j Y Q ω u k) ∧ (∫ t,‖E d j Y Q ω u k t‖)≤A k*P*V := by
    have price (t : ℝ) : ‖g k t‖≤(A k*P)*linePrice t := by
      rw [show ‖g k t‖=‖term d j Y Q 0 0 k t‖ from weighted j Y Q d k t]
      exact H Y y1 d j 0 0 Q k t
    have gm : Continuous (g k) := continuous_const.mul (mode_cont (zero_lt_one.trans_le y1) (k 0))
    simpa only [dr,funext (er k)] using R d j u (v k) (w k) (g k) (mul_nonneg (an k) (by dsimp only [P];positivity))
      price gm.aestronglyMeasurable
  have bound (f : (D4→ℤ)→ℂ) (v : ℂ) (sv : HasSum f v) (p : ∀ k,‖f k‖≤A k*P*V) :
      ‖v‖≤K*(1+Real.log (2*Y)^2)*(1+(classicalMScale j)^(1+ε)/(d.val:ℝ))*energy (dyadicWindow j) u := by
    have big := (sa.mul_right P).mul_right V
    have sm := big.of_nonneg_of_le (fun _ => norm_nonneg _) p
    have cap := sm.tsum_le_tsum p big
    rw [←sv.tsum_eq]
    apply (norm_tsum_le_tsum_norm sm).trans (cap.trans_eq ?_)
    rw [tsum_mul_right,tsum_mul_right]
    dsimp only [K,P,V];ring
  refine ⟨bound _ _ (principal_fourier d j Y Q ω y1 qp u).2 (fun k =>
    (norm_tsum_le_tsum_norm (per k).1).trans (per k).2.1),?_⟩
  exact bound _ _ (incoming_fourier d j Y Q ω y1 qp u).2.2 (fun k =>
    (norm_integral_le_integral_norm _).trans (per k).2.2.2)

end
end ImbalancedChen.Part3.OriginalSwitchedCubicReflected20261113
