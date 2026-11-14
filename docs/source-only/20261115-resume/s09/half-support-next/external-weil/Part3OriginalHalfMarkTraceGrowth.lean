import ImbalancedChen.Part3OriginalSwitchedInitialTraceGeometry
import ImbalancedChen.Part3FixedMarkHalfEulerSummability

/-! Diagonal single-mark trace at a fixed positive Fourier frequency.
The constant may depend on the mark and on the strictly subcritical tilt. -/
namespace ImbalancedChen.Part3.OriginalHalfMarkTraceGrowth20261115
noncomputable section
open Finset Set Complex
open scoped Classical BigOperators
open FixedMarkHalfTail20261115 (majorant majorant_nonneg price price_nonneg summable_majorant_price physical_le_majorant)
open OriginalSameInfinityScalarGeometry20261113 (term)
open OriginalInfinitySwitchedGeometry20261113 (argument)
open OriginalSwitchedLevelIdentity20261113 (single spectral)
open OriginalSwitchedPrescribedTrace20261113 (same_infinity_cutoff_trace)
open OriginalSwitchedCutoffFamily20261113 (profile)
open CommonSmoothCutoff (dyadicCutoff dyadicCutoff_le_one dyadicCutoff_nonneg dyadicCutoff_tsupport_eq_tight)
open OriginalSmoothPoissonTail (kloosterman)

private theorem summable_at (m : ℕ+) {δ : ℝ} (hd : δ<1/2) :
    Summable (fun k : ℕ+ => price (m.val:ℤ) δ k.val) :=
  (summable_majorant_price (m:=(m.val:ℤ)) (by exact_mod_cast m.property.ne') hd).comp_injective
    (show Function.Injective (fun k : ℕ+ => k.val) from Subtype.coe_injective)

theorem geometry (m : ℕ+) {δ : ℝ} (hd : δ<1/2) :
    ∃ K : ℝ,0≤K ∧ ∀ (q : ℕ+) {Y : ℝ},0<Y →
      ‖spectral q m m (single Y)‖≤K*Y^(1-δ) := by
  let M : ℝ := m.val
  let v := 1-δ
  let W := (8*Real.pi*M)^v
  let f := fun k : ℕ+ => price (m.val:ℤ) δ k.val
  have mp : 0<M := by exact_mod_cast m.property
  have vp : 0≤v := by dsimp only [v];linarith only [hd]
  have wp : 0≤W := Real.rpow_nonneg (by positivity) _
  have sf : Summable f := summable_at m hd
  have np (k : ℕ+) : 0≤f k := price_nonneg _ _ _
  refine ⟨W*(∑' k,f k),mul_nonneg wp (tsum_nonneg np),fun q Y yp => ?_⟩
  let a := 8*Real.pi*M*Y
  have ap : 0<a := by dsimp [a];positivity
  have wf : a^v=W*Y^v := Real.mul_rpow (by positivity) yp.le
  have src := same_infinity_cutoff_trace q m m false 0 Y yp
  have eq : (∑' k,term (single Y) q m m k)=spectral q m m (single Y) := by
    simpa only [single,profile,Bool.false_eq_true,if_false,mul_one,spectral] using src.2
  have ss : Summable (fun k => ‖term (single Y) q m m k‖) := by
    simpa only [single,profile,Bool.false_eq_true,if_false,mul_one] using src.1
  have bound (k : ℕ+) : ‖term (single Y) q m m k‖≤a^v*f k := by
    let b : ℝ := k.val
    have bp : 0<b := by exact_mod_cast k.property
    have nonneg := mul_nonneg (Real.rpow_nonneg ap.le v) (np k)
    by_cases dvd : q.val∣k.val
    case neg => simpa only [term,if_neg dvd,norm_zero] using nonneg
    let x := Y*argument m m k
    by_cases z : dyadicCutoff x=0
    · simpa only [term,if_pos dvd,single,x,show dyadicCutoff (Y*argument m m k)=0 from z,
        Complex.ofReal_zero,mul_zero,norm_zero] using nonneg
    have h : x∈tsupport dyadicCutoff := subset_tsupport _ z
    rw [dyadicCutoff_tsupport_eq_tight] at h
    have arg : x=Y*(4*Real.pi*M/b) := by
      simp only [x,argument,show Real.sqrt ((m.val:ℝ)*(m.val:ℝ))=M from
        (Real.sqrt_mul_self mp.le)]
    have small : b≤a := by
      have cut := h.1
      change 1/2≤x at cut
      rw [arg,show Y*(4*Real.pi*M/b)=(Y*(4*Real.pi*M))/b by ring] at cut
      have prod := (le_div_iff₀ bp).mp cut
      dsimp only [a]
      nlinarith only [prod]
    have mag : ‖single Y (argument m m k)‖≤1 := by
      change ‖(dyadicCutoff x:ℂ)‖≤1
      simpa only [Complex.norm_real,Real.norm_of_nonneg (dyadicCutoff_nonneg _)] using dyadicCutoff_le_one x
    have up := (div_le_div_of_nonneg_right (physical_le_majorant (m.val:ℤ) k.val (m.val:ℤ)) bp.le)
    have pw := Real.rpow_le_rpow bp.le small vp
    have pay : majorant (m.val:ℤ) k.val/b=b^v*f k := by
      simp only [f,price,if_neg k.property.ne']
      change _=b^v*(majorant (m.val:ℤ) k.val*b^(-2+δ))
      rw [mul_left_comm,←Real.rpow_add bp,show v+(-2+δ)=-1 by dsimp [v];ring,Real.rpow_neg_one]
      ring
    rw [term,if_pos dvd,norm_mul,norm_div,Complex.norm_natCast]
    apply (mul_le_of_le_one_right (div_nonneg (norm_nonneg _) bp.le) mag).trans
    exact up.trans (pay.le.trans (mul_le_mul_of_nonneg_right pw (np k)))
  rw [←eq]
  apply (norm_tsum_le_tsum_norm ss).trans ((ss.tsum_le_tsum bound (sf.mul_left _)).trans_eq ?_)
  rw [tsum_mul_left,wf]
  dsimp only [v];ring

end
end ImbalancedChen.Part3.OriginalHalfMarkTraceGrowth20261115
