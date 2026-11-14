import ImbalancedChen.Part3OriginalHalfMarkTraceGrowth
import ImbalancedChen.Part3OriginalPositiveMarkOrder
import ImbalancedChen.Part3OriginalNativeCriticalTransport

/-! Source-only half-order coefficient elimination using the actual external
prime-Weil theorem through the half-tilted Euler majorant.  The paid regular
singleton and the positive floor over the WHOLE finite exceptional family
are reused verbatim from the reviewed positive6 module via private imports.
This is not a global spectral-gap statement.  No local compilation performed. -/
namespace ImbalancedChen.Part3.OriginalPositiveHalfSupport20261115
noncomputable section
open Finset Filter Real Complex
open scoped Classical MatrixGroups
open OriginalHalfMarkTraceGrowth20261115 (geometry)
open private others from ImbalancedChen.Part3OriginalPositiveMarkOrder
open private slot_floor from ImbalancedChen.Part3OriginalPositiveMarkOrder
open OriginalExceptionalJNativeCompletion20261110 (exceptional tau)
open ActualCuspBasisWhittakerCoefficients20261102 (basisR basisRhoK basisR_eq_half_native)
open OriginalSwitchedTraceProjection20261113 (complement mark_split)
open OriginalSwitchedLevelIdentity20261113 (single spectral)
open OriginalSwitchedRegularMarkExchange20261113 (principal incoming)
open OriginalSameInfinityWeightedHol20261113 (holSum)

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

theorem high_positive_zero (q m : ℕ+) (i : ↥(exceptional q)) (high : 1/2<tau q i.val) :
    basisR q.val q.property i.val 1 (m.val:ℤ)=0 := by
  let s := tau q i.val
  let v := (s+1/2)/2
  have vb : 1/2<v := by dsimp only [v,s];linarith only [high]
  have vs : v<s := by dsimp only [v,s];linarith only [high]
  have vp : 0<v := by linarith only [vb]
  let δ := 1-v
  have hδ : δ<1/2 := by dsimp only [δ];linarith only [vb]
  obtain ⟨A,an,P⟩ := geometry m hδ
  obtain ⟨D,dn,S⟩ := others q m vp
  obtain ⟨c,Y₀,cp,y1,F⟩ := slot_floor q m
  let r := ‖basisR q.val q.property i.val 1 (m.val:ℤ)‖^2
  by_contra nz
  have rp : 0<r := sq_pos_of_pos (norm_pos_iff.mpr nz)
  have raw (Y : ℝ) (hy : Y₀≤Y) : (c*r)*Y^(s-v)≤A+D := by
    have y := y1.trans hy
    have yp := zero_lt_one.trans_le y
    have a := P q yp
    rw [show 1-δ=v by dsimp only [δ];ring] at a
    have b := S Y y
    have split := mark_split false q m m (Q:=1) y zero_lt_one
    change spectral q m m (single Y)=complement q m m (single Y)+principal q m m (single Y)+
      incoming q m m (single Y)+holSum q m m (single Y) at split
    have ex := congrArg Complex.re split
    simp only [Complex.add_re] at ex
    have l := F Y hy i
    change c*Y^s*r≤(complement q m m (single Y)).re at l
    have negre (z : ℂ) : -z.re≤‖z‖ := by simpa only [Complex.neg_re,norm_neg] using Complex.re_le_norm (-z)
    have x : c*Y^s*r≤(A+D)*Y^v := by
      nlinarith only [l,ex,(Complex.re_le_norm (spectral q m m (single Y))).trans a,
        b,negre (principal q m m (single Y)),negre (incoming q m m (single Y)),negre (holSum q m m (single Y))]
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos yp v)).mp
    rw [mul_assoc ((c*r)) (Y^(s-v)),←Real.rpow_add yp,sub_add_cancel]
    nlinarith only [x]
  have growth := (tendsto_rpow_atTop (sub_pos.mpr vs)).eventually_gt_atTop ((A+D)/(c*r))
  obtain ⟨Y,hy,h⟩ := (growth.and (eventually_ge_atTop Y₀)).exists
  have fail := (div_lt_iff₀ (mul_pos cp rp)).mp hy
  exact (not_lt_of_ge (raw Y h)) (by linarith only [fail])


theorem rho_zero (q m : ℕ+) (i : ↥(exceptional q)) (hi : 1/2<tau q i.val) :
    basisRhoK q.val q.property i.val 1 (m.val:ℤ)=0 := by
  have h := high_positive_zero q m i hi
  rw [basisR_eq_half_native q.val q.property i.val 1 (by exact_mod_cast m.property.ne')] at h
  exact (div_eq_zero_iff.mp h).resolve_right (by norm_num)

/-- The precise previously unpaid interface, now sourced from prime Weil.
The zero and negative Fourier marks and other cusp coordinates are not claimed. -/
theorem positive_half_support :
    OriginalNativeCriticalTransport20261113.positiveHalfSupport := by
  intro q m i hi
  exact rho_zero q m i hi

end
end ImbalancedChen.Part3.OriginalPositiveHalfSupport20261115
