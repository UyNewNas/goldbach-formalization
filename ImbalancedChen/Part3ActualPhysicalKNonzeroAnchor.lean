import ImbalancedChen.Part3ActualPhysicalKJets
import ImbalancedChen.Part3ComplexOrderKLargeArgument

/-!
# Actual physical K is nontrivial beyond every prescribed height

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal all-complex-order K asymptotic has nonzero leading constant
sqrt(pi/2). Hence actual K is eventually nonzero on the positive q axis,
and sqrt(y)K_nu(a*y) has a nonzero value above max(1,Y) for EVERY Y.
No nowhere-zero assertion, basis, spectral expansion, ODE classification
or held imaginary radial derivative/selection supplier is used.
-/

namespace ImbalancedChen.Part3.ActualPhysicalKNonzeroAnchor20261026b

noncomputable section
open Set Filter
open scoped Topology
open ActualPhysicalKJets20261026b ComplexOrderKBridgeSourceOnly
open ComplexOrderKLargeArgument20261025a

/-- The actual all-complex-order large-q asymptotic makes K eventually
nonzero. This is a proved property of the literal integral. -/
theorem complexOrderK_eventually_ne_zero (nu : ℂ) :
    ∀ᶠ q : ℝ in atTop, complexOrderK nu q ≠ 0 := by
  have hne : (Real.sqrt (Real.pi/2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  have he := (complexOrderK_large_argument nu).eventually (eventually_ne_nhds hne)
  filter_upwards [he] with q hq
  intro hz
  apply hq
  rw [hz,mul_zero]

/-- A genuine nonzero initial value exists above every requested physical
height, and strictly above 1. Real, imaginary and zero orders are included. -/
theorem physicalK_nonzero_anchor (nu : ℂ) {a : ℝ} (ha : 0<a) (Y : ℝ) :
    ∃ y : ℝ, max 1 Y<y ∧ physicalK nu a y ≠ 0 := by
  obtain ⟨q,hq,hKq⟩ :=
    ((eventually_gt_atTop (a*max 1 Y)).and (complexOrderK_eventually_ne_zero nu)).exists
  have hy : max 1 Y<q/a :=
    (lt_div_iff₀ ha).mpr (by simpa only [mul_comm] using hq)
  have hy0 : 0<q/a := zero_lt_one.trans ((le_max_left 1 Y).trans_lt hy)
  have hs : a*(q/a)=q := by field_simp [ha.ne']
  refine ⟨q/a,hy,?_⟩
  rw [physicalK,hs]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy0).ne') hKq

end
end ImbalancedChen.Part3.ActualPhysicalKNonzeroAnchor20261026b
