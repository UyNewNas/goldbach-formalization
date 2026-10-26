import ImbalancedChen.Part3ActualICoreZeroOrderDerivative
import ImbalancedChen.Part3ActualCutPlaneKIModel
import ImbalancedChen.Part3ActualZeroOrderKIConnection
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

The actual zero-order principal-slit K model is the negative order
derivative of the actual complex I model at zero. Its derivative is
computed as a logarithmic I_0 term plus the actual entire order-derivative
core supplied by the previous leaf. This proves z holomorphy on the slit.
The genuine positive-real zero-order K/I supplier then fixes the real
axis value, and the actual identity theorem proves agreement with the
literal Laplace K_0 throughout Re(z)>0. No singular sine quotient is
evaluated at zero and no continued-K identity is assumed.
-/

namespace ImbalancedChen.Part3.ActualCutPlaneKZeroModel20261026b

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open GeneralComplexISeriesSourceOnly GeneralIOrderHolomorphySourceOnly
open ComplexOrderKBridgeSourceOnly
open ActualComplexArgumentISlit20261026b ActualICoreZeroOrderDerivative20261026b
open ActualComplexArgumentKLaplace20261026b ActualComplexArgumentKHolomorphic20261026b
open ActualComplexMacdonaldQuarterL120261026b ActualComplexMacdonaldQuarterIdentity20261026b
open ActualCutPlaneKIModel20261026b

theorem complexArgumentI_order_analyticAt (nu : ℂ) {z : ℂ}
    (hnu : -1 < nu.re) (hz : z ≠ 0) :
    AnalyticAt ℂ (fun mu : ℂ => complexArgumentI mu z) nu := by
  have hbase : z / 2 ≠ 0 := div_ne_zero hz (by norm_num)
  have hp : Differentiable ℂ (fun mu : ℂ => (z / 2) ^ mu) :=
    differentiable_id.const_cpow (Or.inl hbase)
  exact (hp.analyticAt nu).mul (analyticAt_generalICore_order nu ((z / 2) ^ (2 : ℕ)) hnu)

/-- Actual product differentiation in the order at zero. Its core
derivative is the literal derivative, already proved entire in z. -/
theorem complexArgumentI_order_zero_hasDerivAt {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (fun nu : ℂ => complexArgumentI nu z)
      (Complex.log (z / 2) * complexArgumentI 0 z + coreOrderDerivativeZero ((z / 2) ^ (2 : ℕ))) 0 := by
  have hbase : z / 2 ≠ 0 := div_ne_zero hz (by norm_num)
  have hp : HasDerivAt (fun nu : ℂ => (z / 2) ^ nu) (Complex.log (z / 2)) 0 := by
    simpa only [Complex.cpow_zero, one_mul, mul_one] using
      (hasDerivAt_id (0 : ℂ)).const_cpow (Or.inl hbase)
  have hc : HasDerivAt (fun nu : ℂ => generalICore nu ((z / 2) ^ (2 : ℕ)))
      (coreOrderDerivativeZero ((z / 2) ^ (2 : ℕ))) 0 :=
    (analyticAt_generalICore_order 0 ((z / 2) ^ (2 : ℕ)) (by norm_num)).differentiableAt.hasDerivAt
  simpa only [complexArgumentI, Complex.cpow_zero, one_mul] using hp.mul hc

/-- The actual zero-order cut model, defined by an actual order derivative. -/
def cutPlaneKZero (z : ℂ) : ℂ := -deriv (fun nu : ℂ => complexArgumentI nu z) 0

theorem cutPlaneKZero_eq_formula {z : ℂ} (hz : z ≠ 0) :
    cutPlaneKZero z = -(Complex.log (z / 2) * complexArgumentI 0 z +
      coreOrderDerivativeZero ((z / 2) ^ (2 : ℕ))) := by
  unfold cutPlaneKZero
  rw [(complexArgumentI_order_zero_hasDerivAt hz).deriv]

/-- Slit holomorphy is derived from the explicit actual mixed derivative
formula, without supplying the desired K_0 continuation as a hypothesis. -/
theorem cutPlaneKZero_analyticAt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    AnalyticAt ℂ cutPlaneKZero z := by
  have hh : AnalyticAt ℂ (fun w : ℂ => w / 2) z := analyticAt_id.div_const
  have hlog : AnalyticAt ℂ (fun w : ℂ => Complex.log (w / 2)) z :=
    hh.clog (halfArgument_mem_slit hz)
  have hI := complexArgumentI_analyticAt (nu := 0) (by norm_num) hz
  have hcore := (coreOrderDerivativeZero_analyticAt ((z / 2) ^ (2 : ℕ))).comp (hh.pow 2)
  have hf := ((hlog.mul hI).add hcore).neg
  apply hf.congr
  filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with w hw
  exact (cutPlaneKZero_eq_formula (Complex.slitPlane_ne_zero hw)).symm

theorem cutPlaneKZero_analyticOnNhd : AnalyticOnNhd ℂ cutPlaneKZero Complex.slitPlane :=
  fun _ hz => cutPlaneKZero_analyticAt hz

/-- Exact binding to the supplied actual positive-real zero-order
connection. Equality of the I functions is proved before differentiating. -/
theorem cutPlaneKZero_real {q : ℝ} (hq : 0 < q) :
    cutPlaneKZero (q : ℂ) = complexOrderK 0 q := by
  have he : (fun nu : ℂ => complexArgumentI nu (q : ℂ)) =
      (fun nu : ℂ => generalI nu q) := funext (fun nu => complexArgumentI_real nu q)
  unfold cutPlaneKZero
  rw [he]
  exact (ActualZeroOrderKIConnectionSourceOnly.complexOrderK_zero_eq_neg_order_deriv hq).symm

/-- The actual zero-order cut model agrees with the actual hyperbolic
Laplace integral throughout the right half-plane, by a proved identity
theorem from its supplied positive-real values. -/
theorem cutPlaneKZero_eq_actual {z : ℂ} (hz : 0 < z.re) :
    cutPlaneKZero z = complexArgumentK 0 z := by
  have hcut : AnalyticOnNhd ℂ cutPlaneKZero rightHalfPlane :=
    cutPlaneKZero_analyticOnNhd.mono rightHalfPlane_subset_slit
  have hactual := complexArgumentK_analyticOnNhd (0 : ℂ)
  have hquarter : EqOn cutPlaneKZero (complexArgumentK 0) strictQuarterSector := by
    apply eqOn_sector_of_positive_real
      (hcut.mono (fun _ hw => strictQuarterSector_re_pos hw))
      (hactual.mono (fun _ hw => strictQuarterSector_re_pos hw))
    intro q hq
    rw [complexArgumentK_real]
    exact cutPlaneKZero_real hq
  have hnear : cutPlaneKZero =ᶠ[𝓝 (1 : ℂ)] complexArgumentK 0 := by
    filter_upwards [strictQuarterSector_isOpen.mem_nhds
      (positive_real_mem_sector (by norm_num : (0 : ℝ) < 1))] with w hw
    exact hquarter hw
  exact hcut.eqOn_of_preconnected_of_eventuallyEq hactual rightHalfPlane_convex.isPreconnected
    (by change 0 < (1 : ℂ).re; norm_num) hnear hz

end
end ImbalancedChen.Part3.ActualCutPlaneKZeroModel20261026b
