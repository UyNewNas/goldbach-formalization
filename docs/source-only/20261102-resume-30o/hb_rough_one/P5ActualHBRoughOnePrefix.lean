import ImbalancedChen.P5ActualHBRoughBrunRates
import ImbalancedChen.P5ActualHBAuxiliaryPrefixes

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original rough-one base prefix has arbitrary fixed real logarithmic
saving, at the actual real chart cutoff and for every positive modulus.
The finite prefix maximum is never evaluated. Native intervals are (u,v]
with literal floors, and empty prefixes are handled before subtraction.
This is the base supplier for the frozen M role reductions. It changes
neither their logarithm numerator nor their auxiliary divisor order one.
-/
namespace ImbalancedChen.P5Z.ActualHBRoughOnePrefix
noncomputable section
open Classical Filter Finset
open scoped Topology BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.ActualRoughContourParameters20261026b
open ActualHBRoughBrunFinite ActualHBRoughBrunRates
open ActualHBGroupLogAbelPrefix OriginalBetaPrimeSource

theorem roughOne_Ioc_bound {z : ℝ} (hz : 1 ≤ z) (j L H q b : ℕ)
    (hLH : L ≤ H) (hq : 0 < q) (hb : b.Coprime q) :
    ‖auxiliarySWError (Ioc L H) (roughOneSlot z) 1 q b‖ ≤
      12*z^(2*j+1) + 2*gapDensity z j*((H-L : ℕ) : ℝ)/(q : ℝ) := by
  have he : Ico (L+1) (H+1) = Ioc L H := by
    ext n
    simp only [mem_Ico, mem_Ioc]
    omega
  have h := roughOne_interval_bound hz j (L+1) (H+1) q b (by omega) hq hb
  simpa only [he, Nat.add_sub_add_right] using h

/-- Literal maximum over every prefix of the SAME positive carrier.
The bound includes the exact mean and both interval endpoint errors. -/
theorem roughOne_prefixNorm_bound {z : ℝ} (hz : 1 ≤ z) (j : ℕ)
    {U u v : ℝ} (hU : 0 < U) (hUu : U ≤ u) (huv : u ≤ v) (hvU : v ≤ 2*U)
    (q b : ℕ) (hq : 0 < q) (hb : b.Coprime q) :
    prefixNorm (roughOneSlot z) u v q b ≤ 12*z^(2*j+1)+4*gapDensity z j*U := by
  have he0 := gapDensity_nonneg z j
  have hv0 : 0 ≤ v := hU.le.trans (hUu.trans huv)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  apply Finset.sup'_le
  intro H hH
  by_cases hlow : H ≤ Nat.floor u
  · simp only [prefix, Finset.Ioc_eq_empty_of_le hlow, Finset.sum_empty, norm_zero]
    positivity
  have hLH : Nat.floor u ≤ H := by omega
  have hHle : H ≤ Nat.floor v := Nat.lt_succ_iff.mp (Finset.mem_range.mp hH)
  have hlen : ((H-Nat.floor u : ℕ) : ℝ) ≤ 2*U := by
    calc
      _ ≤ (H : ℝ) := by exact_mod_cast Nat.sub_le H (Nat.floor u)
      _ ≤ (Nat.floor v : ℝ) := by exact_mod_cast hHle
      _ ≤ v := Nat.floor_le hv0
      _ ≤ _ := hvU
  have h := roughOne_Ioc_bound hz j (Nat.floor u) H q b hLH hq hb
  rw [error_eq_kernel] at h
  change ‖prefix (roughOneSlot z) u q b H‖ ≤ _ at h
  have hpay : 2*gapDensity z j*((H-Nat.floor u : ℕ) : ℝ)/(q : ℝ) ≤
      4*gapDensity z j*U := by
    calc
      _ ≤ 2*gapDensity z j*((H-Nat.floor u : ℕ) : ℝ) :=
        div_le_self (by positivity) hq1
      _ ≤ 2*gapDensity z j*(2*U) :=
        mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = _ := by ring
  exact h.trans (add_le_add_left hpay _)

/-- One threshold precedes U,u,v,q,b. Only xi>0 is required; A may be
any fixed real. There is no upper scale bound on U or upper modulus cap. -/
theorem eventually_roughOne_prefix_log_saving (xi A : ℝ) (hxi : 0 < xi) :
    ∀ᶠ x : ℝ in atTop, ∀ U u v : ℝ, ∀ q b : ℕ,
      x^xi ≤ U → U ≤ u → u ≤ v → v ≤ 2*U →
      0 < q → b.Coprime q →
      prefixNorm (roughOneSlot (roughZ x)) u v q b ≤
        16*U/(Real.log x)^A := by
  filter_upwards [eventually_actual_brun_payments xi A hxi] with x hx
  intro U u v q b hscale hUu huv hvU hq hb
  have hxp : 0 < x := zero_lt_one.trans hx.1
  have hU : 0 < U := (Real.rpow_pos_of_pos hxp xi).trans_le hscale
  have hden : 0 < (Real.log x)^A := Real.rpow_pos_of_pos hx.2.2.1 _
  have hY : supportSize x ≤ U/(Real.log x)^A :=
    hx.2.2.2.1.trans (div_le_div_of_nonneg_right hscale hden.le)
  have he := hx.2.2.2.2.1
  have h := roughOne_prefixNorm_bound hx.2.1 (halfOrder x) hU hUu huv hvU q b hq hb
  change prefixNorm (roughOneSlot (roughZ x)) u v q b ≤
    12*supportSize x+4*epsilon x*U at h
  calc
    _ ≤ 12*supportSize x+4*epsilon x*U := h
    _ ≤ 12*(U/(Real.log x)^A)+4*(1/(Real.log x)^A)*U :=
      add_le_add (mul_le_mul_of_nonneg_left hY (by norm_num))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he (by norm_num)) hU.le)
    _ = _ := by ring

/-- The requested k=1 discrepancy, with its literal coprime coefficient
mass /phi(q), follows from the computed prefix maximum. -/
theorem eventually_roughOne_interval_log_saving (xi A : ℝ) (hxi : 0 < xi) :
    ∀ᶠ x : ℝ in atTop, ∀ U u v : ℝ, ∀ q b : ℕ,
      x^xi ≤ U → U ≤ u → u ≤ v → v ≤ 2*U →
      0 < q → b.Coprime q →
      ‖auxiliarySWError (Ioc (Nat.floor u) (Nat.floor v))
        (roughOneSlot (roughZ x)) 1 q b‖ ≤ 16*U/(Real.log x)^A := by
  filter_upwards [eventually_roughOne_prefix_log_saving xi A hxi] with x hx
  intro U u v q b hscale hUu huv hvU hq hb
  rw [error_eq_kernel]
  exact (prefix_le (roughOneSlot (roughZ x)) u v q b le_rfl).trans
    (hx U u v q b hscale hUu huv hvU hq hb)

end
end ImbalancedChen.P5Z.ActualHBRoughOnePrefix
