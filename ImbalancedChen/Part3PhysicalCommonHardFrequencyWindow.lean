import ImbalancedChen.Part3PhysicalHardSchwartzTail

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
One raw hard common completed-m window for every 0<q≤10C:
Icc(-ceil(10*C*Z/M),ceil(10*C*Z/M)). It has no residue, factor, coefficient,
or unit-z argument. Eta is exactly1; inverse(z) and every mode inside the
window, including zero, are unchanged. Actual f,u,v mass lifting is not
part of this generic physical-frequency module.
-/

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail.HardCompletedSchwartz20261026b
noncomputable section
open Classical
open scoped BigOperators

def commonHardWindow (C M Z : ℝ) : Finset ℤ :=
  Finset.Icc (-(Nat.ceil (10 * C * Z / M) : ℤ)) (Nat.ceil (10 * C * Z / M) : ℤ)

theorem zero_mem_commonHardWindow (C M Z : ℝ) : 0 ∈ commonHardWindow C M Z := by
  apply Finset.mem_Icc.mpr
  constructor <;> omega

/-- The common radius is selected before q and the residue/factor family.
Every omitted completed mode is at the true physical frequency at least Z. -/
theorem outside_commonHardWindow_frequency (C M Z : ℝ)
    (hC : 0 < C) (hM : 0 < M) (hZ : 0 < Z)
    (q : ℕ) (hq : 0 < q) (hqC : (q : ℝ) ≤ 10 * C)
    (m : ℤ) (hm : m ∉ commonHardWindow C M Z) :
    Z ≤ |(M / (q : ℝ)) * (m : ℝ)| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hAbs : (Nat.ceil (10 * C * Z / M) : ℤ) < |m| := by
    apply lt_of_not_ge
    intro h
    exact hm (Finset.mem_Icc.mpr (abs_le.mp h))
  have hAbsR : (Nat.ceil (10 * C * Z / M) : ℝ) < |(m : ℝ)| := by exact_mod_cast hAbs
  have hceil : 10 * C * Z / M ≤ (Nat.ceil (10 * C * Z / M) : ℝ) := Nat.le_ceil _
  have hmul := (div_lt_iff₀ hM).mp (hceil.trans_lt hAbsR)
  have hzq : Z * (q : ℝ) ≤ 10 * C * Z := by
    nlinarith [mul_le_mul_of_nonneg_right hqC hZ.le]
  have hbound : Z ≤ (M * |(m : ℝ)|) / (q : ℝ) := by
    apply (le_div_iff₀ hqR).mpr
    nlinarith only [hmul, hzq]
  rw [abs_mul, abs_of_pos (div_pos hM hqR)]
  simpa only [div_mul_eq_mul_div] using hbound

/-- The constant is fixed by r before all physical parameters. One and
the same hard K works for every positive q≤10C and every a,y,z, with no
unit hypothesis and the original inverse(z) retained inside frequency. -/
theorem frequency_common_hard_window_tail (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : ℝ, 0 < C → ∀ M : ℝ, 0 < M →
      ∀ Z : ℝ, 0 < Z → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ 10 * C →
      ∀ a y z : ℤ,
        Summable (fun m => ‖hardOmitted (commonHardWindow C M Z) (frequency M q a y z) m‖) ∧
        (∑' m : ℤ, ‖hardOmitted (commonHardWindow C M Z) (frequency M q a y z) m‖) ≤
          A * (q : ℝ) / Z ^ (r - 1) ∧
        ‖(∑' m : ℤ, frequency M q a y z m) -
            ∑ m ∈ commonHardWindow C M Z, frequency M q a y z m‖ ≤
          A * (q : ℝ) / Z ^ (r - 1) := by
  obtain ⟨A, hA, htail⟩ := frequency_hard_window_tail r hr
  refine ⟨A, hA, ?_⟩
  intro C hC M hM Z hZ q hq hqC a y z
  exact htail M hM q hq Z hZ (commonHardWindow C M Z)
    (zero_mem_commonHardWindow C M Z)
    (fun m hm => outside_commonHardWindow_frequency C M Z hC hM hZ q hq hqC m hm) a y z

/-- A simultaneous cap form, useful before a positive coefficient mass is
inserted. No selected coefficient/mass appears among these assumptions. -/
theorem frequency_common_hard_window_tail_cap (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : ℝ, 0 < C → ∀ M : ℝ, 0 < M →
      ∀ Z : ℝ, 0 < Z → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ 10 * C → ∀ a y z : ℤ,
        ‖(∑' m : ℤ, frequency M q a y z m) -
            ∑ m ∈ commonHardWindow C M Z, frequency M q a y z m‖ ≤
          10 * A * C / Z ^ (r - 1) := by
  obtain ⟨A, hA, htail⟩ := frequency_common_hard_window_tail r hr
  refine ⟨A, hA, ?_⟩
  intro C hC M hM Z hZ q hq hqC a y z
  have h := (htail C hC M hM Z hZ q hq hqC a y z).2.2
  have hscale := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hqC hA.le) (pow_nonneg hZ.le (r - 1))
  calc
    _ ≤ A * (q : ℝ) / Z ^ (r - 1) := h
    _ ≤ _ := by nlinarith only [hscale]

end
end ImbalancedChen.Part3.OriginalSmoothPoissonTail.HardCompletedSchwartz20261026b
