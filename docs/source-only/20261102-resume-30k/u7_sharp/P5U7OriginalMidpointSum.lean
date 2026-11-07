import ImbalancedChen.P5OriginalSignedMidpoint
import ImbalancedChen.P5U7OriginalMidpointDerivatives

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Complete original 1024-cell midpoint/error binding for BOTH actual U7
scalar integrals. The original prime interval and Fubini correction
interval, their exact endpoints and their positive addition are retained.
There is no numerical endpoint, derivative bound or finite guard premise.
The signed error integrals are not evaluated by this file.
-/

namespace ImbalancedChen.P5U7OriginalMidpoint

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P5OriginalSignedMidpoint P5U7OriginalScalarCorrection

/-- Literal rational mesh, with the saved producer's cell count. -/
def mesh1024 (a b : ℚ) (k : ℕ) : ℚ := a + (b - a) * (k : ℚ) / 1024

theorem mesh1024_zero (a b : ℚ) : mesh1024 a b 0 = a := by simp [mesh1024]

theorem mesh1024_last (a b : ℚ) : mesh1024 a b 1024 = b := by
  norm_num [mesh1024] <;> ring

theorem mesh1024_step (a b : ℚ) (k : ℕ) :
    mesh1024 a b (k + 1) = mesh1024 a b k + (b - a) / 1024 := by
  simp only [mesh1024, Nat.cast_add, Nat.cast_one]
  ring

theorem mesh1024_monotone {a b : ℚ} (hab : a ≤ b) : Monotone (mesh1024 a b) := by
  intro k j hkj
  have hcast : (k : ℚ) ≤ (j : ℚ) := by exact_mod_cast hkj
  exact add_le_add_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcast (sub_nonneg.mpr hab)) (by norm_num)) a

theorem mesh1024_bounds {a b : ℚ} (hab : a ≤ b) (k : ℕ) (hk : k ≤ 1024) :
    a ≤ mesh1024 a b k ∧ mesh1024 a b k ≤ b := by
  have hL := mesh1024_monotone hab (Nat.zero_le k)
  have hU := mesh1024_monotone hab hk
  rw [mesh1024_zero] at hL
  rw [mesh1024_last] at hU
  exact ⟨hL, hU⟩

theorem mesh1024_cell_subset {a b : ℚ} (hab : a ≤ b) {k : ℕ} (hk : k < 1024) :
    Icc (mesh1024 a b k : ℝ) (mesh1024 a b (k + 1) : ℝ) ⊆ Icc (a : ℝ) (b : ℝ) := by
  have hL : (a : ℝ) ≤ (mesh1024 a b k : ℝ) := by
    exact_mod_cast (mesh1024_bounds hab k hk.le).1
  have hU : (mesh1024 a b (k + 1) : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast (mesh1024_bounds hab (k + 1) (by omega)).2
  exact fun x hx => ⟨hL.trans hx.1, hx.2.trans hU⟩

def midpoint1024 (a b : ℚ) (k : ℕ) : ℚ :=
  (mesh1024 a b k + mesh1024 a b (k + 1)) / 2

/-- The exact real expression underlying the producer before outward
rounding: midpoint sample times step PLUS the genuine signed remainder. -/
def exactCell (f f'' : ℝ → ℝ) (a b : ℚ) (k : ℕ) : ℝ :=
  ((b - a : ℚ) / 1024 : ℝ) * f (midpoint1024 a b k : ℝ) +
    midpointError f'' (mesh1024 a b k : ℝ) (mesh1024 a b (k + 1) : ℝ)

def exactSum1024 (f f'' : ℝ → ℝ) (a b : ℚ) : ℝ :=
  ∑ k ∈ Finset.range 1024, exactCell f f'' a b k

private theorem exactCell_eq_integral {f f' f'' : ℝ → ℝ} {a b : ℚ}
    (hab : a ≤ b)
    (hf : ∀ x ∈ Icc (a : ℝ) (b : ℝ), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc (a : ℝ) (b : ℝ), HasDerivAt f' (f'' x) x)
    (hc : ContinuousOn f'' (Icc (a : ℝ) (b : ℝ)))
    {k : ℕ} (hk : k < 1024) :
    exactCell f f'' a b k =
      ∫ x in (mesh1024 a b k : ℝ)..(mesh1024 a b (k + 1) : ℝ), f x := by
  have hs := mesh1024_cell_subset hab hk
  have horder : (mesh1024 a b k : ℝ) ≤ (mesh1024 a b (k + 1) : ℝ) := by
    exact_mod_cast mesh1024_monotone hab (Nat.le_succ k)
  have hid := midpoint_identity horder (fun x hx => hf x (hs hx))
    (fun x hx => hf' x (hs hx)) (hc.mono hs)
  have hstep : (mesh1024 a b (k + 1) : ℝ) - (mesh1024 a b k : ℝ) =
      ((b - a : ℚ) / 1024 : ℝ) := by
    rw [mesh1024_step]
    push_cast
    ring
  rw [hstep] at hid
  simpa only [exactCell, midpoint1024, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat] using hid.symm

/-- Adjacent-interval summation proves complete coverage; there is no
enumerated-cell or finite-sum equality premise. -/
theorem exactSum1024_eq_integral {f f' f'' : ℝ → ℝ} {a b : ℚ}
    (hab : a ≤ b)
    (hf : ∀ x ∈ Icc (a : ℝ) (b : ℝ), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc (a : ℝ) (b : ℝ), HasDerivAt f' (f'' x) x)
    (hc : ContinuousOn f'' (Icc (a : ℝ) (b : ℝ))) :
    exactSum1024 f f'' a b = ∫ x in (a : ℝ)..(b : ℝ), f x := by
  have hcell (k : ℕ) (hk : k < 1024) :
      IntervalIntegrable f volume (mesh1024 a b k : ℝ) (mesh1024 a b (k + 1) : ℝ) := by
    have hs := mesh1024_cell_subset hab hk
    have horder : (mesh1024 a b k : ℝ) ≤ (mesh1024 a b (k + 1) : ℝ) := by
      exact_mod_cast mesh1024_monotone hab (Nat.le_succ k)
    apply ContinuousOn.intervalIntegrable_of_Icc horder
    exact fun x hx => (hf x (hs hx)).continuousAt.continuousWithinAt
  have hpartition := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k => (mesh1024 a b k : ℝ)) hcell
  rw [mesh1024_zero, mesh1024_last] at hpartition
  unfold exactSum1024
  calc
    _ = ∑ k ∈ Finset.range 1024,
        ∫ x in (mesh1024 a b k : ℝ)..(mesh1024 a b (k + 1) : ℝ), f x := by
      apply Finset.sum_congr rfl
      intro k hk
      exact exactCell_eq_integral hab hf hf' hc (Finset.mem_range.mp hk)
    _ = _ := hpartition

/-- The archived prime scalar integral, with the actual producer derivative. -/
theorem primeIntegral_eq_exactSum1024 :
    p5U7ComponentPrimeIntegral = exactSum1024 primeValue primeSecond (59 / 250) (1 / 3) := by
  have hsum := exactSum1024_eq_integral (a := (59 / 250 : ℚ)) (b := (1 / 3 : ℚ))
    (by norm_num) (by simpa using prime_regular.1)
    (by simpa using prime_regular.2.1) (by simpa using prime_regular.2.2)
  rw [hsum, p5U7ComponentPrimeIntegral_eq_logIntegral]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (59 / 250 : ℝ) ≤ 1 / 3)] at ht
  exact (primeValue_eq (by linarith [ht.1]) (by linarith [ht.2])).symm

/-- The archived correction scalar integral, including both closed ends. -/
theorem correctionIntegral_eq_exactSum1024 :
    scalarCorrection = exactSum1024 scalarCorrectionKernel correctionSecond 2 (132 / 59) := by
  have hsum := exactSum1024_eq_integral (a := (2 : ℚ)) (b := (132 / 59 : ℚ))
    (by norm_num) (by simpa using correction_regular.1)
    (by simpa using correction_regular.2.1) (by simpa using correction_regular.2.2)
  simpa only [scalarCorrection, Rat.cast_div, Rat.cast_ofNat] using hsum.symm

/-- The complete original source, both original 1024 sums, and the true
signed error. No coarse correction enclosure is substituted. -/
theorem originalOmegaIntegral_eq_two_exactSum1024 :
    p5U7OriginalOmegaIntegral 1 =
      exactSum1024 primeValue primeSecond (59 / 250) (1 / 3) +
        exactSum1024 scalarCorrectionKernel correctionSecond 2 (132 / 59) := by
  rw [p5U7Component_integral_split, semiprimeIntegral_eq_scalarCorrection,
    primeIntegral_eq_exactSum1024, correctionIntegral_eq_exactSum1024]

/-- Archive K0 multiplies BOTH sums; the root's later multiplicity two
and Chen quarter are absent from this primitive U7 cost identity. -/
theorem archivedU7_eq_two_exactSum1024 :
    p5U7OriginalOmegaIntegral (67619 / 10000) = (67619 / 10000 : ℝ) *
      (exactSum1024 primeValue primeSecond (59 / 250) (1 / 3) +
        exactSum1024 scalarCorrectionKernel correctionSecond 2 (132 / 59)) := by
  rw [originalOmegaIntegral_eq_mul, originalOmegaIntegral_eq_two_exactSum1024]

end
end ImbalancedChen.P5U7OriginalMidpoint
