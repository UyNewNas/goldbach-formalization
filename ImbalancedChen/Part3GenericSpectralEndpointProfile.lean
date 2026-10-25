import ImbalancedChen.Part3GenericSpectralLeftLimit

/-!
Specific endpoint-weighted interval calculus needed for strong Stone.
The operator Q_(A,B)=1/2(P_B+P_<B-P_A-P_<A) is approximated by actual
continuous CFC ramps, with a genuine f-dependent diagonal choice proved
from the already established strong ramp limits. A lower bound on the
diagonal index ensures the correct OPEN endpoint, including its atom.
Actual μ-DCT then proves the exact CFC-versus-Q error norm identity.
No global Borel calculus, limiting-vector premise or Stone identity input.
SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
-/

namespace ImbalancedChen.Part3.GenericSpectralEndpointProfile20261025a
noncomputable section
open MeasureTheory Filter
open scoped Topology
open GenericResolventScalarMeasure20261025a ClosedIntervalSpectralRamps20261025a
open GenericIntervalProjectionLimit20261025a GenericSpectralLeftLimit20261025a

def endpointStep (A B r : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (closedCut B r + strictCut B r - closedCut A r - strictCut A r)

theorem moving_ramp_zero {a r : ℝ} (har : a ≤ r) {n m : ℕ} (hnm : n ≤ m) :
    ramp (below a n) m r = 0 := by
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hcast : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
  have hlow : 1 / ((n : ℝ) + 1) ≤ r - below a n := by dsimp [below]; linarith
  have hprod : 1 ≤ ((m : ℝ) + 1) * (r - below a n) := by
    calc
      _ ≤ ((m : ℝ) + 1) / ((n : ℝ) + 1) := (le_div_iff₀ hden).mpr (by simpa using hcast)
      _ = ((m : ℝ) + 1) * (1 / ((n : ℝ) + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
  have hh : min 1 (1 - ((m : ℝ) + 1) * (r - below a n)) ≤ 0 :=
    (min_le_right _ _).trans (by linarith)
  exact max_eq_left hh

theorem moving_ramp_eventually_strict (a r : ℝ) (m : ℕ → ℕ) (hm : ∀ n, n ≤ m n) :
    (fun n => ramp (below a n) (m n) r) =ᶠ[atTop] (fun _ => strictCut a r) := by
  by_cases hr : r < a
  · have ht := (below_tendsto a).eventually (gt_mem_nhds hr)
    filter_upwards [ht] with n hn
    simp only [ramp_eq_one_of_le hn.le, strictCut, if_pos hr]
  · exact Eventually.of_forall (fun n => by
      rw [moving_ramp_zero (le_of_not_gt hr) (hm n)]
      simp only [strictCut, if_neg hr])

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

def endpointOperator (A B : ℝ) : H →L[ℂ] H :=
  (1 / 2 : ℝ) • (intervalProjection R hSA B + leftProjection R hSA B -
    intervalProjection R hSA A - leftProjection R hSA A)

theorem exists_diagonal_index (A B : ℝ) (f : H) (n : ℕ) :
    ∃ m : ℕ, n ≤ m ∧
      ‖rampOperator R hSA (below A n) m f - intervalProjection R hSA (below A n) f‖ <
        1 / ((n : ℝ) + 1) ∧
      ‖rampOperator R hSA (below B n) m f - intervalProjection R hSA (below B n) f‖ <
        1 / ((n : ℝ) + 1) := by
  have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  have hA := (tendsto_iff_norm_sub_tendsto_zero.mp
    (tendsto_intervalProjection R hSA (below A n) f)).eventually (gt_mem_nhds hpos)
  have hB := (tendsto_iff_norm_sub_tendsto_zero.mp
    (tendsto_intervalProjection R hSA (below B n) f)).eventually (gt_mem_nhds hpos)
  have hall : ∀ᶠ m in atTop, n ≤ m ∧
      ‖rampOperator R hSA (below A n) m f - intervalProjection R hSA (below A n) f‖ <
        1 / ((n : ℝ) + 1) ∧
      ‖rampOperator R hSA (below B n) m f - intervalProjection R hSA (below B n) f‖ <
        1 / ((n : ℝ) + 1) := by
    filter_upwards [eventually_ge_atTop n, hA, hB] with m hm ha hb
    exact ⟨hm, ha, hb⟩
  exact hall.exists

def diagonalIndex (A B : ℝ) (f : H) (n : ℕ) : ℕ :=
  (exists_diagonal_index R hSA A B f n).choose

theorem diagonalIndex_ge (A B : ℝ) (f : H) (n : ℕ) : n ≤ diagonalIndex R hSA A B f n :=
  (exists_diagonal_index R hSA A B f n).choose_spec.1

theorem moving_ramp_vector_tendsto (a : ℝ) (f : H) (m : ℕ → ℕ)
    (herror : ∀ n, ‖rampOperator R hSA (below a n) (m n) f -
      intervalProjection R hSA (below a n) f‖ < 1 / ((n : ℝ) + 1)) :
    Tendsto (fun n => rampOperator R hSA (below a n) (m n) f) atTop
      (𝓝 (leftProjection R hSA a f)) := by
  have hnorm : Tendsto (fun n => ‖rampOperator R hSA (below a n) (m n) f -
      intervalProjection R hSA (below a n) f‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => (herror n).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hzero := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hsum := hzero.add (tendsto_leftProjection R hSA a f)
  simpa only [sub_add_cancel, zero_add] using hsum

def diagonalMap (A B : ℝ) (f : H) (n : ℕ) : C(ResolventSpectrum R, ℝ) :=
  (1 / 2 : ℝ) • (spectralRamp R B n + spectralRamp R (below B n) (diagonalIndex R hSA A B f n) -
    spectralRamp R A n - spectralRamp R (below A n) (diagonalIndex R hSA A B f n))

theorem diagonalMap_bounds (A B : ℝ) (f : H) (n : ℕ) (r : ResolventSpectrum R) :
    |diagonalMap R hSA A B f n r| ≤ 1 := by
  have h1 := ramp_bounds B n (r : ℝ)
  have h2 := ramp_bounds (below B n) (diagonalIndex R hSA A B f n) (r : ℝ)
  have h3 := ramp_bounds A n (r : ℝ)
  have h4 := ramp_bounds (below A n) (diagonalIndex R hSA A B f n) (r : ℝ)
  change |(1 / 2 : ℝ) * (ramp B n (r : ℝ) +
    ramp (below B n) (diagonalIndex R hSA A B f n) (r : ℝ) - ramp A n (r : ℝ) -
    ramp (below A n) (diagonalIndex R hSA A B f n) (r : ℝ))| ≤ 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem diagonalMap_eventually_step (A B : ℝ) (f : H) (r : ResolventSpectrum R) :
    (fun n => diagonalMap R hSA A B f n r) =ᶠ[atTop] (fun _ => endpointStep A B (r : ℝ)) := by
  filter_upwards [ramp_eventually_eq_cut B (r : ℝ), ramp_eventually_eq_cut A (r : ℝ),
    moving_ramp_eventually_strict B (r : ℝ) (diagonalIndex R hSA A B f)
      (diagonalIndex_ge R hSA A B f),
    moving_ramp_eventually_strict A (r : ℝ) (diagonalIndex R hSA A B f)
      (diagonalIndex_ge R hSA A B f)] with n hB hA hBo hAo
  change (1 / 2 : ℝ) * (ramp B n (r : ℝ) +
    ramp (below B n) (diagonalIndex R hSA A B f n) (r : ℝ) - ramp A n (r : ℝ) -
    ramp (below A n) (diagonalIndex R hSA A B f n) (r : ℝ)) = _
  rw [hB, hA, hBo, hAo]
  rfl

theorem diagonalMap_vector_tendsto (A B : ℝ) (f : H) :
    Tendsto (fun n => resolventCFC R hSA (diagonalMap R hSA A B f n) f) atTop
      (𝓝 (endpointOperator R hSA A B f)) := by
  have hA := moving_ramp_vector_tendsto R hSA A f (diagonalIndex R hSA A B f)
    (fun n => (exists_diagonal_index R hSA A B f n).choose_spec.2.1)
  have hB := moving_ramp_vector_tendsto R hSA B f (diagonalIndex R hSA A B f)
    (fun n => (exists_diagonal_index R hSA A B f n).choose_spec.2.2)
  have hsum := (((tendsto_intervalProjection R hSA B f).add hB).sub
    (tendsto_intervalProjection R hSA A f)).sub hA
  simpa only [diagonalMap, map_smul, map_sub, map_add,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    endpointOperator, rampOperator] using hsum.const_smul (1 / 2 : ℝ)

/-- Exact actual-mu error identity for this specific endpoint-weighted
operator. The comparison vector is constructed from strong projection
limits; no Borel norm or Stone formula is supplied as a hypothesis. -/
theorem cfc_endpoint_error_norm_sq (A B : ℝ) (f : H) (phi : C(ResolventSpectrum R, ℝ)) :
    ‖resolventCFC R hSA phi f - endpointOperator R hSA A B f‖ ^ 2 =
      ∫ r : ResolventSpectrum R, (phi r - endpointStep A B (r : ℝ)) ^ 2
        ∂scalarMeasure R hSA f := by
  have hmeas (n : ℕ) : Measurable (fun r : ResolventSpectrum R =>
      (phi r - diagonalMap R hSA A B f n r) ^ 2) :=
    ((phi.continuous.measurable.sub (diagonalMap R hSA A B f n).continuous.measurable).pow_const 2)
  have hdct := tendsto_integral_of_dominated_convergence
    (μ := scalarMeasure R hSA f)
    (F := fun n r => (phi r - diagonalMap R hSA A B f n r) ^ 2)
    (f := fun r : ResolventSpectrum R => (phi r - endpointStep A B (r : ℝ)) ^ 2)
    (fun _ => (‖phi‖ + 1) ^ 2)
    (fun n => (hmeas n).aestronglyMeasurable) (integrable_const _)
    (fun n => Eventually.of_forall (fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hp : |phi r| ≤ ‖phi‖ := by simpa only [Real.norm_eq_abs] using phi.norm_coe_le_norm r
      have htriangle : |phi r - diagonalMap R hSA A B f n r| ≤
          |phi r| + |diagonalMap R hSA A B f n r| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          (abs_add_le (phi r) (-diagonalMap R hSA A B f n r))
      have hb : |phi r - diagonalMap R hSA A B f n r| ≤ ‖phi‖ + 1 :=
        htriangle.trans (add_le_add hp (diagonalMap_bounds R hSA A B f n r))
      have hm := mul_le_mul hb hb (abs_nonneg _) (by positivity : 0 ≤ ‖phi‖ + 1)
      nlinarith [sq_abs (phi r - diagonalMap R hSA A B f n r)]))
    (Eventually.of_forall (fun r => by
      apply tendsto_const_nhds.congr'
      filter_upwards [diagonalMap_eventually_step R hSA A B f r] with n hn
      rw [hn]))
  have hnorm : Tendsto (fun n =>
      ‖resolventCFC R hSA phi f - resolventCFC R hSA (diagonalMap R hSA A B f n) f‖ ^ 2)
      atTop (𝓝 (‖resolventCFC R hSA phi f - endpointOperator R hSA A B f‖ ^ 2)) :=
    (tendsto_const_nhds.sub (diagonalMap_vector_tendsto R hSA A B f)).norm.pow 2
  have heq (n : ℕ) :
      ‖resolventCFC R hSA phi f - resolventCFC R hSA (diagonalMap R hSA A B f n) f‖ ^ 2 =
      ∫ r : ResolventSpectrum R, (phi r - diagonalMap R hSA A B f n r) ^ 2
        ∂scalarMeasure R hSA f := by
    have hh := realCFC_norm_sq R hSA f (phi - diagonalMap R hSA A B f n)
    rw [map_sub, ContinuousLinearMap.sub_apply] at hh
    exact hh
  simp_rw [heq] at hnorm
  exact tendsto_nhds_unique hnorm hdct

end
end ImbalancedChen.Part3.GenericSpectralEndpointProfile20261025a
