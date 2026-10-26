import ImbalancedChen.Part3LocalRectangleFourierTail
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Actual product-circle finite BOX projection, quantitative two-derivative
error, compact bounded low-frequency images and total boundedness of the
actual Fourier H1 ball. The physical compact-rectangle derivative bridge
is supplied separately; no Rellich or compact embedding is an input. -/

namespace ImbalancedChen.Part3.ProductCircleFiniteBoxRellich20261026a
noncomputable section
open Set MeasureTheory Filter Topology Metric
open scoped BigOperators ENNReal
open LocalRectangleFourierTail20261026a

abbrev Torus := UnitAddTorus (Fin 2)
abbrev TorusL2 := Lp ℂ 2 (volume : Measure Torus)
abbrev Frequency := Fin 2 → ℤ

def box (K : ℕ) : Finset Frequency := Fintype.piFinset (fun _ => frequencyWindow K)

def projection (K : ℕ) (u : TorusL2) : TorusL2 :=
  ∑ k ∈ box K, UnitAddTorus.mFourierCoeff u k • UnitAddTorus.mFourierBasis k

def DerivativePair (u : TorusL2) (D : Fin 2 → TorusL2) : Prop :=
  ∀ j k, UnitAddTorus.mFourierCoeff (D j) k =
    (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) * UnitAddTorus.mFourierCoeff u k

def energyBall (B E : ℝ) : Set TorusL2 :=
  {u | ‖u‖ ≤ B ∧ ∃ D : Fin 2 → TorusL2, DerivativePair u D ∧ ∑ j, ‖D j‖^2 ≤ E}

theorem norm_square_integral (u : TorusL2) :
    ‖u‖^2 = ∫ z : Torus, ‖u z‖^2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner u u)]
  simp only [inner_self_eq_norm_sq_to_K, Complex.ofReal_re]

theorem parseval_norm (u : TorusL2) :
    HasSum (fun k : Frequency => ‖UnitAddTorus.mFourierCoeff u k‖^2) (‖u‖^2) := by
  simpa only [norm_square_integral] using UnitAddTorus.hasSum_sq_mFourierCoeff u

theorem projection_coefficient (K : ℕ) (u : TorusL2) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (u - projection K u) k =
      if k ∈ box K then 0 else UnitAddTorus.mFourierCoeff u k := by
  let b := UnitAddTorus.mFourierBasis (d := Fin 2)
  have hr : b.repr (u - projection K u) =
      b.repr u - ∑ m ∈ box K, b.repr u m • lp.single 2 m (1 : ℂ) := by
    simp only [projection, map_sub, map_sum, map_smul,
      ← UnitAddTorus.mFourierBasis_repr, HilbertBasis.repr_self]
  rw [← UnitAddTorus.mFourierBasis_repr]
  change b.repr (u - projection K u) k = _
  rw [hr]
  by_cases hk : k ∈ box K <;> simp [hk, ← UnitAddTorus.mFourierBasis_repr, b]

theorem projection_error_square (K : ℕ) (u : TorusL2) :
    ‖u - projection K u‖^2 =
      ∑' k : Frequency, if k ∈ box K then 0 else ‖UnitAddTorus.mFourierCoeff u k‖^2 := by
  rw [← (parseval_norm (u - projection K u)).tsum_eq]
  apply tsum_congr
  intro k
  rw [projection_coefficient]
  split_ifs <;> simp

private theorem outside_box_frequency (K : ℕ) (k : Frequency) (hk : k ∉ box K) :
    ∃ j : Fin 2, (K : ℝ) ≤ ‖(k j : ℂ)‖ := by
  have hj : ∃ j : Fin 2, k j ∉ frequencyWindow K := by
    by_contra h
    exact hk (Fintype.mem_piFinset.mpr (by simpa only [not_exists, not_not] using h))
  obtain ⟨j, hj⟩ := hj
  refine ⟨j, ?_⟩
  rw [Complex.norm_intCast]
  by_contra h
  have habs := abs_le.mp (lt_of_not_ge h).le
  exact hj (Finset.mem_Icc.mpr ⟨by exact_mod_cast habs.1, by exact_mod_cast habs.2⟩)

/-- Both physical derivatives enter a single FINITE box error estimate.
No directionwise infinite-rank truncation is called finite rank. -/
theorem projection_error_le (K : ℕ) (hK : 0 < K) (u : TorusL2)
    (D : Fin 2 → TorusL2) (hD : DerivativePair u D) :
    ‖u - projection K u‖^2 ≤ tailConstant K * ∑ j, ‖D j‖^2 := by
  let C : ℝ := 4 * Real.pi^2 * (K : ℝ)^2
  have hC : 0 < C := by dsimp [C]; positivity
  have htail : Summable (fun k : Frequency =>
      if k ∈ box K then 0 else ‖UnitAddTorus.mFourierCoeff u k‖^2) := by
    apply Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity)
      (fun k => by split_ifs <;> positivity) (parseval_norm u).summable
  have hsum : Summable (fun k : Frequency =>
      ∑ j : Fin 2, ‖UnitAddTorus.mFourierCoeff (D j) k‖^2) := by
    simpa only [Fin.sum_univ_two] using
      (parseval_norm (D 0)).summable.add (parseval_norm (D 1)).summable
  have hsumEq : (∑' k : Frequency,
      ∑ j : Fin 2, ‖UnitAddTorus.mFourierCoeff (D j) k‖^2) = ∑ j, ‖D j‖^2 := by
    simp only [Fin.sum_univ_two]
    rw [(parseval_norm (D 0)).summable.tsum_add (parseval_norm (D 1)).summable,
      (parseval_norm (D 0)).tsum_eq, (parseval_norm (D 1)).tsum_eq]
  have hp (k : Frequency) :
      C * (if k ∈ box K then 0 else ‖UnitAddTorus.mFourierCoeff u k‖^2) ≤
        ∑ j : Fin 2, ‖UnitAddTorus.mFourierCoeff (D j) k‖^2 := by
    split_ifs with hk
    · simp only [mul_zero]
      positivity
    · obtain ⟨j, hj⟩ := outside_box_frequency K k hk
      have hf : ‖2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)‖ =
          (2 * Real.pi) * ‖(k j : ℂ)‖ := by
        simp [norm_mul, Complex.norm_ofReal, abs_of_pos Real.pi_pos]
      have hscale := mul_le_mul_of_nonneg_left hj (show 0 ≤ 2 * Real.pi by positivity)
      have hsq := pow_le_pow_left₀ (by positivity) hscale 2
      apply le_trans _ (Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ j))
      rw [hD j k, norm_mul, hf, mul_pow]
      dsimp [C]
      nlinarith [mul_le_mul_of_nonneg_right hsq
        (sq_nonneg (‖UnitAddTorus.mFourierCoeff u k‖))]
  have hle := (htail.mul_left C).tsum_le_tsum hp hsum
  rw [htail.tsum_mul_left, hsumEq] at hle
  rw [← projection_error_square] at hle
  have hquot := (le_div_iff₀ hC).mpr (by simpa only [mul_comm] using hle)
  simpa only [tailConstant, C, div_eq_mul_inv, mul_comm] using hquot

def synthesis (K : ℕ) (a : ↥(box K) → ℂ) : TorusL2 :=
  ∑ k : ↥(box K), a k • UnitAddTorus.mFourierBasis (k : Frequency)

theorem synthesis_continuous (K : ℕ) : Continuous (synthesis K) := by
  unfold synthesis
  exact continuous_finsetSum _ (fun k _ => (continuous_apply k).smul continuous_const)

theorem projection_eq_synthesis (K : ℕ) (u : TorusL2) :
    projection K u = synthesis K (fun k => UnitAddTorus.mFourierCoeff u k) := by
  simp only [projection, synthesis, Finset.univ_eq_attach, Finset.sum_attach]

/-- Bounded low-frequency images lie in a continuous image of a compact
FINITE coefficient cube. This proves total boundedness, rather than
assuming finite rank implies compactness without a norm bound. -/
theorem low_box_image_totallyBounded (K : ℕ) (s : Set TorusL2) (B : ℝ)
    (hs : ∀ u ∈ s, ‖u‖ ≤ B) : TotallyBounded (projection K '' s) := by
  let A : Set (↥(box K) → ℂ) := Set.pi univ (fun _ => closedBall (0 : ℂ) B)
  have hA : IsCompact A := isCompact_pi_infinite (fun _ => isCompact_closedBall _ _)
  have hc := hA.image (synthesis_continuous K)
  apply hc.totallyBounded.subset
  rintro v ⟨u, hu, rfl⟩
  refine ⟨fun k => UnitAddTorus.mFourierCoeff u k, ?_, (projection_eq_synthesis K u).symm⟩
  intro k _
  have hb : ‖UnitAddTorus.mFourierCoeff u (k : Frequency)‖ ≤ ‖u‖ := by
    rw [← UnitAddTorus.mFourierBasis_repr]
    exact (lp.norm_apply_le_norm (by norm_num) _ _).trans_eq
      (UnitAddTorus.mFourierBasis.repr.norm_map u)
  simpa only [mem_closedBall, dist_zero_right] using hb.trans (hs u hu)

/-- Actual Rellich total boundedness on the product-circle Fourier H1
ball. The witnesses are the two actual L2 derivative coordinates, and
their exact coefficient equations, not a compact embedding hypothesis. -/
theorem energyBall_totallyBounded (B E : ℝ) (hE : 0 ≤ E) :
    TotallyBounded (energyBall B E) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  have ht : Tendsto (fun K => tailConstant K * E) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using tailConstant_tendsto_zero.mul_const E
  have he : ∀ᶠ K : ℕ in atTop, tailConstant K * E < (ε/2)^2 :=
    ht.eventually (gt_mem_nhds (by positivity))
  obtain ⟨K, hK, hsmall⟩ := ((eventually_gt_atTop 0).and he).exists
  have happrox (u : TorusL2) (hu : u ∈ energyBall B E) :
      ‖u - projection K u‖ < ε/2 := by
    obtain ⟨_huB, D, hD, hDE⟩ := hu
    have hsq := (projection_error_le K hK u D hD).trans
      (mul_le_mul_of_nonneg_left hDE (by unfold tailConstant; positivity))
    exact (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp (hsq.trans_lt hsmall)
  have hlow := low_box_image_totallyBounded K (energyBall B E) B (fun u hu => hu.1)
  obtain ⟨t, htfinite, hcover⟩ := Metric.totallyBounded_iff.mp hlow (ε/2) (by positivity)
  refine ⟨t, htfinite, ?_⟩
  intro u hu
  obtain ⟨v, hv, huv⟩ := Set.mem_iUnion₂.mp (hcover ⟨u, hu, rfl⟩)
  apply Set.mem_iUnion₂.mpr
  refine ⟨v, hv, ?_⟩
  apply lt_of_le_of_lt (dist_triangle u (projection K u) v)
  have ha : dist u (projection K u) < ε/2 := by simpa only [dist_eq_norm] using happrox u hu
  exact (add_lt_add ha huv).trans_le (by ring_nf)

end
end ImbalancedChen.Part3.ProductCircleFiniteBoxRellich20261026a
