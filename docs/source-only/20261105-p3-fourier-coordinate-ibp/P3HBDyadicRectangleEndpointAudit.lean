import ImbalancedChen.P3HBRankAdaptiveRetainedSupport
import Mathlib.Tactic

/-!
P3.6 / frozen manuscript §2: audit of literal HB dyadic rectangle lower
endpoints. SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Actual psi(x/L)=chi(x/L)-chi(2*x/L) is supported in [L/2,2L],
so its upper/lower endpoint ratio is FOUR. Six slots imply the safe
bound R/(2*4^6)=R/8192 from the group cutoff, not R/128.
The R/128 inference for the UNREFINED six-axis psi-support boxes is
refuted by the live sample below. The manuscript's R/128 may still hold
for a separately refined 2-to-1 HB rectangle family, but the existence
and source-preserving coverage of that second subdivision are NOT yet
proved here. No PP estimate is assumed or proved.
Manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
§2 lines 84-112. Lean v4.33.0-rc1, Mathlib
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
-/

namespace ImbalancedChen.P3HBDyadicRectangleEndpointAudit
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3HBDyadicTensorPartition
open ImbalancedChen.P3HBRankAdaptiveRetainedSupport

/-- A nonzero literal dyadic piece has strict upper endpoint x<2L. -/
theorem dyadic_piece_lt_double_base (chi : ℝ → ℂ) (x : ℝ) (j : ℕ)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hlive : dyadicPiece chi x j ≠ 0) :
    x < 2 * (2 : ℝ) ^ j := by
  by_contra h
  have hx : 2 * (2 : ℝ) ^ j ≤ x := le_of_not_gt h
  have hp : 0 < (2 : ℝ) ^ j := by positivity
  have hfirst : 2 ≤ x / (2 : ℝ) ^ j :=
    (le_div_iff₀ hp).2 hx
  have hsecond : 2 ≤ 2 * x / (2 : ℝ) ^ j :=
    (le_div_iff₀ hp).2 (by linarith)
  apply hlive
  unfold dyadicPiece
  rw [hlarge _ hfirst, hlarge _ hsecond]
  ring

/-- The original six-slot tensor preserves the individual upper endpoints. -/
theorem hb_tensor_live_coordinate_upper (chi : ℝ → ℂ)
    (label : Fin 6 → ℕ) (marked hb : List ℕ)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hlive : hbDyadicCut chi label marked hb ≠ 0) (i : Fin 6) :
    ((hb.getD i.val 1 : ℕ) : ℝ) <
      2 * (2 : ℝ) ^ (label i) := by
  have hpiece :
      dyadicPiece chi ((hb.getD i.val 1 : ℕ) : ℝ) (label i) ≠ 0 := by
    intro hzero
    apply hlive
    unfold hbDyadicCut
    exact Finset.prod_eq_zero (Finset.mem_univ i) hzero
  exact dyadic_piece_lt_double_base chi _ _ hlarge hpiece

/-- All six rectangle lower endpoints L_i/2, without label coalescence. -/
def sixAxisLowerEndpointProduct (label : Fin 6 → ℕ) : ℝ :=
  (∏ i : Fin 6, (2 : ℝ) ^ (label i)) / 64

theorem sixAxisLowerEndpointProduct_eq_prod (label : Fin 6 → ℕ) :
    sixAxisLowerEndpointProduct label =
      ∏ i : Fin 6, ((2 : ℝ) ^ (label i)) / 2 := by
  simp [sixAxisLowerEndpointProduct, Finset.prod_div_distrib]

/-- Corrected quantitative envelope from actual six-position cutoff support
and the original strict group window R/2<n, with no arithmetic hypothesis. -/
theorem six_axis_R8192_lower_envelope (x : Fin 6 → ℝ)
    (label : Fin 6 → ℕ) (R : ℝ)
    (hx : ∀ i, 0 ≤ x i)
    (hupper : ∀ i, x i < 2 * (2 : ℝ) ^ (label i))
    (hgroup : R / 2 < ∏ i : Fin 6, x i) :
    R / 8192 < sixAxisLowerEndpointProduct label := by
  have hprod : (∏ i : Fin 6, x i) ≤
      ∏ i : Fin 6, 2 * (2 : ℝ) ^ (label i) := by
    apply Finset.prod_le_prod
    · intro i _
      exact hx i
    · intro i _
      exact (hupper i).le
  have hscale :
      (∏ i : Fin 6, 2 * (2 : ℝ) ^ (label i)) =
      4096 * sixAxisLowerEndpointProduct label := by
    rw [Finset.prod_mul_distrib]
    simp [sixAxisLowerEndpointProduct]
    <;> ring
  have htotal : R / 2 < 4096 * sixAxisLowerEndpointProduct label :=
    lt_of_lt_of_le hgroup (by
      rw [← hscale]
      exact hprod)
  linarith

/-- The stronger R/128 is indeed available IF a separately supplied
six-axis refinement has actual ratio-two intervals x_i ≤ 2*lower_i.
This is a genuine additional geometrical condition, NOT a property
of the coarse psi(x/2^j) support [2^(j-1),2^(j+1)] itself.
The manuscript's exact selected refined rectangles still need proving. -/
theorem refined_two_to_one_R128_lower_envelope
    (x lower : Fin 6 → ℝ) (R : ℝ)
    (hx : ∀ i, 0 ≤ x i)
    (hrefined : ∀ i, x i ≤ 2 * lower i)
    (hgroup : R / 2 < ∏ i : Fin 6, x i) :
    R / 128 < ∏ i : Fin 6, lower i := by
  have hprod : (∏ i : Fin 6, x i) ≤
      ∏ i : Fin 6, 2 * lower i := by
    apply Finset.prod_le_prod
    · intro i _
      exact hx i
    · intro i _
      exact hrefined i
  have hscale :
      (∏ i : Fin 6, 2 * lower i) =
      64 * ∏ i : Fin 6, lower i := by
    rw [Finset.prod_mul_distrib]
    simp
  have htotal : R / 2 < 64 * ∏ i : Fin 6, lower i :=
    lt_of_lt_of_le hgroup (by
      rw [← hscale]
      exact hprod)
  linarith

/-- Genuine group/tensor cutoffs imply the corrected envelope.
hphysical is only the algebraic padded HB product identity and still
requires a source-to-factorTuples bridge, not a PP estimate. -/
theorem original_hb_live_R8192_lower_envelope (chi : ℝ → ℂ)
    (label : Fin 6 → ℕ) (marked hb : List ℕ) (n : ℕ) (R : ℝ)
    (hR : 0 < R)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hgroup : chi ((n : ℝ) / R) - chi (2 * (n : ℝ) / R) ≠ 0)
    (hlive : hbDyadicCut chi label marked hb ≠ 0)
    (hphysical : (∏ i : Fin 6, ((hb.getD i.val 1 : ℕ) : ℝ)) = (n : ℝ)) :
    R / 8192 < sixAxisLowerEndpointProduct label := by
  have hlow : R / 2 < (n : ℝ) :=
    original_group_dyadic_lower_window chi (n : ℝ) R hR hsmall hgroup
  apply six_axis_R8192_lower_envelope
      (fun i : Fin 6 => ((hb.getD i.val 1 : ℕ) : ℝ)) label R
  · intro i
    exact Nat.cast_nonneg _
  · intro i
    exact hb_tensor_live_coordinate_upper chi label marked hb hlarge hlive i
  · simpa [hphysical] using hlow

/-- Any x in the upper half (L,2L) is live when chi is nonzero
inside (1,2), as for standard smooth monotone transition profiles. -/
theorem dyadic_piece_live_in_upper_half (chi : ℝ → ℂ)
    (x : ℝ) (j : ℕ)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hmid : ∀ t : ℝ, 1 < t → t < 2 → chi t ≠ 0)
    (hlo : (2 : ℝ) ^ j < x)
    (hhi : x < 2 * (2 : ℝ) ^ j) :
    dyadicPiece chi x j ≠ 0 := by
  have hp : 0 < (2 : ℝ) ^ j := by positivity
  have hqlo : 1 < x / (2 : ℝ) ^ j :=
    (lt_div_iff₀ hp).2 hlo
  have hqhi : x / (2 : ℝ) ^ j < 2 :=
    (div_lt_iff₀ hp).2 (by simpa [mul_comm] using hhi)
  have hq2 : 2 ≤ 2 * x / (2 : ℝ) ^ j :=
    (le_div_iff₀ hp).2 (by linarith)
  unfold dyadicPiece
  rw [hlarge _ hq2]
  simpa using hmid _ hqlo hqhi

/-- Literal rank-six squarefree HB sample: truncated mu slots 3,5,7,
remaining slots 11,13,19, group n=285285. All six pieces are live. -/
theorem six_prime_live_pieces (chi : ℝ → ℂ)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hmid : ∀ t : ℝ, 1 < t → t < 2 → chi t ≠ 0) :
    dyadicPiece chi 3 1 ≠ 0 ∧
    dyadicPiece chi 5 2 ≠ 0 ∧
    dyadicPiece chi 7 2 ≠ 0 ∧
    dyadicPiece chi 11 3 ≠ 0 ∧
    dyadicPiece chi 13 3 ≠ 0 ∧
    dyadicPiece chi 19 4 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact dyadic_piece_live_in_upper_half chi 3 1 hlarge hmid (by norm_num) (by norm_num)
  · exact dyadic_piece_live_in_upper_half chi 5 2 hlarge hmid (by norm_num) (by norm_num)
  · exact dyadic_piece_live_in_upper_half chi 7 2 hlarge hmid (by norm_num) (by norm_num)
  · exact dyadic_piece_live_in_upper_half chi 11 3 hlarge hmid (by norm_num) (by norm_num)
  · exact dyadic_piece_live_in_upper_half chi 13 3 hlarge hmid (by norm_num) (by norm_num)
  · exact dyadic_piece_live_in_upper_half chi 19 4 hlarge hmid (by norm_num) (by norm_num)

/-- Exact rational contradiction to UNREFINED R/128 for a live rank-six
dyadic rectangle: lower endpoints 1,2,2,4,4,8 multiply to 512,
whereas 285285/128 exceeds 512. -/
theorem six_prime_rectangle_refutes_R128 :
    ¬ ((285285 : ℝ) / 128 ≤ (1 : ℝ) * 2 * 2 * 4 * 4 * 8) := by
  norm_num

end ImbalancedChen.P3HBDyadicRectangleEndpointAudit
