import ImbalancedChen.Part3HilbertBoundedWeakSubsequence

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact lower semicontinuity of the sum of two Hilbert gradient energies,
proved from the squared-distance variational inequality. The extracted
weak pair retains the ORIGINAL squared energy constant, rather than the
coarser auxiliary norm constant used to obtain a weak subsequence. -/

namespace ImbalancedChen.Part3.HilbertWeakGradientEnergyBound20261026b
noncomputable section
open Filter
open scoped Topology
open HilbertBoundedWeakSubsequence20261026b

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem weak_pair_energy_le (X Y : ℕ → E) (gx gy : E) (C : ℝ)
    (hx : ∀ z, Tendsto (fun n => inner ℂ z (X n)) atTop (𝓝 (inner ℂ z gx)))
    (hy : ∀ z, Tendsto (fun n => inner ℂ z (Y n)) atTop (𝓝 (inner ℂ z gy)))
    (hbound : ∀ n, ‖X n‖^2 + ‖Y n‖^2 ≤ C) : ‖gx‖^2 + ‖gy‖^2 ≤ C := by
  have htx : Tendsto (fun n => (inner ℂ gx (X n)).re) atTop (𝓝 (‖gx‖^2)) := by
    simpa only [← InnerProductSpace.norm_sq_eq_re_inner] using (hx gx).re
  have hty : Tendsto (fun n => (inner ℂ gy (Y n)).re) atTop (𝓝 (‖gy‖^2)) := by
    simpa only [← InnerProductSpace.norm_sq_eq_re_inner] using (hy gy).re
  have ht : Tendsto (fun n =>
      2*(inner ℂ gx (X n)).re + 2*(inner ℂ gy (Y n)).re - (‖gx‖^2+‖gy‖^2))
      atTop (𝓝 (‖gx‖^2+‖gy‖^2)) := by
    convert ((htx.const_mul 2).add (hty.const_mul 2)).sub tendsto_const_nhds using 1 <;> ring
  apply le_of_tendsto ht
  exact Eventually.of_forall fun n => by
    have hdx := sq_nonneg ‖gx-X n‖
    have hdy := sq_nonneg ‖gy-Y n‖
    rw [norm_sub_sq] at hdx hdy
    have he := hbound n
    nlinarith

variable [CompleteSpace E] [TopologicalSpace.SeparableSpace E]

theorem exists_weak_pair_with_energy_bound (X Y : ℕ → E) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n, ‖X n‖^2 + ‖Y n‖^2 ≤ C) :
    ∃ gx gy : E, ‖gx‖^2+‖gy‖^2 ≤ C ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ z, Tendsto (fun n => inner ℂ z (X (σ n))) atTop (𝓝 (inner ℂ z gx))) ∧
      (∀ z, Tendsto (fun n => inner ℂ z (Y (σ n))) atTop (𝓝 (inner ℂ z gy))) := by
  have hx (n : ℕ) : ‖X n‖ ≤ C+1 := by
    have he := hbound n
    nlinarith [sq_nonneg ‖Y n‖,sq_nonneg (‖X n‖-1),norm_nonneg (X n)]
  have hy (n : ℕ) : ‖Y n‖ ≤ C+1 := by
    have he := hbound n
    nlinarith [sq_nonneg ‖X n‖,sq_nonneg (‖Y n‖-1),norm_nonneg (Y n)]
  obtain ⟨gx,gy,_,_,σ,hσ,hxl,hyl⟩ := exists_two_bounded_weak_subsequences X Y (C+1) hx hy
  exact ⟨gx,gy,weak_pair_energy_le (fun n => X (σ n)) (fun n => Y (σ n)) gx gy C
    hxl hyl (fun n => hbound (σ n)),σ,hσ,hxl,hyl⟩

end
end ImbalancedChen.Part3.HilbertWeakGradientEnergyBound20261026b
