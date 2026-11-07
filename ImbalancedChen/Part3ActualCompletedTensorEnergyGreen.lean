import ImbalancedChen.Part3ActualCompletedTensorEnergyForm

/-!
The completed energy pairing agrees on its actual core with the actual
shifted coordinate Maass graph. Real polarization uses the already proved
actual norm-energy identity; multiplication by i recovers the imaginary
part. No Green identity or form-operator identification is an input.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualCompletedTensorEnergyGreen20261025a

noncomputable section

open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.MaassFiniteCoreL2LinearOperator20261025a
open ImbalancedChen.Part3.ActualNestedTensorRitzEnergy20261025a
open ImbalancedChen.Part3.ActualCompletedTensorEnergyForm20261025a

theorem coreEmbedding_re_inner_self (u : actualTensorDomain) :
    (inner ℂ (coreEmbedding u) (coreEmbedding u)).re = shiftedEnergy u := by
  rw [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.ofReal_re]
  exact coreEmbedding_norm_sq_eq_energy u

/-- The actual real Dirichlet pairing is recovered from the completed
Hilbert energy by real polarization, before any completion limit. -/
theorem coreEmbedding_re_inner (u v : actualTensorDomain) :
    (inner ℂ (coreEmbedding u) (coreEmbedding v)).re = shiftedDirichlet u v := by
  have hu := coreEmbedding_re_inner_self u
  have hv := coreEmbedding_re_inner_self v
  have huv := coreEmbedding_re_inner_self (u + v)
  have hsym := inner_re_symm (𝕜 := ℂ) (coreEmbedding u) (coreEmbedding v)
  have he := shiftedEnergy_add u v
  simp only [map_add, inner_add_left, inner_add_right, Complex.add_re] at huv
  linarith only [hu, hv, huv, hsym, he]

theorem shiftedDirichlet_I_right (u v : actualTensorDomain) :
    shiftedDirichlet u (Complex.I • v) =
      -(inner ℂ (u : HyperbolicL2) ((v : HyperbolicL2) + actualTensorLaplacian v)).im := by
  unfold shiftedDirichlet
  simp only [Submodule.coe_smul, map_smul]
  rw [← smul_add, inner_smul_right]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]

/-- Full complex Green identity on the actual core, obtained from true
actual energy and actual operator linearity, with no supplier premise. -/
theorem coreEmbedding_inner_eq_shiftedMaass (u v : actualTensorDomain) :
    inner ℂ (coreEmbedding u) (coreEmbedding v) =
      inner ℂ (u : HyperbolicL2) ((v : HyperbolicL2) + actualTensorLaplacian v) := by
  apply Complex.ext
  · exact coreEmbedding_re_inner u v
  · have hi := coreEmbedding_re_inner u (Complex.I • v)
    rw [map_smul, inner_smul_right, shiftedDirichlet_I_right] at hi
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at hi
    exact neg_inj.mp hi

/-- The same actual graph is symmetric, so the shifted coordinate Maass
operator can equivalently be placed in the first input of the inner product. -/
theorem coreEmbedding_inner_eq_shiftedMaass_left (u v : actualTensorDomain) :
    inner ℂ (coreEmbedding u) (coreEmbedding v) =
      inner ℂ ((u : HyperbolicL2) + actualTensorLaplacian u) (v : HyperbolicL2) := by
  rw [coreEmbedding_inner_eq_shiftedMaass, inner_add_right, inner_add_left]
  congr 1
  exact (ImbalancedChen.Part3.MaassFiniteCoreL2Symmetry20261025a.finiteTensorL2Graph_symmetric
    (actualTensorLaplacian_mem_graph u) (actualTensorLaplacian_mem_graph v)).symm

end

end ImbalancedChen.Part3.ActualCompletedTensorEnergyGreen20261025a
