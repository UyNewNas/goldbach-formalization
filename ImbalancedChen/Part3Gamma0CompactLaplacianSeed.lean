import ImbalancedChen.Part3Gamma0CompactTensorPoincareC2Core

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual compact C2 tensor seed has a C0 compactly supported Laplacian.
Its second derivatives are only asserted continuous; this seed is NOT
relabeled as a CompactTensor with nonexistent fourth derivatives. The
support lies in the SAME explicit finite compact support container as the
original seed. Canonical hyperbolic L1 integrability is then proved, and
the existing genuine whole-plane seed L2 theorem remains available.

This is seed analysis for an actual effective-Gamma0 periodization. It does
not turn the whole-plane tensor operator into a quotient operator, nor
assert Delta commutation, spectral decomposition or an assumed L2 supplier.
-/

namespace ImbalancedChen.Part3.Gamma0CompactLaplacianSeed20261025a

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a

theorem compactTensor_second_derivative_continuous (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) :
    Continuous (deriv (deriv f)) := by
  have hs : ContDiff ℝ ((1 : ℕ∞ω) + 1) f := by simpa using hf
  exact (contDiff_succ_iff_deriv.mp hs).2.2.continuous_deriv_one

/-- Only C0 regularity of the actual second-order image is needed here. -/
theorem tensorLaplacian_continuous (T : CompactTensor) :
    Continuous (tensorHyperbolicLaplacianH T.horizontal T.vertical) := by
  have hh := compactTensor_second_derivative_continuous T.horizontal T.horizontal_smooth
  have hv := compactTensor_second_derivative_continuous T.vertical T.vertical_smooth
  change Continuous (fun z : UpperHalfPlane => -((z.im : ℂ) ^ 2 *
    (deriv (deriv T.horizontal) z.re * T.vertical z.im +
      T.horizontal z.re * deriv (deriv T.vertical) z.im)))
  exact (((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).pow 2).mul
    (((hh.comp UpperHalfPlane.continuous_re).mul
      (T.vertical_smooth.continuous.comp UpperHalfPlane.continuous_im)).add
      ((T.horizontal_smooth.continuous.comp UpperHalfPlane.continuous_re).mul
        (hv.comp UpperHalfPlane.continuous_im)))).neg

theorem finiteCoreLaplacian_continuous {ι : Type*} (s : Finset ι) (T : ι → CompactTensor) :
    Continuous (finiteCoreLaplacian s T) :=
  continuous_finsetSum s (fun i _ => tensorLaplacian_continuous (T i))

/-- Derivation cannot enlarge either original closed support. Hence the
actual Laplacian uses the original compact rectangle, not a new C2 seed. -/
theorem tensorLaplacian_support_subset (T : CompactTensor) :
    Function.support (tensorHyperbolicLaplacianH T.horizontal T.vertical) ⊆
      compactTensorSupportK T := by
  intro z hz
  by_contra hnot
  apply hz
  change -((z.im : ℂ) ^ 2 *
    (deriv (deriv T.horizontal) z.re * T.vertical z.im +
      T.horizontal z.re * deriv (deriv T.vertical) z.im)) = 0
  by_cases hh : z.re ∈ tsupport T.horizontal
  · have hv : z.im ∉ tsupport T.vertical := fun h => hnot ⟨hh, h⟩
    have hddv : z.im ∉ tsupport (deriv (deriv T.vertical)) :=
      fun h => hv (tsupport_deriv_subset (tsupport_deriv_subset h))
    rw [image_eq_zero_of_notMem_tsupport hv, image_eq_zero_of_notMem_tsupport hddv]
    simp
  · have hddh : z.re ∉ tsupport (deriv (deriv T.horizontal)) :=
      fun h => hh (tsupport_deriv_subset (tsupport_deriv_subset h))
    rw [image_eq_zero_of_notMem_tsupport hh, image_eq_zero_of_notMem_tsupport hddh]
    simp

theorem finiteCoreLaplacian_support_subset {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    Function.support (finiteCoreLaplacian s T) ⊆ finiteCompactTensorSupportK s T := by
  intro z hz
  by_contra hnot
  apply hz
  apply Finset.sum_eq_zero
  intro i hi
  by_contra hnonzero
  exact hnot (mem_iUnion.mpr ⟨⟨i, hi⟩, tensorLaplacian_support_subset (T i) hnonzero⟩)

theorem finiteCoreLaplacian_hasCompactSupport {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    HasCompactSupport (finiteCoreLaplacian s T) := by
  apply (finiteCompactTensorSupportK_isCompact s T).of_isClosed_subset isClosed_closure
  exact closure_minimal (finiteCoreLaplacian_support_subset s T)
    (finiteCompactTensorSupportK_isCompact s T).isClosed

/-- Genuine seed L1, obtained from continuity and the derived compact
support for canonical hyperbolic volume, not a tsum-integral assumption. -/
theorem finiteCoreLaplacian_integrable {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    Integrable (finiteCoreLaplacian s T) (volume : Measure UpperHalfPlane) :=
  (finiteCoreLaplacian_continuous s T).integrable_of_hasCompactSupport
    (finiteCoreLaplacian_hasCompactSupport s T)

end
end ImbalancedChen.Part3.Gamma0CompactLaplacianSeed20261025a
