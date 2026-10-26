import ImbalancedChen.Part3InfinityZeroActualQuotientGeometricAssembly

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO FORMAL CREDIT.

The genuine zero-cusp orbit-quotient function, whose value is the literal
sigma0 pullback of the original actual Poincare sum, is measurable and
globally bounded by the actual compact-transporter theorem. Finiteness
of the canonical spatial quotient measure then proves MemLp2, rather
than taking it or a prescribed mixed pairing as a premise. Its actual
L2 representative has the previously proved spatial and finite all-d
mixed geometric pairing. No special-function normalization is involved.
-/

noncomputable section

namespace ImbalancedChen.Part3.InfinityZeroActualQuotientL220261026b

open Set MeasureTheory Filter
open scoped UpperHalfPlane BigOperators
open ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a
open ImbalancedChen.Part3.InfinityZeroArithmetic20261025a
open ImbalancedChen.Part3.InfinityZeroActualFiberGeometricPair20261026a
open ImbalancedChen.Part3.InfinityZeroActualQuotientGeometricAssembly20261026b
open ImbalancedChen.Part3.CompactCuspParabolicL220261025a
open ImbalancedChen.Part3.CompactCuspParabolicPairing20261025a
open ImbalancedChen.Part3.CompactCuspQuotientGeometricPairing20261025a
open ImbalancedChen.Part3.CompactCuspGeometricFubini20261025a
open ImbalancedChen.Part3.Gamma0ActualParabolicUnfolding20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.OriginalSmoothPoissonTail

/-- The constructed orbit-quotient function has the original scaled sum
as its value at every original H point, not merely almost everywhere. -/
theorem zeroCuspPoincare_orbitProjection (N : ℕ) (hN : 0 < N) (n : ℤ)
    (φ : ℝ → ℂ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ))
    (z : UpperHalfPlane) :
    zeroCuspPoincare N hN n φ hcφ hposφ (orbitProjection N z) =
      zeroChartTrace N hN n φ z := rfl

theorem zeroCuspPoincare_measurable (N : ℕ) (hN : 0 < N) (n : ℤ)
    (φ : ℝ → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Measurable (zeroCuspPoincare N hN n φ hcφ hposφ) := by
  apply measurable_from_quotient.mpr
  change Measurable (zeroChartTrace N hN n φ)
  exact zeroChartTrace_measurable N hN n φ hφ

/-- The actual global compact-transporter estimate survives both the
literal zero chart and the actual orbit quotient, with no L2 assumption. -/
theorem zeroCuspPoincare_global_bound (N : ℕ) (hN : 0 < N) (n : ℤ)
    (φ : ℝ → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖zeroCuspPoincare N hN n φ hcφ hposφ u‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compactCusp_trace_global_bound N n φ hφ hcφ hposφ
  refine ⟨C, hC, ?_⟩
  intro u
  refine Quotient.inductionOn u ?_
  intro z
  change ‖zeroChartTrace N hN n φ z‖ ≤ C
  simpa only [zeroChartTrace, actualCompactPoincare_eq_parabolicTrace] using hb (zeroSL N hN • z)

/-- Actual zero-cusp MemLp2 follows from geometry and the finite canonical
quotient measure. No supplied pairing or spectral norm is used. -/
theorem zeroCuspPoincare_memLp_two (N : ℕ) [NeZero N] (hN : 0 < N) (n : ℤ)
    (φ : ℝ → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    MemLp (zeroCuspPoincare N hN n φ hcφ hposφ) 2 (carrierPushforward N) := by
  letI : IsFiniteMeasure (carrierPushforward N) := ⟨carrierPushforward_finite N⟩
  obtain ⟨C, _hC, hb⟩ := zeroCuspPoincare_global_bound N hN n φ hφ hcφ hposφ
  exact MemLp.of_bound
    (zeroCuspPoincare_measurable N hN n φ hφ hcφ hposφ).aestronglyMeasurable C
    (Filter.Eventually.of_forall hb)

def zeroCuspPoincareL2 (N : ℕ) [NeZero N] (hN : 0 < N) (n : ℤ)
    (φ : ℝ → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Lp ℂ 2 (carrierPushforward N) :=
  (zeroCuspPoincare_memLp_two N hN n φ hφ hcφ hposφ).toLp
    (zeroCuspPoincare N hN n φ hcφ hposφ)

theorem zeroCuspPoincareL2_coeFn (N : ℕ) [NeZero N] (hN : 0 < N) (n : ℤ)
    (φ : ℝ → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    (zeroCuspPoincareL2 N hN n φ hφ hcφ hposφ : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      zeroCuspPoincare N hN n φ hcφ hposφ :=
  (zeroCuspPoincare_memLp_two N hN n φ hφ hcφ hposφ).coeFn_toLp

/-- The genuine Hilbert inner product equals the actual spatial quotient
pairing by the two proved representative identities. -/
theorem mixed_L2_inner_eq_spatial (N : ℕ) [NeZero N] (hN : 0 < N)
    (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    inner ℂ (compactCuspPoincareL2 N m ψ hψ hcψ hposψ)
      (zeroCuspPoincareL2 N hN n φ hφ hcφ hposφ) =
      ∫ u, star (parabolicComplexPoincare N (fourierRadialSeed m ψ) u) *
        zeroCuspPoincare N hN n φ hcφ hposφ u ∂carrierPushforward N := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have hm := (compactCuspPoincare_memLp_two N m ψ hψ hcψ hposψ).coeFn_toLp
  have hn := zeroCuspPoincareL2_coeFn N hN n φ hφ hcφ hposφ
  filter_upwards [hm, hn] with u hum hun
  rw [hum, hun]
  simp only [RCLike.inner_apply', Complex.star_def]

/-- The actual mixed quotient L2 pairing has the finite physical all-d
formula, including the sole exceptional level-one diagonal. -/
theorem mixed_L2_inner_eq_finite_geometric (N : ℕ) [NeZero N] (hN : 0 < N)
    (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℕ+,
      inner ℂ (compactCuspPoincareL2 N m ψ hψ hcψ hposψ)
        (zeroCuspPoincareL2 N hN n φ hφ hcφ hposφ) =
        (if N = 1 ∧ m = n then ∫ y : ℝ, radialWeight ψ y * φ y else 0) +
        ∑ d ∈ Finset.Icc (1 : ℕ+) C,
          (if N.Coprime (d : ℕ) then
            kloosterman (d : ℕ) (-m * inverseResidue (d : ℕ) (N : ℤ)) (-n) else 0) *
              ∫ x : ℝ, ∫ y : ℝ, mixedOrbitKernel N (d : ℕ) m n ψ φ (x, y) := by
  rw [mixed_L2_inner_eq_spatial N hN m n ψ φ hψ hcψ hposψ hφ hcφ hposφ]
  exact mixed_quotient_pairing_eq_finite_geometric N hN m n ψ φ hψ hcψ hposψ hφ hcφ hposφ

end ImbalancedChen.Part3.InfinityZeroActualQuotientL220261026b
