import ImbalancedChen.Part3CompactCuspParabolicL2
import ImbalancedChen.Part3Gamma0CompactSeedQuotientL2Budget
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Literal two-parabolic-Poincare inner-product unfolding for continuous
compact positive-height radial cusp seeds. A true finite-support reindex
identifies the parabolic trace on H with the effective-group trace of its
compact STRIP INDICATOR. Actual Gamma0 invariance and finite compact
transporter overlap supply the full second trace's global bound.
Therefore the periodic product seed star(F_m)*P_n is strip-L1, without an
integrability supplier. The proved genuine parabolic unfolding then gives
the actual quotient pair integral and its actual L2 inner product.
No spectral expansion or Bessel/geometric evaluation is claimed.
-/

namespace ImbalancedChen.Part3.CompactCuspParabolicPairing20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a
open ImbalancedChen.Part3.CompactCuspParabolicL220261025a
open ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.Gamma0ParabolicEffectiveDecomposition20261025a
open ImbalancedChen.Part3.Gamma0ActualParabolicUnfolding20261025a
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a
open ImbalancedChen.Part3.Gamma0CompactGlobalOverlap20261025a
open ImbalancedChen.Part3.Gamma0CompactSeedSharpL2Budget20261025a
open ImbalancedChen.Part3.Gamma0CompactSeedQuotientL2Budget20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a

/-- The actual H parabolic trace equals its effective compact-indicator
trace everywhere; finite compact overlap licenses the complex reindex. -/
theorem compactCusp_trace_eq_full (N : ℕ) (m : ℤ) (ψ : ℝ → ℂ)
    (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    parabolicTraceComplex N (fourierRadialSeed m ψ) z = complexSeedTrace N (cuspStripSeed m ψ) z := by
  obtain ⟨M, hM, hfinite⟩ := compact_seed_uniform_finite_support N (cuspStripSeed m ψ)
    (cuspSupportK_isCompact ψ hc hpos) (cuspStripSeed_support_subset m ψ)
  obtain ⟨S, _hcard, hzero⟩ := hfinite z
  have hs : Summable (fun e : effectiveGamma0 N => cuspStripSeed m ψ (effectiveMatrixAction N e z)) :=
    summable_of_ne_finset_zero (s := S) hzero
  have hprod := (parabolicEffectiveEquiv N).summable_iff.mpr hs
  have hprod' : Summable (fun p : GammaInfinityCosets N × ℤ =>
      cuspStripSeed m ψ (translate p.2 (parabolicRepresentative N p.1 • z))) := by
    apply hprod.congr
    rintro ⟨q, k⟩
    exact congrArg (cuspStripSeed m ψ) (parabolicPair_action N q k z)
  symm
  change (∑' e : effectiveGamma0 N, cuspStripSeed m ψ (effectiveMatrixAction N e z)) = _
  calc
    _ = ∑' p : GammaInfinityCosets N × ℤ,
        cuspStripSeed m ψ (effectiveMatrixAction N (parabolicEffectiveEquiv N p) z) :=
      ((parabolicEffectiveEquiv N).tsum_eq _).symm
    _ = ∑' p : GammaInfinityCosets N × ℤ,
        cuspStripSeed m ψ (translate p.2 (parabolicRepresentative N p.1 • z)) := by
      apply tsum_congr
      rintro ⟨q, k⟩
      exact congrArg (cuspStripSeed m ψ) (parabolicPair_action N q k z)
    _ = ∑' q : GammaInfinityCosets N, ∑' k : ℤ,
        cuspStripSeed m ψ (translate k (parabolicRepresentative N q • z)) := hprod'.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro q
      exact periodic_strip_indicator_tsum _ (fourierRadialSeed_periodic m ψ) _

/-- Genuine Gamma0 invariance of the actual parabolic trace on H. -/
theorem compactCusp_trace_gamma0_invariant (N : ℕ) (m : ℤ) (ψ : ℝ → ℂ)
    (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ Ioi (0 : ℝ))
    (γ : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    parabolicTraceComplex N (fourierRadialSeed m ψ) (γ • z) =
      parabolicTraceComplex N (fourierRadialSeed m ψ) z := by
  rw [compactCusp_trace_eq_full N m ψ hc hpos, compactCusp_trace_eq_full N m ψ hc hpos]
  exact compactSeedTrace_gamma0_invariant N (cuspStripSeed m ψ) γ z

/-- The global bound comes from the actual compact transporter, not from
an assumed boundedness of an automorphic or periodic function. -/
theorem compactCusp_trace_global_bound (N : ℕ) (m : ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z,
      ‖parabolicTraceComplex N (fourierRadialSeed m ψ) z‖ ≤ C := by
  obtain ⟨B, hB, hb⟩ := cuspStripSeed_bound m ψ hψ hc
  let M := compactOverlapBound N (cuspSupportK ψ)
  refine ⟨(M : ℝ) * B, mul_nonneg (Nat.cast_nonneg _) hB, ?_⟩
  intro z
  rw [compactCusp_trace_eq_full N m ψ hc hpos]
  obtain ⟨S, hcard, hzero, htrace, _hCS⟩ := compactSeed_finite_cauchy N (cuspStripSeed m ψ)
    (cuspSupportK_isCompact ψ hc hpos) (cuspStripSeed_support_subset m ψ) z
  rw [htrace]
  calc
    _ ≤ ∑ q ∈ S, ‖translatedSeed N (cuspStripSeed m ψ) q z‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ S, B := Finset.sum_le_sum (fun q _ => hb _)
    _ = (S.card : ℝ) * B := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ) * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB

/-- One literal periodic cusp seed paired with the FULL second Poincare trace. -/
def cuspPairingSeed (N : ℕ) (m n : ℤ) (ψ φ : ℝ → ℂ) (z : UpperHalfPlane) : ℂ :=
  star (fourierRadialSeed m ψ z) * parabolicTraceComplex N (fourierRadialSeed n φ) z

theorem cuspPairingSeed_measurable (N : ℕ) (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hφ : Continuous φ) : Measurable (cuspPairingSeed N m n ψ φ) :=
  (fourierRadialSeed_measurable m ψ hψ).star.mul
    (parabolicTraceComplex_measurable N _ (fourierRadialSeed_measurable n φ hφ))

theorem cuspPairingSeed_periodic (N : ℕ) (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    ∀ k : ℤ, ∀ z, cuspPairingSeed N m n ψ φ (translate k z) = cuspPairingSeed N m n ψ φ z := by
  intro k z
  have hG := compactCusp_trace_gamma0_invariant N n φ hcφ hposφ (translationGamma N k) z
  rw [translationGamma_smul] at hG
  simp only [cuspPairingSeed, fourierRadialSeed_periodic m ψ k z, hG]

/-- Required strip-L1 is DERIVED from the actual first seed strip-L1 and
proved global compact-overlap bound for the full second trace. -/
theorem cuspPairingSeed_integrableOn_strip (N : ℕ) (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    IntegrableOn (cuspPairingSeed N m n ψ φ) strip := by
  obtain ⟨C, hC, hbound⟩ := compactCusp_trace_global_bound N n φ hφ hcφ hposφ
  have hfirst := fourierRadialSeed_integrableOn_strip m ψ hψ hcψ hposψ
  apply (hfirst.norm.mul_const C).mono'
    (cuspPairingSeed_measurable N m n ψ φ hψ hφ).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  change ‖star (fourierRadialSeed m ψ z) * parabolicTraceComplex N (fourierRadialSeed n φ) z‖ ≤ _
  rw [norm_mul, norm_star]
  exact mul_le_mul_of_nonneg_left (hbound z) (norm_nonneg _)

/-- Actual parabolic trace multiplication: Gamma0 invariance moves the
full second trace out of the ACTUAL left-coset sum. -/
theorem cuspPairingSeed_trace (N : ℕ) (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    parabolicTraceComplex N (cuspPairingSeed N m n ψ φ) z =
      star (parabolicTraceComplex N (fourierRadialSeed m ψ) z) *
        parabolicTraceComplex N (fourierRadialSeed n φ) z := by
  change (∑' q : GammaInfinityCosets N, cuspPairingSeed N m n ψ φ (parabolicRepresentative N q • z)) = _
  calc
    _ = ∑' q : GammaInfinityCosets N,
        star (fourierRadialSeed m ψ (parabolicRepresentative N q • z)) *
          parabolicTraceComplex N (fourierRadialSeed n φ) z := by
      apply tsum_congr
      intro q
      exact congrArg (fun c : ℂ => star (fourierRadialSeed m ψ (parabolicRepresentative N q • z)) * c)
        (compactCusp_trace_gamma0_invariant N n φ hcφ hposφ (parabolicRepresentative N q) z)
    _ = _ := by
      change (∑' q : GammaInfinityCosets N,
        star (fourierRadialSeed m ψ (parabolicRepresentative N q • z)) *
          parabolicTraceComplex N (fourierRadialSeed n φ) z) =
        star (∑' q : GammaInfinityCosets N, fourierRadialSeed m ψ (parabolicRepresentative N q • z)) *
          parabolicTraceComplex N (fourierRadialSeed n φ) z
      rw [tsum_mul_right, ← tsum_star]

/-- The quotient extension of the actual paired seed is the pointwise
product of the two actual parabolic quotient series, including off-section zeros. -/
theorem cuspPairingSeed_quotient (N : ℕ) [NeZero N] (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    parabolicComplexPoincare N (cuspPairingSeed N m n ψ φ) =
      fun u => star (parabolicComplexPoincare N (fourierRadialSeed m ψ) u) *
        parabolicComplexPoincare N (fourierRadialSeed n φ) u := by
  funext u
  by_cases hu : u ∈ range (reducedProjection N)
  · obtain ⟨z, rfl⟩ := hu
    rw [parabolicComplexPoincare_projection, parabolicComplexPoincare_projection,
      parabolicComplexPoincare_projection]
    exact cuspPairingSeed_trace N m n ψ φ hcφ hposφ z
  · have hzero (F : UpperHalfPlane → ℂ) : parabolicComplexPoincare N F u = 0 :=
      Function.extend_apply' _ _ u hu
    simp only [hzero, star_zero, zero_mul]

/-- Integrability of the actual quotient pairing also follows from the
independently proved actual compact-cusp L2 suppliers. -/
theorem compactCusp_quotient_pair_integrable (N : ℕ) [NeZero N] (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Integrable (fun u => star (parabolicComplexPoincare N (fourierRadialSeed m ψ) u) *
      parabolicComplexPoincare N (fourierRadialSeed n φ) u) (carrierPushforward N) :=
  MemLp.integrable_mul (p := 2) (q := 2)
    (compactCuspPoincare_memLp_two N m ψ hψ hcψ hposψ).star
    (compactCuspPoincare_memLp_two N n φ hφ hcφ hposφ)

/-- Literal genuine two-parabolic-Poincare spatial pairing unfolding. -/
theorem compactCusp_quotient_pairing_unfolding (N : ℕ) [NeZero N] (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    (∫ u, star (parabolicComplexPoincare N (fourierRadialSeed m ψ) u) *
      parabolicComplexPoincare N (fourierRadialSeed n φ) u ∂carrierPushforward N) =
      ∫ z in strip, star (fourierRadialSeed m ψ z) * parabolicTraceComplex N (fourierRadialSeed n φ) z := by
  rw [← cuspPairingSeed_quotient N m n ψ φ hcφ hposφ]
  exact complex_parabolic_quotient_unfolding N (cuspPairingSeed N m n ψ φ)
    (cuspPairingSeed_periodic N m n ψ φ hcφ hposφ)
    (cuspPairingSeed_measurable N m n ψ φ hψ hφ)
    (cuspPairingSeed_integrableOn_strip N m n ψ φ hψ hcψ hposψ hφ hcφ hposφ)

/-- The genuine quotient Hilbert inner product has the same literal strip
unfolding, using the actual L2 representative equalities. -/
theorem compactCuspPoincareL2_inner_unfolding (N : ℕ) [NeZero N] (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    inner ℂ (compactCuspPoincareL2 N m ψ hψ hcψ hposψ) (compactCuspPoincareL2 N n φ hφ hcφ hposφ) =
      ∫ z in strip, star (fourierRadialSeed m ψ z) * parabolicTraceComplex N (fourierRadialSeed n φ) z := by
  rw [← compactCusp_quotient_pairing_unfolding N m n ψ φ hψ hcψ hposψ hφ hcφ hposφ, L2.inner_def]
  apply integral_congr_ae
  have hm := (compactCuspPoincare_memLp_two N m ψ hψ hcψ hposψ).coeFn_toLp
  have hn := (compactCuspPoincare_memLp_two N n φ hφ hcφ hposφ).coeFn_toLp
  filter_upwards [hm, hn] with u hum hun
  rw [hum, hun]
  simp only [RCLike.inner_apply', Complex.star_def]

end
end ImbalancedChen.Part3.CompactCuspParabolicPairing20261025a
