import ImbalancedChen.Part3InfinityZeroActualQuotientGeometricAssembly
import ImbalancedChen.Part3ZeroCuspActualSmoothCompactPullback

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO FORMAL CREDIT.

The actual integer Fricke automorphism preserves the FULL actual action
kernel, including the central signs. It therefore induces a constructed
involutive automorphism of the existing effectiveGamma0 index group.
The actual action intertwines with literal zeroSL, proving term-by-term
and full Poincare-sum covariance by this genuine quotient permutation.
Compact support proves absolute convergence everywhere. No effective
Fricke supplier, canonical replacement series or assumed sum identity.
-/

noncomputable section

namespace ImbalancedChen.Part3.ZeroCuspEffectiveFrickePeriodization20261026b

open Set Matrix Matrix.SpecialLinearGroup
open scoped UpperHalfPlane
open ImbalancedChen.Part3.InfinityZeroArithmetic20261025a
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.InfinityZeroActualQuotientGeometricAssembly20261026b
open ImbalancedChen.Part3.ZeroCuspActualSmoothCompactPullback20261026b
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a
open ImbalancedChen.Part3.Gamma0CompactGlobalOverlap20261025a

/-- Actual action covariance, rather than a presumed quotient map,
proves that the genuine scalar action kernel is preserved. -/
theorem fricke_preserves_actionKernel (N : ℕ) (hN : 0 < N)
    (g : CongruenceSubgroup.Gamma0 N) (hg : g ∈ gamma0ActionKernel N) :
    frickeGamma0 N g ∈ gamma0ActionKernel N := by
  have hfix : ∀ z : UpperHalfPlane, g • z = z :=
    (sl2_fixed_all_iff (g : SL(2, ℤ))).mpr ((gamma0_actionKernel_iff N g).mp hg)
  apply (gamma0_actionKernel_iff N (frickeGamma0 N g)).mpr
  apply (sl2_fixed_all_iff (frickeGamma0 N g : SL(2, ℤ))).mp
  intro z
  have hcov := zeroSL_intertwines N hN g (zeroSL N hN • z)
  have hW : zeroSL N hN • (zeroSL N hN • z) = z := zeroSL_action_involutive N hN z
  simpa only [hfix, hW] using hcov.symm

theorem fricke_map_actionKernel (N : ℕ) (hN : 0 < N) :
    (gamma0ActionKernel N).map (frickeGamma0Aut N hN).toMonoidHom = gamma0ActionKernel N := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact fricke_preserves_actionKernel N hN h hh
  · intro hg
    refine ⟨frickeGamma0 N g, fricke_preserves_actionKernel N hN g hg, ?_⟩
    exact frickeGamma0_involutive N hN g

/-- The real Poincare index quotient counts +I and -I only once. The
Fricke permutation is constructed on this exact existing quotient. -/
def effectiveFrickeEquiv (N : ℕ) (hN : 0 < N) : effectiveGamma0 N ≃* effectiveGamma0 N :=
  QuotientGroup.congr (gamma0ActionKernel N) (gamma0ActionKernel N)
    (frickeGamma0Aut N hN) (fricke_map_actionKernel N hN)

theorem effectiveFrickeEquiv_mk (N : ℕ) (hN : 0 < N)
    (g : CongruenceSubgroup.Gamma0 N) :
    effectiveFrickeEquiv N hN (QuotientGroup.mk g) = QuotientGroup.mk (frickeGamma0 N g) := rfl

theorem effectiveFrickeEquiv_involutive (N : ℕ) (hN : 0 < N) :
    Function.Involutive (effectiveFrickeEquiv N hN) := by
  intro q
  refine Quotient.inductionOn' q ?_
  intro g
  rw [effectiveFrickeEquiv_mk, effectiveFrickeEquiv_mk, frickeGamma0_involutive N hN g]

/-- The chosen actual representative actions intertwine, regardless of
the arbitrary choices of effectiveRepresentative on the two sides. -/
theorem effectiveFricke_action (N : ℕ) (hN : 0 < N)
    (q : effectiveGamma0 N) (z : UpperHalfPlane) :
    zeroSL N hN • effectiveMatrixAction N q z =
      effectiveMatrixAction N (effectiveFrickeEquiv N hN q) (zeroSL N hN • z) := by
  refine Quotient.inductionOn' q ?_
  intro g
  rw [effectiveFrickeEquiv_mk, effectiveMatrixAction_mk_gamma, effectiveMatrixAction_mk_gamma]
  exact zeroSL_intertwines N hN g z

theorem translatedSeed_zeroPullback (N : ℕ) (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (q : effectiveGamma0 N) (z : UpperHalfPlane) :
    translatedSeed N (zeroSeedPullback N hN f) q z =
      translatedSeed N f (effectiveFrickeEquiv N hN q) (zeroSL N hN • z) := by
  unfold translatedSeed zeroSeedPullback
  rw [effectiveFricke_action]

/-- This is a true permutation of the ORIGINAL effective group sum;
it involves no Fubini, grouping, or changed series definition. -/
theorem complexSeedTrace_zeroPullback (N : ℕ) (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    complexSeedTrace N (zeroSeedPullback N hN f) z =
      complexSeedTrace N f (zeroSL N hN • z) := by
  unfold complexSeedTrace
  simp_rw [translatedSeed_zeroPullback]
  exact (effectiveFrickeEquiv N hN).toEquiv.tsum_eq
    (fun q => translatedSeed N f q (zeroSL N hN • z))

/-- Actual compact-transporter geometry supplies absolute convergence at
EVERY H point; convergence is not an assumption of compact covariance. -/
theorem compactSeed_actual_norm_summable (N : ℕ) (f : UpperHalfPlane → ℂ)
    (hfc : HasCompactSupport f) (z : UpperHalfPlane) :
    Summable (fun q : effectiveGamma0 N => ‖translatedSeed N f q z‖) := by
  obtain ⟨_M, _hM, hfinite⟩ := compact_seed_uniform_finite_support N f hfc (subset_tsupport f)
  obtain ⟨S, _hcard, hz⟩ := hfinite z
  apply summable_of_ne_finset_zero (s := S)
  intro q hq
  simp only [translatedSeed, hz q hq, norm_zero]

/-- Both actual compact series in the zero-chart identity are absolute,
including the full scalar-kernel quotient exactly once. -/
theorem compactSeed_zeroPullback_absolute_covariance (N : ℕ) (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f) (z : UpperHalfPlane) :
    Summable (fun q : effectiveGamma0 N => ‖translatedSeed N (zeroSeedPullback N hN f) q z‖) ∧
    Summable (fun q : effectiveGamma0 N => ‖translatedSeed N f q (zeroSL N hN • z)‖) ∧
    complexSeedTrace N (zeroSeedPullback N hN f) z =
      complexSeedTrace N f (zeroSL N hN • z) :=
  ⟨compactSeed_actual_norm_summable N _ (zeroSeedPullback_hasCompactSupport N hN f hfc) z,
    compactSeed_actual_norm_summable N f hfc _, complexSeedTrace_zeroPullback N hN f z⟩

end ImbalancedChen.Part3.ZeroCuspEffectiveFrickePeriodization20261026b
