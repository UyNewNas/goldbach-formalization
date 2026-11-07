import ImbalancedChen.Part3Gamma0CompactSeedQuotientL2Budget
import ImbalancedChen.Part3ActualPoincareMaassLocalFinite
import ImbalancedChen.Part3ActualMobiusMaassEquivariance

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The genuine coordinate upperMaass of the actual finite tensor Poincare sum
equals the actual effective-Gamma0 trace of its genuine Laplacian seed,
pointwise on H. A COMMON compact-hit finite set is constructed for both
the input seed and its C0 compact Laplacian. Thus vanishing outside the
finite sum for the output is proved from its own derived compact support;
no derivative vanishing is inferred from a seed's value at one point.

The actual local finite coordinate derivative theorem and the full C2
Mobius-Laplacian equivariance theorem supply the two independent analytic
steps. No derivative-series exchange, commutation target, or L2 output is
assumed. The existing canonical quotient output L2 is thereby identified
with the genuine geometric Laplacian on the actual reduced carrier.
-/

namespace ImbalancedChen.Part3.ActualTensorPoincareMaassJoin20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane Pointwise BigOperators
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a
open ImbalancedChen.Part3.Gamma0CompactLaplacianSeed20261025a
open ImbalancedChen.Part3.Gamma0CompactSeedQuotientL2Budget20261025a
open ImbalancedChen.Part3.ActualPoincareMaassLocalFinite20261025a
open ImbalancedChen.Part3.ActualMobiusMaassEquivariance20261025a

/-- One actual compact-hit set simultaneously kills BOTH seeds on a whole
neighborhood. The second assertion uses the proved support of Delta f,
not the invalid implication f(w)=0 => Delta f(w)=0. -/
theorem finiteTensor_and_laplacian_common_local_support (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (z : UpperHalfPlane) :
    ∃ U ∈ 𝓝 z, ∃ S : Finset (effectiveGamma0 N),
      ∀ w ∈ U, ∀ q ∉ S,
        finiteCoreFunction s T (effectiveMatrixAction N q w) = 0 ∧
        finiteCoreLaplacian s T (effectiveMatrixAction N q w) = 0 := by
  obtain ⟨U, hUc, hUn⟩ := exists_compact_mem_nhds z
  have hfinite := finite_effective_compact_hits N hUc (finiteCompactTensorSupportK_isCompact s T)
  refine ⟨U, hUn, hfinite.toFinset, ?_⟩
  intro w hw q hq
  have hzero (f : UpperHalfPlane → ℂ)
      (hsupp : Function.support f ⊆ finiteCompactTensorSupportK s T) :
      f (effectiveMatrixAction N q w) = 0 := by
    by_contra hnonzero
    apply hq
    apply hfinite.mem_toFinset.mpr
    exact ⟨effectiveMatrixAction N q w, ⟨w, hw, rfl⟩, hsupp hnonzero⟩
  exact ⟨hzero _ (finiteCoreFunction_support_subset s T),
    hzero _ (finiteCoreLaplacian_support_subset s T)⟩

private theorem chartLift_continuousAt_positive {p : ℝ × ℝ} (hp : 0 < p.2) :
    ContinuousAt chartLift p := by
  apply (UpperHalfPlane.contMDiffAt_ofComplex (n := 2) hp).continuousAt.comp
  have heq : complexOfPair =
      (fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) := by
    funext q
    ext <;> simp [complexOfPair]
  rw [heq]
  fun_prop

/-- The true operator identity, with every local differentiation and
actual Mobius second-jet input supplied by proved source theorems. -/
theorem upperMaass_finiteCompactTensorPoincare_eq_trace (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    upperMaass (finiteCompactTensorPoincare N s T) =
      complexSeedTrace N (finiteCoreLaplacian s T) := by
  funext z
  let p : ℝ × ℝ := Complex.measurableEquivRealProd (z : ℂ)
  have hp : 0 < p.2 := z.im_pos
  have hlift : chartLift p = z := by
    apply UpperHalfPlane.ext
    rw [chartLift_of_positive hp]
    rfl
  obtain ⟨U, hU, S, hS⟩ := finiteTensor_and_laplacian_common_local_support N s T z
  have hpre : ∀ᶠ p' in 𝓝 p, chartLift p' ∈ U :=
    (chartLift_continuousAt_positive hp) (by simpa only [hlift] using hU)
  have hpos : ∀ᶠ p' in 𝓝 p, 0 < p'.2 :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hp
  have heq : extendUpper (finiteCompactTensorPoincare N s T) =ᶠ[𝓝 p]
      (fun p' => ∑ q ∈ S, translatedFiniteTensorChart N q s T p') := by
    filter_upwards [hpre, hpos] with p' hpU hp'
    have hext : extendUpper (finiteCompactTensorPoincare N s T) p' =
        finiteCompactTensorPoincare N s T (chartLift p') := by
      simp only [extendUpper, dif_pos hp', chartLift_of_positive hp']
    rw [hext]
    have hsum : finiteCompactTensorPoincare N s T (chartLift p') =
        ∑ q ∈ S, finiteCoreFunction s T (effectiveMatrixAction N q (chartLift p')) :=
      tsum_eq_sum (fun q hq => (hS (chartLift p') hpU q hq).1)
    rw [hsum]
    apply Finset.sum_congr rfl
    intro q _
    exact (translatedFiniteTensorChart_eq_actual N q s T hp').symm
  change chartMaass (extendUpper (finiteCompactTensorPoincare N s T)) p = _
  calc
    _ = chartMaass (fun p' => ∑ q ∈ S, translatedFiniteTensorChart N q s T p') p :=
      chartMaass_eq_of_eventuallyEq heq
    _ = ∑ q ∈ S, chartMaass (translatedFiniteTensorChart N q s T) p := by
      apply chartMaass_finsetSum S (fun q => translatedFiniteTensorChart N q s T)
      intro q _ p' hp'
      exact (translatedFiniteTensorChart_contDiffAt N q s T hp').contDiffWithinAt
    _ = ∑ q ∈ S, finiteCoreLaplacian s T (effectiveMatrixAction N q z) := by
      apply Finset.sum_congr rfl
      intro q _
      simpa only [hlift] using chartMaass_translatedFiniteTensorChart N q s T p hp
    _ = complexSeedTrace N (finiteCoreLaplacian s T) z :=
      (tsum_eq_sum (fun q hq => (hS z (mem_of_mem_nhds hU) q hq).2)).symm

/-- Genuine geometric Delta of the actual Poincare input is Gamma0
invariant because it is now identified with the actual translated output. -/
theorem upperMaass_Poincare_gamma0_invariant (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor)
    (gamma : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    upperMaass (finiteCompactTensorPoincare N s T) (gamma • z) =
      upperMaass (finiteCompactTensorPoincare N s T) z := by
  rw [upperMaass_finiteCompactTensorPoincare_eq_trace]
  exact compactSeedTrace_gamma0_invariant N (finiteCoreLaplacian s T) gamma z

/-- The previously constructed output quotient L2 function is exactly
the genuine geometric operator on the actual canonical carrier. -/
theorem quotientTensorLaplacianPoincare_projection_eq_upperMaass
    (N : ℕ) [NeZero N] {ι : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (z : reducedCarrier N) :
    quotientTensorLaplacianPoincare N s T (reducedProjection N z) =
      upperMaass (finiteCompactTensorPoincare N s T) z := by
  calc
    _ = complexSeedTrace N (finiteCoreLaplacian s T) z :=
      complexPoincare_projection N (finiteCoreLaplacian s T) z
    _ = _ := (congrFun (upperMaass_finiteCompactTensorPoincare_eq_trace N s T) z).symm

/-- Actual geometric Delta belongs to canonical carrier L2, derived from
the actual quotient output L2 and the proved operator identity. -/
theorem actualUpperMaassPoincare_memLp_carrier (N : ℕ) [NeZero N] {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    MemLp (fun z : reducedCarrier N => upperMaass (finiteCompactTensorPoincare N s T) z)
      2 (reducedCarrierMeasure N) := by
  have h := (quotientTensorLaplacianPoincare_memLp_two N s T).comp_measurePreserving
    (reducedProjection_measurePreserving N)
  apply h.congr
  exact Filter.Eventually.of_forall
    (quotientTensorLaplacianPoincare_projection_eq_upperMaass N s T)

end
end ImbalancedChen.Part3.ActualTensorPoincareMaassJoin20261025a
