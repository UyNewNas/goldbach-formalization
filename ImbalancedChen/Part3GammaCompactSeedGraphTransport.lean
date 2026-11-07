import ImbalancedChen.Part3GammaCompactSeedL2Transport
import ImbalancedChen.Part3ActualCompactSeedMaassJoin
import ImbalancedChen.Part3Gamma0ActualMaassClosedOperator
import ImbalancedChen.Part3Gamma0SmoothCoreFinitePoincareRepresentation

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual compact C2 seed has a genuine quotient input/output L2 pair.
Common-compact sup errors of the seed and its literal upperMaass give a
quantitative graph-norm bound. Every finite smooth tensor approximant
lands in the ACTUAL Gamma0 core graph by identifying both existing L2
coordinates with the original seedPair generator. No arbitrary compact
smooth function is declared to belong to the finite tensor span.
-/

namespace ImbalancedChen.Part3.GammaCompactSeedGraphTransport20261026a

noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane ENNReal
open MaassWeakOperatorCore20261024zz MaassFiniteCoreL2Graph20261025a
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a Gamma0CompactSeedQuotientL2Budget20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open Gamma0QuotientConullTransport20261025a Gamma0CarrierMeasurableInverse20261025a
open Gamma0CompactTensorQuotientL2Core20261025a Gamma0SmoothCompactTensorCore20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0ActualMaassClosedOperator20261025a
open GammaCompactSeedL2Transport20261026a ActualCompactSeedMaassJoin20261025a

abbrev nativeC2 (f : UpperHalfPlane → ℂ) : Prop :=
  ContDiffOn ℝ 2 (extendUpper f) positiveChart

def compactInput (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ) (hf : nativeC2 f)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hs : Function.support f ⊆ K) :
    Lp ℂ 2 (carrierPushforward N) :=
  seedL2 N f (native_C2_continuous f hf) K hK hs

def compactOutput (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ) (hf : nativeC2 f)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hs : Function.support f ⊆ K) :
    Lp ℂ 2 (carrierPushforward N) :=
  seedL2 N (upperMaass f) (native_C2_upperMaass_continuous f hf) K hK
    (upperMaass_support_subset_closed f hK.isClosed hs)

def compactGraphPair (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ) (hf : nativeC2 f)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hs : Function.support f ⊆ K) :
    Lp ℂ 2 (carrierPushforward N) × Lp ℂ 2 (carrierPushforward N) :=
  (compactInput N f hf K hK hs, compactOutput N f hf K hK hs)

theorem compactInput_ae (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ)
    (hf : nativeC2 f) (K : Set UpperHalfPlane) (hK : IsCompact K)
    (hs : Function.support f ⊆ K) :
    (compactInput N f hf K hK hs : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N f := seedL2_ae N f _ K hK hs

theorem compactOutput_ae (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ)
    (hf : nativeC2 f) (K : Set UpperHalfPlane) (hK : IsCompact K)
    (hs : Function.support f ⊆ K) :
    (compactOutput N f hf K hK hs : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (upperMaass f) := seedL2_ae N (upperMaass f) _ K hK _

/-- Exact graph-norm transport on the original quotient. Neither constant
nor support container depends on the approximation accuracy. -/
theorem compactGraphPair_distance_bound (N : ℕ) [NeZero N]
    (f g : UpperHalfPlane → ℂ) (hf : nativeC2 f) (hg : nativeC2 g)
    (K : Set UpperHalfPlane) (hK : IsCompact K)
    (hfs : Function.support f ⊆ K) (hgs : Function.support g ⊆ K)
    {epsilon : ℝ} (he : 0 ≤ epsilon)
    (hvalue : ∀ z ∈ K, ‖f z - g z‖ ≤ epsilon)
    (hlap : ∀ z ∈ K, ‖upperMaass f z - upperMaass g z‖ ≤ epsilon) :
    dist (compactGraphPair N f hf K hK hfs) (compactGraphPair N g hg K hK hgs) ≤
      transportConstant N K * epsilon := by
  have hinput := seedL2_difference_bound N f g (native_C2_continuous f hf)
    (native_C2_continuous g hg) K hK hfs hgs he hvalue
  have houtput := seedL2_difference_bound N (upperMaass f) (upperMaass g)
    (native_C2_upperMaass_continuous f hf) (native_C2_upperMaass_continuous g hg)
    K hK (upperMaass_support_subset_closed f hK.isClosed hfs)
    (upperMaass_support_subset_closed g hK.isClosed hgs) he hlap
  rw [dist_eq_norm]
  change max ‖compactInput N f hf K hK hfs - compactInput N g hg K hK hgs‖
    ‖compactOutput N f hf K hK hfs - compactOutput N g hg K hK hgs‖ ≤ _
  exact max_le hinput houtput

/-- Native C2 regularity of a genuine finite smooth tensor seed. -/
theorem finiteTensor_nativeC2 {n : ℕ} (T : Fin n → SmoothCompactTensor) :
    nativeC2 (finiteCoreFunction Finset.univ (fun i => (T i).toCompactTensor)) := by
  unfold nativeC2
  rw [extendUpper_finiteCoreFunction]
  exact ((finiteSmoothChart_contDiff Finset.univ T).of_le (by simp)).contDiffOn

/-- Both constructions use the SAME true quotient vector, even though the
generic compact-seed representative is extended from a conull section. -/
theorem compactInput_finiteTensor_eq (N : ℕ) [NeZero N] {n : ℕ}
    (T : Fin n → SmoothCompactTensor) (K : Set UpperHalfPlane) (hK : IsCompact K)
    (hs : Function.support (finiteCoreFunction Finset.univ
      (fun i => (T i).toCompactTensor)) ⊆ K) :
    compactInput N _ (finiteTensor_nativeC2 T) K hK hs = seedVector N ⟨n, T⟩ := by
  apply Lp.ext
  filter_upwards [compactInput_ae N _ (finiteTensor_nativeC2 T) K hK hs,
    (quotientTensorPoincare_memLp_two N Finset.univ
      (fun i => (T i).toCompactTensor)).coeFn_toLp,
    reducedProjection_range_ae N] with q hleft hright hsection
  obtain ⟨z, rfl⟩ := hsection
  change compactInput N _ (finiteTensor_nativeC2 T) K hK hs (reducedProjection N z) =
    smoothQuotientPoincareL2 N Finset.univ T (reducedProjection N z)
  rw [hleft, hright, complexPoincare_projection]
  rfl

theorem compactOutput_finiteTensor_eq (N : ℕ) [NeZero N] {n : ℕ}
    (T : Fin n → SmoothCompactTensor) (K : Set UpperHalfPlane) (hK : IsCompact K)
    (hs : Function.support (finiteCoreFunction Finset.univ
      (fun i => (T i).toCompactTensor)) ⊆ K) :
    compactOutput N _ (finiteTensor_nativeC2 T) K hK hs = seedOutput N ⟨n, T⟩ := by
  apply Lp.ext
  filter_upwards [compactOutput_ae N _ (finiteTensor_nativeC2 T) K hK hs,
    (quotientTensorLaplacianPoincare_memLp_two N Finset.univ
      (fun i => (T i).toCompactTensor)).coeFn_toLp] with q hleft hright
  rw [hleft, hright]
  change complexPoincare N (upperMaass (finiteCoreFunction Finset.univ
      (fun i => (T i).toCompactTensor))) q = _
  rw [upperMaass_finiteCoreFunction]
  rfl

/-- The approximants belong to the existing finite-generator graph by
construction, not by calling arbitrary smooth compact functions core tests. -/
theorem compactGraphPair_finiteTensor_mem_coreGraph (N : ℕ) [NeZero N] {n : ℕ}
    (T : Fin n → SmoothCompactTensor) (K : Set UpperHalfPlane) (hK : IsCompact K)
    (hs : Function.support (finiteCoreFunction Finset.univ
      (fun i => (T i).toCompactTensor)) ⊆ K) :
    compactGraphPair N _ (finiteTensor_nativeC2 T) K hK hs ∈ coreGraph N := by
  change (compactInput N _ (finiteTensor_nativeC2 T) K hK hs,
    compactOutput N _ (finiteTensor_nativeC2 T) K hK hs) ∈ coreGraph N
  rw [compactInput_finiteTensor_eq N T K hK hs, compactOutput_finiteTensor_eq N T K hK hs]
  exact Submodule.subset_span ⟨⟨n, T⟩, rfl⟩

end
end ImbalancedChen.Part3.GammaCompactSeedGraphTransport20261026a
