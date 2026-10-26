import ImbalancedChen.Part3LocalH1FiniteTensorDensity
import ImbalancedChen.Part3GammaFiniteTensorGraphCore
import ImbalancedChen.Part3UpperRectangleMollifierGeometry

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A compact H1 jet has a sequence of literal ORIGINAL SmoothSeed families
whose actual planar first jets converge in L2. Finite reindexing preserves
EVERY factor support, hence one common compact upper-half-plane container
works for all approximants. No approximation/energy-domain premise occurs.
-/
namespace ImbalancedChen.Part3.LocalH1NormalizedTensorSequence20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open CompactC2ProductMollifier20261026a
open SupportedH1FiniteTensorDensity20261026a
open WeakH1ProductMollifierDerivative20261026a
open ProductKernelL2TranslationAverage20261026a
open Gamma0SmoothCompactTensorCore20261025a MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open LocalH1Tests20261026b UpperRectangleMollifierGeometry20261026b

/-- Original Fin ABI, with original factors copied through the explicit
finite-set equivalence. The support theorem below concerns the factors,
not just a potentially cancelling finite sum. -/
def enumerateTensors {ι : Type} (s : Finset ι) (T : ι → SmoothCompactTensor) :
    Fin (Fintype.card s) → SmoothCompactTensor :=
  fun i => T (((Fintype.equivFin s).symm i) : s).val

theorem enumerateTensors_chart {ι : Type} (s : Finset ι) (T : ι → SmoothCompactTensor) :
    finiteChartFunction Finset.univ (fun i => (enumerateTensors s T i).toCompactTensor) =
      finiteChartFunction s (fun i => (T i).toCompactTensor) := by
  classical
  funext p
  change (∑ i : Fin (Fintype.card s),
    (T (((Fintype.equivFin s).symm i) : s).val).horizontal p.1 *
      (T (((Fintype.equivFin s).symm i) : s).val).vertical p.2) = _
  simpa only [Finset.sum_coe_sort] using
    ((Fintype.equivFin s).symm.sum_comp
      (fun i : s => (T i.val).horizontal p.1 * (T i.val).vertical p.2))

theorem smoothJetClass_congr {F G : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) (heq : F = G) :
    smoothJetClass hF hFc = smoothJetClass hG hGc := by
  subst G
  rfl

structure NormalizedH1TensorSequence (J : CompactH1Jet) (L R a b : ℝ) where
  size : ℕ → ℕ
  tensors : (k : ℕ) → Fin (size k) → SmoothCompactTensor
  compact : ∀ k, HasCompactSupport
    (finiteChartFunction Finset.univ (fun i => (tensors k i).toCompactTensor))
  horizontal_support : ∀ k i, tsupport (tensors k i).horizontal ⊆ Ioo L R
  vertical_support : ∀ k i, tsupport (tensors k i).vertical ⊆ Ioo a b
  jet_tendsto : Tendsto (fun k =>
    smoothJetClass (finiteSmoothChart_contDiff Finset.univ (tensors k)) (compact k))
      atTop (𝓝 (h1JetClass J))

def NormalizedH1TensorSequence.seed {J : CompactH1Jet} {L R a b : ℝ}
    (P : NormalizedH1TensorSequence J L R a b) (k : ℕ) : SmoothSeed := ⟨P.size k,P.tensors k⟩

theorem NormalizedH1TensorSequence.common_support {J : CompactH1Jet} {L R a b : ℝ}
    (P : NormalizedH1TensorSequence J L R a b) (k : ℕ) :
    finiteCompactTensorSupportK Finset.univ (seedTensors (P.seed k)) ⊆ upperRectangle L R a b := by
  intro z hz
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  exact ⟨⟨(P.horizontal_support k i hi.1).1.le,(P.horizontal_support k i hi.1).2.le⟩,
    ⟨(P.vertical_support k i hi.2).1.le,(P.vertical_support k i hi.2).2.le⟩⟩

/-- Explicit normalized sequence from the PROVED support-preserving H1
density theorem. There is no caller sequence, tensor approximation, or
finite-span membership premise. -/
theorem exists_normalizedH1TensorSequence (J : CompactH1Jet)
    (hx : HasCompactSupport J.dx) (hy : HasCompactSupport J.dy)
    (L R a b : ℝ) (ha : 0 < a) (hLR : L < R) (hab : a < b)
    (hs : tsupport J.value ⊆ openRect L R a b) :
    Nonempty (NormalizedH1TensorSequence J L R a b) := by
  classical
  have hdense := compactH1_mem_localFiniteTensorJets_closure J hx hy L R a b ha hLR hab hs
  obtain ⟨v,hv,hlim⟩ := mem_closure_iff_seq_limit.mp hdense
  choose ι s T hc hTs heq using hv
  let U (k : ℕ) := enumerateTensors (s k) (T k)
  have hUeq (k : ℕ) :
      finiteChartFunction Finset.univ (fun i => (U k i).toCompactTensor) =
        finiteChartFunction (s k) (fun i => (T k i).toCompactTensor) :=
    enumerateTensors_chart (s k) (T k)
  have hUc (k : ℕ) : HasCompactSupport
      (finiteChartFunction Finset.univ (fun i => (U k i).toCompactTensor)) := by
    rw [hUeq k]
    exact hc k
  have hjet (k : ℕ) :
      smoothJetClass (finiteSmoothChart_contDiff Finset.univ (U k)) (hUc k) = v k :=
    (smoothJetClass_congr _ _ _ _ (hUeq k)).trans (heq k).symm
  refine ⟨{ size := fun k => Fintype.card (s k),tensors := U,compact := hUc,
    horizontal_support := ?_,vertical_support := ?_,jet_tendsto := ?_ }⟩
  · intro k i
    exact (hTs k (((Fintype.equivFin (s k)).symm i) : s k).val).1
  · intro k i
    exact (hTs k (((Fintype.equivFin (s k)).symm i) : s k).val).2
  · simpa only [hjet] using hlim

end
end ImbalancedChen.Part3.LocalH1NormalizedTensorSequence20261026b
