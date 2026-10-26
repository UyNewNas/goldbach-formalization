import ImbalancedChen.Part3LocalH1NormalizedTensorSequence
import ImbalancedChen.Part3Gamma0ActualEnergyCompletion
import ImbalancedChen.Part3Gamma0SmoothCoreFinitePoincareRepresentation

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact subtraction in the original finite smooth tensor ABI, simultaneously
on the planar seed, its native L2 first jet, and the ACTUAL quotient energy
core. Negative coefficients are absorbed into actual horizontal factors,
so every difference retains the same factor supports and compact container.
-/
namespace ImbalancedChen.Part3.LocalH1TensorDifferenceABI20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open CompactC2ProductMollifier20261026a CompactC2JetCutoffEstimate20261026a
open SupportedH1FiniteTensorDensity20261026a ProductKernelL2TranslationAverage20261026a
open Gamma0SmoothCompactTensorCore20261025a MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0SmoothTensorSpanRendering20261025a
open Gamma0SmoothCoreFinitePoincareRepresentation20261025a
open Gamma0ActualEnergyCompletion20261025a
open LocalH1Tests20261026b LocalH1NormalizedTensorSequence20261026b
open UpperRectangleMollifierGeometry20261026b

def differenceTensors {n m : ℕ} (T : Fin n → SmoothCompactTensor)
    (U : Fin m → SmoothCompactTensor) : Fin (n+m) → SmoothCompactTensor :=
  appendSmoothTensors T (fun i => scaleSmoothTensor (-1) (U i))

theorem differenceTensors_chart {n m : ℕ} (T : Fin n → SmoothCompactTensor)
    (U : Fin m → SmoothCompactTensor) :
    finiteChartFunction Finset.univ (fun i => (differenceTensors T U i).toCompactTensor) =
      finiteChartFunction Finset.univ (fun i => (T i).toCompactTensor) -
        finiteChartFunction Finset.univ (fun i => (U i).toCompactTensor) := by
  change smoothChartFinite (appendSmoothTensors T (fun i => scaleSmoothTensor (-1) (U i))) =
    smoothChartFinite T - smoothChartFinite U
  rw [smoothChartFinite_append,smoothChartFinite_scale]
  simp only [neg_one_smul,sub_eq_add_neg]

theorem differenceTensors_factor_supports {n m : ℕ} (T : Fin n → SmoothCompactTensor)
    (U : Fin m → SmoothCompactTensor) (L R a b : ℝ)
    (hT : ∀ i, tsupport (T i).horizontal ⊆ Ioo L R ∧ tsupport (T i).vertical ⊆ Ioo a b)
    (hU : ∀ i, tsupport (U i).horizontal ⊆ Ioo L R ∧ tsupport (U i).vertical ⊆ Ioo a b) :
    ∀ i, tsupport (differenceTensors T U i).horizontal ⊆ Ioo L R ∧
      tsupport (differenceTensors T U i).vertical ⊆ Ioo a b := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [differenceTensors,appendSmoothTensors,Fin.addCases_left] using hT j
  · intro j
    change tsupport (fun x => (-1 : ℂ) * (U j).horizontal x) ⊆ Ioo L R ∧
      tsupport (U j).vertical ⊆ Ioo a b
    exact ⟨tsupport_mul_subset_right.trans (hU j).1,(hU j).2⟩

theorem differenceTensors_compact {n m : ℕ} (T : Fin n → SmoothCompactTensor)
    (U : Fin m → SmoothCompactTensor)
    (hT : HasCompactSupport (finiteChartFunction Finset.univ (fun i => (T i).toCompactTensor)))
    (hU : HasCompactSupport (finiteChartFunction Finset.univ (fun i => (U i).toCompactTensor))) :
    HasCompactSupport (finiteChartFunction Finset.univ (fun i => (differenceTensors T U i).toCompactTensor)) := by
  rw [differenceTensors_chart]
  exact hT.sub hU

theorem smoothJetClass_sub {F G : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hG : ContDiff ℝ ∞ G) (hcG : HasCompactSupport G) :
    smoothJetClass (hF.sub hG) (hcF.sub hcG) = smoothJetClass hF hcF - smoothJetClass hG hcG := by
  funext i
  apply Lp.ext
  filter_upwards [(partial_memLp (hF.sub hG) (hcF.sub hcG) (firstIndex i)).coeFn_toLp,
    Lp.coeFn_sub (smoothJetClass hF hcF i) (smoothJetClass hG hcG i),
    (partial_memLp hF hcF (firstIndex i)).coeFn_toLp,
    (partial_memLp hG hcG (firstIndex i)).coeFn_toLp] with p hp hsub hf hg
  rw [hp,hsub,hf,hg]
  rw [partialJet_eq_mixedJet (hF.sub hG),partialJet_eq_mixedJet hF,partialJet_eq_mixedJet hG]
  simpa only [Pi.sub_apply] using congrFun (mixedJet_sub hF hG (firstIndex i)) p

theorem differenceTensors_jet {n m : ℕ} (T : Fin n → SmoothCompactTensor)
    (U : Fin m → SmoothCompactTensor)
    (hT : HasCompactSupport (finiteChartFunction Finset.univ (fun i => (T i).toCompactTensor)))
    (hU : HasCompactSupport (finiteChartFunction Finset.univ (fun i => (U i).toCompactTensor))) :
    smoothJetClass (finiteSmoothChart_contDiff Finset.univ (differenceTensors T U))
      (differenceTensors_compact T U hT hU) =
    smoothJetClass (finiteSmoothChart_contDiff Finset.univ T) hT -
      smoothJetClass (finiteSmoothChart_contDiff Finset.univ U) hU :=
  (smoothJetClass_congr _ _ _ _ (differenceTensors_chart T U)).trans
    (smoothJetClass_sub _ _ _ _)

def familyEnergyCore (N : ℕ) [NeZero N] {n : ℕ} (T : Fin n → SmoothCompactTensor) : EnergyCore N :=
  seedCoreElement N ⟨n,T⟩

/-- Actual quotient subtraction, not an abstract core-vector or graph
compatibility premise. The existing finite periodization sum laws pay the
summability needed for this identity. -/
theorem differenceTensors_energyCore (N : ℕ) [NeZero N] {n m : ℕ}
    (T : Fin n → SmoothCompactTensor) (U : Fin m → SmoothCompactTensor) :
    familyEnergyCore N (differenceTensors T U) = familyEnergyCore N T - familyEnergyCore N U := by
  apply Subtype.ext
  change smoothQuotientPoincareL2 N Finset.univ (differenceTensors T U) =
    smoothQuotientPoincareL2 N Finset.univ T - smoothQuotientPoincareL2 N Finset.univ U
  simp only [differenceTensors,smoothQuotientL2_append,smoothQuotientL2_scale,
    neg_one_smul,sub_eq_add_neg]

/-- The same compact upper-half-plane support container is preserved
for every pairwise difference of a normalized H1 approximation sequence. -/
theorem NormalizedH1TensorSequence.difference_common_support
    {J : WeakH1ProductMollifierDerivative20261026a.CompactH1Jet} {L R a b : ℝ}
    (P : NormalizedH1TensorSequence J L R a b) (j k : ℕ) :
    finiteCompactTensorSupportK Finset.univ
      (fun i => (differenceTensors (P.tensors j) (P.tensors k) i).toCompactTensor) ⊆
        upperRectangle L R a b := by
  have hs := differenceTensors_factor_supports (P.tensors j) (P.tensors k) L R a b
    (fun i => ⟨P.horizontal_support j i,P.vertical_support j i⟩)
    (fun i => ⟨P.horizontal_support k i,P.vertical_support k i⟩)
  intro z hz
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  exact ⟨⟨((hs i).1 hi.1).1.le,((hs i).1 hi.1).2.le⟩,
    ⟨((hs i).2 hi.2).1.le,((hs i).2 hi.2).2.le⟩⟩

end
end ImbalancedChen.Part3.LocalH1TensorDifferenceABI20261026b

