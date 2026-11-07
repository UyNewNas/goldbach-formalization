import ImbalancedChen.Part3CompactH1PoincareFormDomain
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A genuine CLOSED LINEAR subspace of three ordinary planar L2 components:
the value and both literal weak first derivatives have common rectangle
support a.e. Weak identities are native L2 pairings against EVERY compact
smooth scalar test. Both support closure and weak-identity closure are
proved, with no caller regularity, density, or limit premise.
-/
namespace ImbalancedChen.Part3.FixedRectangleH1JetSpace20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open CompactC2ProductMollifier20261026a ProductKernelL2TranslationAverage20261026a
open LocalH1Tests20261026b

abbrev JetSpace := Fin 3 → ProductKernelL2TranslationAverage20261026a.PlaneL2

def supportedJets (K : Set Plane) : Submodule ℂ JetSpace where
  carrier := {v | ∀ i, ∀ᵐ p ∂(volume : Measure Plane), p ∉ K → v i p = 0}
  zero_mem' := by
    intro i
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure Plane)] with p hp
    intro _
    exact hp
  add_mem' := by
    intro v w hv hw i
    filter_upwards [hv i,hw i,Lp.coeFn_add (v i) (w i)] with p hvp hwp hsum
    intro hp
    change (v i + w i) p = 0
    simp only [hsum,Pi.add_apply,hvp hp,hwp hp,add_zero]
  smul_mem' := by
    intro c v hv i
    filter_upwards [hv i,Lp.coeFn_smul c (v i)] with p hvp hsmul
    intro hp
    change (c • v i) p = 0
    simp only [hsmul,Pi.smul_apply,hvp hp,smul_zero]

theorem supportedJets_isClosed (K : Set Plane) : IsClosed (supportedJets K : Set JetSpace) := by
  apply IsSeqClosed.isClosed
  intro v z hv hlim i
  have hi : Tendsto (fun n => v n i) atTop (𝓝 (z i)) :=
    ((continuous_apply i).tendsto z).comp hlim
  have hmem : ∀ n, ∀ᵐ p ∂(volume : Measure Plane), p ∉ K → v n i p = 0 := fun n => hv n i
  obtain ⟨ns,hns,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hi).exists_seq_tendsto_ae
  filter_upwards [countable_iInter_mem.mpr hmem,hae] with p hp hpae
  intro hout
  have hzero : ∀ n : ℕ, v (ns n) i p = 0 := fun n => (Set.mem_iInter.mp hp (ns n)) hout
  have hz : Tendsto (fun n => v (ns n) i p) atTop (𝓝 (0 : ℂ)) := by
    simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hpae hz

def testClass (ψ : Plane → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    ProductKernelL2TranslationAverage20261026a.PlaneL2 :=
  (hψ.continuous.memLp_of_hasCompactSupport hc).toLp ψ

def derivativeTestClass (v : Plane) (ψ : Plane → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    ProductKernelL2TranslationAverage20261026a.PlaneL2 :=
  ((directional_smooth v hψ).continuous.memLp_of_hasCompactSupport
    (directional_compact v hc)).toLp (directional v ψ)

def derivativeIndex (vertical : Bool) : Fin 3 := if vertical then 2 else 1

def derivativeDirection (vertical : Bool) : Plane := if vertical then ey else ex

def weakJets : Submodule ℂ JetSpace where
  carrier := {z | ∀ vertical : Bool, ∀ ψ : Plane → ℂ, ∀ hψ : ContDiff ℝ ∞ ψ,
    ∀ hc : HasCompactSupport ψ,
      inner ℂ (testClass ψ hψ hc) (z (derivativeIndex vertical)) +
        inner ℂ (derivativeTestClass (derivativeDirection vertical) ψ hψ hc) (z 0) = 0}
  zero_mem' := by
    intro vertical ψ hψ hc
    simp only [Pi.zero_apply,inner_zero_right,add_zero]
  add_mem' := by
    intro z w hz hw vertical ψ hψ hc
    change inner ℂ (testClass ψ hψ hc) (z (derivativeIndex vertical) + w (derivativeIndex vertical)) +
      inner ℂ (derivativeTestClass (derivativeDirection vertical) ψ hψ hc) (z 0 + w 0) = 0
    simp only [inner_add_right]
    linear_combination hz vertical ψ hψ hc + hw vertical ψ hψ hc
  smul_mem' := by
    intro c z hz vertical ψ hψ hc
    change inner ℂ (testClass ψ hψ hc) (c • z (derivativeIndex vertical)) +
      inner ℂ (derivativeTestClass (derivativeDirection vertical) ψ hψ hc) (c • z 0) = 0
    rw [inner_smul_right,inner_smul_right]
    calc
      _ = c * (inner ℂ (testClass ψ hψ hc) (z (derivativeIndex vertical)) +
        inner ℂ (derivativeTestClass (derivativeDirection vertical) ψ hψ hc) (z 0)) := by ring
      _ = 0 := by rw [hz vertical ψ hψ hc,mul_zero]

theorem weakJets_isClosed : IsClosed (weakJets : Set JetSpace) := by
  apply IsSeqClosed.isClosed
  intro z w hz hlim vertical ψ hψ hc
  let A := testClass ψ hψ hc
  let B := derivativeTestClass (derivativeDirection vertical) ψ hψ hc
  have hcont : Continuous (fun v : JetSpace => inner ℂ A (v (derivativeIndex vertical)) + inner ℂ B (v 0)) :=
    (continuous_const.inner (continuous_apply _)).add (continuous_const.inner (continuous_apply 0))
  have ht := (hcont.tendsto w).comp hlim
  have heq : (fun n => inner ℂ A (z n (derivativeIndex vertical)) + inner ℂ B (z n 0)) = fun _ : ℕ => (0 : ℂ) :=
    funext fun n => hz n vertical ψ hψ hc
  have hzero : Tendsto (fun n => inner ℂ A (z n (derivativeIndex vertical)) + inner ℂ B (z n 0))
      atTop (𝓝 0) := by rw [heq]; exact tendsto_const_nhds
  exact tendsto_nhds_unique ht hzero

/-- Fixed SOURCE rectangle. Both derivative components share the same
AE support, so a genuine compact representative is constructed later. -/
def rectangleH1Jets (L R a b : ℝ) : Submodule ℂ JetSpace :=
  supportedJets (rect L R a b) ⊓ weakJets

theorem rectangleH1Jets_isClosed (L R a b : ℝ) :
    IsClosed (rectangleH1Jets L R a b : Set JetSpace) :=
  (supportedJets_isClosed (rect L R a b)).inter weakJets_isClosed

end
end ImbalancedChen.Part3.FixedRectangleH1JetSpace20261026b
