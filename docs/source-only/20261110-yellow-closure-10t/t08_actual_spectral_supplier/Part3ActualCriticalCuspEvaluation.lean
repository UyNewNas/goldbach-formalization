import ImbalancedChen.Part3ActualYoungCriticalCusps
import ImbalancedChen.Part3ActualParabolicIncoming
import Mathlib.Analysis.Meromorphic.Complex
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! Independence of the continued physical cusp functions at almost every
real spectral parameter. The witness is one actual horocycle evaluation
point per cusp, with the same height for the entire original level. -/
namespace ImbalancedChen.Part3.ActualCriticalCuspEvaluation20261110

noncomputable section
open Set Filter Topology Complex UpperHalfPlane Matrix MeasureTheory
open scoped BigOperators MatrixGroups UpperHalfPlane
open ActualYoungCriticalCusps20261110 ActualYoungCriticalD20261110
open ActualCharacterCriticalFamily20261110 ActualYoungDilationInverse20261110
open ActualYoungCuspCoefficients20261110 ActualCharacterCuspExpansion20261110
open ActualParabolicIncoming20261110 CharacterEisensteinGrowingHeight20261026b
open Gamma0GeneralCuspUnitPeriod20261025a Gamma0DegeneracyMapSourceOnly
open CompletedActualEisensteinIdentity20261025a NativeAllCuspEisenstein20261026b

local instance (N : ℕ) : DecidableEq (CuspRowClass N) := Classical.decEq _
local instance (N : ℕ) : DecidableEq (NativeCusps N) := Classical.decEq _

private theorem entire_meromorphic {f : ℂ → ℂ} (hf : Differentiable ℂ f) : Meromorphic f :=
  fun x => ((analyticOnNhd_univ_iff_differentiable.mpr hf) x (mem_univ x)).meromorphicAt

private theorem reciprocal_meromorphic {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Meromorphic (reciprocalL χ) := by
  by_cases h : χ = 1
  · simpa only [reciprocalL,if_pos h] using
      (entire_meromorphic (differentiable_id.sub_const (1 : ℂ))).fun_div
        (entire_meromorphic (DirichletCharacter.differentiable_LFunctionTrivChar₁ q))
  · have hL : Differentiable ℂ χ.LFunction := fun u => DirichletCharacter.differentiableAt_LFunction χ u (.inr h)
    simpa only [reciprocalL,if_neg h] using (entire_meromorphic hL).fun_inv

theorem ordinary_meromorphic {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℍ) :
    Meromorphic (fun s => ordinary χ s z) := by
  have hpow (c : ℂ) (hc : c ≠ 0) : Meromorphic (fun s : ℂ => c^s) :=
    entire_meromorphic (fun _ => differentiableAt_id.const_cpow (.inl hc))
  have hpi := hpow (Real.pi : ℂ) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hrec {n : ℕ} [NeZero n] (η : DirichletCharacter ℂ n) :
      Meromorphic (fun s : ℂ => reciprocalL η (2*s)) :=
    fun s => ((reciprocal_meromorphic η) (2*s)).comp_analyticAt
      (show AnalyticAt ℂ (fun w : ℂ => 2*w) s by fun_prop)
  by_cases h : q = 1
  · simpa only [ordinary,if_pos h,principalOrdinary] using
      (((hpi.fun_div Meromorphic.Gamma).fun_mul (hrec (1 : DirichletCharacter ℂ 1))).fun_mul
        (completedActualEisenstein_meromorphic z))
  · have hq := hpow (q : ℂ) (Nat.cast_ne_zero.mpr (NeZero.ne q))
    simpa only [ordinary,if_neg h,primitiveFamily,uncompletionFactor] using
      (((((hpi.fun_div hq).fun_mul (Meromorphic.const _)).fun_div Meromorphic.Gamma).fun_mul
        (hrec (χ^2))).fun_mul (entire_meromorphic (completedFamily_entire χ z)))

private theorem meromorphic_det {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ℂ → Matrix ι ι ℂ)
    (hA : ∀ i j, Meromorphic (fun w => A w i j)) : Meromorphic (fun w => (A w).det) := by
  simp only [Matrix.det_apply']
  apply Meromorphic.fun_sum
  intro σ _
  exact (Meromorphic.const _).fun_mul (Meromorphic.fun_prod (fun i _ => hA (σ i) i))

theorem criticalD_meromorphic {q L : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hL : 0 < L) (j : Div L) (z : ℍ) : Meromorphic (fun s => criticalD χ hL j s z) := by
  classical
  let K := fun s => kernelMatrix χ s L
  let V := fun s (b : Div L) => ordinary χ s (degeneracyDiagonal (dilation hL b) (dilation hL b).pos • z)
  have hK (i k : Div L) : Meromorphic (fun w => K w i k) := by
    have h (a : ℕ) : Meromorphic (fun w => twist χ w a) :=
      entire_meromorphic (fun w => (((differentiableAt_id.neg).mul_const (Real.log (a : ℝ) : ℂ)).cexp).const_mul _)
    exact (h _).fun_mul (h _)
  have hnum : Meromorphic (fun w => ((K w).updateCol j (V w)).det) := by
    apply meromorphic_det
    intro i k
    by_cases h : k = j
    · subst k
      simpa only [Matrix.updateCol_self,V] using ordinary_meromorphic χ _
    · simpa only [Matrix.updateCol_ne h] using hK i k
  have hlevel : Meromorphic (levelFactor (q^2*L) (q*j.1)) :=
    entire_meromorphic (fun _ => (differentiableAt_id.mul_const _).cexp)
  simpa only [criticalD,Matrix.cramer_apply,K,V] using
    hnum.fun_div ((meromorphic_det K hK).fun_mul hlevel)

/-- Global meromorphy supplies an open neighborhood across each critical
parameter, including the principal character at conductor one. -/
theorem cuspFamily_meromorphic (N : ℕ) [NeZero N] (a : NativeCusps N) (z : ℍ) :
    Meromorphic (fun s => cuspFamily N a s z) := by
  classical
  let d := (ActualCuspDenominatorClasses20261110.youngCuspEquiv N).symm a
  have hd : 0 < ActualCuspDenominatorClasses20261110.band N d.1.1 :=
    Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp d.1.2).1 (NeZero.pos N))
  letI : NeZero (ActualCuspDenominatorClasses20261110.band N d.1.1) := ⟨hd.ne'⟩
  change Meromorphic (fun s => parameterFamily d s z)
  unfold parameterFamily
  apply (Meromorphic.const _).fun_mul
  apply Meromorphic.fun_sum
  intro ξ _
  letI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  exact (Meromorphic.const _).fun_mul (criticalD_meromorphic ξ.primitiveCharacter _ _ z)

private def observer (N : ℕ) [NeZero N] (y : ℝ) (a : CuspRowClass N) : ℍ :=
  normalizedScaling N (NeZero.pos N) (classFrame a) • cuspPoint 0 y

private def evaluation (N : ℕ) [NeZero N] (y : ℝ) (s : ℂ) : Matrix (CuspRowClass N) (CuspRowClass N) ℂ :=
  fun i j => cuspFamily N ((nativeCuspEquiv N) j) s (observer N y i) / ((y^(2 : ℝ) : ℝ) : ℂ)

private theorem evaluation_initial_limit (N : ℕ) [NeZero N] :
    Tendsto (fun y : ℝ => evaluation N y 2) atTop (𝓝 1) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hiff : nativeFrameOrbit N (classFrame i) = nativeFrameOrbit N (classFrame j) ↔ i = j :=
    (nativeCuspEquiv N).injective.eq_iff
  change Tendsto (fun y : ℝ =>
    cuspFamily N (nativeFrameOrbit N (classFrame j)) 2 (observer N y i)/_) atTop (𝓝 ((1 : Matrix _ _ ℂ) i j))
  simp_rw [cuspFamily_initial N _ 2 (by norm_num)]
  simpa only [observer,Complex.ofReal_ofNat,Matrix.one_apply,hiff] using
    parabolic_incoming N (NeZero.pos N) (classFrame j) (classFrame i) 2 (by norm_num) 0

private theorem one_height (N : ℕ) [NeZero N] :
    ∃ y : ℝ, 1 ≤ y ∧ (evaluation N y 2).det ≠ 0 := by
  have hc : Continuous (fun M : Matrix (CuspRowClass N) (CuspRowClass N) ℂ => M.det) :=
    continuous_id.matrix_det
  have ht : Tendsto (fun y : ℝ => (evaluation N y 2).det) atTop (𝓝 1) := by
    simpa using (hc.tendsto 1).comp (evaluation_initial_limit N)
  exact ((eventually_ge_atTop (1 : ℝ)).and (ht.eventually (eventually_ne_nhds one_ne_zero))).exists

private theorem evaluation_continuous_two (N : ℕ) [NeZero N] (y : ℝ) :
    ContinuousAt (fun w => (evaluation N y w).det) 2 := by
  have hc : Continuous (fun M : Matrix (CuspRowClass N) (CuspRowClass N) ℂ => M.det) :=
    continuous_id.matrix_det
  apply hc.continuousAt.comp
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  exact ((parameterFamily_differentiable _ (observer N y i) 2 (by norm_num) (by norm_num)).continuousAt).div_const _

def criticalPoint (t : ℝ) : ℂ := 1/2+Complex.I*t

private theorem criticalPoint_injective : Function.Injective criticalPoint := by
  intro a b h
  simpa [criticalPoint,Complex.mul_im] using congrArg Complex.im h

/-- The exceptional set is bounded above by the critical zeros of one
realized meromorphic evaluation determinant. In particular it is countable. -/
theorem countable_dependence (N : ℕ) [NeZero N] :
    Set.Countable {t : ℝ | ¬ LinearIndependent ℂ (fun a : NativeCusps N => cuspFamily N a (criticalPoint t))} := by
  classical
  obtain ⟨y,_,h₂⟩ := one_height N
  let H := fun s => (evaluation N y s).det
  have hm : Meromorphic H := meromorphic_det _ (fun i j =>
    (cuspFamily_meromorphic N _ (observer N y i)).fun_div (Meromorphic.const _))
  have htop : meromorphicOrderAt H 2 ≠ ⊤ := by
    intro he
    have hz := meromorphicOrderAt_eq_top_iff.mp he
    have hn : ∀ᶠ w in 𝓝[≠] (2 : ℂ), H w ≠ 0 := ((evaluation_continuous_two N y).tendsto.eventually
      (eventually_ne_nhds h₂)).filter_mono nhdsWithin_le_nhds
    obtain ⟨w,hw,hw'⟩ := (hz.and hn).exists
    exact hw' hw
  have hall := hm.exists_meromorphicOrderAt_ne_top_iff_forall.mp ⟨2,htop⟩
  let Z : Set ℂ := {s | H s = 0}
  have hZ : Zᶜ ∈ codiscrete ℂ := hm.meromorphicOn.codiscreteWithin_setOfPred_ne_zero (fun z _ => hall z)
  obtain ⟨hclosed,hdiscrete⟩ := compl_mem_codiscrete_iff.mp hZ
  have hcZ : Z.Countable := hclosed.isLindelof.countable_of_isDiscrete hdiscrete
  apply (hcZ.preimage criticalPoint_injective).mono
  intro t ht
  by_contra hnot
  have hdet : (evaluation N y (criticalPoint t)).det ≠ 0 := hnot
  apply ht
  apply (linearIndependent_equiv (nativeCuspEquiv N)).mp
  apply Fintype.linearIndependent_iff.mpr
  intro u hu j
  let A := evaluation N y (criticalPoint t)
  have hz (i : CuspRowClass N) :
      ∑ k : CuspRowClass N, u k * cuspFamily N ((nativeCuspEquiv N) k) (criticalPoint t) (observer N y i) = 0 := by
    simpa only [Function.comp_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using
      congrFun hu (observer N y i)
  have hvec : A *ᵥ u = 0 := by
    funext i
    change (∑ k : CuspRowClass N, (cuspFamily N ((nativeCuspEquiv N) k) (criticalPoint t) (observer N y i) /
      ((y^(2 : ℝ) : ℝ) : ℂ))*u k) = 0
    calc
      _ = (∑ k : CuspRowClass N, u k*cuspFamily N ((nativeCuspEquiv N) k) (criticalPoint t)
          (observer N y i))/((y^(2 : ℝ) : ℝ) : ℂ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = 0 := by rw [hz,zero_div]
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr (A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet))
  exact congrFun (hinj (hvec.trans (Matrix.mulVec_zero A).symm)) j

theorem ae_native_cusps_independent (N : ℕ) [NeZero N] :
    ∀ᵐ t : ℝ ∂volume, LinearIndependent ℂ (fun a : NativeCusps N => cuspFamily N a (criticalPoint t)) :=
  ae_iff.mpr ((countable_dependence N).measure_zero volume)

end
end ImbalancedChen.Part3.ActualCriticalCuspEvaluation20261110

