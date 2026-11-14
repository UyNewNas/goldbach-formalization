import ImbalancedChen.Part3OriginalSwitchedCubicMeasures
import ImbalancedChen.Part3OriginalSwitchedRegularRows
import ImbalancedChen.Part3OriginalSwitchedHolShellPrice

/-! The two real-parameter Gram forms in their native normalization. The
arbitrary phases occur inside the common coefficient row before the norm. -/
namespace ImbalancedChen.Part3.OriginalSwitchedCubicRows20261113
noncomputable section
open Finset MeasureTheory Complex
open scoped Classical MatrixGroups
open OriginalSwitchedCubicMeasures20261113 (native_cubic)
open ActualMarkedCubicPrice20261112 (slotPrice linePrice slotPrice_nn linePrice_pos)
open ActualUnitBandSpectralMass20261112 (exceptional height)
open ActualFullCuspEigenbasis20261026b
open ActualCuspBasisWhittakerCoefficients20261102 (basisR)
open ActualCuspDenominatorClasses20261110 (Parameters)
open ActualContinuousClassFourier20261110 (nativeR)
open OriginalContinuousCuspGram20261110 (nativeMass)
open OriginalContinuousClassRemoval20261110 (markedRow)
open OriginalRegularPacketTest20261113 (energy Dyadic mark discreteRow lineMass nativeRow)
open ActualContinuousPoincarePairing20261110 (originalFrame)
open ActualIntervalGeometricSumSourceOnly (phaseAt)
open private phaseAt_norm from ImbalancedChen.Part3ActualIntervalGeometricSum
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open OriginalExceptionalJNativeCompletion20261110 (mem_full_classical_block)
open OriginalSwitchedSeparatedBlocks20261113 (rowSum)

local instance (d : ℕ+) : NeZero d.val := ⟨d.property.ne'⟩
abbrev Idx (d : ℕ+) := actualCuspBasisIndex d.val (NeZero.pos d.val)

def X (d : ℕ+) (j : ℕ) (u : ℕ→ℂ) (v : ℝ) (i : Idx d) :=
  rowSum j v (fun m => u m*basisR d.val (NeZero.pos d.val) i 1 (m:ℤ))
def Z (d : ℕ+) (j : ℕ) (u : ℕ→ℂ) (v : ℝ) (t : ℝ) (a : Parameters d.val) :=
  rowSum j v (fun m => u m*nativeR a false (m:ℤ) t)
def Xmass (d : ℕ+) (j : ℕ) (u : ℕ→ℂ) (v : ℝ) (i : Idx d) :=
  slotPrice d.val i*‖X d j u v i‖^2
def Zmass (d : ℕ+) (j : ℕ) (u : ℕ→ℂ) (v t : ℝ) :=
  linePrice t*nativeMass d.val (Z d j u v t)

theorem squares {ε : ℝ} (ep : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (d : ℕ+) (j : ℕ) (u : ℕ→ℂ) (v : ℝ),
      let B := C*(1+(classicalMScale j)^(1+ε)/(d.val:ℝ))*energy (dyadicWindow j) u
      Summable (Xmass d j u v) ∧ (∑' i,Xmass d j u v i)≤B ∧
      Integrable (Zmass d j u v) ∧ (∫ t,Zmass d j u v t)≤B := by
  obtain ⟨C,cp,P⟩ := native_cubic ep
  refine ⟨C,cp,fun d j u v => ?_⟩
  let S := dyadicWindow j
  let f := fun n => phaseAt v n*u n
  have h := P d.val false false (classicalMScale_bounds j).1 S f
    (fun n hn => (mem_full_classical_block j n).mp hn)
  have e : energy S f=energy S u := by simp only [energy,f,norm_mul,phaseAt_norm,one_mul]
  have x (i : Idx d) : discreteRow d.val false false S f i=X d j u v i := by
    simp only [discreteRow,markedRow,originalFrame,mark,S,f,X,rowSum,Finset.univ_eq_attach,Finset.sum_attach,
      Function.Embedding.coeFn_mk,Bool.false_eq_true,if_false,mul_assoc]
  have z (a : Parameters d.val) (t) : nativeRow d.val false false S f a t=Z d j u v t a := by
    simp only [nativeRow,markedRow,mark,S,f,Z,rowSum,Finset.univ_eq_attach,Finset.sum_attach,
      Function.Embedding.coeFn_mk,Bool.false_eq_true,if_false,mul_assoc]
  simpa only [Xmass,Zmass,e,lineMass,x,z] using h

def Dterm (d : ℕ+) (j : ℕ) (u : ℕ→ℂ) (v w : ℝ) (g : ℝ→ℂ) (i : Idx d) :=
  if exceptional d.val i then 0 else g (height d.val i)*star (X d j u v i)*X d j u w i

def Eterm (d : ℕ+) (j : ℕ) (u : ℕ→ℂ) (v w : ℝ) (g : ℝ→ℂ) (t : ℝ) :=
  ∑ a : Parameters d.val,g t*star (Z d j u v t a)*Z d j u w t a/(4*(Real.pi:ℂ))

theorem cross {ε : ℝ} (ep : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (d : ℕ+) (j : ℕ) (u : ℕ→ℂ) (v w : ℝ) (g : ℝ→ℂ) {P : ℝ},
      0≤P → (∀ t,‖g t‖≤P*linePrice t) → AEStronglyMeasurable g volume →
      let B := P*(C*(1+(classicalMScale j)^(1+ε)/(d.val:ℝ))*energy (dyadicWindow j) u)
      Summable (fun i => ‖Dterm d j u v w g i‖) ∧ (∑' i,‖Dterm d j u v w g i‖)≤B ∧
      Integrable (Eterm d j u v w g) ∧ (∫ t,‖Eterm d j u v w g t‖)≤B := by
  obtain ⟨C,cp,H⟩ := squares ep
  refine ⟨2*C,by positivity,fun d j u v w g P pp price gm => ?_⟩
  let B := C*(1+(classicalMScale j)^(1+ε)/(d.val:ℝ))*energy (dyadicWindow j) u
  have A := H d j u v
  have B' := H d j u w
  have pr (t : ℝ) (a b : ℂ) : ‖g t*star a*b‖≤P*(linePrice t*‖a‖^2+linePrice t*‖b‖^2) := by
    simp only [norm_mul,norm_star]
    have le := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (price t) (norm_nonneg a)) (norm_nonneg b)
    have am : ‖a‖*‖b‖≤‖a‖^2+‖b‖^2 := by nlinarith only [sq_nonneg (‖a‖-‖b‖),sq_nonneg ‖a‖,sq_nonneg ‖b‖]
    nlinarith only [le,mul_le_mul_of_nonneg_left am (mul_nonneg pp (linePrice_pos t).le)]
  have small (i : Idx d) : ‖Dterm d j u v w g i‖≤P*(Xmass d j u v i+Xmass d j u w i) := by
    by_cases hi : exceptional d.val i
    · simp only [Dterm,Xmass,slotPrice,if_pos hi,norm_zero,zero_mul,add_zero,mul_zero,le_refl]
    · simpa only [Dterm,Xmass,slotPrice,if_neg hi] using pr (height d.val i) (X d j u v i) (X d j u w i)
  have agg := (A.1.add B'.1).mul_left P
  have sm := agg.of_nonneg_of_le (fun _ => norm_nonneg _) small
  have large (t : ℝ) : ‖Eterm d j u v w g t‖≤P*(Zmass d j u v t+Zmass d j u w t) := by
    let δ := 4*Real.pi
    have dp : 0<δ := by dsimp [δ];positivity
    apply (norm_sum_le _ _).trans
    have e (a : Parameters d.val) :
        ‖g t*star (Z d j u v t a)*Z d j u w t a/(4*(Real.pi:ℂ))‖≤
          P*(linePrice t*(‖Z d j u v t a‖^2/δ)+linePrice t*(‖Z d j u w t a‖^2/δ)) := by
      have dnorm : ‖(4:ℂ)*(Real.pi:ℂ)‖=δ := by simp [δ,norm_mul,Real.pi_pos.le]
      rw [norm_div,dnorm]
      exact (div_le_div_of_nonneg_right (pr t _ _) dp.le).trans_eq (by ring)
    apply (sum_le_sum (s:=univ) (fun a _ => e a)).trans_eq
    simp only [Zmass,nativeMass,Finset.mul_sum,Finset.sum_add_distrib,δ,mul_add]
  have cost : P*(B+B)=P*((2*C)*(1+(classicalMScale j)^(1+ε)/(d.val:ℝ))*energy (dyadicWindow j) u) := by dsimp only [B];ring
  have zc (a : Parameters d.val) (v : ℝ) : Continuous (fun t => Z d j u v t a) := by
    apply continuous_finsetSum
    intro m _
    exact continuous_const.mul (continuous_const.mul
      (OriginalCumulativeContinuousRemoval20261110.nativeR_cont a false _))
  have em : AEStronglyMeasurable (Eterm d j u v w g) volume := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro a _
    exact ((gm.mul (zc a v).star.aestronglyMeasurable).mul (zc a w).aestronglyMeasurable).div
      aestronglyMeasurable_const
  have int := ((A.2.2.1.add B'.2.2.1).const_mul P).mono' em (ae_of_all _ large)
  refine ⟨sm,?_,?_⟩
  · have h := sm.tsum_le_tsum small agg
    rw [tsum_mul_left,A.1.tsum_add B'.1] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (add_le_add A.2.1 B'.2.1) pp).trans_eq cost)
  · refine ⟨int,?_⟩
    have h := integral_mono int.norm ((A.2.2.1.add B'.2.2.1).const_mul P) large
    rw [integral_const_mul,integral_add A.2.2.1 B'.2.2.1] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (add_le_add A.2.2.2 B'.2.2.2) pp).trans_eq cost)

end
end ImbalancedChen.Part3.OriginalSwitchedCubicRows20261113
