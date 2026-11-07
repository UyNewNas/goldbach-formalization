import ImbalancedChen.P5OriginalJointPresievedCentrePayment
import ImbalancedChen.P5ZU1011JointNearCapPrimeReserve
import ImbalancedChen.CurrentChenTrueLiNormalization

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The common-beta attachment and centre errors are paid on the actual
original normalization, while the signed AP error retains the SAME newly
constructed presieved coefficient. The comparison main is the literal
native ALL16 row density sum; no sharp numerical K bound is assumed.
The uniform original prime-box mass and true logarithmic integral bounds
are used to pay the attachment reserve after its common beta choice.
-/

namespace ImbalancedChen.P5Z.OriginalJointPresievedNativeReduction

noncomputable section
open Filter Topology
open scoped BigOperators
open Classical
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open OriginalCommonBetaActualParameters OriginalJointPresievedCompiler
open OriginalJointCommonBetaModel OriginalJointPresievedCentrePayment
open U1011AdaptivePrimeError JointNearCapPrimeReserve
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

def prefixMass (n N:ℕ) (E:ℕ×ℕ→Prop) : ℝ :=
  ∑t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
    1/(Nat.totient (fullPrefix t):ℝ)

def nativeMean (n N:ℕ) (eta:ℚ) (E:ℕ×ℕ→Prop) : ℝ :=
  ∑t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
    (1/(Nat.totient (fullPrefix t):ℝ))*
      actualSmallRosserPlusDensity N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
        (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
        (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)

private theorem prefixMass_le_originalCube {n N:ℕ} (hN:1<N) (E:ℕ×ℕ→Prop)
    (hbox:actualPrimeBoxMass N (fun _:Fin 4=>(417/5000:ℝ)) (fun _=>(59/250:ℝ))≤
      originalCubeMassBound) : prefixMass n N E≤originalCubeMassBound := by
  have hsub : U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E⊆jointSelector N E :=
    Finset.filter_subset _ _
  have hboxMass : jointMass N E (fun _=>True) (fun _=>1)≤
      actualPrimeBoxMass N (fun _:Fin 4=>(417/5000:ℝ)) (fun _=>(59/250:ℝ)) := by
    rw [jointMass_eq_box hN E (fun _=>True) (fun _=>1)]
    change (∑q∈BufferedPrimeErrorPayment.tuples N,
      if jointKept N E (fun _=>True) q then BufferedPrimeErrorPayment.weight q*1 else 0)≤
      ∑q∈BufferedPrimeErrorPayment.tuples N,BufferedPrimeErrorPayment.weight q
    apply Finset.sum_le_sum
    intro q hq
    by_cases hk:jointKept N E (fun _=>True) q
    · simp only [if_pos hk,mul_one,le_refl]
    · simp only [if_neg hk]
      exact actualPrimeBoxWeight_nonneg hq
  calc
    prefixMass n N E≤∑t∈jointSelector N E,1/(Nat.totient (fullPrefix t):ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _=>one_div_nonneg.mpr (Nat.cast_nonneg _))
    _ = jointMass N E (fun _=>True) (fun _=>1) := by simp only [jointMass,if_true]
    _ ≤ originalCubeMassBound := hboxMass.trans hbox

/-- Actual original full-source reduction with both attachment and centre
paid, leaving the explicit native density mean and the signed AP error of
the SAME physical presieved rho. No AP or numerical-density hypothesis is
among the inputs. The original fallback remains an actual count. -/
theorem exists_original_joint_presieved_reduction (n:ℕ) (eta:ℚ) (heta:0<eta)
    (nu error:ℝ) (hnu:0<nu) (herror:0<error) :
    ∃epsilon:ℝ,0<epsilon ∧ epsilon<epsilonBudget n eta nu ∧
      ∃N0:ℕ,4≤N0 ∧ ∀N:ℕ,N0≤N → Even N → ∀E:ℕ×ℕ→Prop,
        let w:=(N:ℝ)^(nu*epsilon^2)
        let B:=(N:ℝ)^(nu*epsilon)
        currentChenUpsilon10 N+currentChenUpsilon11 N E≤
          (∑t∈U1011OriginalSixteenJointNearCapCompiler.fallbackTuples n N E,U11Adaptive.weight N t)+
          trueLogarithmicIntegral N*nativeMean n N eta E+
            jointAP n N eta w B E+error*singularNormalization N := by
  let C:=originalCubeMassBound
  have hC:0≤C := by dsimp only [C,originalCubeMassBound]; positivity
  have hC1:0<C+1 := by linarith
  let reserve:=error/(4*(C+1))
  have hreserve:0<reserve := by dsimp only [reserve]; positivity
  have hreserveEq:reserve*(4*(C+1))=error := by
    dsimp only [reserve]
    exact div_mul_cancel₀ _ (by positivity)
  have hscalar:2*reserve*C≤error/2 := by nlinarith
  obtain ⟨epsilon,he,heBudget,Nmodel,hNmodel,hmodel⟩ :=
    exists_original_joint_common_beta_model n eta heta nu reserve hnu hreserve
  obtain ⟨Ncentre,hNcentre⟩ := eventually_atTop.mp
    (eventually_original_joint_upper_centre_paid (error/2) (half_pos herror))
  obtain ⟨Nli,hNli⟩ := eventually_atTop.mp (eventually_currentChen_trueLi_le 1 (by norm_num))
  obtain ⟨Nmass,hNmass⟩ := eventually_atTop.mp eventually_originalCube_mass_bounded
  refine ⟨epsilon,he,heBudget,4+Nmodel+Ncentre+Nli+Nmass,by omega,?_⟩
  intro N hN hEven E
  have hNm:Nmodel≤N := by omega
  have hNc:Ncentre≤N := by omega
  have hNl:Nli≤N := by omega
  have hNp:Nmass≤N := by omega
  have hN4:4≤N := by omega
  have hN1:1<N := by omega
  have hn:(1:ℝ)<N := by exact_mod_cast hN1
  have hn0:(0:ℝ)<N := zero_lt_one.trans hn
  have hlog:0<Real.log (N:ℝ) := Real.log_pos hn
  have hLi:0≤trueLogarithmicIntegral N := by
    change 0≤MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral (2/Real.log 2) (N:ℝ)
    exact MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg _ (by positivity)
      (by exact_mod_cast (show 2≤N by omega))
  have hLiUpper:trueLogarithmicIntegral N≤2*(N:ℝ)/Real.log (N:ℝ) := by
    simpa only [show (1:ℝ)+1=2 by norm_num] using hNli N hNl
  have hmass:prefixMass n N E≤C := prefixMass_le_originalCube hN1 E (hNmass N hNp)
  have hnorm:0≤singularNormalization N := by unfold singularNormalization; positivity
  have hrnorm:0≤reserve*singularSeries N/Real.log (N:ℝ) :=
    div_nonneg (mul_nonneg hreserve.le (singularSeries_pos N).le) hlog.le
  have hm:=hmodel N hNm hEven E
  dsimp only at hm
  have hcomparison : jointDensity n N eta ((N:ℝ)^(nu*epsilon^2)) ((N:ℝ)^(nu*epsilon)) E≤
      nativeMean n N eta E+(reserve*singularSeries N/Real.log (N:ℝ))*prefixMass n N E :=
    hm.2.2.1
  have hbeta : trueLogarithmicIntegral N *
      ((reserve*singularSeries N/Real.log (N:ℝ))*prefixMass n N E)≤
      (error/2)*singularNormalization N := by
    calc
      _ ≤ trueLogarithmicIntegral N *((reserve*singularSeries N/Real.log (N:ℝ))*C) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass hrnorm) hLi
      _ ≤ (2*(N:ℝ)/Real.log (N:ℝ))*((reserve*singularSeries N/Real.log (N:ℝ))*C) :=
        mul_le_mul_of_nonneg_right hLiUpper (mul_nonneg hrnorm hC)
      _ = (2*reserve*C)*singularNormalization N := by
        unfold singularNormalization
        field_simp [hlog.ne']
        ring
      _ ≤ (error/2)*singularNormalization N := mul_le_mul_of_nonneg_right hscalar hnorm
  have hmean : trueLogarithmicIntegral N *
      jointDensity n N eta ((N:ℝ)^(nu*epsilon^2)) ((N:ℝ)^(nu*epsilon)) E≤
      trueLogarithmicIntegral N*nativeMean n N eta E+(error/2)*singularNormalization N := by
    have h:=mul_le_mul_of_nonneg_left hcomparison hLi
    rw [mul_add] at h
    exact h.trans (add_le_add_left hbeta _)
  have hupper:=hNcentre N hNc n eta heta nu epsilon hnu he heBudget E
  dsimp only at hupper ⊢
  linarith

end
end ImbalancedChen.P5Z.OriginalJointPresievedNativeReduction
