import ImbalancedChen.Part3OriginalSwitchedCubicReflected
import ImbalancedChen.Part3OriginalSwitchedProjectionMask
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! The original single-cutoff trace paired with an arbitrary common row.
Finite mark pairing is performed before taking the two native positive
squares. -/
namespace ImbalancedChen.Part3.OriginalSwitchedCubicSingle20261113
noncomputable section
open Finset MeasureTheory Complex
open scoped Classical BigOperators MatrixGroups
open OriginalSwitchedCubicRows20261113 (Idx X Z Dterm Eterm cross)
open OriginalSwitchedCubicReflected20261113 (mode_cont)
open OriginalSwitchedRegularFourierBudget20261113 (scaled)
open OriginalSwitchedRegularMarkExchange20261113 (principal incoming)
open OriginalSwitchedRegularRows20261113 (amplitude)
open OriginalSwitchedLevelIdentity20261113 (single)
open OriginalSwitchedCutoffModes20261113 (mode coefficient)
open OriginalSwitchedCutoffFamily20261113 (profile)
open OriginalSwitchedUniformRegularTransform20261113 (regular_return)
open OriginalSwitchedModeTransforms20261113 (tested_transforms)
open ActualPrescribedPositiveJ20261112 (positiveWeight)
open ActualMarkedCubicPrice20261112 (linePrice linePrice_pos slotPrice)
open ActualPositiveNativeDiagonal20261112 (nativeWeight)
open ActualUnitBandSpectralMass20261112 (exceptional height)
open OriginalSameInfinityTensorSpectrum20261113 (disc cont)
open OriginalSameInfinityScalarPrices20261113 (cubic_prices covariance_meas)
open OriginalSwitchedSeparatedBlocks20261113 (rowSum)
open OriginalContinuousCuspGram20261110 (nativeProduct)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualIntervalGeometricSumSourceOnly (phaseAt)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open OriginalClassicalSpectralSupports20261102 (classicalMScale)
open OriginalRegularPacketTest20261113 (energy)
open ActualCuspDenominatorClasses20261110 (Parameters)
open ActualCuspBasisWhittakerCoefficients20261102 (basisR)
open ActualContinuousClassFourier20261110 (nativeR)
open private price_div from ImbalancedChen.Part3OriginalMarkedPacketLimits
open private mark from ImbalancedChen.Part3OriginalSwitchedNativeBilinearTrace

local instance (d : ℕ+) : NeZero d.val := ⟨d.property.ne'⟩

theorem scalar :
    ∃ K : ℝ,0≤K ∧ ∀ Y : ℝ,1≤Y →
      AEStronglyMeasurable (scaled (single Y)) volume ∧
      ∀ t,‖scaled (single Y) t‖≤(K*(1+Real.log (2*Y)^2))*linePrice t := by
  obtain ⟨K,kp,H⟩ := regular_return
  refine ⟨K,kp,fun Y y1 => ?_⟩
  let g := scaled (single Y)
  let c := coefficient false 0
  let f := fun n t => c n*scaled (spectralTest (mode n) Y⁻¹) t
  have yp := zero_lt_one.trans_le y1
  have val (t : ℝ) : (∑' n : ℤ,f n t)=g t := by
    have p := ((tested_transforms false 0 Y yp).1 t).div_const (Real.cosh (Real.pi*t):ℂ)
    have eq := p.tsum_eq
    simp only [profile,Bool.false_eq_true,if_false,mul_one] at eq
    simpa only [f,c,g,scaled,single,mul_div_assoc] using eq
  constructor
  · have mf (n : ℤ) : AEStronglyMeasurable (f n) volume := aestronglyMeasurable_const.mul (mode_cont yp n).aestronglyMeasurable
    exact (AEStronglyMeasurable.tsum mf).congr (ae_of_all _ val)
  · intro t
    apply price_div
    have ch := Real.cosh_pos (Real.pi*t)
    simp only [scaled,norm_div,Complex.norm_real,Real.norm_of_nonneg ch.le]
    rw [show (1+|t|)^3*Real.cosh (Real.pi*t)*(‖positiveWeight (single Y) t‖/Real.cosh (Real.pi*t))=
      (1+|t|)^3*‖positiveWeight (single Y) t‖ by field_simp [ch.ne']]
    simpa only [single,profile,Bool.false_eq_true,if_false,mul_one] using H Y y1 false 0 t

def first (J : ℕ+→ℕ+→(ℝ→ℂ)→ℂ) (d : ℕ+) (j : ℕ) (Y ω : ℝ) (u : ℕ→ℂ) :=
  ∑ m : ↥(dyadicWindow j),∑ n : ↥(dyadicWindow j),amplitude u ω m.val n.val*J (mark m) (mark n) (single Y)

private theorem joined (j : ℕ) (ω : ℝ) (u r : ℕ→ℂ) (g : ℂ) :
    (∑ m : ↥(dyadicWindow j),∑ n : ↥(dyadicWindow j),
      amplitude u ω m.val n.val*(g*(star (r m.val)*r n.val)))=
        g*star (rowSum j ω (fun m => u m*r m))*rowSum j ω (fun m => u m*r m) := by
  let I := ↥(dyadicWindow j)
  let f (m : I) := phaseAt ω m.val*(u m.val*r m.val)
  have point (m n : I) : amplitude u ω m.val n.val*(g*(star (r m.val)*r n.val))=
      g*(star (f m)*f n) := by
    dsimp only [amplitude,f];simp only [star_mul'];ring
  simp_rw [point]
  change (∑ m : I,∑ n : I,g*(star (f m)*f n))=g*star (∑ m : I,f m)*(∑ n : I,f n)
  have outer : (∑ m : I,∑ n : I,g*(star (f m)*f n))=g*(∑ m : I,∑ n : I,star (f m)*f n) := by
    simp only [Finset.mul_sum]
  have inner (m : I) : (∑ n : I,star (f m)*f n)=star (f m)*(∑ n : I,f n) := by rw [Finset.mul_sum]
  rw [outer,star_sum]
  simp_rw [inner]
  rw [←Finset.sum_mul,mul_assoc]

theorem original {ε : ℝ} (ep : 0<ε) :
    ∃ C : ℝ,0≤C ∧ ∀ (d : ℕ+) (j : ℕ) (u : ℕ→ℂ) (Y ω : ℝ),1≤Y →
      let B := C*(1+Real.log (2*Y)^2)*(1+(classicalMScale j)^(1+ε)/(d.val:ℝ))*energy (dyadicWindow j) u
      ‖first (principal d) d j Y ω u‖≤B ∧ ‖first (incoming d) d j Y ω u‖≤B := by
  obtain ⟨K,kp,scalarPrice⟩ := scalar
  obtain ⟨H,hp,row⟩ := cross ep
  refine ⟨K*H,mul_nonneg kp hp.le,fun d j u Y ω y1 => ?_⟩
  let g := scaled (single Y)
  let P := K*(1+Real.log (2*Y)^2)
  let B := H*(1+(classicalMScale j)^(1+ε)/(d.val:ℝ))*energy (dyadicWindow j) u
  have pp : 0≤P := mul_nonneg kp (by positivity)
  obtain ⟨gm,price⟩ := scalarPrice Y y1
  have r := row d j u ω ω g pp price gm
  let I := ↥(dyadicWindow j)
  let a (m n : I) := amplitude u ω m.val n.val
  let fd (m n : I) (i : Idx d) := if exceptional d.val i then 0 else
    g (height d.val i)*disc d (mark m) (mark n) i
  let fe (m n : I) (t : ℝ) := g t*cont d (mark m) (mark n) t
  have hd (m n : I) : HasSum (fd m n) (principal d (mark m) (mark n) (single Y)) := by
    have dom := (cubic_prices d (mark m) (mark n)).1.mul_left P
    have summ : Summable (fd m n) := dom.of_norm_bounded (fun i => by
      by_cases hi : exceptional d.val i
      · simp only [fd,slotPrice,if_pos hi,norm_zero,zero_mul,mul_zero,le_refl]
      · simp only [fd,slotPrice,if_neg hi,norm_mul]
        exact (mul_le_mul_of_nonneg_right (price _) (norm_nonneg _)).trans_eq (by ring))
    have eq (i : Idx d) : (if exceptional d.val i then 0 else nativeWeight d.val (single Y) i*disc d (mark m) (mark n) i)=fd m n i := by
      by_cases hi : exceptional d.val i <;> simp only [fd,hi,if_true,if_false,nativeWeight,g,scaled]
    simpa only [principal,eq] using summ.hasSum
  have he (m n : I) : Integrable (fe m n) :=
    ((cubic_prices d (mark m) (mark n)).2.const_mul P).mono' (gm.mul (covariance_meas d (mark m) (mark n)))
      (ae_of_all _ (fun t => by rw [show ‖fe m n t‖=‖g t‖*‖cont d (mark m) (mark n) t‖ from norm_mul _ _]
                                exact (mul_le_mul_of_nonneg_right (price t) (norm_nonneg _)).trans_eq (by ring)))
  have xd (i : Idx d) : (∑ m : I,∑ n : I,a m n*fd m n i)=Dterm d j u ω ω g i := by
    by_cases hi : exceptional d.val i
    · simp only [fd,Dterm,if_pos hi,mul_zero,sum_const_zero]
    · simpa only [a,fd,Dterm,if_neg hi,disc,mark,X] using
        joined j ω u (fun m => basisR d.val (NeZero.pos d.val) i 1 (m:ℤ)) (g (height d.val i))
  have xe (t : ℝ) : (∑ m : I,∑ n : I,a m n*fe m n t)=Eterm d j u ω ω g t := by
    let δ : ℂ := 4*(Real.pi:ℂ)
    let R (b : Parameters d.val) (m : ℕ) := nativeR b false (m:ℤ) t
    let z (m n : I) (b : Parameters d.val) := a m n*(g t*(star (R b m.val)*R b n.val))/δ
    calc
      _ = ∑ m : I,∑ n : I,∑ b : Parameters d.val,z m n b := by
        simp only [fe,cont,nativeProduct,Finset.mul_sum,mark,z,R,δ,mul_div_assoc]
      _ = ∑ b : Parameters d.val,∑ m : I,∑ n : I,z m n b := by
        rw [sum_comm (s:=(univ:Finset (Parameters d.val))) (t:=(univ:Finset I))]
        apply sum_congr rfl
        intro m _
        rw [sum_comm (s:=(univ:Finset (Parameters d.val))) (t:=(univ:Finset I))]
      _ = _ := by
        apply sum_congr rfl
        intro b _
        simp only [z,←Finset.sum_div]
        exact congrArg (fun c : ℂ => c/δ) (joined j ω u (R b) (g t))
  have terms := hasSum_sum (s:=univ) (fun m (_ : m∈(univ:Finset I)) => hasSum_sum (s:=univ)
    (fun n (_ : n∈(univ:Finset I)) => (hd m n).mul_left (a m n)))
  have dval : HasSum (Dterm d j u ω ω g) (first (principal d) d j Y ω u) :=
    terms.congr_fun (fun i => (xd i).symm)
  have eval : first (incoming d) d j Y ω u=∫ t,Eterm d j u ω ω g t := by
    simp_rw [←xe]
    rw [integral_finsetSum univ (fun m _ => integrable_finsetSum univ (fun n _ => (he m n).const_mul _))]
    apply sum_congr rfl
    intro m _
    rw [integral_finsetSum univ (fun n _ => (he m n).const_mul _)]
    simp only [integral_const_mul,first,incoming,fe,g,a]
  have pack : P*B=(K*H)*(1+Real.log (2*Y)^2)*(1+(classicalMScale j)^(1+ε)/(d.val:ℝ))*energy (dyadicWindow j) u := by
    dsimp only [P,B];ring
  rw [←dval.tsum_eq,eval]
  exact ⟨(norm_tsum_le_tsum_norm r.1).trans (r.2.1.trans_eq pack),
    (norm_integral_le_integral_norm _).trans (r.2.2.2.trans_eq pack)⟩

end
end ImbalancedChen.Part3.OriginalSwitchedCubicSingle20261113
