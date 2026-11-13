import ImbalancedChen.Part3OriginalSwitchedRegularModePrice
import ImbalancedChen.Part3OriginalSwitchedModeTransforms
import ImbalancedChen.Part3OriginalSameInfinityFixedScalarTrace

/-! Exchange the period series with both complete weight-zero
spectra of the same quotient, with the actual two marked coordinates. -/
namespace ImbalancedChen.Part3.OriginalSwitchedMaassExchange20261113
noncomputable section
open Set MeasureTheory Complex
open scoped Topology BigOperators Classical
open OriginalSwitchedCutoffModes20261113 OriginalSwitchedModeTransforms20261113
open OriginalSwitchedCutoffFamily20261113 (profile)
open OriginalSwitchedSchwartzPrices20261113 (weight)
open OriginalSwitchedRegularModePrice20261113 (regular_mode_price)
open OriginalSameInfinityFixedScalarTrace20261113 (total)
open OriginalSameInfinityTensorSpectrum20261113 (disc cont)
open OriginalSameInfinityScalarPrices20261113 (cubic_prices covariance_meas)
open ActualPositiveNativeDiagonal20261112 ActualPrescribedPositiveJ20261112
open ActualUnitBandSpectralMass20261112 ActualMarkedCubicPrice20261112
open ActualFullCuspEigenbasis20261026b ActualCuspBasisIndexCounting20261026b
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open private price_div from ImbalancedChen.Part3OriginalMarkedPacketLimits

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

def mass (q m n : ℕ+) (Φ : ℝ→ℂ) :=
  total q m n (nativeWeight q.val Φ) (fun t => positiveWeight Φ t/(Real.cosh (Real.pi*t):ℂ))

private theorem rectangle {ι κ : Type*} {A : ι→ℝ} {B : κ→ℝ}
    (a : Summable A) (b : Summable B) (an : ∀ i,0≤A i) (bn : ∀ i,0≤B i) :
    Summable (fun p : ι×κ => A p.1*B p.2) := by
  apply (summable_prod_of_nonneg (fun _ => mul_nonneg (an _) (bn _))).mpr
  exact ⟨fun i => b.mul_left (A i),by simpa only [tsum_mul_left] using a.mul_right (∑' i,B i)⟩

theorem maass_exchange (q m n : ℕ+) (s : Bool) (L Y : ℝ) (yp : 0<Y) :
    HasSum (fun k : ℤ => coefficient s L k*mass q m n (spectralTest (mode k) Y⁻¹))
      (mass q m n (fun x => profile s L (Y*x))) := by
  let Φ := fun k : ℤ => spectralTest (mode k) Y⁻¹
  let f := fun x => profile s L (Y*x)
  let c := coefficient s L
  let Idx := actualCuspBasisIndex q.val (NeZero.pos q.val)
  let W := fun k (t : ℝ) => positiveWeight (Φ k) t/(Real.cosh (Real.pi*t):ℂ)
  let V := fun t : ℝ => positiveWeight f t/(Real.cosh (Real.pi*t):ℂ)
  let H := fun k (i : Idx) => c k*(nativeWeight q.val (Φ k) i*disc q m n i)
  let G := fun k (t : ℝ) => c k*(W k t*cont q m n t)
  obtain ⟨r,C,cp,p⟩ := regular_mode_price (inv_pos.mpr yp)
  let A := fun k : ℤ => ‖c k‖*(C*(weight k)^r)
  have apos (k : ℤ) : 0≤A k := by
    have w := OriginalSwitchedSchwartzPrices20261113.w_one k
    exact mul_nonneg (norm_nonneg _) (mul_nonneg cp (pow_nonneg (zero_le_one.trans w) _))
  have sa : Summable A := by
    obtain ⟨_,_,ss⟩ := mode_budget r
    simpa only [A,c,weight,mul_assoc,mul_comm,mul_left_comm] using (ss s L).1.mul_left C
  have bound (k : ℤ) (t : ℝ) : ‖W k t‖≤(C*(weight k)^r)*linePrice t := by
    apply price_div
    have cp' : 0<Real.cosh (Real.pi*t) := Real.cosh_pos _
    rw [show ‖W k t‖=‖positiveWeight (Φ k) t‖/Real.cosh (Real.pi*t) by
      simp only [W,norm_div,Complex.norm_real,Real.norm_of_nonneg cp'.le]]
    rw [show (1+|t|)^3*Real.cosh (Real.pi*t)*(‖positiveWeight (Φ k) t‖/Real.cosh (Real.pi*t))=
      (1+|t|)^3*‖positiveWeight (Φ k) t‖ by field_simp [cp'.ne']]
    exact p k t
  have T := tested_transforms s L Y yp
  have point (i : Idx) : HasSum (fun k => H k i) (nativeWeight q.val f i*disc q m n i) := by
    by_cases e : exceptional q.val i
    · obtain ⟨a,b,_⟩ := complementary_range q.val e
      have X := ((T.2.1 _ a.le b).div_const (Real.cos (Real.pi*complementaryHeight q.val i):ℂ)).mul_right (disc q m n i)
      simpa only [H,Φ,f,c,nativeWeight,if_pos e,div_eq_mul_inv,mul_assoc] using X
    · have X := ((T.1 (height q.val i)).div_const (Real.cosh (Real.pi*height q.val i):ℂ)).mul_right (disc q m n i)
      simpa only [H,Φ,f,c,nativeWeight,if_neg e,div_eq_mul_inv,mul_assoc] using X
  have line (t : ℝ) : HasSum (fun k => G k t) (V t*cont q m n t) := by
    have X := ((T.1 t).div_const (Real.cosh (Real.pi*t):ℂ)).mul_right (cont q m n t)
    simpa only [G,W,V,Φ,f,c,div_eq_mul_inv,mul_assoc] using X
  obtain ⟨dprice,cprice⟩ := cubic_prices q m n
  let E := {i : Idx | exceptional q.val i}
  have finite : E.Finite := (actualCuspIndexSublevel_finite q.val (NeZero.pos q.val) (1/4)).subset (fun _ h => h.le)
  let exc := fun p : Idx×ℤ => if p.1∈E then ‖H p.2 p.1‖ else 0
  have se : Summable exc := by
    apply (summable_prod_of_nonneg (fun p => by dsimp only [exc];split_ifs <;> positivity)).mpr
    constructor
    · intro i
      by_cases e : i∈E
      · simpa only [exc,if_pos e] using summable_norm_iff.mpr (point i).summable
      · simp [exc,e]
    · apply summable_of_hasFiniteSupport
      apply finite.subset
      intro i nz
      by_contra hi
      exact nz (by simp [exc,hi])
  have sr := rectangle sa dprice apos (fun i => mul_nonneg (slotPrice_nn _ _) (norm_nonneg _))
  have hs : Summable (Function.uncurry H) := by
    apply Summable.of_norm
    apply (sr.add se.prod_symm).of_nonneg_of_le (fun _ => norm_nonneg _)
    rintro ⟨k,i⟩
    by_cases hi : i∈E
    · change ‖H k i‖≤A k*(slotPrice q.val i*‖disc q m n i‖)+exc (i,k)
      rw [show exc (i,k)=‖H k i‖ from if_pos hi]
      exact le_add_of_nonneg_left (mul_nonneg (apos _) (mul_nonneg (slotPrice_nn _ _) (norm_nonneg _)))
    · change ‖H k i‖≤A k*(slotPrice q.val i*‖disc q m n i‖)+exc (i,k)
      simp only [H,exc,if_neg hi,add_zero,slotPrice,nativeWeight,if_neg (show ¬exceptional q.val i from hi),norm_mul]
      change ‖c k‖*(‖W k _‖*_)≤A k*(_*_)
      calc
        _ ≤ ‖c k‖*((C*(weight k)^r*linePrice (height q.val i))*‖disc q m n i‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (bound k _) (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by dsimp only [A]; ring
  have DS := hs.prod.hasSum
  rw [hs.tsum_comm.symm] at DS
  simp_rw [(point _).tsum_eq] at DS
  have gp (k : ℤ) (t : ℝ) : ‖G k t‖≤A k*(linePrice t*‖cont q m n t‖) := by
    simp only [G,norm_mul]
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (bound k t) (norm_nonneg _)) (norm_nonneg _)).trans_eq
    dsimp only [A]
    ring
  have gi (k : ℤ) : Integrable (G k) := by
    have e : (fun t => positiveWeight (Φ k) t)=(weightSchwartz (mode k) (inv_pos.mpr yp):ℝ→ℂ) :=
      funext (fun t => (regular_transform _ _ t).2)
    have mw : AEStronglyMeasurable (W k) volume := by
      unfold W
      simp_rw [show ∀ t,positiveWeight (Φ k) t=weightSchwartz (mode k) (inv_pos.mpr yp) t from fun t => congrFun e t]
      exact (weightSchwartz _ _).continuous.aestronglyMeasurable.div
        (by fun_prop : Continuous (fun t : ℝ => (Real.cosh (Real.pi*t):ℂ))).aestronglyMeasurable
    exact (cprice.const_mul (A k)).mono'
      (aestronglyMeasurable_const.mul (mw.mul (covariance_meas q m n))) (ae_of_all _ (gp k))
  have sg : Summable (fun k => ∫ t,‖G k t‖) := by
    apply (sa.mul_right (∫ t,linePrice t*‖cont q m n t‖)).of_nonneg_of_le
      (fun k => integral_nonneg fun _ => norm_nonneg _)
    intro k
    simpa only [integral_const_mul] using integral_mono (gi k).norm (cprice.const_mul (A k)) (gp k)
  have CS := hasSum_integral_of_summable_integral_norm gi sg
  simp_rw [(line _).tsum_eq] at CS
  apply (DS.add CS).congr_fun
  intro k
  simp only [H,G,W,Φ,c,mass,total,tsum_mul_left,integral_const_mul,mul_add]

end
end ImbalancedChen.Part3.OriginalSwitchedMaassExchange20261113
