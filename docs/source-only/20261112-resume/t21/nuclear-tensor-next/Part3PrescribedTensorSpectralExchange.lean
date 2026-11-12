import ImbalancedChen.Part3PrescribedTensorPacketPrice
import Batteries.Tactic.OpenPrivate

/-! Absolute exchange on the whole native discrete basis and, separately,
at every incoming cusp of the original full-line continuous resolution. -/
namespace ImbalancedChen.Part3.PrescribedTensorSpectralExchange20261112
noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators MatrixGroups UpperHalfPlane
open PrescribedLogTensorWindows20261112 PrescribedLogTensorCoefficients20261112
open PrescribedLogTensorExpansion20261112 PrescribedTensorPacketPrice20261112
open ActualMarkedContinuousCoordinates20261112 ActualContinuousResolution20261112
open AngularFourierUnitary20261026b OriginalMarkedWeakAdjoint20261112
open OriginalContinuousPoincarePackets20261110 OriginalCuspidalPoincareTrace20261110
open OriginalNativeCuspFunctionals20261102 ActualCuspBasisWhittakerCoefficients20261102
open ActualFullCuspEigenbasis20261026b ActualFullCuspResolvent20261026b
open ActualCuspDenominatorClasses20261110 Gamma0QuotientCellPushforward20261025a
open Gamma0ActualConstantMode20261025a OriginalSimultaneousPrefixCompletion20261102
open OriginalCompletedReciprocalSource20261102 OriginalCommonPoissonLanes20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZFourierAssembly20261102
open OriginalSignedTraceInput20261102 OriginalContinuousClassRemoval20261110
open P3NativePeriod64SamplingSourceOnly (D4)
open private common_nonzero row_nonzero from ImbalancedChen.Part3OriginalCuspidalPoincareTrace
open private angular_L1_iff from ImbalancedChen.Part3ActualMarkedContinuousCoordinates

private theorem finite_cs {ι : Type*} (S : Finset ι) (f g : ι → ℝ) {U V : ℝ}
    (hU : 0≤U) (hV : 0≤V) (hf : ∑ b∈S,f b^2≤U^2) (hg : ∑ b∈S,g b^2≤V^2) :
    ∑ b∈S,f b*g b ≤ U*V := by
  have h := (Finset.sum_mul_sq_le_sq_mul_sq S f g).trans
    (mul_le_mul hf hg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _))
  have ht : (∑ b∈S,f b*g b)^2≤(U*V)^2 := by simpa only [mul_pow] using h
  exact le_of_sq_le_sq ht (mul_nonneg hU hV)

private theorem angular_cs (f g : AngularL2) :
    (∫ t,‖f t‖*‖g t‖ ∂angularMeasure) ≤ ‖f‖*‖g‖ := by
  have E (h : AngularL2) : (∫ t,‖h t‖^2 ∂angularMeasure)=‖h‖^2 := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℂ),L2.inner_def,
      ← integral_re (L2.integrable_inner h h)]
    exact integral_congr_ae (ae_of_all _ (fun t => InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℂ) (h t)))
  have H := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all angularMeasure (fun t => norm_nonneg (f t)))
    (ae_of_all angularMeasure (fun t => norm_nonneg (g t)))
    (by simpa only [ENNReal.ofReal_ofNat] using f.memLp.norm)
    (by simpa only [ENNReal.ofReal_ofNat] using g.memLp.norm)
  simpa only [Real.rpow_ofNat,← Real.sqrt_eq_rpow,E,Real.sqrt_sq (norm_nonneg _)] using H

private theorem angular_energy (N : ℕ) [NeZero N] (v : QuotientL2 N) :
    ∑ a : Parameters N,‖analysis N a v‖^2≤2*‖v‖^2 := by
  have P := congrArg Complex.re (continuous_projection_gram N v v)
  simp only [inner_self_eq_norm_sq_to_K,← Complex.ofReal_pow,← Complex.ofReal_sum,
    ← Complex.ofReal_one,← Complex.ofReal_ofNat,← Complex.ofReal_div,← Complex.ofReal_mul,
    Complex.ofReal_re] at P
  have h := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr ((centeredSpace N).norm_starProjection_apply_le v)
  linarith

private theorem angular_total (N : ℕ) [NeZero N] (v w : QuotientL2 N) :
    (1/2:ℝ)*(∑ a : Parameters N,∫ t,‖analysis N a v t‖*‖analysis N a w t‖ ∂angularMeasure)
      ≤ ‖v‖*‖w‖ := by
  let A := fun a => ‖analysis N a v‖
  let B := fun a => ‖analysis N a w‖
  have h1 := Finset.sum_le_sum (s:=Finset.univ)
    (fun (a : Parameters N) _ => angular_cs (analysis N a v) (analysis N a w))
  have h := (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Parameters N)) A B).trans
    (mul_le_mul (angular_energy N v) (angular_energy N w)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity))
  have H : (∑ a : Parameters N,A a*B a) ≤ 2*(‖v‖*‖w‖) :=
    (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))) (by positivity)).mp
      (by nlinarith only [h])
  dsimp only [A,B] at H
  linarith only [h1,H]

section Marking
variable (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
  (ha : D.block.atom.residue ≠ 0) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ)
local instance nzLevel : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩

def discrete (q : Modes) (i : actualCuspBasisIndex z.val (NeZero.pos z.val)) : ℂ :=
  (star (orderProbe 1 (pattern q.1.1 q.2.1) (basisOrder z.val (NeZero.pos z.val) i))*
    orderProbe 1 (rightPattern q.1.2 q.2.2) (basisOrder z.val (NeZero.pos z.val) i))*
    (star (originalMFunctional J j ell z.val (NeZero.pos z.val) i)*
      originalNFunctional D r k upper negativeM ell z.val (NeZero.pos z.val) i)

def continuousRow (q : Modes) (a : Parameters z.val) (t : ℝ) : ℂ :=
  star (spectrum z.val (mPacket z.val J j ell (pattern q.1.1 q.2.1)) a t)*
    spectrum z.val (nPacket D r k z upper negativeM ell (rightPattern q.1.2 q.2.2)) a t /
      (4*(Real.pi:ℂ))

include ha in
theorem discrete_price (q : Modes) :
    let F := discrete D r k z upper negativeM J j ell q
    Summable (fun i => ‖F i‖) ∧ (∑' i,‖F i‖) ≤
      ‖mVector z.val J j ell q‖*‖nVector D r k z ha upper negativeM ell q‖ := by
  classical
  let ψ := pattern q.1.1 q.2.1
  let φ := rightPattern q.1.2 q.2.2
  let B := actualCuspHilbertBasis z.val (NeZero.pos z.val)
  let v := mVector z.val J j ell q
  let w := nVector D r k z ha upper negativeM ell q
  let F := discrete D r k z upper negativeM J j ell q
  have H := original_cuspidal_trace D r k z ha upper negativeM J j ell ψ φ
    (pattern_test _ _).1 (pattern_test _ _).2.1 (pattern_test _ _).2.2
    (right_test _ _).1 (right_test _ _).2.1 (right_test _ _).2.2
  have hf : Summable (fun i => ‖F i‖) := summable_norm_iff.mpr H.summable
  refine ⟨hf,le_of_tendsto hf.hasSum (Eventually.of_forall (fun S => ?_))⟩
  have hB : Orthonormal ℂ (fun i => (B i : QuotientL2 z.val)) :=
    orthonormal_iff_ite.mpr (fun i j => (orthonormal_iff_ite.mp B.orthonormal) i j)
  let A := fun i => ‖inner ℂ v (B i : QuotientL2 z.val)‖
  let T := fun i => ‖inner ℂ w (B i : QuotientL2 z.val)‖
  have E (i) : ‖F i‖=A i*T i := by
    have m := basis_packet_inner z.val i false _ _ _ (common_nonzero J j) ψ
      (pattern_test _ _).1 (pattern_test _ _).2.1 (pattern_test _ _).2.2
    have n := basis_packet_inner z.val i true _ _ _ (row_nonzero D k z ha negativeM) φ
      (right_test _ _).1 (right_test _ _).2.1 (right_test _ _).2.2
    change ‖_‖=‖inner ℂ v (B i : QuotientL2 z.val)‖*‖inner ℂ w (B i : QuotientL2 z.val)‖
    rw [show inner ℂ v (B i : QuotientL2 z.val)=_ from m,show inner ℂ w (B i : QuotientL2 z.val)=_ from n]
    simp only [F,discrete,norm_mul,norm_star,OriginalNativeCuspFunctionals20261102.originalMFunctional,
      OriginalNativeCuspFunctionals20261102.originalNFunctional,ψ,φ]
    ring
  simp_rw [E]
  apply finite_cs S A T (norm_nonneg _) (norm_nonneg _)
  · simpa only [A,norm_inner_symm (𝕜:=ℂ) (x:=v)] using hB.sum_inner_products_le (s:=S) v
  · simpa only [T,norm_inner_symm (𝕜:=ℂ) (x:=w)] using hB.sum_inner_products_le (s:=S) w

include ha in
theorem discrete_exchange {Y : ℝ} (hY : 0<Y) :
    Summable (fun p : Modes × actualCuspBasisIndex z.val (NeZero.pos z.val) =>
      ‖c ell Y p.1*discrete D r k z upper negativeM J j ell p.1 p.2‖) := by
  let Dq := discrete D r k z upper negativeM J j ell
  have hd := discrete_price D r k z ha upper negativeM J j ell
  have hc := marked_trace_class D r k z ha upper negativeM J j ell hY
  simp only [norm_mul]
  apply (summable_prod_of_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  constructor
  · intro q; exact (hd q).1.mul_left _
  · simp_rw [tsum_mul_left]
    exact hc.of_nonneg_of_le (fun q => mul_nonneg (norm_nonneg _) (tsum_nonneg (fun _ => norm_nonneg _)))
      (fun q => mul_le_mul_of_nonneg_left (hd q).2 (norm_nonneg _))

include ha in
theorem continuous_price (q : Modes) :
    let G := continuousRow D r k z upper negativeM J j ell q
    (∀ a, Integrable (G a)) ∧ (∑ a : Parameters z.val,∫ t,‖G a t‖) ≤
      ‖mVector z.val J j ell q‖*‖nVector D r k z ha upper negativeM ell q‖ := by
  let ψ := pattern q.1.1 q.2.1
  let φ := rightPattern q.1.2 q.2.2
  let v := mVector z.val J j ell q
  let w := nVector D r k z ha upper negativeM ell q
  let G := continuousRow D r k z upper negativeM J j ell q
  let A := fun a => analysis z.val a v
  let B := fun a => analysis z.val a w
  have W := (original_marked_weak D r k z ha upper negativeM J j ell ψ φ
    (pattern_test _ _).1 (pattern_test _ _).2.1 (pattern_test _ _).2.2
    (right_test _ _).1 (right_test _ _).2.1 (right_test _ _).2.2).1
  have ae (a : Parameters z.val) : (fun t => A a t*star (B a t)/(4*(Real.pi:ℂ))) =ᵐ[angularMeasure] G a := by
    filter_upwards [(W a).1,(W a).2] with t ht hu
    simp only [A,B,v,w,ht,hu,star_star,G,continuousRow,ψ,φ]
  refine ⟨fun a => (angular_L1_iff _).mp (((A a).memLp.integrable_mul (B a).memLp.star).div_const
    (4*(Real.pi:ℂ)) |>.congr (ae a)),?_⟩
  have mass (a : Parameters z.val) : (∫ t,‖G a t‖) =
      (1/2:ℝ)*∫ t,‖A a t‖*‖B a t‖ ∂angularMeasure := by
    have hsc : ENNReal.ofReal ((2*Real.pi)⁻¹)≠0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
    have h := ae a
    rw [angularMeasure,Measure.ae_smul_measure_eq hsc volume] at h
    calc
      _ = ∫ t,(4*Real.pi)⁻¹*(‖A a t‖*‖B a t‖) := by
        apply integral_congr_ae; filter_upwards [h] with t ht
        rw [← ht,norm_div,norm_mul,norm_star,show (4*(Real.pi:ℂ))= ((4*Real.pi:ℝ):ℂ) by push_cast; rfl,
          Complex.norm_real,Real.norm_of_nonneg (by positivity)]
        ring
      _ = _ := by
        rw [integral_const_mul,angularMeasure,integral_smul_measure,ENNReal.toReal_ofReal (by positivity),smul_eq_mul]
        field_simp [Real.pi_ne_zero] <;> ring
  change (∑ a : Parameters z.val,∫ t,‖G a t‖)≤_
  simp_rw [mass]
  rw [← Finset.mul_sum]
  exact angular_total z.val v w

include ha in
theorem continuous_exchange {Y : ℝ} (hY : 0<Y) :
    let G := continuousRow D r k z upper negativeM J j ell
    Summable (fun q : Modes => ∑ a : Parameters z.val,∫ t,‖c ell Y q*G q a t‖) ∧
    ∀ a : Parameters z.val,
      (∫ t,∑' q : Modes,c ell Y q*G q a t) = ∑' q : Modes,∫ t,c ell Y q*G q a t := by
  let G := continuousRow D r k z upper negativeM J j ell
  have H := continuous_price D r k z ha upper negativeM J j ell
  have A : Summable (fun q : Modes => ∑ a : Parameters z.val,∫ t,‖c ell Y q*G q a t‖) := by
    simp_rw [norm_mul,integral_const_mul,← Finset.mul_sum]
    apply (marked_trace_class D r k z ha upper negativeM J j ell hY).of_nonneg_of_le
      (fun q => mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))))
    exact fun q => mul_le_mul_of_nonneg_left (H q).2 (norm_nonneg _)
  refine ⟨A,fun a => (integral_tsum_of_summable_integral_norm
    (fun q => ((H q).1 a).const_mul (c ell Y q)) ?_).symm⟩
  exact A.of_nonneg_of_le (fun q => integral_nonneg (fun _ => norm_nonneg _))
    (fun q => Finset.single_le_sum (fun b _ => integral_nonneg (fun _ => norm_nonneg _)) (Finset.mem_univ a))

end Marking
end
end ImbalancedChen.Part3.PrescribedTensorSpectralExchange20261112
