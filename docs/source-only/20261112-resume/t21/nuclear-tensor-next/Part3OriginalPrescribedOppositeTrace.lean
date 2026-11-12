import ImbalancedChen.Part3PrescribedTensorBesselGeometry
import ImbalancedChen.Part3PrescribedTensorSpectralExchange
import Mathlib.Data.PNat.Interval
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Batteries.Tactic.OpenPrivate

/-! Opposite-sign Kuznetsov at one original marked row for exactly its
period-64 manuscript test. All three sides use the same log-tile series. -/
namespace ImbalancedChen.Part3.OriginalPrescribedOppositeTrace20261112
noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators
open PrescribedLogTensorWindows20261112 PrescribedLogTensorCoefficients20261112
open PrescribedLogTensorExpansion20261112 PrescribedTensorOrbitExchange20261112
open PrescribedTensorBesselGeometry20261112 PrescribedTensorSpectralExchange20261112
open ActualOppositeBesselTransform20261112 OriginalOppositeMarkedKuznetsov20261112
open ActualMarkedBruhatTest20261112 OriginalMarkedArithmeticTrace20261112
open OriginalProjectedContinuousCovariance20261112 ActualCuspDenominatorClasses20261110
open ActualContinuousPoincarePairing20261110 ActualOrdinaryContinuousModes20261110
open ActualContinuousClassFourier20261110 OriginalContinuousPoincarePackets20261110
open OriginalContinuousCuspGram20261110 OriginalCuspidalPoincareTrace20261110
open OriginalNativeCuspFunctionals20261102 ActualCuspBasisWhittakerCoefficients20261102
open ActualFullCuspEigenbasis20261026b OriginalSimultaneousPrefixCompletion20261102
open OriginalSignedTraceInput20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalTwoZFourierAssembly20261102 OriginalContinuousClassRemoval20261110
open P3NativePeriod64SamplingSourceOnly (D4) P3Period64NativeReconstructionSourceOnly (spectralTest)
open private common_nonzero row_nonzero from ImbalancedChen.Part3OriginalCuspidalPoincareTrace
open private probe_basis from ImbalancedChen.Part3OriginalOppositeMarkedKuznetsov
open private regular_density from ImbalancedChen.Part3OriginalMarkedArithmeticTrace

variable (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
  (ha : D.block.atom.residue≠0) (upper negativeM : Bool) (J j : ℕ) (ell : D4→ℤ)
local instance nzLevel : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩

private def geom (Φ : ℝ→ℂ) :=
  ∑ n∈nCarrier D k z.val,∑ p∈commonMBlock J j,(commonPoissonCompleted J j (ell 1)).weight p*
    traceBeta D r k upper negativeM ell z.val n*∑' d : ℕ+,modulusTerm Φ z.val p (traceIndex D k negativeM z.val n) d
private def disc (Φ : ℝ→ℂ) (i : actualCuspBasisIndex z.val (NeZero.pos z.val)) :=
  (8*kTransform (basisOrder z.val (NeZero.pos z.val) i) Φ)*
    (star (originalMFunctional J j ell z.val (NeZero.pos z.val) i)*
      originalNFunctional D r k upper negativeM ell z.val (NeZero.pos z.val) i)
private def cont (Φ : ℝ→ℂ) (t : ℝ) := continuousDensity Φ z.val t
  (fun a => M J j ell (fun n => nativeR a false n t))
  (fun a => source D r k z upper negativeM ell (fun n => nativeR a true n t))
local notation "L" => geom D r k z upper negativeM J j ell
local notation "F" => disc D r k z upper negativeM J j ell
local notation "G" => cont D r k z upper negativeM J j ell

include ha in
private theorem geometry_sum {Y : ℝ} (hY : 0<Y) :
    (∀ n∈nCarrier D k z.val,∀ p∈commonMBlock J j,
      Summable (modulusTerm (spectralTest ell Y) z.val p (traceIndex D k negativeM z.val n))) ∧
    HasSum (fun q : Modes => c ell Y q*L (orbit q)) (L (spectralTest ell Y)) := by
  classical
  obtain ⟨D₀,h₀⟩ := common_modulus_cutoff D k z ha negativeM J j ell hY
  let U := Finset.Icc (1:ℕ+) (⟨D₀+1,Nat.succ_pos _⟩ : ℕ+)
  let Φ := spectralTest ell Y
  let ind := traceIndex D k negativeM z.val
  have outside (d : ℕ+) (hd : d∉U) : D₀<(d:ℕ) := by
    by_contra! h
    exact hd (Finset.mem_Icc.mpr ⟨show (1:ℕ)≤(d:ℕ) from d.property,
      show (d:ℕ)≤D₀+1 from h.trans (Nat.le_succ _)⟩)
  have point (n : ℕ) (hn : n∈nCarrier D k z.val) (p : ℕ) (hp : p∈commonMBlock J j) :
      HasSum (fun q : Modes => c ell Y q*∑' d : ℕ+,modulusTerm (orbit q) z.val p (ind n) d)
        (∑' d : ℕ+,modulusTerm Φ z.val p (ind n) d) := by
    have hpp : 0<p := Nat.pos_of_ne_zero (fun e => common_nonzero J j p hp (by simp [e]))
    have H (d : ℕ+) := modulus_reconstruction ell hY z.val p (levelCarrier_licensed D k z.property).1
      hpp (ind n) (row_nonzero D k z ha negativeM n hn) d
    have eq (q : Modes) : c ell Y q*(∑' d : ℕ+,modulusTerm (orbit q) z.val p (ind n) d) =
        ∑ d∈U,c ell Y q*modulusTerm (orbit q) z.val p (ind n) d := by
      rw [← tsum_mul_left]; exact tsum_eq_sum (fun d hd => (h₀ n hn p hp d (outside d hd)).1 q)
    simp_rw [eq]
    rw [tsum_eq_sum (s:=U) (fun d hd => (h₀ n hn p hp d (outside d hd)).2)]
    exact hasSum_sum (fun d (_ : d∈U) => H d)
  refine ⟨fun n hn p hp => summable_of_ne_finset_zero (s:=U)
    (fun d hd => (h₀ n hn p hp d (outside d hd)).2),?_⟩
  have H := hasSum_sum (fun n (hn : n∈nCarrier D k z.val) =>
    hasSum_sum (fun p (hp : p∈commonMBlock J j) => (point n hn p hp).mul_left
      ((commonPoissonCompleted J j (ell 1)).weight p*traceBeta D r k upper negativeM ell z.val n)))
  apply H.congr_fun
  intro q; simp only [geom,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro p _; ring

private theorem disc_atom (q : Modes) (i : actualCuspBasisIndex z.val (NeZero.pos z.val)) :
    discrete D r k z upper negativeM J j ell q i=F (orbit q) i := by
  have H := (induced_transform (basisOrder z.val (NeZero.pos z.val) i) _ _
    (pattern_test q.1.1 q.2.1).1 (pattern_test _ _).2.1 (pattern_test _ _).2.2
    (right_test q.1.2 q.2.2).1 (right_test _ _).2.1 (right_test _ _).2.2).2
  rw [probe_basis] at H
  exact congrArg (fun x => x*_) H.symm

include ha in
private theorem discrete_sum {Y : ℝ} (hY : 0<Y) :
    Summable (F (spectralTest ell Y)) ∧ HasSum (fun q : Modes => c ell Y q*∑' i,F (orbit q) i)
      (∑' i,F (spectralTest ell Y) i) := by
  let A (q : Modes) (i : actualCuspBasisIndex z.val (NeZero.pos z.val)) := c ell Y q*F (orbit q) i
  have H : Summable (Function.uncurry A) := by
    apply summable_norm_iff.mp
    simpa only [Function.uncurry,A,← disc_atom] using discrete_exchange D r k z ha upper negativeM J j ell hY
  have point (i : actualCuspBasisIndex z.val (NeZero.pos z.val)) : HasSum (fun q => A q i) (F (spectralTest ell Y) i) := by
    have h := ((transform_reconstruction ell hY (basisOrder z.val (NeZero.pos z.val) i)).mul_left 8).mul_right
      (star (originalMFunctional J j ell z.val (NeZero.pos z.val) i)*
        originalNFunctional D r k upper negativeM ell z.val (NeZero.pos z.val) i)
    apply h.congr_fun
    intro q; dsimp [A,disc]; ring
  refine ⟨H.prod_symm.prod.congr (fun i => (point i).tsum_eq),?_⟩
  have total := H.prod.hasSum
  have e (q : Modes) : (∑' i,A q i)=c ell Y q*∑' i,F (orbit q) i := tsum_mul_left
  have E : (∑' q,∑' i,A q i) = ∑' i,F (spectralTest ell Y) i :=
    H.tsum_comm.trans (tsum_congr (fun i => (point i).tsum_eq))
  rw [E] at total
  exact total.congr_fun (fun q => (e q).symm)

include ha in
private theorem cont_atom (q : Modes) (t : ℝ) :
    (∑ a : Parameters z.val,continuousRow D r k z upper negativeM J j ell q a t)=G (orbit q) t := by
  let ψ := pattern q.1.1 q.2.1
  let φ := rightPattern q.1.2 q.2.2
  have H := (original_projected_trace D r k z ha upper negativeM J j ell ψ φ
    (pattern_test _ _).1 (pattern_test _ _).2.1 (pattern_test _ _).2.2
    (right_test _ _).1 (right_test _ _).2.1 (right_test _ _).2.2).2.2.2.2 t
  change nativeProduct z.val _ _=_
  rw [H,original_projected_product D r k z upper negativeM J j ell t,regular_density,cont,
    continuousDensity,show oppositeWeight (orbit q) t=probeWeight ψ φ t from
      induced_weight ψ φ (pattern_test _ _).1 (pattern_test _ _).2.1 (pattern_test _ _).2.2
        (right_test _ _).1 (right_test _ _).2.1 (right_test _ _).2.2 t]
  rfl

include ha in
private theorem continuous_sum {Y : ℝ} (hY : 0<Y) :
    Integrable (G (spectralTest ell Y)) ∧ HasSum (fun q : Modes => c ell Y q*∫ t,G (orbit q) t)
      (∫ t,G (spectralTest ell Y) t) := by
  let R := continuousRow D r k z upper negativeM J j ell
  let A (q : Modes) (t : ℝ) := c ell Y q*G (orbit q) t
  have hP := continuous_price D r k z ha upper negativeM J j ell
  have RX (q : Modes) (t : ℝ) : A q t=∑ a : Parameters z.val,c ell Y q*R q a t := by
    rw [A,← cont_atom D r k z ha upper negativeM J j ell,Finset.mul_sum]
  have IR (q : Modes) (a : Parameters z.val) := ((hP q).1 a).const_mul (c ell Y q)
  have I (q : Modes) : Integrable (A q) := by
    simp_rw [funext (RX q)]
    exact integrable_finsetSum _ (fun a _ => IR q a)
  have T := (continuous_exchange D r k z ha upper negativeM J j ell hY).1
  have S : Summable (fun q : Modes => ∫ t,‖A q t‖) := by
    apply T.of_nonneg_of_le (fun q => integral_nonneg (fun _ => norm_nonneg _))
    intro q
    rw [← integral_finsetSum Finset.univ (fun a _ => (IR q a).norm)]
    exact integral_mono (I q).norm (integrable_finsetSum _ (fun a _ => (IR q a).norm))
      (fun t => by rw [RX]; exact norm_sum_le _ _)
  have point (t : ℝ) : HasSum (fun q => A q t) (G (spectralTest ell Y) t) := by
    let Z := ∑ a : Parameters z.val,star (M J j ell (fun n => nativeR a false n t))*
      source D r k z upper negativeM ell (fun n => nativeR a true n t)
    let C := (8*(Real.cosh (Real.pi*t):ℂ))*Z/(4*(Real.pi:ℂ)*(Real.cosh (Real.pi*t):ℂ))
    have H := (transform_reconstruction ell hY ((t:ℂ)*Complex.I)).mul_left C
    convert H using 1
    · funext q; dsimp [A,cont,continuousDensity,oppositeWeight,C,Z]; ring
    · dsimp [cont,continuousDensity,oppositeWeight,C,Z]; ring
  have E : (fun t => ∑' q : Modes,A q t)=G (spectralTest ell Y) := funext (fun t => (point t).tsum_eq)
  have integ : Integrable (fun t => ∑' q : Modes,A q t) := by
    refine ⟨(AEMeasurable.tsum (fun q => (I q).aemeasurable)).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    apply (lintegral_mono (fun t => enorm_tsum_le_tsum_enorm (f:=fun q => A q t))).trans_lt
    rw [lintegral_tsum (fun q => (I q).aemeasurable.enorm)]
    have eq (q : Modes) : (∫⁻ t,‖A q t‖ₑ) = ‖∫ t,‖A q t‖‖ₑ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (I q).norm,ENNReal.coe_nnreal_eq,coe_nnnorm,
        Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      simp only [coe_nnnorm]
    simp_rw [eq]
    exact (ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 S.abs)).lt_top
  have H := hasSum_integral_of_summable_integral_norm I S
  rw [E] at integ H
  refine ⟨integ,H.congr_fun ?_⟩
  intro q; simp only [A,integral_const_mul]

/-- The manuscript test at every positive physical modulus in this row,
with the original signed functionals, all discrete orders and the
original full-line incoming-cusp normalization. -/
theorem original_prescribed_opposite_trace (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (z : Row D k) (ha : D.block.atom.residue≠0) (upper negativeM : Bool)
    (hs : traceNegative D k negativeM=true) (J j : ℕ) (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    let Φ := spectralTest ell Y
    let ind := traceIndex D k negativeM z.val
    let β := traceBeta D r k upper negativeM ell z.val
    let W := (commonPoissonCompleted J j (ell 1)).weight
    let C := fun t => continuousDensity Φ z.val t
      (fun a => M J j ell (fun n => nativeR a false n t))
      (fun a => source D r k z upper negativeM ell (fun n => nativeR a true n t))
    let B := fun i : actualCuspBasisIndex z.val (NeZero.pos z.val) =>
      (8*kTransform (basisOrder z.val (NeZero.pos z.val) i) Φ)*
        (star (originalMFunctional J j ell z.val (NeZero.pos z.val) i)*
          originalNFunctional D r k upper negativeM ell z.val (NeZero.pos z.val) i)
    Integrable C ∧ Summable B ∧
      (∀ n∈nCarrier D k z.val,∀ p∈commonMBlock J j,Summable (modulusTerm Φ z.val p (ind n))) ∧
      (∑ n∈nCarrier D k z.val,∑ p∈commonMBlock J j,W p*β n*∑' d : ℕ+,modulusTerm Φ z.val p (ind n) d)
        = (∑' i,B i)+(∫ t,C t) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  obtain ⟨hL,HL⟩ := geometry_sum D r k z ha upper negativeM J j ell hY
  obtain ⟨hD,HD⟩ := discrete_sum D r k z ha upper negativeM J j ell hY
  obtain ⟨hC,HC⟩ := continuous_sum D r k z ha upper negativeM J j ell hY
  refine ⟨hC,hD,hL,HL.unique ((HD.add HC).congr_fun ?_)⟩
  intro q
  have H := (original_opposite_trace D r k z ha upper negativeM hs J j ell
    (pattern q.1.1 q.2.1) (rightPattern q.1.2 q.2.2)
    (pattern_test _ _).1 (pattern_test _ _).2.1 (pattern_test _ _).2.2
    (right_test _ _).1 (right_test _ _).2.1 (right_test _ _).2.2).2.2.2
  exact (congrArg (fun x => c ell Y q*x) H).trans (mul_add _ _ _)

end
end ImbalancedChen.Part3.OriginalPrescribedOppositeTrace20261112
