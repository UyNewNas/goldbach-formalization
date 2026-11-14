import ImbalancedChen.Part3OriginalRegularCompactEnergy
import ImbalancedChen.Part3OriginalRegularPacketTest
import ImbalancedChen.Part3OriginalSameInfinityCompactTrace

/-! Positive discrete and all incoming continuous squares of an
arbitrary compact physical seed in either manuscript observation. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularCompactCoordinates20261113
open Real Set MeasureTheory Finset Complex
open scoped MatrixGroups BigOperators
open ActualInfinityCuspAnnihilator20261026b (HeightSeed)
open ActualCuspDenominatorClasses20261110 ActualContinuousPoincarePairing20261110
open ActualContinuousClassFourier20261110 OriginalContinuousPoincarePackets20261110
open ActualFullCuspEigenbasis20261026b ActualCuspBasisWhittakerCoefficients20261102
open OriginalContinuousClassRemoval20261110 OriginalContinuousCuspGram20261110
open ActualMarkedContinuousCoordinates20261112 ActualContinuousResolution20261112
open ActualMarkedHorocycleSupport20261112 OriginalCuspidalPoincareTrace20261110
open Gamma0QuotientCellPushforward20261025a Gamma0ActualConstantMode20261025a
open ActualCriticalCuspEvaluation20261110
open OriginalRegularCompactGram20261113 (mark mark_of_pos vector)
open private packetVector from ImbalancedChen.Part3OriginalInfinitySwitchedGeometry
open private positiveIndex singleton_vector from ImbalancedChen.Part3OriginalSameInfinityCompactTrace
open private packet_projection from ImbalancedChen.Part3OriginalResidualPoincarePackets
open private integrated_native from ImbalancedChen.Part3OriginalMarkedWeakAdjoint
open private native_self_re from ImbalancedChen.Part3OriginalContinuousCuspGram

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

def spatial (q : ℕ+) (one : Bool) (S : Finset ℕ) (a : ℕ→ℂ) (f : ℕ→ℤ)
    (nf : ∀ n∈S,f n≠0) (ψ : HeightSeed) : QuotientL2 q.val :=
  (packet_L2 q.val one S a f nf ψ.toFun ψ.continuous ψ.compact ψ.positive).toLp
    (packet q.val one S a f ψ.toFun)

def native (q : ℕ+) (one : Bool) (S : Finset ℕ) (a : ℕ→ℂ) (f : ℕ→ℤ) (t : ℝ) :=
  nativeMass q.val (fun b => markedRow S a f (fun n => nativeR b one n t))

theorem native_nonnegative (q : ℕ+) (one : Bool) (S : Finset ℕ) (a : ℕ→ℂ) (f : ℕ→ℤ) (t : ℝ) :
    0≤native q one S a f t := sum_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (by positivity))

theorem spectral_squares (q : ℕ+) (one : Bool) (S : Finset ℕ) (a : ℕ→ℂ) (f : ℕ→ℤ)
    (nf : ∀ n∈S,f n≠0) (ψ : HeightSeed) :
    let B := ‖spatial q one S a f nf ψ‖^2
    let D := fun i => markedRow S a f (basisR q.val q.property i (originalFrame one))
    let C := fun t : ℝ => ‖orderProbe 1 ψ.toFun ((t:ℂ)*I)‖^2*native q one S a f t
    (∀ J : Finset (actualCuspBasisIndex q.val q.property),
      (∑ i∈J,‖orderProbe 1 ψ.toFun (basisOrder q.val q.property i)*D i‖^2)≤B) ∧
      Integrable C ∧ (∫ t,C t)≤B := by
  let X := packet q.val one S a f ψ.toFun
  let hx := packet_L2 q.val one S a f nf ψ.toFun ψ.continuous ψ.compact ψ.positive
  let V := hx.toLp X
  let B := actualCuspHilbertBasis q.val q.property
  have o : Orthonormal ℂ (fun i => (B i : QuotientL2 q.val)) :=
    orthonormal_iff_ite.mpr (fun i j => (orthonormal_iff_ite.mp B.orthonormal) i j)
  constructor
  · intro J
    apply le_trans _ (o.sum_inner_products_le (s:=J) V)
    apply Finset.sum_le_sum
    intro i _
    have e := basis_packet_inner q.val i one S a f nf ψ.toFun ψ.continuous ψ.compact ψ.positive
    exact (congrArg (fun u : ℝ => u^2) ((congrArg norm e.symm).trans
      (norm_inner_symm (𝕜:=ℂ) V (B i : QuotientL2 q.val)))).le
  · let F := fun t : ℝ => ‖orderProbe 1 ψ.toFun ((t:ℂ)*I)‖^2*native q one S a f t
    let G := fun t => nativeProduct q.val (fun b => spectrum q.val X b t) (fun b => spectrum q.val X b t)
    have cx := marked_support q.val one S a f nf ψ.toFun ψ.continuous ψ.compact ψ.positive
    have z := packet_projection q.val one S a f nf ψ.toFun ψ.continuous ψ.compact ψ.positive
    obtain ⟨hi,hg⟩ := integrated_native q.val hx hx cx cx z z
    have eq (t : ℝ) : (G t).re=F t := by
      have arg : criticalPoint t-1/2=(t:ℂ)*I := by unfold criticalPoint;ring
      have coord (b : Parameters q.val) : spectrum q.val X b t=orderProbe 1 ψ.toFun ((t:ℂ)*I)*
          markedRow S a f (fun n => nativeR b one n t) := by
        simpa only [X,show radialProbe 1 ψ.toFun t=orderProbe 1 ψ.toFun (criticalPoint t-1/2) from rfl,arg]
          using (packet_spectrum q.val one S a f nf ψ.toFun ψ.continuous ψ.compact ψ.positive b t).2
      change (nativeProduct _ _ _).re=_
      rw [native_self_re]
      simp only [F,native,nativeMass,coord,norm_mul,mul_pow,Finset.mul_sum,mul_div_assoc]
    have hG : Integrable G := hi
    refine ⟨hG.re.congr (ae_of_all _ eq),?_⟩
    rw [nativeSynthesis_analysis_eq_projection] at hg
    calc
      (∫ t,F t)=(∫ t,G t).re := by
        rw [←integral_re hG]
        exact integral_congr_ae (ae_of_all _ (fun t => (eq t).symm))
      _=(inner ℂ V ((centeredSpace q.val).starProjection V)).re := congrArg Complex.re hg.symm
      _≤‖V‖^2 := (Complex.re_le_norm _).trans ((norm_inner_le_norm V _).trans (by
        rw [sq];exact mul_le_mul_of_nonneg_left ((centeredSpace q.val).norm_starProjection_apply_le V) (norm_nonneg _)))

def block (M : ℕ) := range (M+1)
def row (M : ℕ) (a : ℕ→ℂ) (i : ℕ) := a (M+i)
def index (M : ℕ) (i : ℕ) : ℤ := (M+i:ℕ)
theorem nonzero {M : ℕ} (hM : 0<M) : ∀ i∈block M,index M i≠0 := by
  intro i _;exact_mod_cast (show M+i≠0 by omega)

theorem positive_vector (q : ℕ+) {M : ℕ} (hM : 0<M) (a : ℕ→ℂ) (ψ : HeightSeed) :
    spatial q false (block M) (row M a) (index M) (nonzero hM) ψ=vector q M a ψ := by
  classical
  let S := block M
  let w := row M a
  let f := index M
  let hx := packet_L2 q.val false S w f (nonzero hM) ψ.toFun ψ.continuous ψ.compact ψ.positive
  let X := packet q.val false S w f ψ.toFun
  let V := fun i => star (a (M+i)) • packetVector q (mark (M+i)) ψ
  have h (i : ℕ) : ⇑(V i)=ᵐ[carrierPushforward q.val] fun u =>
      star (a (M+i))*originalPoincare q.val false (f i) (scaledSeed (f i) ψ.toFun) u := by
    let m := mark (M+i)
    let one := packet q.val false {m.val} (fun _ => 1) (fun n => (n:ℤ)) ψ.toFun
    let h1 := packet_L2 q.val false {m.val} (fun _ => 1) (fun n => (n:ℤ)) (positiveIndex m)
      ψ.toFun ψ.continuous ψ.compact ψ.positive
    have E : (h1.toLp one)=packetVector q m ψ := singleton_vector q m ψ
    have v := h1.coeFn_toLp
    rw [E] at v
    filter_upwards [Lp.coeFn_smul (star (a (M+i))) (packetVector q m ψ),v] with x hx hv
    change _=star (a (M+i))*originalPoincare q.val false (f i) (scaledSeed (f i) ψ.toFun) x
    rw [hx,hv]
    simp [one,packet,m,mark_of_pos (show 0<M+i by omega),f,index,smul_eq_mul]
  have sum := ae_all_iff.mpr (fun i : ↥S => h i.val)
  apply Lp.ext
  filter_upwards [hx.coeFn_toLp,Lp.coeFn_fun_finsetSum S V,sum] with u hu hv ht
  change (hx.toLp X) u=(∑ i∈S,V i) u
  rw [hu,hv]
  exact Finset.sum_congr rfl (fun i hi => (ht ⟨i,hi⟩).symm)

end ImbalancedChen.Part3.OriginalRegularCompactCoordinates20261113
end

