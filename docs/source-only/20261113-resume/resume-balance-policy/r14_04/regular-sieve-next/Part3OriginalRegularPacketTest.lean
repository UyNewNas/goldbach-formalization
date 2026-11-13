import ImbalancedChen.Part3OriginalHighStripPacketBudget
import ImbalancedChen.Part3ActualUnitBandSpectralMass
import ImbalancedChen.Part3OriginalCumulativeContinuousRemoval
import Batteries.Tactic.OpenPrivate

/-! Bound the full signed coefficient packet before restricting height.
The spatial test is exactly the one from the two-cusp packing lemma;
its spectral coordinates are those of the original finite physical
packet, with arbitrary coefficients shared by all spectral coordinates. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularPacketTest20261113
open Set Filter MeasureTheory Complex
open scoped MatrixGroups BigOperators Classical
open ActualCuspDenominatorClasses20261110 ActualContinuousClassFourier20261110
open ActualContinuousPoincarePairing20261110 OriginalContinuousPoincarePackets20261110
open ActualFullCuspEigenbasis20261026b ActualCuspBasisWhittakerCoefficients20261102
open OriginalContinuousCuspGram20261110 OriginalContinuousClassRemoval20261110
open OriginalCuspidalPoincareTrace20261110 ActualMarkedHorocycleSupport20261112
open ActualMarkedContinuousCoordinates20261112 ActualContinuousResolution20261112
open Gamma0QuotientCellPushforward20261025a Gamma0ActualConstantMode20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a NormalizedCuspCompactPoincare20261026b
open NormalizedCuspCompactFourierFubini20261026b NormalizedCuspCompactQuotientLp20261026b
open ActualSignedPoincareEnvelope20261112 OriginalExceptionalHeightWindow20261112
open OriginalHighStripPacketBudget20261113 OriginalUnitStripPacketMass20261113
open ActualCriticalCuspEvaluation20261110
open private packet_projection from ImbalancedChen.Part3OriginalResidualPoincarePackets
open private integrated_native from ImbalancedChen.Part3OriginalMarkedWeakAdjoint
open private native_self_re from ImbalancedChen.Part3OriginalContinuousCuspGram

def mark (neg : Bool) : ℕ ↪ ℤ where
  toFun n := if neg then -(n:ℤ) else (n:ℤ)
  inj' := by cases neg <;> intro a b h <;> simp_all

@[simp] theorem mark_natAbs (neg : Bool) (n : ℕ) : (mark neg n).natAbs=n := by
  cases neg <;> simp [mark]

theorem mark_abs (neg : Bool) (n : ℕ) : |((mark neg n:ℤ):ℝ)|=(n:ℝ) := by
  cases neg <;> simp [mark]

def energy (S : Finset ℕ) (a : ℕ→ℂ) : ℝ := ∑ n∈S,‖a n‖^2
theorem energy_nonneg (S : Finset ℕ) (a : ℕ→ℂ) : 0≤energy S a := Finset.sum_nonneg fun _ _ => sq_nonneg _

def Dyadic (L : ℝ) (S : Finset ℕ) : Prop := ∀ n∈S,L<(n:ℝ) ∧ (n:ℝ)≤2*L

theorem mark_ne {L : ℝ} (hL : 0<L) (S : Finset ℕ) (band : Dyadic L S) (neg : Bool) :
    ∀ n∈S,mark neg n≠0 := by
  intro n hn hz
  have s := hL.trans (band n hn).1
  have e := congrArg Int.natAbs hz
  simp only [mark_natAbs,Int.natAbs_zero] at e
  simpa [e] using s

variable (N : ℕ) [NeZero N]
local notation "Idx" => actualCuspBasisIndex N (NeZero.pos N)

def discreteRow (one neg : Bool) (S : Finset ℕ) (a : ℕ→ℂ) (i : Idx) : ℂ :=
  markedRow S a (mark neg) (basisR N (NeZero.pos N) i (originalFrame one))

def nativeRow (one neg : Bool) (S : Finset ℕ) (a : ℕ→ℂ) (b : Parameters N) (t : ℝ) : ℂ :=
  markedRow S a (mark neg) (fun m => nativeR b one m t)

def lineMass (one neg : Bool) (S : Finset ℕ) (a : ℕ→ℂ) (t : ℝ) : ℝ :=
  nativeMass N (fun b => nativeRow N one neg S a b t)

theorem lineMass_nonneg (one neg : Bool) (S : Finset ℕ) (a : ℕ→ℂ) (t : ℝ) :
    0≤lineMass N one neg S a t := Finset.sum_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (by positivity))

private theorem packet_cost (one neg : Bool) {H L : ℝ} (hH : 0<H) (hL : 0<L)
    (S : Finset ℕ) (a : ℕ→ℂ) (band : Dyadic L S) :
    let ξ := seed H
    let X := packet N one S a (mark neg) ξ.toFun
    let hx := packet_L2 N one S a (mark neg) (mark_ne hL S band neg) ξ.toFun ξ.continuous ξ.compact ξ.positive
    ‖hx.toLp X‖^2 ≤ (8+32*(L*H/(N:ℝ)))*energy S a := by
  classical
  let ξ := seed H
  let X := packet N one S a (mark neg) ξ.toFun
  let nz := mark_ne hL S band neg
  let hx := packet_L2 N one S a (mark neg) nz ξ.toFun ξ.continuous ξ.compact ξ.positive
  let T := S.map (mark neg)
  let b := fun m : ℤ => star (a m.natAbs)
  let v := packetVector N one H T b
  have bn (m : ℤ) (hm : m∈T) : L≤|(m:ℝ)| ∧ |(m:ℝ)|≤2*L := by
    obtain ⟨n,hn,rfl⟩ := Finset.mem_map.mp hm
    rw [mark_abs]
    exact ⟨(band n hn).1.le,(band n hn).2⟩
  have E : coeffMass T b=energy S a := by
    simp only [coeffMass,energy,T,b,Finset.sum_map,mark_natAbs,norm_star]
  let P := fun n => originalPoincare N one (mark neg n) (scaledSeed (mark neg n) ξ.toFun)
  have row (n) (hn : n∈S) : ⇑(b (mark neg n) • modeVector N one H (mark neg n)) =ᵐ[carrierPushforward N]
      (fun u => star (a n)*P n u) := by
    let m := mark neg n
    let η := seed (H*|(m:ℝ)|)
    have Eη : η.toFun=scaledSeed m ξ.toFun := seed_scaling H m (nz n hn)
    have e : P n=complexPoincare N (physicalFrameSeed N (NeZero.pos N) (originalFrame one) m η.toFun) := by
      change originalPoincare N one m (scaledSeed m ξ.toFun)=_
      rw [← Eη]
      exact original_eq_framed N one m η.toFun η.compact η.positive
    have rep := framedVector_ae N (originalFrame one) m η.toFun η.continuous η.compact η.positive
    filter_upwards [Lp.coeFn_smul (b m) (modeVector N one H m),rep] with u hu hr
    change _ = star (a n)*P n u
    rw [e]
    have alg : b m=star (a n) := by simp [b,m]
    exact hu.trans ((congrArg (fun c : ℂ => b m*c) hr).trans (by rw [alg]))
  have vEq : v=∑ n∈S,b (mark neg n) • modeVector N one H (mark neg n) := by
    simp only [v,packetVector,T,Finset.sum_map]
  have rep : ⇑v =ᵐ[carrierPushforward N] X := by
    rw [vEq]
    have all := ae_all_iff.mpr (fun n : ↥S => row n.val n.property)
    filter_upwards [Lp.coeFn_fun_finsetSum S (fun n => b (mark neg n) • modeVector N one H (mark neg n)),all]
      with u hu hall
    exact hu.trans (Finset.sum_congr rfl (fun n hn => hall ⟨n,hn⟩))
  have same : hx.toLp X=v := Lp.ext (hx.coeFn_toLp.trans rep.symm)
  have np : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  have price : overlap N (bottom H L)=2+8*(L*H/(N:ℝ)) := by
    unfold overlap bottom
    field_simp [hH.ne',hL.ne',np.ne'] <;> ring
  have u := packet_norm_budget N one hH hL T b bn
  rw [price,E] at u
  change ‖hx.toLp X‖^2≤_
  rw [same]
  exact u.trans_eq (by ring)

/-- Uniform cost of the actual nonnegative probed squares.  In the continuous
branch the full line and every native incoming cusp occur together. -/
theorem packet_test (one neg : Bool) {L H : ℝ} (hL : 0<L) (hH : 0<H)
    (S : Finset ℕ) (a : ℕ→ℂ) (band : Dyadic L S) :
    let ξ := seed H
    let B := (8+32*(L*H/(N:ℝ)))*energy S a
    let F := fun t : ℝ => ‖orderProbe 1 ξ.toFun ((t:ℂ)*I)‖^2*lineMass N one neg S a t
    (∀ J : Finset Idx,(∑ i∈J,‖orderProbe 1 ξ.toFun (basisOrder N (NeZero.pos N) i)*
      discreteRow N one neg S a i‖^2) ≤ B) ∧ Integrable F ∧ (∫ t,F t)≤B := by
  classical
  let ξ := seed H
  let nz := mark_ne hL S band neg
  let X := packet N one S a (mark neg) ξ.toFun
  let hx := packet_L2 N one S a (mark neg) nz ξ.toFun ξ.continuous ξ.compact ξ.positive
  let v := hx.toLp X
  let B := (8+32*(L*H/(N:ℝ)))*energy S a
  have cost : ‖v‖^2≤B := packet_cost N one neg hH hL S a band
  constructor
  · intro J
    let basis := actualCuspHilbertBasis N (NeZero.pos N)
    have ortho : Orthonormal ℂ (fun i => (basis i : QuotientL2 N)) :=
      orthonormal_iff_ite.mpr (fun i j => (orthonormal_iff_ite.mp basis.orthonormal) i j)
    apply le_trans _ ((ortho.sum_inner_products_le (s:=J) v).trans cost)
    apply Finset.sum_le_sum
    intro i _
    have coord := basis_packet_inner N i one S a (mark neg) nz ξ.toFun ξ.continuous ξ.compact ξ.positive
    exact le_of_eq (congrArg (fun x : ℝ => x^2)
      ((congrArg norm coord.symm).trans (norm_inner_symm (𝕜:=ℂ) v (basis i : QuotientL2 N))))
  · let F := fun t : ℝ => ‖orderProbe 1 ξ.toFun ((t:ℂ)*I)‖^2*lineMass N one neg S a t
    let G := fun t => nativeProduct N (fun b => spectrum N X b t) (fun b => spectrum N X b t)
    have cx := marked_support N one S a (mark neg) nz ξ.toFun ξ.continuous ξ.compact ξ.positive
    have z := packet_projection N one S a (mark neg) nz ξ.toFun ξ.continuous ξ.compact ξ.positive
    obtain ⟨hi,hg⟩ := integrated_native N hx hx cx cx z z
    have eq (t : ℝ) : (G t).re=F t := by
      have arg : criticalPoint t-1/2=(t:ℂ)*I := by unfold criticalPoint; ring
      have coord (b : Parameters N) : spectrum N X b t =
          orderProbe 1 ξ.toFun ((t:ℂ)*I)*nativeRow N one neg S a b t := by
        simpa only [nativeRow,X,show radialProbe 1 ξ.toFun t=
          orderProbe 1 ξ.toFun (criticalPoint t-1/2) from rfl,arg]
          using (packet_spectrum N one S a (mark neg) nz ξ.toFun ξ.continuous ξ.compact ξ.positive b t).2
      change (nativeProduct _ _ _).re=_
      rw [native_self_re]
      simp only [F,lineMass,nativeMass,coord,norm_mul,mul_pow,Finset.mul_sum,mul_div_assoc]
    have hG : Integrable G := hi
    refine ⟨hG.re.congr (ae_of_all _ eq),?_⟩
    rw [nativeSynthesis_analysis_eq_projection] at hg
    calc
      (∫ t,F t) = (∫ t,G t).re := by
        rw [← integral_re hG]
        exact integral_congr_ae (ae_of_all _ fun t => (eq t).symm)
      _ = (inner ℂ v ((centeredSpace N).starProjection v)).re := congrArg Complex.re hg.symm
      _ ≤ ‖v‖^2 := (Complex.re_le_norm _).trans ((norm_inner_le_norm v _).trans (by
        rw [sq]; exact mul_le_mul_of_nonneg_left ((centeredSpace N).norm_starProjection_apply_le v) (norm_nonneg _)))
      _ ≤ B := cost

end ImbalancedChen.Part3.OriginalRegularPacketTest20261113
end
