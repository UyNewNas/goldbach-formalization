import ImbalancedChen.Part3OriginalSwitchedRegularBlockExchange
import ImbalancedChen.Part3OriginalSwitchedIntervalTraceSlots
import ImbalancedChen.Part3OriginalSwitchedHolTraceError

/-! Split the prescribed native trace into its four actual spectral
contributions on both sides of the switch. -/
namespace ImbalancedChen.Part3.OriginalSwitchedTraceProjection20261113
noncomputable section
open Finset Complex MeasureTheory
open scoped BigOperators Classical
open ActualFullCuspEigenbasis20261026b
open OriginalExceptionalJNativeCompletion20261110 (exceptional mem_exceptional native_cusp_eigenvalue_pos)
open ActualPositiveNativeDiagonal20261112 (nativeWeight)
open ActualUnitBandSpectralMass20261112 (height)
open ActualMarkedCubicPrice20261112 (linePrice slotPrice slotPrice_nn)
open OriginalSwitchedRegularFourierBudget20261113 (scaled)
open OriginalSwitchedRegularMarkExchange20261113 (principal incoming)
open OriginalSameInfinityTensorSpectrum20261113 (disc)
open OriginalSameInfinityScalarPrices20261113 (cubic_prices)
open OriginalSwitchedHolTraceError20261113 (test)
open OriginalSwitchedCutoffFamily20261113 (profile)
open OriginalSwitchedLevelIdentity20261113 (single spectral)
open OriginalSwitchedMaassExchange20261113 (mass)
open OriginalSameInfinityFixedScalarTrace20261113 (total)
open OriginalSameInfinityWeightedHol20261113 (holSum)
open OriginalSwitchedUniformRegularTransform20261113 (regular_return)
open OriginalSwitchedInitialTraceGeometry20261113 (mark)
open OriginalSwitchedIntervalTraceSlots20261113 (slot input output)
open ActualIntervalGeometricSumSourceOnly (phaseAt)
open private cut_eq from ImbalancedChen.Part3OriginalSwitchedLevelIdentity
open private price_div from ImbalancedChen.Part3OriginalMarkedPacketLimits

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

def complement (q m n : ℕ+) (Φ : ℝ→ℂ) :=
  ∑ i : ↥(exceptional q),nativeWeight q.val Φ i.val*disc q m n i.val

theorem mark_split (s : Bool) (q m n : ℕ+) {Y Q : ℝ} (y1 : 1≤Y) (qp : 0<Q) :
    let Φ := test s q Y Q m.val n.val
    spectral q m n Φ=complement q m n Φ+principal q m n Φ+incoming q m n Φ+holSum q m n Φ := by
  let Φ := test s q Y Q m.val n.val
  let L := Y*(4*Real.pi*Real.sqrt ((m.val:ℝ)*(n.val:ℝ)))/((q.val:ℝ)*Q)
  have yp := zero_lt_one.trans_le y1
  have eq : (fun x => profile s L (Y*x))=Φ := by
    cases s
    · funext x;simp only [Φ,test,single,profile,Bool.false_eq_true,if_false,mul_one]
    · exact cut_eq m n q yp qp
  obtain ⟨K,kp,bound⟩ := regular_return
  let A := K*(1+Real.log (2*Y)^2)
  have scalar (t : ℝ) : ‖scaled Φ t‖≤A*linePrice t := by
    apply price_div
    have ch := Real.cosh_pos (Real.pi*t)
    simp only [scaled,norm_div,Complex.norm_real,Real.norm_of_nonneg ch.le]
    rw [show (1+|t|)^3*Real.cosh (Real.pi*t)*
      (‖ActualPrescribedPositiveJ20261112.positiveWeight Φ t‖/Real.cosh (Real.pi*t))=
      (1+|t|)^3*‖ActualPrescribedPositiveJ20261112.positiveWeight Φ t‖ by field_simp [ch.ne']]
    simpa only [eq] using bound Y y1 s L t
  let Idx := actualCuspBasisIndex q.val (NeZero.pos q.val)
  let W := fun i : Idx => nativeWeight q.val Φ i*disc q m n i
  let e := ActualUnitBandSpectralMass20261112.exceptional q.val
  let P := fun i : Idx => if e i then 0 else W i
  let X := fun i : Idx => if e i then W i else 0
  have inE (i : Idx) : i∈exceptional q ↔ e i :=
    (mem_exceptional q i).trans ⟨And.right,fun h => ⟨native_cusp_eigenvalue_pos q.val q.property i,h⟩⟩
  have xh : HasSum X (complement q m n Φ) := by
    have h : HasSum X (∑ i∈exceptional q,X i) := hasSum_sum_of_ne_finset_zero
      (fun i hi => if_neg (fun he => hi ((inE i).mpr he)))
    have val : (∑ i∈exceptional q,X i)=complement q m n Φ := by
      rw [complement,Finset.univ_eq_attach,Finset.sum_attach]
      exact sum_congr rfl (fun i hi => if_pos ((inE i).mp hi))
    exact val ▸ h
  have p : Summable P := by
    apply ((cubic_prices q m n).1.mul_left A).of_norm_bounded
    intro i
    by_cases hi : e i
    · simp only [P,if_pos hi,norm_zero,slotPrice,if_pos (show ActualUnitBandSpectralMass20261112.exceptional q.val i from hi),
        zero_mul,mul_zero,le_refl]
    · simp only [P,if_neg hi,W,nativeWeight,if_neg (show ¬ActualUnitBandSpectralMass20261112.exceptional q.val i from hi),
        slotPrice,norm_mul]
      have h := mul_le_mul_of_nonneg_right (scalar (height q.val i)) (norm_nonneg (disc q m n i))
      exact h.trans_eq (by ring)
  have both : HasSum W (complement q m n Φ+principal q m n Φ) := by
    apply (xh.add p.hasSum).congr_fun
    intro i
    by_cases h : e i <;> simp [X,P,h]
  change (∑' i,W i)+incoming q m n Φ+holSum q m n Φ=_
  rw [both.tsum_eq]

def pair {a : ℕ} (ap : 0<a) (b : ℕ) (ω : ℝ) (f : ℕ+→ℕ+→ℂ) :=
  ∑ m : ↥(Ico a b),∑ n : ↥(Ico a b),star (phaseAt ω m.val)*phaseAt ω n.val*
    f (mark a ap m) (mark a ap n)

def E (s : Bool) (q : ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) (Y Q ω : ℝ) :=
  ∑ i : ↥(exceptional q),if s then output q i ap b Y Q ω else input q i ap b Y ω

def R (s : Bool) (q : ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) (Y Q ω : ℝ) :=
  pair ap b ω (fun m n => principal q m n (test s q Y Q m.val n.val))
def C (s : Bool) (q : ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) (Y Q ω : ℝ) :=
  pair ap b ω (fun m n => incoming q m n (test s q Y Q m.val n.val))
def H (s : Bool) (q : ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) (Y Q ω : ℝ) :=
  pair ap b ω (fun m n => holSum q m n (test s q Y Q m.val n.val))
def all (s : Bool) (q : ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) (Y Q ω : ℝ) :=
  pair ap b ω (fun m n => spectral q m n (test s q Y Q m.val n.val))

theorem interval_split (s : Bool) (q : ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) {Y Q : ℝ} (y1 : 1≤Y) (qp : 0<Q) (ω : ℝ) :
    all s q ap b Y Q ω=E s q ap b Y Q ω+R s q ap b Y Q ω+C s q ap b Y Q ω+H s q ap b Y Q ω := by
  let e := pair ap b ω (fun m n => complement q m n (test s q Y Q m.val n.val))
  have hE : e=E s q ap b Y Q ω := by
    let I := ↥(Ico a b)
    let J := ↥(exceptional q)
    have reindex (f : I→I→J→ℂ) : (∑ m : I,∑ n : I,∑ i : J,f m n i)=∑ i : J,∑ m : I,∑ n : I,f m n i := by
      rw [sum_comm (s:=(univ:Finset J)) (t:=(univ:Finset I))]
      apply sum_congr rfl
      intro m _
      rw [sum_comm (s:=(univ:Finset J)) (t:=(univ:Finset I))]
    have h := reindex (fun m n i => star (phaseAt ω m.val)*phaseAt ω n.val*
      (nativeWeight q.val (test s q Y Q m.val n.val) i.val*disc q (mark a ap m) (mark a ap n) i.val))
    cases s <;> simpa only [e,pair,complement,E,input,output,slot,test,mark,Bool.false_eq_true,if_false,ite_true,
      Finset.mul_sum] using h
  calc
    _ = e+R s q ap b Y Q ω+C s q ap b Y Q ω+H s q ap b Y Q ω := by
      simp only [all,e,R,C,H,pair]
      have point (m n : ℕ+) := mark_split s q m n y1 qp
      simp_rw [point]
      simp only [mul_add,Finset.sum_add_distrib]
    _ = _ := by rw [hE]

end
end ImbalancedChen.Part3.OriginalSwitchedTraceProjection20261113
