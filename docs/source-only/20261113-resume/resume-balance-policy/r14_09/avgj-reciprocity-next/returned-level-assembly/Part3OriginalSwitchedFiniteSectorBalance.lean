import ImbalancedChen.Part3OriginalSwitchedActiveLevels

/-! Localize the original sector identity and extract the lower
complementary square using nonnegative input weights. -/
namespace ImbalancedChen.Part3.OriginalSwitchedFiniteSectorBalance20261113
noncomputable section
open Finset Complex
open scoped BigOperators Classical
open OriginalSwitchedActiveLevels20261113 (inputLevels outputLevels outside_input outside_output)
open OriginalSwitchedIntervalLevelSwitch20261113 (interval_level_switch)
open OriginalSwitchedTraceProjection20261113 (all E R C H interval_split)
open OriginalSwitchedInitialProjection20261113 (bandEnergy outsideSlot)
open OriginalSwitchedIntervalTraceSlots20261113 (input output)
open private input_value from ImbalancedChen.Part3OriginalSwitchedIntervalTraceSlots
open OriginalSwitchedIntervalReturn20261113 (retained)
open OriginalSwitchedMellinRows20261113 (nativeRow twistedRow)
open OriginalSwitchedLevelIdentity20261113 (levelWeight single)
open OriginalExceptionalJNativeCompletion20261110 (exceptional tau classicalLevels mem_classicalLevels)
open OriginalExceptionalNativeEnvelope20261113 (native_band)
open CommonSmoothCutoff (dyadicCutoff dyadicCutoff_nonneg dyadicCutoff_eq_one dyadicCutoff_le_one)

def low (s : Bool) (z : ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) (T Y Q ω : ℝ) :=
  ∑ i∈retained T z,if s then output z i ap b Y Q ω else input z i ap b Y ω

def high (s : Bool) (z : ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) (T Y Q ω : ℝ) :=
  ∑ i : ↥(exceptional z),if T<tau z i.val then
    (if s then output z i ap b Y Q ω else input z i ap b Y ω) else 0

def rest (s : Bool) (z : ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) (T Y Q ω : ℝ) :=
  high s z ap b T Y Q ω+R s z ap b Y Q ω+C s z ap b Y Q ω+H s z ap b Y Q ω

theorem split_rest (s : Bool) (z : ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) {Y Q : ℝ} (y1 : 1≤Y) (qp : 0<Q) (T ω : ℝ) :
    all s z ap b Y Q ω=low s z ap b T Y Q ω+rest s z ap b T Y Q ω := by
  have h : E s z ap b Y Q ω=low s z ap b T Y Q ω+high s z ap b T Y Q ω := by
    simp only [E,low,high,retained,Finset.sum_filter,←Finset.sum_add_distrib]
    apply sum_congr rfl
    intro i _
    by_cases p : tau z i.val≤T
    · simp only [if_pos p,if_neg (not_lt.mpr p),add_zero]
    · simp only [if_neg p,if_pos (lt_of_not_ge p),zero_add]
  rw [interval_split s z ap b y1 qp ω,h]
  dsimp only [rest];ring

theorem balance (j a b : ℕ) (lo : 2^j≤a) (hi : b≤2^(j+1)) {Y Q : ℝ} (y1 : 1≤Y) (qp : 0<Q) (T ω : ℝ) :
    let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
    (∑ q∈inputLevels Q,levelWeight Q q*low false q ap b T Y Q ω)+
      (∑ q∈inputLevels Q,levelWeight Q q*rest false q ap b T Y Q ω)=
      (∑ d∈outputLevels j Y Q,low true d ap b T Y Q ω)+(∑ d∈outputLevels j Y Q,rest true d ap b T Y Q ω) := by
  let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
  let yp := zero_lt_one.trans_le y1
  have sum := (interval_level_switch ap b yp qp ω).1.tsum_eq.symm
  have inW (q : ℕ+) (h : q∉inputLevels Q) : levelWeight Q q*all false q ap b Y Q ω=0 := by rw [outside_input qp q h,zero_mul]
  rw [tsum_eq_sum inW,tsum_eq_sum (fun d h => outside_output j a b lo hi yp qp d h ω)] at sum
  have left (q : ℕ+) := split_rest false q ap b y1 qp T ω
  have right (q : ℕ+) := split_rest true q ap b y1 qp T ω
  simpa only [left,right,mul_add,Finset.sum_add_distrib] using sum

theorem lower_input {T : ℝ} (tp : 0≤T) (t1 : T<1) :
    ∃ c Y₀ : ℝ,0<c ∧ 1≤Y₀ ∧ ∀ Y≥Y₀,∀ Q : ℝ,0<Q → ∀ (ω : ℝ) (a b : ℕ) (ap : 0<a),
      c*bandEnergy (classicalLevels Q) T Y ω a b≤
        4*(∑ q∈inputLevels Q,levelWeight Q q*low false q ap b T Y Q ω).re := by
  obtain ⟨c,_,X,cp,_,x1,p⟩ := native_band tp t1
  refine ⟨c,X,cp,x1,fun Y hy Q qp ω a b ap => ?_⟩
  let L := classicalLevels Q
  let U := inputLevels Q
  let f (q : ℕ+) := (levelWeight Q q*low false q ap b T Y Q ω).re
  let yp := zero_lt_one.trans_le (x1.trans hy)
  have floor (q : ℕ+) (i : ↥(exceptional q)) (hi : i∈retained T q) :
      c*(Y^(tau q i.val)*‖twistedRow (Ico a b) (nativeRow q i.val ω) 0‖^2)≤4*(input q i ap b Y ω).re := by
    rw [input_value,←mul_assoc]
    exact mul_le_mul_of_nonneg_right (p Y hy q i (Finset.mem_filter.mp hi).2).1 (sq_nonneg _)
  have f0 (q : ℕ+) : 0≤f q := by
    simp only [f,levelWeight,Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,zero_mul,sub_zero]
    apply mul_nonneg (dyadicCutoff_nonneg _)
    simp only [low,Bool.false_eq_true,if_false,Complex.re_sum]
    apply sum_nonneg
    intro i hi
    have fl := floor q i hi
    have n := mul_nonneg cp.le (mul_nonneg (Real.rpow_nonneg yp.le (tau q i.val))
      (sq_nonneg ‖twistedRow (Ico a b) (nativeRow q i.val ω) 0‖))
    linarith only [n,fl]
  have sub : L⊆U := by
    intro q hq
    apply Finset.mem_biUnion.mpr
    refine ⟨2,by decide,?_⟩
    change q∈classicalLevels ((2:ℝ)^2*Q/4)
    simpa only [show (2:ℝ)^2*Q/4=Q by ring] using hq
  have per (q : ℕ+) (hq : q∈L) : c*(∑ i∈retained T q,Y^(tau q i.val)*
      ‖twistedRow (Ico a b) (nativeRow q i.val ω) 0‖^2)≤4*f q := by
    have v := (mem_classicalLevels Q q).mp hq
    have w : levelWeight Q q=1 := by
      simp only [levelWeight,dyadicCutoff_eq_one (show (q.val:ℝ)/Q∈Set.Icc 1 2 from
        ⟨(le_div_iff₀ qp).mpr (by simpa only [one_mul] using v.1.le),(div_le_iff₀ qp).mpr v.2⟩),Complex.ofReal_one]
    simp only [f,w,one_mul,low,Bool.false_eq_true,if_false,Complex.re_sum,Finset.mul_sum]
    exact sum_le_sum (floor q)
  have small := Finset.sum_le_sum (s:=L) (fun q hq => per q hq)
  let each (q : ℕ+) := ∑ i∈retained T q,Y^(tau q i.val)*
    ‖twistedRow (Ico a b) (nativeRow q i.val ω) 0‖^2
  change (∑ q∈L,c*each q)≤∑ q∈L,4*f q at small
  rw [←Finset.mul_sum L each c,←Finset.mul_sum L f 4] at small
  have large := Finset.sum_le_sum_of_subset_of_nonneg sub (fun q _ _ => f0 q)
  simp only [Complex.re_sum]
  exact small.trans (mul_le_mul_of_nonneg_left large (by norm_num : (0:ℝ)≤4))

end
end ImbalancedChen.Part3.OriginalSwitchedFiniteSectorBalance20261113
