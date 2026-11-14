import ImbalancedChen.Part3OriginalSwitchedIntervalLevelSwitch

/-! Extract the actual complementary band from the first geometric
trace. The unpriced part of the spectrum is displayed with its sign. -/
namespace ImbalancedChen.Part3.OriginalSwitchedInitialProjection20261113
noncomputable section
open Finset Complex
open scoped BigOperators Classical
open OriginalSwitchedTraceProjection20261113 (all E R C H interval_split)
open OriginalSwitchedInitialTraceGeometry20261113 (initial_geometry)
open OriginalSwitchedIntervalTraceSlots20261113 (input output input_floor)
open OriginalSwitchedIntervalReturn20261113 (retained)
open OriginalSwitchedMellinRows20261113 (nativeRow twistedRow)
open OriginalExceptionalJNativeCompletion20261110 (exceptional tau classicalLevels mem_classicalLevels)
open OriginalClassicalSpectralSupports20261102 (classicalMScale)
open OriginalSwitchedLevelIdentity20261113 (levelWeight)
open CommonSmoothCutoff (dyadicCutoff dyadicCutoff_eq_one)

def bandEnergy (L : Finset ℕ+) (T Y ω : ℝ) (a b : ℕ) :=
  ∑ z∈L,∑ i∈retained T z,Y^(tau z i.val)*‖twistedRow (Ico a b) (nativeRow z i.val ω) 0‖^2

def outsideSlot (q : ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) (T Y ω : ℝ) :=
  ∑ i : ↥(exceptional q),if T<tau q i.val then input q i ap b Y ω else 0

def remainder (q : ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) (T Y Q ω : ℝ) :=
  ‖outsideSlot q ap b T Y ω‖+‖R false q ap b Y Q ω‖+‖C false q ap b Y Q ω‖+‖H false q ap b Y Q ω‖

private theorem retained_re (q : ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) {Y Q : ℝ} (y1 : 1≤Y) (qp : 0<Q) (T ω : ℝ) :
    (∑ i∈retained T q,(input q i ap b Y ω).re)≤‖all false q ap b Y Q ω‖+remainder q ap b T Y Q ω := by
  let z := ∑ i∈retained T q,input q i ap b Y ω
  let w := outsideSlot q ap b T Y ω
  let r := R false q ap b Y Q ω
  let c := C false q ap b Y Q ω
  let h := H false q ap b Y Q ω
  have ex : E false q ap b Y Q ω=z+w := by
    simp only [E,Bool.false_eq_true,if_false,z,w,outsideSlot,retained,sum_filter,←Finset.sum_add_distrib]
    apply sum_congr rfl
    intro i _
    by_cases t : tau q i.val≤T
    · simp only [if_pos t,if_neg (not_lt.mpr t),add_zero]
    · simp only [if_neg t,if_pos (lt_of_not_ge t),zero_add]
  have e := interval_split false q ap b y1 qp ω
  rw [ex] at e
  change all false q ap b Y Q ω=z+w+r+c+h at e
  have cost (v : ℂ) : -v.re≤‖v‖ := (neg_le_abs v.re).trans (Complex.abs_re_le_norm _)
  have ze := congrArg Complex.re e
  simp only [Complex.add_re] at ze
  change _≤‖all false q ap b Y Q ω‖+(‖w‖+‖r‖+‖c‖+‖h‖)
  rw [show (∑ i∈retained T q,(input q i ap b Y ω).re)=z.re by rw [z,Complex.re_sum]]
  linarith only [ze,Complex.re_le_norm (all false q ap b Y Q ω),cost w,cost r,cost c,cost h]

/-- Native interval version of the initial geometric price with all
remaining contributions named. The high-order complementary tail is
an actual sum, so no spectral gap is assumed. -/
theorem initial_projection {T ε : ℝ} (tp : 0≤T) (t1 : T<1) (ep : 0<ε) :
    ∃ c D Y₀ : ℝ,0<c ∧ 0<D ∧ 1≤Y₀ ∧ ∀ (j a b : ℕ) (lo : 2^j≤a),a≤b → b≤2^(j+1) →
      ∀ (Y Q ω : ℝ),Y₀≤Y → 0<Q →
      let M := classicalMScale j
      let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
      c*bandEnergy (classicalLevels Q) T Y ω a b≤
        4*(D*((1+M)*(1+Y))^ε*(M+Y)*M+∑ q∈classicalLevels Q,remainder q ap b T Y Q ω) := by
  obtain ⟨c,X,cp,x1,f⟩ := input_floor tp t1
  obtain ⟨D,dp,g⟩ := initial_geometry ep
  refine ⟨c,D,X,cp,dp,x1,fun j a b lo ab hi Y Q ω hy qp => ?_⟩
  let L := classicalLevels Q
  let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
  have y1 := x1.trans hy
  have h := f Y hy L ω a b ap
  have r := sum_le_sum (s:=L) (fun q _ => retained_re q ap b y1 qp T ω)
  rw [Finset.sum_add_distrib] at r
  have geom := g j a b lo ab hi Y Q ω y1 L
  have w (q : ℕ+) (hq : q∈L) : levelWeight Q q=1 := by
    have v := (mem_classicalLevels Q q).mp hq
    simp only [levelWeight,dyadicCutoff_eq_one (show (q.val:ℝ)/Q∈Set.Icc 1 2 from
      ⟨(le_div_iff₀ qp).mpr (by simpa only [one_mul] using v.1.le),(div_le_iff₀ qp).mpr v.2⟩),Complex.ofReal_one]
  have base : (∑ q∈L,‖all false q ap b Y Q ω‖)≤D*((1+classicalMScale j)*(1+Y))^ε*
      (classicalMScale j+Y)*classicalMScale j := by
    apply le_trans _ geom
    apply le_of_eq
    apply sum_congr rfl
    intro q hq
    rw [w q hq,one_mul] <;> rfl
  exact h.trans (mul_le_mul_of_nonneg_left (r.trans (add_le_add base le_rfl)) (by norm_num : (0:ℝ)≤4))

end
end ImbalancedChen.Part3.OriginalSwitchedInitialProjection20261113
