import ImbalancedChen.Part3OriginalSwitchedFiniteSectorBalance

/-! A finite dyadic level-return inequality with its actual unpaid
regular and high-complementary contributions, and its numerical
positive-weight price on both sides. -/
namespace ImbalancedChen.Part3.OriginalSwitchedRetainedRecurrence20261113
noncomputable section
open Finset Complex
open scoped BigOperators Classical
open OriginalSwitchedActiveLevels20261113 (inputLevels outputLevels inScale outScale charge_union)
open OriginalSwitchedFiniteSectorBalance20261113 (low high rest balance lower_input)
open OriginalSwitchedTraceProjection20261113 (R C H)
open OriginalSwitchedInitialProjection20261113 (bandEnergy)
open OriginalSwitchedIntervalTraceSlots20261113 (output output_bound)
open OriginalSwitchedProjectionMask20261113 (hol_price)
open OriginalSwitchedReturnedWindow20261113 (prefixMax)
open OriginalSwitchedIntervalReturn20261113 (retained)
open OriginalSwitchedLevelIdentity20261113 (levelWeight)
open OriginalSwitchedPhysicalWindows20261113 (returnScale)
open OriginalExceptionalJNativeCompletion20261110 (classicalLevels tau exceptional)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open CommonSmoothCutoff (dyadicCutoff_nonneg dyadicCutoff_le_one)

def unpaid (s : Bool) (z : ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) (T Y Q ω : ℝ) :=
  ‖high s z ap b T Y Q ω‖+‖R s z ap b Y Q ω‖+‖C s z ap b Y Q ω‖

private theorem rest_price (s : Bool) (z : ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) (T Y Q ω : ℝ) :
    ‖rest s z ap b T Y Q ω‖≤unpaid s z ap b T Y Q ω+‖H s z ap b Y Q ω‖ := by
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)

private theorem single_upper (j a b : ℕ) (lo : 2^j≤a) (hi : b≤2^(j+1)) {Y Q : ℝ} (y1 : 1≤Y) (qp : 0<Q) (T ω : ℝ) :
    let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
    let U := inputLevels Q
    let V := outputLevels j Y Q
    4*(∑ q∈U,levelWeight Q q*low false q ap b T Y Q ω).re≤
      (4*∑ d∈V,∑ i∈retained T d,‖output d i ap b Y Q ω‖)+
      4*((∑ d∈V,unpaid true d ap b T Y Q ω)+(∑ q∈U,unpaid false q ap b T Y Q ω)+
         (∑ d∈V,‖H true d ap b Y Q ω‖)+(∑ q∈U,‖H false q ap b Y Q ω‖)) := by
  let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
  let U := inputLevels Q
  let V := outputLevels j Y Q
  have eq := congrArg Complex.re (balance j a b lo hi y1 qp T ω)
  simp only [Complex.add_re,Complex.re_sum] at eq
  have outputLow (d : ℕ+) : (low true d ap b T Y Q ω).re≤∑ i∈retained T d,‖output d i ap b Y Q ω‖ := by
    simp only [low,ite_true,Complex.re_sum]
    exact sum_le_sum (fun i _ => Complex.re_le_norm _)
  have outputRest (d : ℕ+) : (rest true d ap b T Y Q ω).re≤unpaid true d ap b T Y Q ω+‖H true d ap b Y Q ω‖ :=
    (Complex.re_le_norm _).trans (rest_price true d ap b T Y Q ω)
  have inputRest (q : ℕ+) : -(levelWeight Q q*rest false q ap b T Y Q ω).re≤
      unpaid false q ap b T Y Q ω+‖H false q ap b Y Q ω‖ := by
    apply ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (rest_price false q ap b T Y Q ω)
    simp only [levelWeight,Complex.norm_real,Real.norm_of_nonneg (dyadicCutoff_nonneg _)]
    exact dyadicCutoff_le_one _
  have loB := Finset.sum_le_sum (s:=V) (fun d _ => outputLow d)
  have outB := Finset.sum_le_sum (s:=V) (fun d _ => outputRest d)
  have inB := Finset.sum_le_sum (s:=U) (fun q _ => inputRest q)
  rw [Finset.sum_add_distrib] at outB
  rw [Finset.sum_add_distrib,Finset.sum_neg_distrib] at inB
  simp only [Complex.re_sum]
  linarith only [eq,loB,outB,inB]

/-- The original single dyadic entry is dominated by six actual
child prefix energies at the retained order, arithmetic-sized positive
weights, and the explicit norm costs of all remaining spectra. -/
theorem retained_recurrence {T ε : ℝ} (tp : 0≤T) (t1 : T<1) (ep : 0<ε) :
    ∃ c K D Y₀ : ℝ,0<c ∧ 0<K ∧ 0≤D ∧ 1≤Y₀ ∧
    ∀ Y≥Y₀,∀ (Q ω : ℝ),0<Q → ∀ (j a b : ℕ) (lo : 2^j≤a) (ab : a≤b),b≤2^(j+1) →
    let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
    let M := classicalMScale j
    let V := outputLevels j Y Q
    let U := inputLevels Q
    c*bandEnergy (classicalLevels Q) T Y ω a b≤
      K*(∑ l∈range 6,prefixMax (classicalLevels (outScale j Y Q l)) Y ω a b ab+
        Y^ε*(outScale j Y Q l+M)*M)+
      4*((∑ d∈V,unpaid true d ap b T Y Q ω)+(∑ q∈U,unpaid false q ap b T Y Q ω)+
        D*((∑ l∈range 6,(outScale j Y Q l+M^(1+ε))*M)+
           (∑ l∈range 4,(inScale Q l+M^(1+ε))*M))) := by
  obtain ⟨c,X,cp,x1,fl⟩ := lower_input tp t1
  obtain ⟨K,Z,kp,z1,ret⟩ := output_bound tp t1 ep
  obtain ⟨D,dp,hol⟩ := hol_price ep
  refine ⟨c,K,D,max X Z,cp,kp,dp,x1.trans (le_max_left _ _),fun Y hy Q ω qp j a b lo ab hi => ?_⟩
  let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
  let M := classicalMScale j
  let U := inputLevels Q
  let V := outputLevels j Y Q
  let O := outScale j Y Q
  let I := inScale Q
  let f (d : ℕ+) := ∑ i∈retained T d,‖output d i ap b Y Q ω‖
  let p (l : ℕ) := prefixMax (classicalLevels (O l)) Y ω a b ab+Y^ε*(O l+M)*M
  have hx := (le_max_left X Z).trans hy
  have hz := (le_max_right X Z).trans hy
  have y1 := x1.trans hx
  have yp := zero_lt_one.trans_le y1
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have op (l : ℕ) : 0<O l := by
    change 0<(2:ℝ)^l*(Real.pi*M*Y/Q)/2
    positivity
  have ip (l : ℕ) : 0<I l := by dsimp only [I,inScale];positivity
  have charge (s : Bool) (J : Finset ℕ) (B : ℕ→ℝ) (bp : ∀ l,0<B l) :
      (∑ d∈J.biUnion (fun l => classicalLevels (B l)),‖H s d ap b Y Q ω‖)≤D*(∑ l∈J,(B l+M^(1+ε))*M) := by
    apply (charge_union J (fun l => classicalLevels (B l)) _ (fun _ => norm_nonneg _)).trans
    have h := sum_le_sum (s:=J) (fun l _ => hol s j a b lo hi Y Q (B l) ω y1 qp (bp l))
    simpa only [Finset.mul_sum,mul_assoc] using h
  have first : (4*∑ d∈V,f d)≤K*(∑ l∈range 6,p l) := by
    have cover := charge_union (range 6) (fun l => classicalLevels (O l)) f
      (fun d => sum_nonneg (fun i _ => norm_nonneg _))
    have h (l : ℕ) : (4*∑ d∈classicalLevels (O l),f d)≤K*p l :=
      ret Y hz Q (O l) qp (op l) ω j a b lo ab hi
    have summed := Finset.sum_le_sum (s:=range 6) (fun l _ => h l)
    rw [←Finset.mul_sum (range 6) (fun l => ∑ d∈classicalLevels (O l),f d) 4,←Finset.mul_sum (range 6) p K] at summed
    exact (mul_le_mul_of_nonneg_left cover (by norm_num : (0:ℝ)≤4)).trans summed
  have lhs := (fl Y hx Q qp ω a b ap).trans (single_upper j a b lo hi y1 qp T ω)
  have both := add_le_add (charge true (range 6) O op) (charge false (range 4) I ip)
  rw [←mul_add] at both
  apply lhs.trans
  apply add_le_add first
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤4)
  linarith only [both]

end
end ImbalancedChen.Part3.OriginalSwitchedRetainedRecurrence20261113
