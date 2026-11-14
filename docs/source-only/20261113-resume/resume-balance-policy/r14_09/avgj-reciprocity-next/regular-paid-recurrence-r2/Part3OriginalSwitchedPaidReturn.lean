import ImbalancedChen.Part3OriginalSwitchedRegularTracePrice
import ImbalancedChen.Part3OriginalSwitchedRetainedRecurrence
import ImbalancedChen.Part3OriginalSwitchedInitialSpectra

/-! Pay the prescribed principal and Eisenstein contributions of both traces
in the additive errors. The actual high complementary slot sum stays explicit. -/
namespace ImbalancedChen.Part3.OriginalSwitchedPaidReturn20261113
noncomputable section
open Finset Complex
open scoped Classical BigOperators
open OriginalSwitchedRegularTracePrice20261113 (regular_dyad)
open OriginalSwitchedInitialSpectra20261113 (paid_initial residual)
open OriginalSwitchedInitialProjection20261113 (outsideSlot bandEnergy)
open OriginalSwitchedTraceProjection20261113 (R C)
open OriginalSwitchedFiniteSectorBalance20261113 (high)
open OriginalSwitchedRetainedRecurrence20261113 (retained_recurrence unpaid)
open OriginalSwitchedReturnedWindow20261113 (prefixMax)
open OriginalSwitchedActiveLevels20261113 (inputLevels outputLevels inScale outScale charge_union)
open OriginalExceptionalJNativeCompletion20261110 (classicalLevels)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)

def allowance (Y : ℝ) := 1+Real.log (2*Y)^2
theorem allowance_one (Y : ℝ) : 1≤allowance Y := le_add_of_nonneg_right (sq_nonneg _)

theorem initial {T ε : ℝ} (tp : 0≤T) (t1 : T<1) (ep : 0<ε) :
    ∃ c K Y₀ : ℝ,0<c ∧ 0<K ∧ 1≤Y₀ ∧
    ∀ (j a b : ℕ) (lo : 2^j≤a),a≤b → b≤2^(j+1) → ∀ (Y Q ω : ℝ),Y₀≤Y → 0<Q →
    let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
    let M := classicalMScale j
    c*bandEnergy (classicalLevels Q) T Y ω a b≤
      K*(((1+M)*(1+Y))^ε*(M+Y)*M+allowance Y*(Q+M^(1+ε))*M)+
      4*∑ q∈classicalLevels Q,‖outsideSlot q ap b T Y ω‖ := by
  obtain ⟨c,D,X,cp,dp,x1,base⟩ := paid_initial tp t1 ep
  obtain ⟨A,an,regular⟩ := regular_dyad ep
  refine ⟨c,D+4*A,X,cp,add_pos_of_pos_of_nonneg dp (mul_nonneg (by norm_num) an),x1,
    fun j a b lo ab hi Y Q ω hy qp => ?_⟩
  let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
  let M := classicalMScale j
  let L := classicalLevels Q
  let G := ((1+M)*(1+Y))^ε*(M+Y)*M
  let V := (Q+M^(1+ε))*M
  let H := ∑ q∈L,‖outsideSlot q ap b T Y ω‖
  let U := ∑ q∈L,(‖R false q ap b Y Q ω‖+‖C false q ap b Y Q ω‖)
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have yp := zero_lt_one.trans_le (x1.trans hy)
  have gp : 0≤G := by dsimp [G]; positivity
  have vp : 0≤V := by dsimp [V]; positivity
  have reg : U≤A*allowance Y*V := (regular false j a b lo hi Y Q Q ω (x1.trans hy) qp qp).trans_eq
    (by dsimp only [allowance,V,M];ring)
  have dec : (∑ q∈L,residual q ap b T Y Q ω)=H+U := by
    simp only [H,U,residual,add_assoc,Finset.sum_add_distrib]
  have b0 := base j a b lo ab hi Y Q ω hy qp
  rw [dec] at b0
  apply b0.trans
  change D*(G+V)+4*(H+U)≤(D+4*A)*(G+allowance Y*(Q+M^(1+ε))*M)+4*H
  rw [mul_assoc (allowance Y) _ M]
  change D*(G+V)+4*(H+U)≤(D+4*A)*(G+allowance Y*V)+4*H
  nlinarith only [reg,mul_nonneg an gp,mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (allowance_one Y) vp) dp.le]

theorem recurrence {T ε : ℝ} (tp : 0≤T) (t1 : T<1) (ep : 0<ε) :
    ∃ c K D Y₀ : ℝ,0<c ∧ 0<K ∧ 0≤D ∧ 1≤Y₀ ∧
    ∀ Y≥Y₀,∀ (Q ω : ℝ),0<Q → ∀ (j a b : ℕ) (lo : 2^j≤a) (ab : a≤b),b≤2^(j+1) →
    let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
    let M := classicalMScale j
    let V := outputLevels j Y Q
    let U := inputLevels Q
    c*bandEnergy (classicalLevels Q) T Y ω a b≤
      K*(∑ l∈range 6,prefixMax (classicalLevels (outScale j Y Q l)) Y ω a b ab+
        Y^ε*(outScale j Y Q l+M)*M)+
      4*((∑ d∈V,‖high true d ap b T Y Q ω‖)+(∑ q∈U,‖high false q ap b T Y Q ω‖)+
        D*allowance Y*((∑ l∈range 6,(outScale j Y Q l+M^(1+ε))*M)+
           (∑ l∈range 4,(inScale Q l+M^(1+ε))*M))) := by
  obtain ⟨c,K,D,X,cp,kp,dp,x1,base⟩ := retained_recurrence tp t1 ep
  obtain ⟨A,an,regular⟩ := regular_dyad ep
  refine ⟨c,K,D+A,X,cp,kp,add_nonneg dp an,x1,fun Y hy Q ω qp j a b lo ab hi => ?_⟩
  let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
  let M := classicalMScale j
  let price (B : ℝ) := (B+M^(1+ε))*M
  let O := outScale j Y Q
  let I := inScale Q
  let U := inputLevels Q
  let V := outputLevels j Y Q
  let h := fun s (d : ℕ+) => ‖high s d ap b T Y Q ω‖
  let r := fun s (d : ℕ+) => ‖R s d ap b Y Q ω‖+‖C s d ap b Y Q ω‖
  have dec (s : Bool) (J : Finset ℕ+) : (∑ d∈J,unpaid s d ap b T Y Q ω)=(∑ d∈J,h s d)+∑ d∈J,r s d := by
    simp only [h,r,unpaid,add_assoc,Finset.sum_add_distrib]
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have y1 := x1.trans hy
  have yp := zero_lt_one.trans_le y1
  have op (l : ℕ) : 0<O l := by change 0<(2:ℝ)^l*(Real.pi*M*Y/Q)/2; positivity
  have ip (l : ℕ) : 0<I l := by dsimp [I,inScale];positivity
  have bill (s : Bool) (J : Finset ℕ) (B : ℕ→ℝ) (bp : ∀ l,0<B l) :
      (∑ d∈J.biUnion (fun l => classicalLevels (B l)),r s d)≤A*allowance Y*∑ l∈J,price (B l) := by
    apply (charge_union J (fun l => classicalLevels (B l)) _ (fun d => add_nonneg (norm_nonneg _) (norm_nonneg _))).trans
    have per (l : ℕ) := regular s j a b lo hi Y Q (B l) ω y1 qp (bp l)
    simpa only [Finset.mul_sum,price,allowance,r,M,mul_assoc] using sum_le_sum (s:=J) (fun l _ => per l)
  let W := (∑ l∈range 6,price (O l))+(∑ l∈range 4,price (I l))
  have w0 : 0≤W := add_nonneg (sum_nonneg fun l _ => mul_nonneg (add_nonneg (op l).le (Real.rpow_nonneg mp.le _)) mp.le)
    (sum_nonneg fun l _ => mul_nonneg (add_nonneg (ip l).le (Real.rpow_nonneg mp.le _)) mp.le)
  have b0 := base Y hy Q ω qp j a b lo ab hi
  rw [dec,dec] at b0
  apply b0.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have R : (∑ d∈V,r true d)+(∑ q∈U,r false q)≤A*allowance Y*W := by
    simpa only [W,mul_add] using add_le_add (bill true (range 6) O op) (bill false (range 4) I ip)
  change ((∑ d∈V,h true d)+(∑ d∈V,r true d))+((∑ q∈U,h false q)+(∑ q∈U,r false q))+D*W≤
    (∑ d∈V,h true d)+(∑ q∈U,h false q)+(D+A)*allowance Y*W
  nlinarith only [R,mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (allowance_one Y) w0) dp]

end
end ImbalancedChen.Part3.OriginalSwitchedPaidReturn20261113
