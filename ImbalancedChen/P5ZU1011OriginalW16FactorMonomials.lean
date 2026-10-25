import ImbalancedChen.P5ZU1011OriginalW16NativeCompletion
import ImbalancedChen.ActualSelectedPairFactorization

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
All three original factor-size monomials for the ACTUAL W16 natural
factors, at the fixed original residue exponent1 and spectral exponent7/32.
The successful three-bin case is proved directly from its three original
capacities. The actual first-overflow/completion case uses the existing
selected-pair monomial theorem with its DERIVED critical middle product.
No target monomial, factorization, AP estimate or spectral permission is
an input. Residual well/rough support remains the same genuine primitive
residual-atom input as in the preceding native completion module.
-/

namespace ImbalancedChen.P5Z.U1011OriginalW16FactorMonomials
noncomputable section
open Classical
open U11Integral U1011OriginalSixteenPolicyBank U1011OriginalSixteenArithmeticProducts
open U1011OriginalW16NativeInitialization U1011OriginalW16NativeCompletion
open P5U1011JointOverlap
open Part3.ActualWThreeCapacityRun Part3.ActualWResidualCompletion

/-- The ORIGINAL successful W capacities, rather than a fake selected
product at their upper endpoint. b may lie BELOW N^(2theta-1). -/
theorem W_success_monomials {x delta nu A a b c : ℝ}
    (hx : 1<x) (hA : 0<A) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hnu : nu≤(153/256:ℝ)) (haA : a≤A)
    (hbB : b≤x^(2*nu-1)) (hcC : c≤x^(1-nu-2*delta)/A) :
    A^2*b*c^2≤x^(1-4*delta) ∧
      x^(7/32:ℝ)*A*a*b^5*c^2≤x^(2-4*delta) ∧
      (A*c/b)^(7/16:ℝ)*A*a*b^5*c^2≤x^(2-39*delta/8) := by
  have hx0 : 0<x := zero_lt_one.trans hx
  have hL : 0<Real.log x := Real.log_pos hx
  have hAc : A*c≤x^(1-nu-2*delta) := by
    have h := (le_div_iff₀ hA).1 hcC
    simpa only [mul_comm] using h
  have hlogAc := (Real.le_rpow_iff_log_le (mul_pos hA hc) hx0).1 hAc
  rw [Real.log_mul hA.ne' hc.ne'] at hlogAc
  have hlogb := (Real.le_rpow_iff_log_le hb hx0).1 hbB
  have hloga : Real.log a≤Real.log A := (Real.log_le_log_iff ha hA).2 haA
  have hnuL := mul_le_mul_of_nonneg_right hnu hL.le
  refine ⟨?_,?_,?_⟩
  · apply Real.le_rpow_of_log_le hx0
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) hb.ne']
    simp only [Real.log_pow]
    nlinarith only [hlogAc,hlogb]
  · apply Real.le_rpow_of_log_le hx0
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) ha.ne',Real.log_mul (by positivity) hA.ne',Real.log_rpow hx0]
    simp only [Real.log_pow]
    nlinarith only [hlogAc,hlogb,hloga,hnuL]
  · apply Real.le_rpow_of_log_le hx0
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) ha.ne',Real.log_mul (by positivity) hA.ne',
      Real.log_rpow (div_pos (mul_pos hA hc) hb),Real.log_div (mul_ne_zero hA.ne' hc.ne') hb.ne',
      Real.log_mul hA.ne' hc.ne']
    simp only [Real.log_pow]
    nlinarith only [hlogAc,hlogb,hloga,hnuL,hL.le]

def completedBins (N : ℕ) (t : Four) (A : ℝ) (tail : List ℕ) : Bins ℕ :=
  let v := coordinates N t
  complete (fun n : ℕ => (n:ℝ)) A ((N:ℝ)^(2*theta v-1))
    ((N:ℝ)^(1-theta v-2*buffer v)/A)
      (initialBins A (firstThree t)) (slots t 2 :: slots t 3 :: tail)

def completedFactors (N : ℕ) (t : Four) (A : ℝ) (tail : List ℕ) : ℕ×ℕ×ℕ :=
  let out := completedBins N t A tail
  (out.left.prod,out.middle.prod,out.right.prod)

/-- The same three ACTUAL natural factors satisfy every original
factor-size monomial in both genuine completion cases. The success case
does not assert a critical lower bound for its smaller middle factor. -/
theorem actual_W16_factorization_monomials {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (he : TypedEligible wPolicy (coordinates N t))
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) (tail : List ℕ)
    (hresidual : actualDwellSupport ((N:ℝ)^residualExponent (coordinates N t)) tail)
    (hrough : ∀ q ∈ tail, Nat.Prime q ∧ (q:ℝ)<(N:ℝ)^cutoffExponent (coordinates N t)) :
    let abc := completedFactors N t A tail
    let delta := buffer (coordinates N t)
    abc.1*abc.2.1*abc.2.2=fullPrefix t*tail.prod ∧
      0<abc.1 ∧ 0<abc.2.1 ∧ 0<abc.2.2 ∧ (abc.1:ℝ)≤A ∧
      A^2*(abc.2.1:ℝ)*(abc.2.2:ℝ)^2≤(N:ℝ)^(1-4*delta) ∧
      (N:ℝ)^(7/32:ℝ)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤(N:ℝ)^(2-4*delta) ∧
      (A*(abc.2.2:ℝ)/(abc.2.1:ℝ))^(7/16:ℝ)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*
        (abc.2.2:ℝ)^2≤(N:ℝ)^(2-39*delta/8) := by
  let v := coordinates N t
  let out := completedBins N t A tail
  obtain ⟨htrace,hprod,hpositive,hcases⟩ := actual_W16_complete_factors hN ht he A hA hAupper tail hresidual hrough
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hApos : 0<A := zero_lt_one.trans_le hA
  have ha : (0:ℝ)<out.left.prod := by exact_mod_cast hpositive.1
  have hb : (0:ℝ)<out.middle.prod := by exact_mod_cast hpositive.2.1
  have hc : (0:ℝ)<out.right.prod := by exact_mod_cast hpositive.2.2
  have hnu : theta v≤(153/256:ℝ) := by
    have h := (U1011OriginalSixteenInteriorArithmetic.interior_admissible wPolicy v he).2.2.2
    change theta v<cap wPolicy v at h
    rw [W_cap] at h
    linarith [coordinate_pos hN ht 2]
  change out.left.prod*out.middle.prod*out.right.prod=fullPrefix t*tail.prod ∧
    0<out.left.prod ∧ 0<out.middle.prod ∧ 0<out.right.prod ∧ (out.left.prod:ℝ)≤A ∧ _
  refine ⟨hprod,hpositive.1,hpositive.2.1,hpositive.2.2,?_⟩
  rcases hcases with hbounded | ⟨hlower,hupper,hleft,hright⟩
  · have hleft : (out.left.prod:ℝ)≤A := by
      simpa only [wp,actualNatList_cast_prod] using hbounded.1
    have hmiddle : (out.middle.prod:ℝ)≤(N:ℝ)^(2*theta v-1) := by
      simpa only [wp,actualNatList_cast_prod] using hbounded.2.1
    have hright : (out.right.prod:ℝ)≤(N:ℝ)^(1-theta v-2*buffer v)/A := by
      simpa only [wp,actualNatList_cast_prod] using hbounded.2.2
    exact ⟨hleft,W_success_monomials hn hApos ha hb hc hnu hleft hmiddle hright⟩
  · have hleft' : (out.left.prod:ℝ)≤A := by simpa only [wp,actualNatList_cast_prod] using hleft
    have hlower' : (N:ℝ)^(2*theta v-1)≤(out.middle.prod:ℝ) := by
      simpa only [wp,actualNatList_cast_prod] using hlower.le
    have hupper' : (out.middle.prod:ℝ)≤(N:ℝ)^actualSelectedSubproductUpper 1 (theta v) := by
      have h := hupper.trans (Real.rpow_le_rpow_of_exponent_le hn.le
        (by linarith [(buffer_bounds v he).1]))
      simpa only [wp,actualNatList_cast_prod] using h
    have hcap : A*(out.middle.prod:ℝ)*(out.right.prod:ℝ)≤(N:ℝ)^(theta v-2*buffer v) := by
      have hh : (out.right.prod:ℝ)≤(N:ℝ)^(theta v-2*buffer v)/(A*(out.middle.prod:ℝ)) := by
        simpa only [wp,actualNatList_cast_prod] using hright
      have h := (le_div_iff₀ (mul_pos hApos hb)).1 hh
      nlinarith only [h]
    refine ⟨hleft',?_⟩
    simpa only [mul_one] using selectedPair_monomials (α := (1:ℝ)) hn hApos ha hb hc hcap hlower' hupper' hleft'

end
end ImbalancedChen.P5Z.U1011OriginalW16FactorMonomials
