import ImbalancedChen.Part3ActualRoughContourEdges

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal lower bound for the genuine conductorWidth used by the actual
contour. Every branch is retained, including the quadratic low-height
width and the reciprocal-height term in its high-height bound. The
result is k(c,A)*m^(-14 eta)/D^24. It is a scalar dictionary for the
already proved analytic width, not an assumed zero-free/SW estimate.
-/

namespace ImbalancedChen.Part3.ActualConductorWidthLower20261026b
noncomputable section
open Classical Complex
open RoughQuadraticLowRectangle20261026b RoughQuadraticFiniteRectangle20261026b
open RoughFiniteRectangleReciprocal20261026b ActualRoughContourHolomorphic20261026b

def heightMultiplier (c : ℝ) : ℝ:=5+128/c

def widthConstant (c A : ℝ) : ℝ:=
  min (1/274877906944) (min (c/256) (A/(heightMultiplier c)^12))

theorem heightMultiplier_pos {c : ℝ} (hc : 0<c) : 0<heightMultiplier c:=by
  unfold heightMultiplier
  positivity

theorem widthConstant_pos {c A : ℝ} (hc : 0<c) (hA : 0<A) : 0<widthConstant c A:=by
  exact lt_min (by norm_num) (lt_min (div_pos hc (by norm_num))
    (div_pos hA (pow_pos (heightMultiplier_pos hc) 12)))

/-- The actual Hbound is logarithmic in the finite height, except for
the explicitly retained q^eta low-height separation cost. -/
theorem quadraticHeightBound_le {c η H : ℝ} (hc : 0<c) (hη : 0≤η)
    (m : ℕ) [NeZero m] (hH : 0≤H) :
    quadraticHeightBound m H (c*(m : ℝ)^(-η))≤
      heightMultiplier c*(m : ℝ)^η*rectangleLog m H^2 := by
  let D:=rectangleLog m H
  let M:=(rectangleCutoff m H : ℝ)
  have hm : (1 : ℝ)≤m:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hmpos : 0<(m : ℝ):=zero_lt_one.trans_le hm
  have hD : 1≤D:=one_le_rectangleLog m H
  have hDpos : 0<D:=zero_lt_one.trans_le hD
  have hMpos : 0<M:=by exact_mod_cast rectangleCutoff_pos m H
  have hblock : H+1≤((Nat.floor (H+1)+1 : ℕ) : ℝ):=by
    exact (Nat.lt_floor_add_one (H+1)).le
  have hHM : H+1≤M:=by
    apply hblock.trans
    dsimp [M,rectangleCutoff]
    push_cast
    exact le_mul_of_one_le_left (by positivity) hm
  have hM1 : 1≤M:=by linarith
  have hlog : Real.log (2*(H+1)+2)≤Real.log 4+Real.log M:=by
    have hl:=Real.log_le_log (by positivity : 0<2*(H+1)+2)
      (show 2*(H+1)+2≤4*M by linarith)
    rw [Real.log_mul (by norm_num : (4 : ℝ)≠0) hMpos.ne'] at hl
    exact hl
  have hlog4 : Real.log (4 : ℝ)≤3:=by
    simpa using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<4)
  have hr : 0<c*(m : ℝ)^(-η):=mul_pos hc (Real.rpow_pos_of_pos hmpos _)
  have hinv : 1/(2*lowHeight m H (c*(m : ℝ)^(-η)))=
      (128/c)*(m : ℝ)^η*D^2:=by
    unfold lowHeight
    rw [Real.rpow_neg hmpos.le]
    dsimp [D]
    field_simp [hc.ne',hDpos.ne',(Real.rpow_pos_of_pos hmpos η).ne']
    ring
  have hhead : 2+Real.log M+Real.log (2*(H+1)+2)≤5*D:=by
    have hDeq : D=1+Real.log M:=rfl
    linarith
  have hmpow : 1≤(m : ℝ)^η:=Real.one_le_rpow hm hη
  have hD2 : D≤D^2:=by nlinarith [sq_nonneg (D-1)]
  have hDgrow : D≤(m : ℝ)^η*D^2:=
    hD2.trans (le_mul_of_one_le_left (sq_nonneg D) hmpow)
  unfold quadraticHeightBound
  rw [hinv]
  change 2+Real.log M+Real.log (2*(H+1)+2)+(128/c)*(m : ℝ)^η*D^2≤_
  calc
    _ ≤ 5*D+(128/c)*(m : ℝ)^η*D^2:=add_le_add_right hhead _
    _ ≤ 5*((m : ℝ)^η*D^2)+(128/c)*(m : ℝ)^η*D^2:=by linarith
    _ = _:=by unfold heightMultiplier; ring

/-- Exact scalar lower bound for the intersection of all genuine
nonquadratic and quadratic branches, including the low-height branch. -/
theorem scalar_width_lower {c A η H : ℝ} (hc : 0<c) (hA : 0<A) (hη : 0<η)
    (m : ℕ) [NeZero m] (hH : 0≤H) :
    widthConstant c A*(m : ℝ)^(-14*η)/(rectangleLog m H)^24≤
      min (nonquadraticWidth m H)
        (quadraticRectangleWidth A η m H (c*(m : ℝ)^(-η))) := by
  let D:=rectangleLog m H
  let k:=widthConstant c A
  let v:=(m : ℝ)^(-14*η)/D^24
  let r:=c*(m : ℝ)^(-η)
  have hm : (1 : ℝ)≤m:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hmpos : 0<(m : ℝ):=zero_lt_one.trans_le hm
  have hD : 1≤D:=one_le_rectangleLog m H
  have hDpos : 0<D:=zero_lt_one.trans_le hD
  have hk : 0<k:=widthConstant_pos hc hA
  have hrad : 0<r:=mul_pos hc (Real.rpow_pos_of_pos hmpos _)
  have hk0 : k≤1/274877906944:=min_le_left _ _
  have hkQuarter : k≤1/4:=hk0.trans (by norm_num)
  have hkOne : k≤1:=hkQuarter.trans (by norm_num)
  have hkc : k≤c/256:=(min_le_right _ _).trans (min_le_left _ _)
  have hkA : k≤A/(heightMultiplier c)^12:=(min_le_right _ _).trans (min_le_right _ _)
  have hmn : 0≤(m : ℝ)^(-14*η):=(Real.rpow_pos_of_pos hmpos _).le
  have hmn1 : (m : ℝ)^(-14*η)≤1:=
    Real.rpow_le_one_of_one_le_of_nonpos hm (by linarith)
  have hv0 : 0≤v:=by dsimp [v]; positivity
  have hv1 : v≤1:=by
    unfold v
    exact (div_le_one (pow_pos hDpos 24)).2 (hmn1.trans (one_le_pow₀ hD 24))
  have hvD : v≤1/D:=by
    simpa only [v,pow_one] using
      div_le_div₀ hmn hmn1 (pow_pos hDpos 1) (pow_le_pow_right₀ hD (by norm_num : 1≤24))
  have hv9 : v≤1/D^9:=
    div_le_div₀ hmn hmn1 (pow_pos hDpos 9) (pow_le_pow_right₀ hD (by norm_num))
  have hv2 : v≤(m : ℝ)^(-η)/D^2:=by
    exact div_le_div₀ hmn
      (Real.rpow_le_rpow_of_exponent_le hm (by linarith))
      (pow_pos hDpos 2) (pow_le_pow_right₀ hD (by norm_num))
  have hquarter : k*v≤1/4:=
    (mul_le_mul hkQuarter hv1 hv0 (by norm_num)).trans_eq (by ring)
  have hsmall : k*v≤1/D:=
    (mul_le_mul_of_nonneg_right hkOne hv0).trans (by simpa only [one_mul] using hvD)
  have hlow : k*v≤lowHeight m H r:=by
    calc
      _ ≤ (c/256)*((m : ℝ)^(-η)/D^2):=
        mul_le_mul hkc hv2 hv0 (by positivity)
      _ = _:=by dsimp [lowHeight,r,D]; ring
  have hlog9 : k*v≤1/(274877906944*D^9):=by
    calc
      _ ≤ (1/274877906944)*(1/D^9):=
        mul_le_mul hk0 hv9 hv0 (by norm_num)
      _ = _:=by ring
  have hHpos : 0<quadraticHeightBound m H r:=quadraticHeightBound_pos m hH hrad
  have hKpos : 0<heightMultiplier c:=heightMultiplier_pos hc
  have hmηpos : 0<(m : ℝ)^η:=Real.rpow_pos_of_pos hmpos _
  have hHpow : (quadraticHeightBound m H r)^12≤
      (heightMultiplier c)^12*((m : ℝ)^η)^12*D^24:=by
    calc
      _ ≤ (heightMultiplier c*(m : ℝ)^η*D^2)^12:=
        pow_le_pow_left₀ hHpos.le (quadraticHeightBound_le hc hη.le m hH) 12
      _ = _:=by rw [mul_pow,mul_pow,← pow_mul]; norm_num <;> ring
  have hmpow : (m : ℝ)^(-14*η)*((m : ℝ)^η)^12=(m : ℝ)^(-2*η):=by
    rw [← Real.rpow_mul_natCast hmpos.le,← Real.rpow_add hmpos]
    congr 1
    ring
  have hhigh : k*v≤A*(m : ℝ)^(-2*η)/(quadraticHeightBound m H r)^12:=by
    calc
      _ ≤ (A/(heightMultiplier c)^12)*v:=mul_le_mul_of_nonneg_right hkA hv0
      _ = A*(m : ℝ)^(-2*η)/((heightMultiplier c)^12*((m : ℝ)^η)^12*D^24):=by
        dsimp [v]
        rw [← hmpow]
        field_simp [hKpos.ne',hDpos.ne',hmηpos.ne']
        ring
      _ ≤ _:=div_le_div_of_nonneg_left (by positivity) (pow_pos hHpos 12) hHpow
  have heq : widthConstant c A*(m : ℝ)^(-14*η)/(rectangleLog m H)^24=k*v:=by
    dsimp [k,v,D]
    ring
  rw [heq]
  apply le_min
  · exact le_min hquarter hlog9
  · apply le_min
    · exact le_min (hquarter.trans (by norm_num)) (le_min hsmall hlow)
    · exact le_min hquarter hhigh

theorem conductorWidth_lower {c A η H : ℝ} (hc : 0<c) (hA : 0<A) (hη : 0<η)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hH : 0≤H) :
    widthConstant c A*(χ.conductor : ℝ)^(-14*η)/(rectangleLog χ.conductor H)^24≤
      conductorWidth c A η χ H := by
  letI : NeZero χ.conductor:=⟨χ.conductor_ne_zero⟩
  exact scalar_width_lower hc hA hη χ.conductor hH

end
end ImbalancedChen.Part3.ActualConductorWidthLower20261026b
