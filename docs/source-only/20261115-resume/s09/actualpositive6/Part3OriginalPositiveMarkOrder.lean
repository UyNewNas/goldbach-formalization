import ImbalancedChen.Part3OriginalFixedMarkTraceGrowth
import ImbalancedChen.Part3OriginalSwitchedRegularTracePrice
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Fix the quotient and a positive mark before sending the cutoff scale
to infinity. The finite exceptional family has a positive test floor at
that quotient. The only conclusion is vanishing of the positive coefficient. -/
namespace ImbalancedChen.Part3.OriginalPositiveMarkOrder20261113
noncomputable section
open Finset Filter Real Complex
open scoped Classical MatrixGroups
open OriginalFixedMarkTraceGrowth20261113 (geometry)
open OriginalExceptionalJNativeCompletion20261110 (exceptional tau mem_exceptional classicalLevels mem_classicalLevels)
open OriginalExceptionalNativeEnvelope20261113 (native_band)
open ActualPositiveNativeDiagonal20261112 (nativeWeight complementaryHeight complementary_range)
open ActualCuspBasisWhittakerCoefficients20261102 (basisR basisR_eq_half_native)
open OriginalSwitchedTraceProjection20261113 (complement mark_split pair R C H)
open OriginalSwitchedLevelIdentity20261113 (single spectral)
open OriginalSwitchedHolTraceError20261113 (test)
open OriginalSwitchedProjectionMask20261113 (hol_price)
open OriginalSwitchedRegularTracePrice20261113 (regular_dyad log_allowance)
open OriginalSwitchedRegularMarkExchange20261113 (principal incoming)
open OriginalSameInfinityWeightedHol20261113 (holSum)
open OriginalSameInfinityTensorSpectrum20261113 (disc)
open OriginalSwitchedInitialTraceGeometry20261113 (mark)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open ActualIntervalGeometricSumSourceOnly (phaseAt)

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

private theorem diagonal (m : ℕ+) (f : ℕ+→ℕ+→ℂ) :
    pair m.property (m.val+1) 0 f=f m m := by
  let S := Finset.Ico m.val (m.val+1)
  let lift (n : ℕ) : ℕ+ := ⟨max 1 n,by omega⟩
  have eq (n : ↥S) : mark m.val m.property n=lift n.val := by
    apply Subtype.ext
    exact (max_eq_right (show 1≤n.val from (mark m.val m.property n).property)).symm
  have id : lift m.val=m := by apply Subtype.ext;exact max_eq_right m.property
  change (∑ n : ↥S,∑ k : ↥S,star (phaseAt 0 n.val)*phaseAt 0 k.val*
    f (mark m.val m.property n) (mark m.val m.property k))=_
  simp_rw [eq]
  simp only [Finset.univ_eq_attach,Finset.sum_attach,S,Nat.Ico_succ_singleton,Finset.sum_singleton,id,
    phaseAt,Complex.ofReal_zero,mul_zero,zero_mul,Complex.exp_zero,star_one,mul_one,one_mul]

private theorem others (q m : ℕ+) {v : ℝ} (vp : 0<v) :
    ∃ K : ℝ,0≤K ∧ ∀ Y≥(1:ℝ),
      ‖principal q m m (single Y)‖+‖incoming q m m (single Y)‖+‖holSum q m m (single Y)‖≤K*Y^v := by
  obtain ⟨j,l,h⟩ := exists_nat_pow_near (show 1≤m.val from m.property) (by decide : 1<(2:ℕ))
  let M := classicalMScale j
  let B := (q.val:ℝ)/2
  have qp : 0<(q.val:ℝ) := by exact_mod_cast q.property
  have bp : 0<B := half_pos qp
  have qmem : q∈classicalLevels B := (mem_classicalLevels B q).mpr ⟨by dsimp only [B];linarith only [qp],
    by dsimp only [B];linarith⟩
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  let V := (B+M^(1+(1:ℝ)))*M
  have vn : 0≤V := by dsimp only [V]; positivity
  obtain ⟨A,an,F⟩ := regular_dyad (by norm_num : (0:ℝ)<1)
  obtain ⟨D,dn,G⟩ := hol_price (by norm_num : (0:ℝ)<1)
  obtain ⟨P,pp,L⟩ := log_allowance vp
  refine ⟨(A*P+D)*V,mul_nonneg (add_nonneg (mul_nonneg an pp.le) dn) vn,fun Y y1 => ?_⟩
  have yp := zero_lt_one.trans_le y1
  let n := m.val+1
  have H := F false j m.val n l (show n≤2^(j+1) from h) Y 1 B 0 y1 zero_lt_one bp
  let U := fun z : ℕ+ => ‖R false z m.property n Y 1 0‖+‖C false z m.property n Y 1 0‖
  let Z := fun z : ℕ+ => ‖OriginalSwitchedTraceProjection20261113.H false z m.property n Y 1 0‖
  have up : U q≤(A*(1+Real.log (2*Y)^2))*V := (Finset.single_le_sum
    (f:=U) (fun z _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) qmem).trans
    (H.trans_eq (by dsimp only [V,M];ring))
  have zp : Z q≤D*V := (Finset.single_le_sum (f:=Z) (fun z _ => norm_nonneg _) qmem).trans
    ((G false j m.val n l (show n≤2^(j+1) from h) Y 1 B 0 y1 zero_lt_one bp).trans_eq (by dsimp only [V,M];ring))
  have ueq : U q=‖principal q m m (single Y)‖+‖incoming q m m (single Y)‖ := by
    dsimp only [U,R,C,n,test,Bool.false_eq_true,if_false]
    rw [diagonal,diagonal]
  have zeq : Z q=‖holSum q m m (single Y)‖ := by
    dsimp only [Z,OriginalSwitchedTraceProjection20261113.H,n,test,Bool.false_eq_true,if_false]
    rw [diagonal]
  rw [ueq] at up
  rw [zeq] at zp
  have reg := up.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (L Y y1) an) vn)
  have hol := mul_le_mul_of_nonneg_left (Real.one_le_rpow y1 vp.le) (mul_nonneg dn vn)
  nlinarith only [reg,zp,hol]

private theorem slot_floor (q m : ℕ+) :
    ∃ c Y₀ : ℝ,0<c ∧ 1≤Y₀ ∧ ∀ Y≥Y₀,∀ i : ↥(exceptional q),
    c*Y^(tau q i.val)*‖basisR q.val q.property i.val 1 (m.val:ℤ)‖^2≤
      (complement q m m (single Y)).re := by
  let J := insert (0:ℝ) ((exceptional q).image (tau q))
  have ne : J.Nonempty := ⟨0,mem_insert_self _ _⟩
  let T := J.max' ne
  have tp : 0≤T := le_max' _ _ (mem_insert_self _ _)
  have t1 : T<1 := by
    change J.max' ne<1
    rcases mem_insert.mp (max'_mem J ne) with e|e
    · change J.max' ne=0 at e
      rw [e];norm_num
    · obtain ⟨i,hi,eq⟩ := mem_image.mp e
      rw [←eq]
      have a := (complementary_range q.val ((mem_exceptional q i).mp hi).2).2.1
      change 2*complementaryHeight q.val i<1
      linarith
  obtain ⟨c,_,Y₀,cp,_,y1,P⟩ := native_band tp t1
  refine ⟨c,Y₀,cp,y1,fun Y hy i => ?_⟩
  let f := fun i : ↥(exceptional q) => (nativeWeight q.val (single Y) i.val).re*
    ‖basisR q.val q.property i.val 1 (m.val:ℤ)‖^2
  have yp := zero_lt_one.trans_le (y1.trans hy)
  have cap (i : ↥(exceptional q)) : tau q i.val≤T := le_max' _ _ (mem_insert_of_mem (mem_image.mpr ⟨i.val,i.property,rfl⟩))
  have bound (i : ↥(exceptional q)) : c*Y^(tau q i.val)*‖basisR q.val q.property i.val 1 (m.val:ℤ)‖^2≤f i :=
    mul_le_mul_of_nonneg_right (P Y hy q i (cap i)).1 (sq_nonneg _)
  have nn (i : ↥(exceptional q)) : 0≤f i := (mul_nonneg (mul_nonneg cp.le (Real.rpow_nonneg yp.le _)) (sq_nonneg _)).trans (bound i)
  apply (bound i).trans ((Finset.single_le_sum (f:=f) (fun i _ => nn i) (mem_univ i)).trans_eq ?_)
  simp only [complement,Complex.re_sum]
  apply sum_congr rfl
  intro i _
  simp only [f,disc,Complex.star_def,←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

theorem high_positive_zero (q m : ℕ+) (i : ↥(exceptional q)) (high : 3/4<tau q i.val) :
    basisR q.val q.property i.val 1 (m.val:ℤ)=0 := by
  let s := tau q i.val
  let v := (s+3/4)/2
  have vb : 3/4<v := by dsimp only [v,s];linarith only [high]
  have vs : v<s := by dsimp only [v,s];linarith only [high]
  have vp : 0<v := by linarith only [vb]
  let δ := 1-v
  have hδ : δ<1/4 := by dsimp only [δ];linarith only [vb]
  obtain ⟨A,an,P⟩ := geometry m hδ
  obtain ⟨D,dn,S⟩ := others q m vp
  obtain ⟨c,Y₀,cp,y1,F⟩ := slot_floor q m
  let r := ‖basisR q.val q.property i.val 1 (m.val:ℤ)‖^2
  by_contra nz
  have rp : 0<r := sq_pos_of_pos (norm_pos_iff.mpr nz)
  have raw (Y : ℝ) (hy : Y₀≤Y) : (c*r)*Y^(s-v)≤A+D := by
    have y := y1.trans hy
    have yp := zero_lt_one.trans_le y
    have a := P q yp
    rw [show 1-δ=v by dsimp only [δ];ring] at a
    have b := S Y y
    have split := mark_split false q m m (Q:=1) y zero_lt_one
    change spectral q m m (single Y)=complement q m m (single Y)+principal q m m (single Y)+
      incoming q m m (single Y)+holSum q m m (single Y) at split
    have ex := congrArg Complex.re split
    simp only [Complex.add_re] at ex
    have l := F Y hy i
    change c*Y^s*r≤(complement q m m (single Y)).re at l
    have negre (z : ℂ) : -z.re≤‖z‖ := by simpa only [Complex.neg_re,norm_neg] using Complex.re_le_norm (-z)
    have x : c*Y^s*r≤(A+D)*Y^v := by
      nlinarith only [l,ex,(Complex.re_le_norm (spectral q m m (single Y))).trans a,
        b,negre (principal q m m (single Y)),negre (incoming q m m (single Y)),negre (holSum q m m (single Y))]
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos yp v)).mp
    rw [mul_assoc ((c*r)) (Y^(s-v)),←Real.rpow_add yp,sub_add_cancel]
    nlinarith only [x]
  have growth := (tendsto_rpow_atTop (sub_pos.mpr vs)).eventually_gt_atTop ((A+D)/(c*r))
  obtain ⟨Y,hy,h⟩ := (growth.and (eventually_ge_atTop Y₀)).exists
  have fail := (div_lt_iff₀ (mul_pos cp rp)).mp hy
  exact (not_lt_of_ge (raw Y h)) (by linarith only [fail])

end
end ImbalancedChen.Part3.OriginalPositiveMarkOrder20261113
