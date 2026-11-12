import ImbalancedChen.Part3OriginalPeterssonNormalizedOrbits

namespace ImbalancedChen.Part3.OriginalPositivePeterssonTrace20261112

noncomputable section
open Set Complex UpperHalfPlane Matrix MeasureTheory
open scoped MatrixGroups UpperHalfPlane ModularForm InnerProductSpace ComplexConjugate
open OriginalPeterssonHorizontalMode20261112 OriginalPeterssonLipschitz20261112
open OriginalPeterssonNormalizedOrbits20261112 OriginalPeterssonCuspLimit20261112
open OriginalHeckeLimitFamily20261112 OriginalHeckeCuspExpansion20261112 OriginalHeckeCuspSeries20261112
open OriginalHeckePoisson20261112 OriginalHolomorphicPoincare20261112 OriginalHeckeStripPairing20261112
open OriginalPeterssonCuspOneArithmetic20261112 OriginalPeterssonPretrace20261112
open OriginalPeterssonNormalization20261112 OriginalHolomorphicCuspFilter20261112
open OriginalHolomorphicCuspFrames20261110 OriginalHolomorphicPeterssonSpace20261112
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalNonzeroCuspOneSource20261102 Gamma0ActualCuspsSourceOnly ActualGeneralJBesselSourceOnly
open OriginalCompletedReciprocalSource20261102 OriginalPrimaryPacketRows20261102
open OriginalSignedTraceInput20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalCommonPoissonLanes20261102 P3Period64NativeReconstructionSourceOnly (e e_add)

private theorem inv_phase (t : ℝ) : e (-t)=(e t)⁻¹ := by
  unfold e
  rw [← Complex.exp_neg]
  push_cast
  congr 1;ring

private theorem raw_horizontal (N r h : ℕ) [NeZero N] (f : Forms N r) :
    raw N (NeZero.pos N) r cuspOneMatrix h f =
      horizontal h (fun x => frameForm N (NeZero.pos N) r f cuspOneMatrix (point x)) := by
  change (qExpansion 1 _).coeff h=_
  rw [ModularFormClass.qExpansion_coeff_eq_intervalIntegral _ (by norm_num : (0:ℝ)<1)
    (normalized_frame_unit_strictPeriod N (NeZero.pos N) cuspOneMatrix) h (by norm_num : (0:ℝ)<1),horizontal]
  simp only [one_div_one,Complex.ofReal_one,one_mul]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr;intro x _
  have H := point_phase h x 0
  have D : Function.Periodic.qParam 1 ((x:ℂ)+I)^h=amplitude h*e ((h:ℝ)*x) := by
    simpa [Q,point,Function.Periodic.qParam,e] using H
  rw [D,one_div,mul_inv,inv_phase];ring

def coincidence (N m h : ℕ) : ℂ := if N=1 ∧ m=h then 1 else 0

private theorem diag_horizontal (N r m h : ℕ) [NeZero N] :
    horizontal h (fun x => (N:ℂ)^r*diagonal N m cuspOneMatrix (zeroS,scaledPoint N (point x))) =
      coincidence N m h := by
  by_cases hn : N=1
  · subst N
    have p (x : ℝ) : (1:ℂ)^r*diagonal 1 m cuspOneMatrix (zeroS,scaledPoint 1 (point x)) =
        amplitude m*e ((m:ℝ)*x) := by
      have H := point_phase m x 0
      simpa [diagonal,cuspOneMatrix,heckeSeed,zeroS,scaledPoint,q,Q,point,Function.Periodic.qParam,e] using H
    simp_rw [p]
    rw [horizontal_char];by_cases h' : h=m <;>simp [coincidence,h',eq_comm,amp_ne]
  · have hh : ¬(N:ℤ)∣(1:ℤ) := by
      intro hd
      exact hn (Nat.dvd_one.mp (by exact_mod_cast hd))
    simp [diagonal,cuspOneMatrix,hh,horizontal,coincidence,hn]

private theorem sum_horizontal (N r m h : ℕ) [NeZero N] (hr : 0<r) (hm : 0<m) (hh : 0<h) :
    HasSum (fun C : ℕ+ => cuspSum N C cuspOneMatrix m h*orbital r m h (modulus N C))
      (raw N (NeZero.pos N) r cuspOneMatrix h (Pvector N r 1 m)-coincidence N m h) := by
  let p := fun x => (zeroS,scaledPoint N (point x))
  let D := fun (C : ℕ+) (x : ℝ) => (N:ℂ)^r*denominator N (2*r) m cuspOneMatrix C (p x)
  let S := fun x : ℝ => (N:ℂ)^r*series N (2*r) m cuspOneMatrix (p x)
  let Z := fun x : ℝ => (N:ℂ)^r*diagonal N m cuspOneMatrix (p x)
  have hp (x : ℝ) : (p x).2.im=(N:ℝ) := by simp [p,scaledPoint,point,Complex.mul_im]
  have hc : Continuous (fun x : ℝ => (p x).2) :=
    (Continuous.subtype_mk (continuous_const.mul (continuous_coe.comp point_continuous)) _)
  have hd (C : ℕ+) : Continuous (D C) :=
    continuous_const.mul ((den_holo N r m hr cuspOneMatrix C).continuous.comp hc)
  have hN : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  obtain ⟨b,hb,h0,hB⟩ := layer_majorant N (2*r) m (by omega) hm hN
  let b' := fun C : ℕ+ => (N:ℝ)^r*((N:ℝ)^(1-((2*r:ℕ):ℝ))*(∑' n,b (C,n)))
  have bound (C : ℕ+) (x : ℝ) : ‖D C x‖≤b' C := by
    have H (n : ℤ) : ‖layer N (2*r) m cuspOneMatrix (C,n) (p x)‖≤(N:ℝ)^(1-((2*r:ℕ):ℝ))*b (C,n) := by
      simpa [hp] using hB cuspOneMatrix (C,n) (p x) (hp x).ge
    have V := (hb.prod_factor C).mul_left ((N:ℝ)^(1-((2*r:ℕ):ℝ)))
    have A := V.of_nonneg_of_le (fun _ => norm_nonneg _) H
    dsimp [D,b']
    rw [norm_mul,norm_pow,Complex.norm_natCast,← (denominator_modes N (2*r) m (by omega) cuspOneMatrix C (p x)).tsum_eq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (norm_tsum_le_tsum_norm A).trans ((A.tsum_le_tsum H V).trans_eq (by rw [tsum_mul_left]))
  have T := horizontal_hasSum h D S hd ((hb.prod.mul_left _).mul_left _) bound
    (fun x => (denominators_sum N (2*r) m (by omega) hm cuspOneMatrix (p x)).mul_left _)
  have hu : Continuous S := by
    have H (x) : (∑' C,D C x)=S x := ((denominators_sum N (2*r) m (by omega) hm cuspOneMatrix (p x)).mul_left _).tsum_eq
    simpa only [H] using continuous_tsum hd (show Summable b' from (hb.prod.mul_left _).mul_left _) bound
  have hz : Continuous Z := by
    unfold Z diagonal;split_ifs
    · dsimp [heckeSeed,q,p,scaledPoint,point,zeroS,Function.Periodic.qParam];fun_prop
    · simp
  have F (x) : frameForm N (NeZero.pos N) r (Pvector N r 1 m) cuspOneMatrix (point x)=Z x+S x := by
    rw [← cuspLimit_eq_Pvector N r m hr hm,frame_one]
    change (N:ℂ)^r*((Pzero N r m ∣[2*(r:ℤ)] cuspOneMatrix) (scaledPoint N (point x)))=_
    rw [Pzero_slash N r m hr hm,expansion,mul_add];rfl
  have R : raw N (NeZero.pos N) r cuspOneMatrix h (Pvector N r 1 m)=coincidence N m h+horizontal h S := by
    rw [raw_horizontal]
    simp_rw [F]
    rw [horizontal_add h hz hu,show horizontal h Z=coincidence N m h from diag_horizontal N r m h]
  rw [R,add_sub_cancel_left]
  exact T.congr_fun (fun C => (den_mode N r m h hr hm hh C).symm)

def geometry (N r m h : ℕ) [NeZero N] (C : ℕ+) : ℂ :=
  if good : N.Coprime (C:ℕ) then
    ((2*Real.pi/modulus N C:ℝ):ℂ)*(-I)^(2*r)*cuspOneMatrixSum N C good m h*
      generalJ ((2*r-1:ℕ):ℂ) (argument (Real.sqrt m) (Real.sqrt h) (modulus N C)) else 0

def spectrum (N r m h : ℕ) [NeZero N] : ℂ :=
  ((4*Real.pi*Real.Gamma (2*(r:ℝ)-1):ℝ):ℂ)*
    ∑ i,conj (frameR N (NeZero.pos N) r (formsBasis N r i) 1 m)*
      frameR N (NeZero.pos N) r (formsBasis N r i) cuspOneMatrix h

/-- Petersson's identity on the original two charts, with the actual full ONB, unscaled
hyperbolic measure, absolute modulus sum, and the true diagonal. Includes weight two. -/
theorem petersson (N r m h : ℕ) [NeZero N] (hr : 0<r) (hm : 0<m) (hh : 0<h) :
    Summable (fun C : ℕ+ => ‖geometry N r m h C‖) ∧
      spectrum N r m h=coincidence N m h+∑' C : ℕ+,geometry N r m h C := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  let a := 2*j+1
  let scale : ℂ := ((Real.sqrt m/Real.sqrt h:ℝ):ℂ)^a
  have ht := (sum_horizontal N (j+1) m h (by omega) hm hh).mul_left scale
  have c (C : ℕ+) : scale*(cuspSum N C cuspOneMatrix m h*orbital (j+1) m h (modulus N C)) =
      geometry N (j+1) m h C := by
    by_cases hc : N.Coprime (C:ℕ)
    · rw [good_modulus hc,geometry,if_pos hc,orbital]
      have E : scale*((Real.sqrt h/Real.sqrt m:ℝ):ℂ)^(2*(j+1)-1)=1 := by
        rw [show 2*(j+1)-1=a by dsimp [a];omega,scale,← mul_pow]
        have H : (Real.sqrt (m:ℝ))/(Real.sqrt h)*(Real.sqrt h/Real.sqrt m)=1 := by
          field_simp [(Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)).ne',(Real.sqrt_pos.mpr (Nat.cast_pos.mpr hh)).ne']
        rw [← Complex.ofReal_mul,H,Complex.ofReal_one,one_pow]
      linear_combination (((2*Real.pi/modulus N C:ℝ):ℂ)*(-I)^(2*(j+1))*cuspOneMatrixSum N C hc m h*
        generalJ (((2*(j+1)-1):ℕ):ℂ) (argument (Real.sqrt m) (Real.sqrt h) (modulus N C)))*E
    · simp [bad_modulus hc,geometry,hc]
  have hdiag : scale*coincidence N m h=coincidence N m h := by
    unfold coincidence;split_ifs with hco
    · simp [scale,hco.2,(Real.sqrt_pos.mpr (Nat.cast_pos.mpr hh)).ne']
    · simp
  have hs : scale*raw N (NeZero.pos N) (j+1) cuspOneMatrix h (Pvector N (j+1) 1 m)=
      spectrum N (j+1) m h := by
    simpa [spectrum,scale,a,show 2*((j:ℝ)+1)-1=2*(j:ℝ)+1 by ring] using
      normalized_P_coefficient N j 1 cuspOneMatrix hm hh
  rw [mul_sub,hs,hdiag] at ht
  have H := ht.congr_fun (fun C => (c C).symm)
  exact ⟨summable_norm_iff.mpr H.summable,by rw [H.tsum_eq];ring⟩

/-- The actual licensed positive manuscript marks use this fixed-weight formula. -/
theorem original_positive_petersson (D : OriginalData) (k : BlockKey) (negativeM : Bool)
    (ha : D.block.atom.residue≠0) (hsign : traceNegative D k negativeM=false)
    (N : ℕ) [NeZero N] (r J j : ℕ) (hr : 0<r) {m n : ℕ}
    (hm : m∈commonMBlock J j) (hn : n∈nCarrier D k N) :
    let h := traceIndex D k negativeM N n
    (h.natAbs:ℤ)=h ∧
    Summable (fun C : ℕ+ => ‖geometry N r m h.natAbs C‖) ∧
    spectrum N r m h.natAbs=coincidence N m h.natAbs+∑' C : ℕ+,geometry N r m h.natAbs C := by
  have h := original_positive_basis_pretrace D k negativeM ha hsign N r J j hm hn
  exact ⟨h.1,petersson N r m _ hr (lt_of_lt_of_le (pow_pos (by norm_num : 0<(2:ℕ)) j) (Finset.mem_Ico.mp hm).1)
    (traceIndex_natAbs_pos D k negativeM N hn ha)⟩

end
end ImbalancedChen.Part3.OriginalPositivePeterssonTrace20261112
