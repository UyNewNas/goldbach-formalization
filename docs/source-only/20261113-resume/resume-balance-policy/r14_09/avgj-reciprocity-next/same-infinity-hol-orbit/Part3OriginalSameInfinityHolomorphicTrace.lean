import ImbalancedChen.Part3OriginalSameInfinityHolomorphicBessel

/-! Apply the existing Petersson pretrace and Hecke-limit construction
to the recovered identity-frame Bessel orbit at all positive weights. -/
namespace ImbalancedChen.Part3.OriginalSameInfinityHolomorphicTrace20261113
noncomputable section
open Set Finset Complex UpperHalfPlane Matrix MeasureTheory
open scoped MatrixGroups UpperHalfPlane ModularForm ComplexConjugate
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalSameInfinityHolomorphicBessel20261113
open OriginalPeterssonHorizontalMode20261112 OriginalPeterssonLipschitz20261112
open OriginalHeckeCuspExpansion20261112 OriginalHeckeCuspSeries20261112 OriginalHeckePoisson20261112
open OriginalHeckeLimitFamily20261112 OriginalPeterssonCuspLimit20261112
open OriginalPeterssonPretrace20261112 OriginalPeterssonNormalization20261112
open OriginalHolomorphicCuspFrames20261110 OriginalHolomorphicPeterssonSpace20261112
open OriginalHeckeStripPairing20261112 OriginalHolomorphicPoincare20261112
open OriginalSmoothPoissonTail ActualGeneralJBesselSourceOnly OriginalPeterssonNormalizedOrbits20261112 (orbital)
open OriginalHolomorphicCuspFilter20261112 (inverse_swap)
open P3Period64NativeReconstructionSourceOnly (e)

private theorem raw_horizontal (N r h : ℕ) [NeZero N] (f : Forms N r) :
    raw N (NeZero.pos N) r 1 h f =horizontal h (fun x => f (point x)) := by
  have frame : (fun w : ℍ => frameForm N (NeZero.pos N) r f (1 : SL(2,ℤ)) w)=f := by
    funext w
    rw [frameForm_apply,(two_actual_frames N (NeZero.pos N)).1]
    simp
  suffices H : raw N (NeZero.pos N) r 1 h f =
      horizontal h (fun x => frameForm N (NeZero.pos N) r f 1 (point x)) by
    exact H.trans (congrArg (fun F : ℍ→ℂ => horizontal h (fun x => F (point x))) frame)
  change (qExpansion 1 _).coeff h=_
  rw [ModularFormClass.qExpansion_coeff_eq_intervalIntegral _ (by norm_num : (0:ℝ)<1)
    (normalized_frame_unit_strictPeriod N (NeZero.pos N) (1 : SL(2,ℤ))) h (by norm_num : (0:ℝ)<1),horizontal]
  simp only [one_div_one,Complex.ofReal_one,one_mul]
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  have Qx : Function.Periodic.qParam 1 ((x:ℂ)+I)^h=amplitude h*e ((h:ℝ)*x) := by
    simpa [Q,point,Function.Periodic.qParam,e] using point_phase h x 0
  have inv : e (-((h:ℝ)*x))=(e ((h:ℝ)*x))⁻¹ := by
    unfold e
    rw [←Complex.exp_neg]
    push_cast
    congr 1
    ring
  rw [Qx,one_div,mul_inv,inv]
  ring

private theorem diagonal_at (N m : ℕ) [NeZero N] (x : ℝ) :
    diagonal N m (1 : SL(2,ℤ)) (zeroS,point x)=amplitude m*e ((m:ℝ)*x) := by
  simpa [diagonal,heckeSeed,zeroS,q,Q,point,Function.Periodic.qParam,e] using point_phase m x 0

private theorem diagonal_slot (N m h : ℕ) [NeZero N] :
    horizontal h (fun x => diagonal N m 1 (zeroS,point x)) = if m=h then 1 else 0 := by
  simp_rw [diagonal_at]
  rw [horizontal_char]
  by_cases same : m=h <;> simp [same,eq_comm,amp_ne]

private theorem raw_trace (N r m h : ℕ) [NeZero N] (hr : 0<r) (hm : 0<m) (hh : 0<h) :
    HasSum (fun C : ℕ+ => if N∣C.val then kloosterman C.val (h:ℤ) (m:ℤ)*orbital r m h (C:ℝ) else 0)
      (raw N (NeZero.pos N) r 1 h (Pvector N r 1 m) - (if m=h then 1 else 0)) := by
  classical
  let p (x : ℝ) := (zeroS,point x)
  let F (C : ℕ+) (x : ℝ) := denominator N (2*r) m 1 C (p x)
  let S (x : ℝ) := series N (2*r) m 1 (p x)
  let D (x : ℝ) := diagonal N m (1 : SL(2,ℤ)) (p x)
  have hd (C : ℕ+) : Continuous (F C) := (den_holo N r m hr 1 C).continuous.comp point_continuous
  obtain ⟨b,hb,h0,hB⟩ := layer_majorant N (2*r) m (by omega) hm (by norm_num : (0:ℝ)<1)
  have bound (C : ℕ+) (x : ℝ) : ‖F C x‖ ≤ ∑' n : ℤ, b (C,n) := by
    have H (n : ℤ) : ‖layer N (2*r) m 1 (C,n) (p x)‖ ≤ b (C,n) := by
      have im_one : (p x).2.im=1 := by simp [p,point]
      simpa only [im_one,Real.one_rpow,one_mul] using hB 1 (C,n) (p x) im_one.ge
    have Fnorm := (hb.prod_factor C).of_nonneg_of_le (fun n => norm_nonneg _) H
    rw [show F C x=∑' n : ℤ,layer N (2*r) m 1 (C,n) (p x) from
      (denominator_modes N (2*r) m (by omega) 1 C (p x)).tsum_eq.symm]
    exact (norm_tsum_le_tsum_norm Fnorm).trans (Fnorm.tsum_le_tsum H (hb.prod_factor C))
  have sum (x : ℝ) : HasSum (fun C => F C x) (S x) := denominators_sum N (2*r) m (by omega) hm 1 (p x)
  have T := horizontal_hasSum h F S hd hb.prod bound sum
  have cs : Continuous S := by
    have e : S=fun x => ∑' C,F C x := funext fun x => (sum x).tsum_eq.symm
    rw [e]
    exact continuous_tsum hd hb.prod bound
  have cd : Continuous D := by
    simp only [D,p,diagonal_at]
    unfold e
    fun_prop
  have E : raw N (NeZero.pos N) r 1 h (Pvector N r 1 m) =
      (if m=h then 1 else 0)+horizontal h S := by
    rw [raw_horizontal,←cuspLimit_eq_Pvector N r m hr hm]
    change horizontal h (fun x => D x+S x)=_
    rw [horizontal_add h cd cs]
    exact congrArg (fun z : ℂ => z+horizontal h S) (diagonal_slot N m h)
  rw [E,add_sub_cancel_left]
  exact T.congr_fun (fun C => (same_infinity_den_mode N r m h hr hm hh C).symm)

/-- Native positive-weight Petersson sector on two identity frames.
The diagonal is identical at every level, and the full positive
denominator is the integer C on the support N|C. Includes weight two. -/
theorem same_infinity_petersson (N j m h : ℕ) [NeZero N] (hm : 0<m) (hh : 0<h) :
    let kappa := 2*(j+1)
    let geo := fun C : ℕ+ => if N∣C.val then
      ((2*Real.pi/(C:ℝ):ℝ):ℂ)*(-I)^kappa*kloosterman C.val (m:ℤ) (h:ℤ)*
        generalJ ((2*j+1:ℕ):ℂ) (argument (Real.sqrt m) (Real.sqrt h) (C:ℝ)) else 0
    Summable (fun C => ‖geo C‖) ∧
      ((4*Real.pi*Real.Gamma (2*(j:ℝ)+1):ℝ):ℂ)*
        ∑ i,conj (frameR N (NeZero.pos N) (j+1) (formsBasis N (j+1) i) 1 m)*
          frameR N (NeZero.pos N) (j+1) (formsBasis N (j+1) i) 1 h =
        (if m=h then 1 else 0)+∑' C : ℕ+,geo C := by
  let a := 2*j+1
  let scale := ((Real.sqrt m/Real.sqrt h:ℝ):ℂ)^a
  have T := (raw_trace N (j+1) m h (by omega) hm hh).mul_left scale
  have cancel : scale*((Real.sqrt h/Real.sqrt m:ℝ):ℂ)^a=1 := by
    rw [scale,←mul_pow]
    have equal : (Real.sqrt (m:ℝ)/Real.sqrt h)*(Real.sqrt (h:ℝ)/Real.sqrt m)=1 := by
      field_simp [(Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)).ne',(Real.sqrt_pos.mpr (Nat.cast_pos.mpr hh)).ne']
    rw [←Complex.ofReal_mul,equal,Complex.ofReal_one,one_pow]
  have diag : scale*(if m=h then (1:ℂ) else 0)=if m=h then 1 else 0 := by
    by_cases equal : m=h
    · simp [equal,scale,(Real.sqrt_pos.mpr (Nat.cast_pos.mpr hh)).ne']
    · simp [equal]
  have norm := normalized_P_coefficient N j 1 1 hm hh
  have norm' : scale*raw N (NeZero.pos N) (j+1) 1 h (Pvector N (j+1) 1 m)=
      ((4*Real.pi*Real.Gamma (2*(j:ℝ)+1):ℝ):ℂ)*
      ∑ i,conj (frameR N (NeZero.pos N) (j+1) (formsBasis N (j+1) i) 1 m)*
          frameR N (NeZero.pos N) (j+1) (formsBasis N (j+1) i) 1 h := by
    simpa only [scale,a,Complex.ofReal_pow] using norm
  rw [mul_sub,norm',diag] at T
  dsimp only
  let geo (C : ℕ+) := if N∣C.val then
    ((2*Real.pi/(C:ℝ):ℝ):ℂ)*(-I)^(2*(j+1))*kloosterman C.val (m:ℤ) (h:ℤ)*
      generalJ ((2*j+1:ℕ):ℂ) (argument (Real.sqrt m) (Real.sqrt h) (C:ℝ)) else 0
  have e (C : ℕ+) : scale*(if N∣C.val then kloosterman C.val (h:ℤ) (m:ℤ)*orbital (j+1) m h (C:ℝ) else 0)=geo C := by
    unfold geo orbital
    split_ifs
    · letI : NeZero C.val := ⟨C.property.ne'⟩
      rw [show 2*(j+1)-1=a by dsimp [a];omega,inverse_swap C.val (h:ℤ) (m:ℤ)]
      linear_combination (((2*Real.pi/(C:ℝ):ℝ):ℂ)*(-I)^(2*(j+1))*kloosterman C.val (m:ℤ) (h:ℤ)*
        generalJ (a:ℂ) (argument (Real.sqrt m) (Real.sqrt h) (C:ℝ)))*cancel
    · simp
  have H := T.congr_fun (fun C => (e C).symm)
  exact ⟨summable_norm_iff.mpr H.summable,by rw [H.tsum_eq]; ring⟩

end
end ImbalancedChen.Part3.OriginalSameInfinityHolomorphicTrace20261113
