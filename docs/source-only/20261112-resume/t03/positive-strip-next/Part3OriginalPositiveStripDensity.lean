import ImbalancedChen.Part3OriginalPositiveCosineInversion

/-! The derivative of the boundary difference is the actual density on cosh w.
All orders retain the positive-line exponential decay needed by compact truncation. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveStripDensity20261112

open Set Filter MeasureTheory Complex
open scoped BigOperators Topology ContDiff
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualPositiveCosineProfile20261112 (testDiv)
open OriginalPositiveJacobiAnger20261112 (oddOrder)
open OriginalPositiveStripData20261112
open OriginalPositiveStripMoments20261112
open OriginalPositiveStripBoundary20261112 (B Q h Q_odd B_entire)
open OriginalPositiveCosineInversion20261112 (C C_apply phi_vanish)
open private div_smooth div_compact jet jet_deriv from ImbalancedChen.Part3ActualPositiveCosineProfile

def tail (ell : D4→ℤ) (Y : ℝ) (r : ℕ) (z : ℂ) :=
  ∑' j,coeff ell Y j*(-(oddOrder j:ℂ))^r*Complex.exp (-(oddOrder j:ℂ)*z)

private theorem jet_major (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (r : ℕ) (R : ℝ) :
    Summable (fun j => ‖coeff ell Y j‖*(oddOrder j:ℝ)^r*(Real.exp R)^(oddOrder j)) :=
  summable_coeff ell hY r (Real.exp_pos _).le

private theorem jet_bound (ell : D4→ℤ) {Y : ℝ} (r j : ℕ) {z : ℂ} {R : ℝ} (hz : ‖z‖≤R) :
    ‖coeff ell Y j*(-(oddOrder j:ℂ))^r*Complex.exp (-(oddOrder j:ℂ)*z)‖≤
      ‖coeff ell Y j‖*(oddOrder j:ℝ)^r*(Real.exp R)^(oddOrder j) := by
  simp only [norm_mul,norm_pow,norm_neg,Complex.norm_natCast,Complex.norm_exp,←Real.exp_nat_mul]
  gcongr
  have h := (neg_le_abs z.re).trans ((Complex.abs_re_le_norm z).trans hz)
  simpa [Complex.mul_re] using mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (oddOrder j) : 0≤(oddOrder j:ℝ))

theorem tail_deriv (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (r : ℕ) (z : ℂ) :
    HasDerivAt (tail ell Y r) (tail ell Y (r+1) z) z := by
  let R := ‖z‖+1
  have hz : z∈Metric.ball (0:ℂ) R := by simpa [R] using lt_add_one ‖z‖
  apply hasDerivAt_tsum_of_isPreconnected (jet_major ell hY (r+1) R) Metric.isOpen_ball
    (convex_ball (0:ℂ) R).isPreconnected _ _ hz _ hz
  · intro j t _
    convert (((hasDerivAt_id t).const_mul (-(oddOrder j:ℂ))).cexp.const_mul
      (coeff ell Y j*(-(oddOrder j:ℂ))^r)) using 1 <;> rw [pow_succ] <;> ring
  · intro j t ht; exact jet_bound ell (r+1) j (by simpa using (Metric.mem_ball.mp ht).le)
  · exact Summable.of_norm_bounded (jet_major ell hY r R) (fun j => jet_bound ell r j (by linarith : ‖z‖≤R))

theorem tail_zero (ell : D4→ℤ) (Y : ℝ) : tail ell Y 0=series ell Y := by
  funext z; simp [tail,series]

theorem tail_pos_bound (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (r : ℕ) :
    ∃ K : ℝ,0≤K ∧ ∀ w : ℝ,0≤w → ‖tail ell Y r w‖≤K*Real.exp (-w) := by
  let a := fun j => ‖coeff ell Y j‖*(oddOrder j:ℝ)^r
  have sa : Summable a := by simpa only [a,one_pow,mul_one] using summable_coeff ell hY r (A:=1) zero_le_one
  refine ⟨∑' j,a j,tsum_nonneg (fun j => by dsimp [a]; positivity),fun w hw => ?_⟩
  rw [←tsum_mul_right]
  apply tsum_of_norm_bounded (sa.mul_right _).hasSum
  intro j
  simp only [a,norm_mul,norm_pow,norm_neg,Complex.norm_natCast,Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have ho : 1≤(oddOrder j:ℝ) := by exact_mod_cast (show 1≤oddOrder j by dsimp [oddOrder]; omega)
  simp [Complex.mul_re]
  nlinarith [mul_le_mul_of_nonneg_right ho hw]

private theorem sin_part (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (s : ℝ) :
    (laplace (fun q => testDiv ell Y q*(I*q)) s +
      laplace (fun q => testDiv ell Y q*(I*q)) (-(s:ℂ)))/(2*I)=C ell hY s := by
  let f := fun q => testDiv ell Y q*(I*q)
  have eq (v : ℂ) : laplace f v=∫ q in Ioi (0:ℝ),f q*Complex.exp (I*q*v) := by
    symm; apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq; simp [f,testDiv,phi_vanish ell hY (not_lt.mp hq)]
  have hi (v : ℂ) : IntegrableOn (fun q => f q*Complex.exp (I*q*v)) (Ioi 0) :=
    ((((div_smooth ell hY).continuous.mul (by fun_prop)).mul (by fun_prop)).integrable_of_hasCompactSupport
      (div_compact ell hY).mul_right.mul_right).integrableOn
  change (laplace f s+laplace f (-(s:ℂ)))/(2*I)=_
  rw [eq,eq,C_apply,←integral_add (hi _) (hi _),div_eq_mul_inv,←integral_mul_const]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  dsimp only [f,testDiv]
  rw [Complex.ofReal_cos,Complex.ofReal_mul,Complex.cos,
    show I*(q:ℂ)*s=((q:ℂ)*s)*I by ring,
    show I*(q:ℂ)*(-(s:ℂ))=(-((q:ℂ)*s))*I by ring]
  field_simp [Complex.ofReal_ne_zero.mpr hq.ne',I_ne_zero] <;> ring_nf <;> simp [I_sq] <;> ring

theorem Q_deriv (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (w : ℝ) :
    HasDerivAt (Q ell Y) ((Real.sinh w:ℂ)*C ell hY (Real.cosh w)-2*tail ell Y 1 w) w := by
  let f := testDiv ell Y
  have D (v : ℝ) := (laplace_deriv f (div_smooth ell hY).continuous (div_compact ell hY)
    (by positivity : 0≤16*Y) (fun q h => by
      obtain ⟨a,b⟩ := div_support ell hY (subset_tsupport _ h)
      rwa [abs_of_nonneg (by linarith : 0≤q)]) (v:ℂ)).comp_ofReal
  have pos := (D (Real.cosh w)).comp w (Real.hasDerivAt_cosh w)
  have neg := (D (-Real.cosh w)).comp w (Real.hasDerivAt_cosh w).neg
  have corr := (tail_deriv ell hY 0 (w:ℂ)).comp_ofReal
  rw [tail_zero] at corr
  have hd := ((pos.sub neg).div_const (2*I)).sub (corr.const_mul 2)
  convert hd using 1
  · funext t
    rw [Q,OriginalPositiveStripBoundary20261112.B_alternate ell hY (-(t:ℂ)),
      B,Complex.cosh_neg,neg_neg,←Complex.ofReal_cosh]
    push_cast; field_simp [I_ne_zero] <;> ring
  · rw [←sin_part ell hY]
    push_cast; field_simp [I_ne_zero] <;> ring

theorem h_formula (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (w : ℝ) :
    h ell Y w=((Real.sinh w:ℂ)*C ell hY (Real.cosh w)-2*tail ell Y 1 w)/(Real.pi:ℂ) := by
  rw [h,(Q_deriv ell hY w).deriv]

theorem h_even (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (w : ℝ) : h ell Y (-w)=h ell Y w := by
  have D := (Q_deriv ell hY (-w)).comp w (hasDerivAt_neg w)
  have E := (Q_deriv ell hY w).neg
  have id : (fun x => Q ell Y (-x))=fun x => -Q ell Y x := funext (Q_odd ell Y)
  rw [show Q ell Y ∘ Neg.neg=(fun x => -Q ell Y x) from id] at D
  have he := D.unique E
  rw [h_formula ell hY,h_formula ell hY]
  congr 1
  linear_combination -he

private theorem h_smooth (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) : ContDiff ℝ ∞ (h ell Y) := by
  have Bc : ContDiff ℝ ∞ (fun x : ℝ => B ell Y x) :=
    ((B_entire ell hY).contDiff.restrictScalars ℝ).comp Complex.ofRealCLM.contDiff
  have Qc : ContDiff ℝ ∞ (Q ell Y) := (Bc.sub (Bc.comp contDiff_neg)).div_const (2*I)
  exact (Qc.deriv (by simp)).div_const _

/-- This includes the origin. Right-line derivative representatives are identities
on all real w, and parity transports their absolute values to the left half-line. -/
theorem h_jets (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (r : ℕ) :
    ∃ K : ℝ,0≤K ∧ ∀ w : ℝ,‖iteratedDeriv r (h ell Y) w‖≤K*Real.exp (-|w|) := by
  let H := h ell Y
  have hs := h_smooth ell hY
  have J (r : ℕ) : ∃ A B : SchwartzMap ℝ ℂ,∀ w : ℝ,
      iteratedDeriv r H w=(jet A B w-2*tail ell Y (r+1) w)/(Real.pi:ℂ) := by
    induction r with
    | zero =>
      exact ⟨0,C ell hY,fun w => by simp [H,h_formula ell hY,jet]⟩
    | succ r ih =>
      obtain ⟨A,B,h⟩ := ih
      have j := jet_deriv A B
      refine ⟨_,_,fun w => ?_⟩
      rw [iteratedDeriv_succ,funext h]
      have dj : Differentiable ℝ (jet A B) := by
        unfold jet; fun_prop (disch := first | exact A.differentiable | exact B.differentiable)
      rw [(((dj w).hasDerivAt.sub ((tail_deriv ell hY (r+1) (w:ℂ)).comp_ofReal.const_mul 2)).div_const _).deriv,j]
  obtain ⟨A,B,hj⟩ := J r
  obtain ⟨T,hT,ht⟩ := tail_pos_bound ell hY (r+1)
  let A0 := SchwartzMap.seminorm ℂ 1 0 A
  let B0 := SchwartzMap.seminorm ℂ 2 0 B
  have a0 : 0≤A0 := apply_nonneg _ _
  have b0 : 0≤B0 := apply_nonneg _ _
  let K := (2*(A0+B0)+2*T)/Real.pi
  have right (w : ℝ) (hw : 0≤w) : ‖iteratedDeriv r H w‖≤K*Real.exp (-w) := by
    let s := Real.cosh w
    have sp : 0<s := Real.cosh_pos _
    have ss : |Real.sinh w|≤s := by simpa [abs_of_nonneg (Real.sinh_nonneg_iff.mpr hw)] using (Real.sinh_lt_cosh w).le
    have ae := SchwartzMap.le_seminorm' ℂ 1 0 A s
    have be := SchwartzMap.le_seminorm' ℂ 2 0 B s
    simp only [Real.norm_eq_abs,abs_of_pos sp,pow_one,iteratedDeriv_zero] at ae be
    have je : s*‖jet A B w‖≤A0+B0 := by
      have p := mul_le_mul_of_nonneg_left (norm_add_le (A s) ((Real.sinh w:ℂ)*B s)) sp.le
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs] at p
      nlinarith only [p,ae,be,mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right ss (norm_nonneg (B s))) sp.le]
    have ew : Real.exp w≤2*s := by dsimp [s]; rw [Real.cosh_eq]; linarith [Real.exp_pos (-w)]
    have jb : ‖jet A B w‖≤2*(A0+B0)*Real.exp (-w) := by
      rw [Real.exp_neg,←div_eq_mul_inv,le_div_iff₀ (Real.exp_pos w)]
      nlinarith only [je,mul_le_mul_of_nonneg_right ew (norm_nonneg (jet A B w))]
    rw [hj,norm_div,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    apply (div_le_iff₀ Real.pi_pos).mpr
    have ne := norm_sub_le (jet A B w) (2*tail ell Y (r+1) w)
    rw [norm_mul,Complex.norm_ofNat] at ne
    dsimp only [K]
    field_simp [Real.pi_ne_zero] <;> nlinarith only [ne,jb,ht w hw]
  refine ⟨K,by dsimp [K]; positivity,fun w => ?_⟩
  by_cases hw : 0≤w
  · simpa only [abs_of_nonneg hw] using right w hw
  · have E : (fun u : ℝ => H (-u))=H := funext (h_even ell hY)
    have D := congrArg (fun f : ℝ→ℂ => iteratedDeriv r f w) E
    have dn := iteratedDeriv_comp_neg r H w
    have eq : ‖iteratedDeriv r H (-w)‖=‖iteratedDeriv r H w‖ := by
      rw [←D,dn,norm_smul]; simp
    simpa only [abs_of_neg (lt_of_not_ge hw),eq] using right (-w) (by linarith)

end ImbalancedChen.Part3.OriginalPositiveStripDensity20261112
end
