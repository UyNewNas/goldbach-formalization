import ImbalancedChen.Part3OriginalPrescribedAbelLift

/-! Fixed-argument negative Bruhat geometry. Positive heights are built
into the integral. The rank-one identity is for the actual conjugated
physical kernel, including the 4π normalization. -/
namespace ImbalancedChen.Part3.OriginalAbelOrbit
noncomputable section
open Set Filter MeasureTheory Complex
open scoped ContDiff Topology
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (e norm_e)
open ActualMarkedBruhatTest20261112 CompactCuspGeometricFubini20261025a
open OriginalAbelGaussian OriginalPrescribedAbelProfile OriginalPrescribedAbelLift20261112
abbrev heights : Measure ℝ := volume.restrict (Ioi 0)

def plane (H : ℝ→ℝ→ℂ) (k x a : ℝ) : ℂ :=
  ((a⁻¹)^2:ℝ) • (H a (k*a/(x^2+a^2))*e (x-k*x/(x^2+a^2)))

def induced (H : ℝ→ℝ→ℂ) (q : ℝ) : ℂ :=
  (4*Real.pi/q:ℝ) • (∫x:ℝ, ∫a,plane H ((q/(4*Real.pi))^2) x a ∂heights)

private lemma opposite_phase (x v : ℝ) : star (e (-x)*e v)=e (x-v) := by
  simp only [e,←Complex.exp_add,Complex.star_def,←Complex.exp_conj,map_add,map_mul,
    Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg,Complex.ofReal_sub]
  congr 1; ring

/-- The atom entering a physical Gram is linear in ψ and conjugate-linear
in φ. Nonpositive first heights in the old full-line integral contribute zero. -/
theorem rank_one (ψ φ : ℝ→ℂ) (hψ : tsupport ψ ⊆ Ioi (0:ℝ)) (q : ℝ) :
    induced (fun a b => ψ a*star (φ b)) q=orbitTest (-1) ψ φ q := by
  let k := (q/(4*Real.pi))^2
  have point (x a : ℝ) : (Ioi (0:ℝ)).indicator (plane (fun a b => ψ a*star (φ b)) k x) a =
      star (orbitTestKernel (-1) ψ φ k x a) := by
    by_cases ha : 0<a
    · rw [indicator_of_mem ha]
      rw [plane,←opposite_phase x (k*x/(x^2+a^2))]
      simp only [orbitTestKernel,radialWeight,Complex.real_smul,star_mul',star_star,
        Int.cast_neg,Int.cast_one,neg_neg,one_mul,Complex.star_def,Complex.conj_ofReal]
      ring
    · have z : ψ a=0 := image_eq_zero_of_notMem_tsupport (fun t => ha (hψ t))
      simp [ha,z,orbitTestKernel,radialWeight,Set.mem_Ioi]
  simp only [induced,orbitTest,Complex.real_smul]
  congr 1
  change (∫x,∫a in Ioi (0:ℝ),plane _ k x a) = _
  simp_rw [←integral_indicator measurableSet_Ioi,point,Complex.star_def,integral_conj]

private def cyl (H : ℝ→ℝ→ℂ) (k s a : ℝ) : ℂ :=
  a⁻¹ • (H a (productAt k s/a)*e ((a-productAt k s/a)*s))
private def val (ell : D4→ℤ) (Y k s w : ℝ) : ℂ :=
  h ell Y (productAt k s)*((g w:ℂ)*e (2*(Real.sqrt (productAt k s)*s)*Real.sinh w))

private lemma density (ell : D4→ℤ) (Y : ℝ) {k : ℝ} (hk : 0<k) (s w : ℝ) :
    let a := dilation (productAt k s) w
    a • cyl (height ell Y) k s a=val ell Y k s w := by
  have hp : 0<productAt k s := by dsimp [productAt]; positivity
  have ha : 0<dilation (productAt k s) w := by unfold dilation; positivity
  dsimp only [cyl,val]
  rw [smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
  exact scaled_density hk s w ell Y

private lemma slope (H : ℝ→ℝ→ℂ) (k : ℝ) {a : ℝ} (ha : 0<a) (s : ℝ) :
    a • plane H k (a*s) a = cyl H k s a := by
  have dn : (a*s)^2+a^2=a^2*(1+s^2) := by ring
  have sq : 1+s^2≠0 := by positivity
  have b : k*a/((a*s)^2+a^2)=productAt k s/a := by
    rw [dn]; dsimp [productAt]; field_simp [ha.ne',sq]; ring
  have ph : a*s-k*(a*s)/((a*s)^2+a^2)=(a-productAt k s/a)*s := by
    rw [dn]; dsimp [productAt]; field_simp [ha.ne',sq]; ring
  simp only [plane,cyl,b,ph,smul_smul]; congr 1; field_simp [ha.ne']

private lemma height_range {p : ℝ} (hp : 0<p) : dilation p '' univ=Ioi 0 := by
  ext a
  constructor
  · rintro ⟨w,_,rfl⟩; dsimp [dilation]; positivity
  · intro ha; refine ⟨Real.log (a/Real.sqrt p),trivial,?_⟩
    dsimp [dilation]; rw [Real.exp_log (div_pos ha (Real.sqrt_pos.mpr hp))]
    field_simp [(Real.sqrt_pos.mpr hp).ne']

private lemma dilation_deriv (p w : ℝ) : HasDerivAt (dilation p) (dilation p w) w :=
  (Real.hasDerivAt_exp w).const_mul _

private lemma dilation_inj {p : ℝ} (hp : 0<p) : InjOn (dilation p) univ :=
  fun _ _ _ _ e => Real.exp_injective (mul_left_cancel₀ (Real.sqrt_pos.mpr hp).ne' e)

private lemma height_integral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {p : ℝ} (hp : 0<p) (I : ℝ→V) :
    (∫a,I a ∂heights)=∫w:ℝ,dilation p w • I (dilation p w) := by
  have C := integral_image_eq_integral_abs_deriv_smul measurableSet_univ
    (fun w _ => (dilation_deriv p w).hasDerivWithinAt) (dilation_inj hp) I
  rw [height_range hp,integral_univ] at C
  have ap (w : ℝ) : 0<dilation p w := by dsimp [dilation]; positivity
  simpa only [abs_of_pos (ap _)] using C

lemma amp_compact (ell : D4→ℤ) {Y k : ℝ} (hY : 0<Y) (hk : 0<k) :
    HasCompactSupport (fun s => h ell Y (productAt k s)) := by
  let A := 1+k/lo Y
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (-A) A))
  intro s hn
  have hp : lo Y<productAt k s := by
    by_contra! he
    have hz := f_jet_below ell hY 0 he
    simp only [iteratedDeriv_zero] at hz
    exact hn (by simp [h,hz])
  have ub : |s|≤A := by
    by_contra! ha
    have hr : k/lo Y<s^2 := by
      have L := div_pos hk (lo_pos hY); dsimp [A] at ha
      nlinarith [sq_abs s,mul_nonneg (sub_nonneg.mpr (show 1≤|s| by linarith)) (abs_nonneg s)]
    have J := (div_lt_iff₀ (lo_pos hY)).mp hr
    have K := (lt_div_iff₀ (by positivity : 0<1+s^2)).mp hp
    nlinarith [lo_pos hY]
  exact abs_le.mp ub

private lemma cylinder_integrable (ell : D4→ℤ) {Y k : ℝ} (hY : 0<Y) (hk : 0<k) :
    Integrable (Function.uncurry (cyl (height ell Y) k)) (volume.prod heights) := by
  have hf := (f_smooth ell hY).continuous.measurable
  have M : Measurable (Function.uncurry (cyl (height ell Y) k)) := by
    unfold Function.uncurry cyl height productAt g h e; fun_prop
  apply (integrable_prod_iff M.aestronglyMeasurable).mpr
  have ppos (s : ℝ) : 0<productAt k s := by dsimp [productAt]; positivity
  have ht (s : ℝ) : Integrable (val ell Y k s) := by
    apply (g_integrable.const_mul ‖h ell Y (productAt k s)‖).mono'
    · unfold val g e; fun_prop
    · filter_upwards with w
      simp [val,norm_e,norm_mul,Real.norm_of_nonneg (g_pos w).le]
  constructor
  · filter_upwards with s
    have J := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_univ
      (fun w _ => (dilation_deriv (productAt k s) w).hasDerivWithinAt)
      (dilation_inj (ppos s)) (cyl (height ell Y) k s)
    rw [height_range (ppos s),integrableOn_univ] at J
    apply J.mpr; apply (ht s).congr
    filter_upwards with w
    rw [abs_of_pos (show 0<dilation (productAt k s) w by dsimp [dilation]; positivity),
      density ell Y hk]
  · have C : Continuous (fun s => h ell Y (productAt k s)) := by
      unfold h productAt; fun_prop (disch := exact (f_smooth ell hY).continuous)
    have base := C.norm.integrable_of_hasCompactSupport (amp_compact ell hY hk).norm
    apply (base.mul_const (∫w:ℝ,g w)).congr
    filter_upwards with s
    rw [height_integral (ppos s),←integral_const_mul]
    apply integral_congr_ae; filter_upwards with w
    have dj := density ell Y hk s w
    have a0 : 0<dilation (productAt k s) w := by dsimp [dilation]; positivity
    simpa [val,norm_mul,norm_e,Complex.norm_real,norm_smul,Real.norm_of_nonneg (g_pos w).le,
      Real.norm_of_nonneg a0.le,smul_eq_mul] using (congrArg norm dj).symm

private lemma x_range {a : ℝ} (ha : 0<a) : (fun s:ℝ => a*s) '' univ=univ := by
  rw [image_univ]; exact (Equiv.mulLeft₀ a ha.ne').surjective.range_eq

private lemma linear_integral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (S : ℝ→V) {a : ℝ} (ha : 0<a) :
      (∫x:ℝ,S x)=∫s:ℝ,a • S (a*s) := by

  have J := integral_image_eq_integral_abs_deriv_smul measurableSet_univ
    (fun s _ => ((hasDerivAt_id s).const_mul a).hasDerivWithinAt)
    (fun _ _ _ _ h => mul_left_cancel₀ ha.ne' h) S
  simpa [x_range ha,abs_of_pos ha,Function.id_def] using J

/-- Finite absolute mass at every fixed physical argument. -/
theorem plane_integrable (ell : D4→ℤ) {Y k : ℝ} (hY : 0<Y) (hk : 0<k) :
    Integrable (Function.uncurry (plane (height ell Y) k)) (volume.prod heights) := by
  let H := height ell Y
  let P := plane H k
  let C := cyl H k
  have CI := cylinder_integrable ell hY hk
  have PM : Measurable (Function.uncurry P) := by
    have hf := (f_smooth ell hY).continuous.measurable
    dsimp [P,plane,H,height,h,g,e,Function.uncurry]; fun_prop
  apply (integrable_prod_iff' PM.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [CI.prod_left_ae,ae_restrict_mem measurableSet_Ioi] with a ac ha
    have J := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_univ
      (fun s _ => ((hasDerivAt_id s).const_mul a).hasDerivWithinAt)
      (fun _ _ _ _ e => mul_left_cancel₀ ha.ne' e) (fun x => P x a)
    simpa [x_range ha,abs_of_pos ha,Function.id_def,P,slope H k ha,integrableOn_univ] using J.mpr
      (by simpa [P,Function.id_def,abs_of_pos ha,slope H k ha,integrableOn_univ] using ac)
  · apply CI.swap.integral_norm_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    rw [linear_integral (fun x => ‖P x a‖) ha]
    apply integral_congr_ae; filter_upwards with s
    simpa [C,P,norm_smul,Real.norm_of_nonneg ha.le,smul_eq_mul] using
      (congrArg norm (slope H k ha s)).symm

/-- Both Fubini changes are justified at this fixed physical argument.
The s support is compact because the original product has a positive floor. -/
theorem orbit_to_slope (ell : D4→ℤ) {Y k : ℝ} (hY : 0<Y) (hk : 0<k) :
    (∫x:ℝ,∫a,plane (height ell Y) k x a ∂heights)=
      ∫s:ℝ,h ell Y (productAt k s)*(Real.exp (-(productAt k s)*s^2):ℝ) := by
  let H := height ell Y
  let P := plane H k
  let C := cyl H k
  have CI := cylinder_integrable ell hY hk
  have PI := plane_integrable ell hY hk
  rw [show (∫x:ℝ,∫a,plane _ k x a ∂heights)=∫a,∫x:ℝ,P x a ∂volume ∂heights from
    integral_integral_swap PI]
  calc
    _ = ∫a,∫s:ℝ,C s a ∂volume ∂heights := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      rw [linear_integral _ ha]; exact integral_congr_ae (ae_of_all _ (slope H k ha))
    _ = ∫s:ℝ,∫a,C s a ∂heights := (integral_integral_swap CI).symm
    _ = _ := by
      apply integral_congr_ae; filter_upwards with s
      have pp : 0<productAt k s := by unfold productAt; positivity
      rw [height_integral pp]
      simp_rw [C,H,density ell Y hk,val,integral_const_mul,transform,mul_pow,Real.sq_sqrt pp.le,neg_mul]

end
end ImbalancedChen.Part3.OriginalAbelOrbit
