import ImbalancedChen.Part3OriginalExceptionalCoreBounds
import ImbalancedChen.Part3ActualPositiveJRotationPair

/-! Quantitative sign and size of the genuine complementary J kernel
on a closed order band below the endpoint one. -/
namespace ImbalancedChen.Part3.OriginalExceptionalBandKernel20261113
noncomputable section
open Set Complex
open OriginalExceptionalCoreBounds20261113 (core_band)
open GeneralComplexISeriesSourceOnly (generalICore) GeneralIOrderHolomorphySourceOnly (analyticAt_generalICore_order)
open ActualGeneralJBesselSourceOnly (generalJ)
open ActualPositiveJRotationPair20261112 (complementaryKernel)

private theorem difference {T s : ℝ} (hs : 0<s) (ht : s≤T) (t1 : T<1) (z : ℂ) (K : ℝ)
    (h : ∀ ν : ℝ,|ν|≤T → ‖deriv (fun μ => generalICore μ z) (ν:ℂ)‖≤K) :
    ‖generalICore (-(s:ℂ)) z-generalICore (s:ℂ) z‖≤2*s*K := by
  let f := fun ν : ℝ => generalICore (ν:ℂ) z
  let g := fun ν : ℝ => deriv (fun μ => generalICore μ z) (ν:ℂ)
  have ord (ν : ℝ) (v : ν∈Icc (-s) s) : -1<(ν:ℂ).re := by simp only [Complex.ofReal_re];linarith only [v.1,ht,t1]
  have hd (ν : ℝ) (v : ν∈Icc (-s) s) : HasDerivWithinAt f (g ν) (Icc (-s) s) ν :=
    (analyticAt_generalICore_order (ν:ℂ) z (ord ν v)).differentiableAt.hasDerivAt.comp_ofReal.hasDerivWithinAt
  have m := (convex_Icc (-s) s).norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun ν v => h ν ((abs_le.mpr v).trans ht))
    (show -s∈Icc (-s) s from ⟨le_rfl,by linarith⟩) (show s∈Icc (-s) s from ⟨by linarith,le_rfl⟩)
  have l : ‖s- -s‖=2*s := by rw [Real.norm_eq_abs,abs_of_nonneg (by linarith)];ring
  rw [l] at m
  rw [norm_sub_rev]
  simpa only [f,Complex.ofReal_neg,mul_comm K] using m

private theorem small_difference {s u c K L : ℝ} (sp : 0<s) (sl : s≤1) (cp : 0<c) (kp : 0<K)
    (lo : 1+2*K/c≤L) (uE : u=Real.exp (-(2*s*L))) :
    0<u ∧ u≤1 ∧ c*s/2≤c*(1-u)-u*(2*s*K) ∧ 1-u≤2*s*L := by
  let p := 2*s*L
  have cL : c*(1+2*K/c)≤c*L := mul_le_mul_of_nonneg_left lo cp.le
  have lp : 0<L := lt_of_lt_of_le (by positivity : 0<1+2*K/c) lo
  have pp : 0≤p := by dsimp [p];positivity
  have up : 0<u := uE ▸ Real.exp_pos _
  have ue : u≤1 := by rw [uE];exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr pp)
  have rem : u*(1+p)≤1 := by
    apply (mul_le_mul_of_nonneg_left (show 1+p≤Real.exp p by linarith only [Real.add_one_le_exp p]) up.le).trans_eq
    rw [uE,←Real.exp_add]; simp [p]
  have cKL : c+2*K≤c*L := by
    have ec : c*(1+2*K/c)=c+2*K := by field_simp [cp.ne'] <;> ring
    simpa only [ec] using cL
  have floor : c/2≤c*(1-s/2) := by nlinarith only [mul_nonneg cp.le (sub_nonneg.mpr sl)]
  have maj : c+2*s*K≤c*(1-s/2)*(1+p) := by
    have hhalf := mul_le_mul_of_nonneg_right floor pp
    dsimp only [p] at hhalf ⊢
    nlinarith only [hhalf,mul_le_mul_of_nonneg_left cKL sp.le,mul_nonneg cp.le sp.le]
  refine ⟨up,ue,?_,?_⟩
  · have a := mul_le_mul_of_nonneg_left maj up.le
    have b := mul_le_mul_of_nonneg_left rem (show 0≤c*(1-s/2) from (by positivity : 0≤c/2).trans floor)
    nlinarith only [a,b]
  · have a := Real.add_one_le_exp (-p)
    rw [uE];dsimp only [p] at a;linarith only [a]

/-- For sufficiently small physical argument the sign is uniform and
the lower exponent is the actual doubled order, also as it tends to
zero. All constants depend only on the upper edge of the order band. -/
theorem band_kernel {T : ℝ} (t0 : 0≤T) (t1 : T<1) :
    ∃ c K δ : ℝ,0<c ∧ 0<K ∧ 0<δ ∧ δ≤1 ∧ ∀ s x : ℝ,0<s → s≤T → 0<x → x≤δ →
      c*(x/2)^(-s)≤(complementaryKernel x (s/2)).re ∧
      ‖complementaryKernel x (s/2)‖≤K*(1+|Real.log (x/2)|)*(x/2)^(-s) := by
  obtain ⟨c,K,d,cp,kp,dp,d1,H⟩ := core_band t0 t1
  let L₀ := 1+2*K/c
  let δ := min d (Real.exp (-L₀))
  have δp : 0<δ := lt_min dp (Real.exp_pos _)
  refine ⟨2*c,4*Real.pi*K,δ,by positivity,by positivity,δp,(min_le_left _ _).trans d1,?_⟩
  intro s x sp st xp xδ
  let b := x/2
  let z : ℂ := -((b:ℂ)^2)
  let P := b^(-s)
  let L := -Real.log b
  let u := Real.exp (-(2*s*L))
  let A := generalICore (-(s:ℂ)) z
  let B := generalICore (s:ℂ) z
  let D := Real.sin (Real.pi*(s/2))
  have bp : 0<b := by dsimp [b];positivity
  have x1 : x≤1 := xδ.trans ((min_le_left _ _).trans d1)
  have Lbig : L₀≤L := by
    have le : b≤Real.exp (-L₀) := (by dsimp [b];linarith : b≤x).trans (xδ.trans (min_le_right _ _))
    have h := Real.log_le_log bp le
    rw [Real.log_exp] at h
    dsimp [L];linarith
  have lp : 0≤L := (by dsimp [L₀];positivity : 0≤L₀).trans Lbig
  have Pp : 0<P := Real.rpow_pos_of_pos bp _
  have hZ : ‖z‖≤d := by
    rw [show ‖z‖=b^2 by simp [z,norm_pow,Complex.norm_real,Real.norm_of_nonneg bp.le]]
    have xx := xδ.trans (min_le_left _ _)
    dsimp [b];nlinarith only [xx,x1,xp, mul_nonneg xp.le (sub_nonneg.mpr x1)]
  have HA := H (-s) (by simpa [abs_neg,abs_of_pos sp] using st) z hZ
  have HB := H s (by simpa only [abs_of_pos sp] using st) z hZ
  have A0 : c≤A.re := by simpa only [A,Complex.ofReal_neg] using HA.1
  have nA : ‖A‖≤K := by simpa only [A,Complex.ofReal_neg] using HA.2.1
  have diff : ‖A-B‖≤2*s*K := difference sp st t1 z K (fun ν hv => (H ν hv z hZ).2.2)
  have diffRe := (abs_le.mp ((Complex.abs_re_le_norm (A-B)).trans diff)).1
  simp only [Complex.sub_re] at diffRe
  obtain ⟨up,ue,small,large⟩ := small_difference sp (st.trans t1.le) cp kp Lbig (show u=Real.exp (-(2*s*L)) from rfl)
  have Pu : b^s=P*u := by
    simp only [P,u,L,Real.rpow_def_of_pos bp,←Real.exp_add]
    congr 1
    ring
  have den : s≤D := by
    have d := Real.le_sin_mul sp.le (st.trans t1.le)
    rwa [show Real.pi/2*s=Real.pi*(s/2) by ring] at d
  have denp : 0<D := sp.trans_le den
  have denU : D≤Real.pi*(s/2) := Real.sin_le (by positivity)
  have E : complementaryKernel x (s/2)=((2*Real.pi*P/D:ℝ):ℂ)*
      (A-(u:ℂ)*B) := by
    rw [complementaryKernel,if_neg (show s/2≠0 by positivity)]
    have a : 2*((s/2:ℝ):ℂ)=(s:ℂ) := by push_cast;ring
    have neg : -2*((s/2:ℝ):ℂ)= -(s:ℂ) := by push_cast;ring
    simp only [a,neg]
    have hm : (b:ℂ)^(-(s:ℂ))=((b^(-s):ℝ):ℂ) := by rw [←Complex.ofReal_neg,←Complex.ofReal_cpow bp.le]
    have hp : (b:ℂ)^(s:ℂ)=((b^s:ℝ):ℂ) := (Complex.ofReal_cpow bp.le s).symm
    simp only [generalJ,hm,hp]
    change (2*(Real.pi:ℂ)/(D:ℂ))*(((b^(-s):ℝ):ℂ)*A-((b^s:ℝ):ℂ)*B)=_
    rw [Pu]
    push_cast
    dsimp only [P]
    ring
  have sc : 0≤2*Real.pi*P/D := by positivity
  have lower : c*s/2≤(A-(u:ℂ)*B).re := by
    rw [Complex.sub_re,Complex.re_ofReal_mul]
    have n := mul_le_mul_of_nonneg_left A0 (sub_nonneg.mpr ue)
    have v := mul_le_mul_of_nonneg_left diffRe up.le
    nlinarith only [small,n,v]
  have upper : ‖A-(u:ℂ)*B‖≤2*s*K*(1+L) := by
    have eq : A-(u:ℂ)*B=((1-u:ℝ):ℂ)*A+(u:ℂ)*(A-B) := by push_cast;ring
    rw [eq]
    apply (norm_add_le _ _).trans
    simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sub_nonneg.mpr ue),Real.norm_of_nonneg up.le]
    have a := mul_le_mul large nA (norm_nonneg _) (by positivity : 0≤2*s*L)
    have b' := mul_le_mul ue diff (norm_nonneg _) zero_le_one
    nlinarith only [a,b']
  rw [E,Complex.re_ofReal_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg sc]
  constructor
  · apply le_trans _ (mul_le_mul_of_nonneg_left lower sc)
    change (2*c)*P≤(2*Real.pi*P/D)*(c*s/2)
    rw [show (2*Real.pi*P/D)*(c*s/2)=(Real.pi*s*(c*P))/D by ring,le_div_iff₀ denp]
    nlinarith only [mul_le_mul_of_nonneg_right denU (by positivity : 0≤2*c*P)]
  · apply (mul_le_mul_of_nonneg_left upper sc).trans
    change (2*Real.pi*P/D)*(2*s*K*(1+L))≤4*Real.pi*K*(1+|Real.log b|)*P
    rw [abs_of_nonpos (show Real.log b≤0 by dsimp [L] at lp;linarith)]
    change (2*Real.pi*P/D)*(2*s*K*(1+L))≤4*Real.pi*K*(1+L)*P
    rw [show (2*Real.pi*P/D)*(2*s*K*(1+L))=(s*(4*Real.pi*K*(1+L)*P))/D by ring,div_le_iff₀ denp]
    simpa only [mul_comm s (4*Real.pi*K*(1+L)*P)] using
      mul_le_mul_of_nonneg_left den (by positivity : 0≤4*Real.pi*K*(1+L)*P)

end
end ImbalancedChen.Part3.OriginalExceptionalBandKernel20261113
