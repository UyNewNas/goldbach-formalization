import ImbalancedChen.Part3OriginalHeckeFourierKernel
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries

namespace ImbalancedChen.Part3.OriginalHeckeCuspSeries20261112

noncomputable section
open Complex Set UpperHalfPlane Filter MeasureTheory
open scoped MatrixGroups UpperHalfPlane FourierTransform Topology
open OriginalHolomorphicCuspFilter20261112 OriginalHeckeFourierKernel20261112
open P3Period64NativeReconstructionSourceOnly (e norm_e)

abbrev Params := (Icc (0:ℝ) 1) × ℍ
def freqPrice (n : ℤ) : ℝ := (if n=0 then 1 else 0)+1/(n:ℝ)^2

theorem freqPrice_nonneg (n : ℤ) : 0≤freqPrice n := by
  unfold freqPrice; split_ifs <;> positivity

theorem freqPrice_summable : Summable freqPrice := by
  have h : Summable (fun n : ℤ => if n=0 then (1:ℝ) else 0) :=
    (hasSum_single 0 (fun j hj => if_neg hj)).summable
  exact h.add (Real.summable_one_div_int_pow.mpr (by norm_num : 1<2))

def Mval (m : ℕ) (C : ℕ+) (w : ℍ) : ℝ := 2*Real.pi*m/((C:ℝ)^2*w.im)
def sample (N : ℕ) (n : ℤ) (w : ℍ) : ℝ := (n:ℝ)*w.im/N

def transformed (N k m : ℕ) (C : ℕ+) (n : ℤ) (p : Params) : ℂ :=
  𝓕 (kernel k p.1.val (Mval m C p.2)) (sample N n p.2)

theorem transformed_continuous (N k m : ℕ) (hk : 2≤k) (C : ℕ+) (n : ℤ) :
    Continuous (transformed N k m C n) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let F := fun (p : Params) (u : ℝ) =>
    Complex.exp (((-2*Real.pi*u*sample N n p.2:ℝ):ℂ)*I) • kernel k p.1.val (Mval m C p.2) u
  have hc (u : ℝ) : Continuous (fun p : Params => F p u) := by
    dsimp [F,sample,Mval,kernel,realPower]
    fun_prop (disch := positivity)
  have hm (p : Params) : Continuous (F p) := by
    dsimp [F,sample,Mval,kernel,realPower,column,resolvent]
    fun_prop (disch := first | positivity | intro h; have h' := congrArg Complex.im h; simp at h')
  have hF : transformed N k m C n = (fun p => ∫ u, F p u) := by
    funext p; exact Real.fourier_real_eq_integral_exp_smul _ _
  rw [hF]
  apply tendsto_integral_filter_of_dominated_convergence column
    (.of_forall fun z => (hm z).aestronglyMeasurable) ?_ integrable_inv_one_add_sq
    (.of_forall fun u => (hc u).continuousAt)
  exact .of_forall fun p => .of_forall fun u => by
    simpa [F,norm_smul,Complex.norm_exp] using
      kernel_le hk p.1.property.1 (by dsimp [Mval]; positivity : 0≤Mval m C p.2) u

private theorem Mle {m : ℕ} {C : ℕ+} {w : ℍ} {H : ℝ} (hH : 0<H) (hw : H≤w.im) :
    Mval m C w∈Icc (0:ℝ) (2*Real.pi*m/H) := by
  have hC : (1:ℝ)≤C := by exact_mod_cast C.property
  refine ⟨by dsimp [Mval]; positivity,?_⟩
  apply div_le_div_of_nonneg_left (by positivity) hH
  nlinarith [mul_nonneg (sub_nonneg.mpr (one_le_pow₀ hC (n:=2))) w.im_pos.le]

theorem transformed_price (N : ℕ) [NeZero N] (k m : ℕ) (hk : 2≤k) {H : ℝ} (hH : 0<H) :
    ∃ A : ℝ, 0≤A ∧ ∀ (C : ℕ+) (n : ℤ) (p : Params), H≤p.2.im →
      ‖transformed N k m C n p‖≤A*freqPrice n := by
  let β := 2*Real.pi*H/N
  let A := fourierCost k (2*Real.pi*m/H)*Real.pi
  have hβ : 0<β := by dsimp [β];positivity
  have hA : 0≤A := by dsimp [A,fourierCost];positivity
  refine ⟨Real.pi + A/β^2,by positivity,?_⟩
  intro C n p hp
  have h := Fourier_bounds hk p.1.property (Mle (m:=m) (C:=C) hH hp) (sample N n p.2)
  by_cases hn : n=0
  · subst n; simpa [freqPrice,transformed] using h.1.trans (le_add_of_nonneg_right (by positivity : 0≤A/β^2))
  · have hn' : 0<|(n:ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
    have he : β*|(n:ℝ)| ≤ 2*Real.pi*|sample N n p.2| := by
      dsimp [β,sample]
      rw [abs_div,abs_mul,abs_of_pos p.2.im_pos,abs_of_pos (by exact_mod_cast NeZero.pos N : 0<(N:ℝ))]
      apply (show 2*Real.pi*H/N*|(n:ℝ)|=2*Real.pi*(|(n:ℝ)|*H/N) by ring).le.trans
      gcongr
    have hs := (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) he 2)
      (norm_nonneg _)).trans h.2
    change _ ≤ _ at hs
    have hh : ‖transformed N k m C n p‖≤(A/β^2)*(1/(n:ℝ)^2) := by
      rw [mul_pow,sq_abs] at hs
      change (β^2*(n:ℝ)^2)*‖transformed N k m C n p‖≤A at hs
      rw [show A/β^2*(1/(n:ℝ)^2)=A/(β^2*(n:ℝ)^2) by ring]
      apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hβ) (sq_pos_of_ne_zero (by exact_mod_cast hn)))).mpr
      simpa only [mul_comm] using hs
    rw [freqPrice,if_neg hn,zero_add]
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left Real.pi_pos.le) (by positivity))

/-- Formula of the c,n layer after horizontal Fourier summation. -/
def layer (N k m : ℕ) [NeZero N] (g : SL(2,ℤ)) (i : ℕ+×ℤ) (p : Params) : ℂ :=
  let C := (i.1:ℝ)
  let y := p.2.im
  let s := p.1.val
  (cuspSum N i.1 g (m:ℤ) i.2/(N:ℂ)) *
    ((1/C^k * C^(-2*s) * y^(1-(k:ℝ)) * y^(-s):ℝ):ℂ) *
    transformed N k m i.1 i.2 p * e ((i.2:ℝ)*p.2.re/N)

private theorem less_power {y H s : ℝ} (hH : 0<H) (hy : H≤y) (hs : s∈Icc (0:ℝ) 1) :
    y^(-s)≤max 1 H⁻¹ := by
  have y0 := hH.trans_le hy
  rcases le_total 1 y with h|h
  · exact (Real.rpow_le_one_of_one_le_of_nonpos h (neg_nonpos.mpr hs.1)).trans (le_max_left _ _)
  · have t := Real.rpow_le_rpow_of_exponent_ge y0 h (by linarith [hs.2] : (-1:ℝ)≤ -s)
    rw [Real.rpow_neg_one] at t
    exact t.trans ((inv_anti₀ hH hy).trans (le_max_right _ _))

/-- The majorant is uniform in the actual integral cusp g, all real x, the entire
height half-line y≥H, and s from zero to one. It also retains the high-cusp factor. -/
theorem layer_majorant (N k m : ℕ) [NeZero N] (hk : 2≤k) (hm : 0<m) {H : ℝ} (hH : 0<H) :
    ∃ b : ℕ+×ℤ→ℝ, Summable b ∧ (∀ i, 0≤b i) ∧
      ∀ (g : SL(2,ℤ)) (i : ℕ+×ℤ) (p : Params), H≤p.2.im →
        ‖layer N k m g i p‖ ≤ p.2.im^(1-(k:ℝ))*b i := by
  obtain ⟨A,hA,hF⟩ := transformed_price N k m hk hH
  let B := max 1 H⁻¹*A
  have B0 : 0≤B := mul_nonneg (le_trans zero_le_one (le_max_left ..)) hA
  let v := fun C : ℕ+ => FixedMarkTail.price (m:ℤ) 0 C
  have hv : Summable v := (FixedMarkTail.summable_majorant_price
    (by exact_mod_cast hm.ne' : (m:ℤ)≠0) (by norm_num : (0:ℝ)<1/4)).comp_injective
      (fun _ _ h => Subtype.ext h)
  have vh (C : ℕ+) : (v C) = FixedMarkTail.majorant m C/(C:ℝ)^2 := by
    simp [v,FixedMarkTail.price,C.property.ne',Real.rpow_neg (by positivity : 0≤(C:ℝ)),
      Real.rpow_two,div_eq_mul_inv]
  have v0 (C : ℕ+) : 0≤v C := FixedMarkTail.price_nonneg _ _ _
  refine ⟨fun i => B*(v i.1*freqPrice i.2),
    (hv.mul_of_nonneg freqPrice_summable v0 freqPrice_nonneg).mul_left B,
    fun i => mul_nonneg B0 (mul_nonneg (v0 i.1) (freqPrice_nonneg _)),?_⟩
  intro g ⟨C,n⟩ p hy
  have c1 : (1:ℝ)≤C := by exact_mod_cast C.property
  have hc := cuspSum_bound N C g m n (FixedMarkTail.majorant_nonneg m C) (fun h => by
    rw [inverse_swap]; exact FixedMarkTail.physical_le_majorant m C h)
  have hNc : ‖cuspSum N C g m n‖/(N:ℝ) ≤FixedMarkTail.majorant m C := by
    rw [div_le_iff₀ (by exact_mod_cast NeZero.pos N : 0<(N:ℝ))]
    simpa [mul_comm] using hc
  have powC : 1/(C:ℝ)^k ≤ 1/(C:ℝ)^2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ c1 hk)
  have powS := Real.rpow_le_one_of_one_le_of_nonpos c1 (by nlinarith [p.1.property.1] : -2*p.1.val≤0)
  have posY := p.2.im_pos
  rw [layer]
  simp only [norm_mul,norm_div,Complex.norm_natCast,Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0≤1/(C:ℝ)^k*(C:ℝ)^(-2*p.1.val)*
        p.2.im^(1-(k:ℝ))*p.2.im^(-p.1.val)),norm_e,mul_one]
  calc
    _ ≤ FixedMarkTail.majorant m C * (1/(C:ℝ)^2*1*p.2.im^(1-(k:ℝ))*max 1 H⁻¹) *
        (A*freqPrice n) := by gcongr <;> first | assumption | exact hF C n p hy | exact less_power hH hy p.1.property
    _ = _ := by rw [vh];dsimp [B];ring

def series (N k m : ℕ) [NeZero N] (g : SL(2,ℤ)) (p : Params) : ℂ :=
  ∑' i : ℕ+×ℤ, layer N k m g i p

theorem series_continuous_above (N k m : ℕ) [NeZero N] (g : SL(2,ℤ))
    (hk : 2≤k) (hm : 0<m) {H : ℝ} (hH : 0<H) :
    ContinuousOn (series N k m g) {p : Params | H≤p.2.im} := by
  obtain ⟨b,hb,h0,hbound⟩ := layer_majorant N k m hk hm hH
  apply continuousOn_tsum (u:=fun i => H^(1-(k:ℝ))*b i) ?_ (hb.mul_left _) ?_
  · intro ⟨C,n⟩
    apply Continuous.continuousOn
    unfold layer
    have hK := transformed_continuous N k m hk C n
    unfold e
    fun_prop (disch := positivity)
  · intro i p hp
    exact (hbound g i p hp).trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hH hp (by have h : 2≤(k:ℝ) := by exact_mod_cast hk; linarith))
      (h0 i))

theorem high_cusp_bound (N k m : ℕ) [NeZero N] (hk : 2≤k) (hm : 0<m) :
    ∃ K : ℝ, 0≤K ∧ ∀ (g : SL(2,ℤ)) (p : Params), 1≤p.2.im →
      ‖series N k m g p‖≤K*p.2.im^(1-(k:ℝ)) := by
  obtain ⟨b,hb,h0,hbound⟩ := layer_majorant N k m hk hm (H:=1) (by norm_num)
  refine ⟨∑' i,b i,tsum_nonneg h0,fun g p hp => ?_⟩
  let F := layer N k m g
  have hsum := (hb.mul_left (p.2.im^(1-(k:ℝ)))).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => hbound g i p hp)
  exact (norm_tsum_le_tsum_norm hsum).trans ((hsum.tsum_le_tsum (fun i => hbound g i p hp)
    (hb.mul_left _)).trans_eq (by rw [tsum_mul_left,mul_comm]))

end
end ImbalancedChen.Part3.OriginalHeckeCuspSeries20261112
