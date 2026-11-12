import ImbalancedChen.P4BOriginalHigherLowKeySupport

namespace ImbalancedChen.P4BOriginalHigherLowLocalWindows
noncomputable section
open VariableEnvelope
open P4BOriginalHigherLowRootRows (Row)
open P4BOriginalHigherLowBins (cover theta)
open P4BOriginalMediumTriplePowers (power power_base power_rpow power_mono positive_le_iff upper_iff)

private theorem scale_error {q s z : ℝ} (hz : 0<z) (hz' : z≤1/400)
    (hq : 1-z≤q) (hq' : q≤1+z) (hs : 0≤s) (hs' : s≤1) :
    s-z≤q*s ∧ q*(s+z)≤s+3*z := by
  constructor
  · nlinarith only [mul_nonneg (sub_nonneg.mpr hq) hs,mul_nonneg hz.le (sub_nonneg.mpr hs')]
  · nlinarith only [mul_nonneg (sub_nonneg.mpr hq') (add_nonneg hs hz.le),
      mul_nonneg hz.le (sub_nonneg.mpr hs'),mul_nonneg hz.le (show 0≤1-z by linarith)]

theorem theta_window {e M q z : ℝ} (b : Row) (he : 0<e) (hes : e≤1/2048)
    (hz : 0<z) (hz' : z≤e/512) (hlo : 1/2≤M) (hhi : M≤cap-2*e)
    (hq : 1-z≤q) (hq' : q≤1+z) :
    cover b M e-z≤q*cover b M e ∧ q*cover b M e≤cover b M e+z ∧
      1/2≤q*cover b M e+2*z ∧ q*cover b M e+2*z≤cap := by
  let C := cover b M e
  have hc : M+e/4≤C ∧ C≤M+e := by unfold C cover; split_ifs <;> constructor <;> linarith
  have hC : 0≤C := by linarith [hc.1]
  have hC' : C≤1 := by dsimp [cap] at hhi; linarith [hc.2]
  have H : C-z≤q*C := (scale_error hz (by linarith) hq hq' hC hC').1
  have K : q*C≤C+z := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hq') hC,mul_nonneg hz.le (sub_nonneg.mpr hC')]
  exact ⟨H,K,by linarith only [H,hc.1,hlo,he,hz],by linarith only [K,hc.2,hhi,hz',he]⟩

theorem conversion {N : ℕ} {x z : ℝ} (hN : 0<(N:ℝ)) (hx : 1<x) (hz : 0<z)
    (hl : x^(1-z)≤(N:ℝ)) (hu : (N:ℝ)≤x^(1+z)) :
    1-z≤power x (N:ℝ) ∧ power x (N:ℝ)≤1+z := by
  exact ⟨by simpa only [power_base hx] using power_mono hx (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _) hl,
    (upper_iff hx hN).mp hu⟩

theorem cover_power {N : ℕ} {x z C : ℝ} (hn : 0<(N:ℝ)) (hx : 1<x) :
    x^(theta N x z C-2*z)=(N:ℝ)^C := by
  rw [show theta N x z C-2*z=power x (N:ℝ)*C by unfold theta; ring]
  exact (Part3.ActualCompactInitialSupport.physical_power_eq_local hn hx C).symm

theorem selected_window {N : ℕ} {x z e M s E k : ℝ} (hn : 0<(N:ℝ)) (hx : 1<x)
    (he : 0<e) (hes : e≤1/2048) (hz : 0<z) (hz' : z≤e/512)
    (hk : k≤z) (hl : x^(1-z)≤(N:ℝ)) (hu : (N:ℝ)≤x^(1+z))
    (hm : 1/2≤M) (hm' : M≤cap-2*e) (hs : 0≤s) (hs' : s≤1)
    (hgate : M+e/2≤v s) (hE : (N:ℝ)^s≤E) (hE' : E≤(N:ℝ)^(s+z)) :
    let v := theta N x z (M+e/4)
    x^(2*v-1)≤E ∧ E≤x^actualSelectedSubproductUpper (1+k) v := by
  let v := theta N x z (M+e/4)
  have hx0 := zero_lt_one.trans hx
  obtain ⟨hq,hq'⟩ := conversion hn hx hz hl hu
  obtain ⟨_,hth,_,_⟩ := theta_window .first he hes hz hz' hm hm' hq hq'
  change power x (N:ℝ)*(M+e/4)≤M+e/4+z at hth
  have ht : v≤M+e/4+3*z := by dsimp [v,theta]; linarith
  obtain ⟨a,b⟩ := scale_error hz (by linarith) hq hq' hs hs'
  have hEp := (Real.rpow_pos_of_pos hn s).trans_le hE
  have low := power_mono hx (Real.rpow_pos_of_pos hn _) hE
  have up := power_mono hx hEp hE'
  rw [power_rpow hn] at low up
  have tent := (actualSelectedSubproduct_critical_iff 1 (M+e/2) s).mp (by rwa [actualSelectedSubproductV_one])
  have h1 := tent.2.trans (min_le_left _ _)
  have h2 := tent.2.trans (min_le_right _ _)
  constructor
  · apply (positive_le_iff hx (Real.rpow_pos_of_pos hx0 _) hEp).mpr
    rw [power_base hx]
    linarith only [tent.1,low,a,ht,hz',he,mul_comm s (power x (N:ℝ))]
  · apply (upper_iff hx hEp).mpr
    apply le_min <;> dsimp [actualSelectedSubproductUpper] at h1 h2 ⊢ <;>
      linarith only [h1,h2,up,b,ht,hz',hk,he,mul_comm (s+z) (power x (N:ℝ))]

/-- All four primitive W key bounds use the unchanged physical cap M,
its larger C0 cover M+e, and the original residue range 1+k. -/
theorem rescue_window {q M e z k a b c a' b' c' : ℝ}
    (he : 0<e) (hes : e≤1/2048) (hz : 0<z) (hz' : z≤e/512) (hk : k≤z)
    (hq : 1-z≤q) (hq' : q≤1+z) (hm : 1/2≤M) (hm' : M≤cap-2*e)
    (hord : Ordered a b c) (hA : A a≤M+11*e/20) (hB : M+2*e≤B c)
    (ha : a'≤q*(a+z)) (hb : b'≤q*(b+z)) (hc : c'≤q*(c+z)) :
    let v := q*(M+e)+2*z
    a'≤2*v-1 ∧ 2*b'≤1-v-2*z ∧
      c'≤actualSelectedSubproductUpper (1+k) v-(2*v-1) := by
  obtain ⟨w1,w2,_,w4⟩ := theta_window .rescue he hes hz hz' hm hm' hq hq'
  change M+e-z≤q*(M+e) at w1
  change q*(M+e)≤M+e+z at w2
  change q*(M+e)+2*z≤cap at w4
  obtain ⟨c0,cb,ba,am⟩ := hord
  have a0 := c0.trans (cb.trans ba)
  have b0 := c0.trans cb
  have a1 : a≤1 := by dsimp [mu] at am; linarith
  have hz1 : z≤1/400 := by linarith
  have aa := ha.trans (scale_error hz hz1 hq hq' a0 a1).2
  have bb := hb.trans (scale_error hz hz1 hq hq' b0 (ba.trans a1)).2
  have cc := hc.trans (scale_error hz hz1 hq hq' c0 (cb.trans (ba.trans a1))).2
  dsimp only
  refine ⟨by dsimp [A] at hA; linarith only [aa,hA,w1,hz',he],
    by dsimp [mu,cap] at am w4; linarith only [bb,ba,am,w4,hes,hz'],?_⟩
  apply le_sub_iff_add_le.mpr
  apply le_min <;> dsimp [B,cap,actualSelectedSubproductUpper] at hB ⊢ <;>
    linarith only [cc,c0,hB,w2,hz',hk,he]

end
end ImbalancedChen.P4BOriginalHigherLowLocalWindows
