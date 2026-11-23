import Mathlib.Tactic

/-! The three selected-subproduct inequalities at the actual local scale.
The enlargement is an auxiliary level for endpoint allocation. The marked
count and its residual are evaluated at the original physical level. -/
namespace ImbalancedChen.P5OriginalH430SingletonCoverRescale

open scoped BigOperators

/-- The lower admissibility line and BOTH upper lines survive the same
perturbation of the complete scale, the residue and the selected endpoint.
Here `q = log_x N`, `y` is the box's upper endpoint for the selected root
prime, and `z` is the small parameter of the three monomial bounds. -/
theorem scaled_singleton_interval {lam t q y alpha z eta : ℝ}
    (hl : 1/2 ≤ lam) (ht : 0 ≤ t) (ht1 : t ≤ 1/3)
    (he : 0 < eta) (he1 : eta ≤ 1/100)
    (ha : lam + 4*eta ≤ (1+t)/2)
    (hm : lam + 4*eta ≤ (32-34*t)/39)
    (hc : lam + 4*eta ≤ 57/64-3*t/2)
    (hcap : lam + 4*eta ≤ 153/256)
    (hq : 1 ≤ q) (hq' : q ≤ 1+eta/4) (hres : q ≤ alpha) (hres' : alpha ≤ 1+eta/2)
    (hy : t ≤ y) (hy' : y ≤ t+eta) (hz : 0 < z) (hz' : z ≤ eta/8) :
    let theta := q*(lam+eta)+2*z
    let b := q*y
    1/2 < theta ∧ theta < 153/256 ∧
      2*theta-1 < b ∧ b < min ((32-39*theta)/34) ((2-2*theta-7*alpha/32)/3) := by
  dsimp only
  have hd : 0 ≤ lam+eta := by linarith
  have hd' : lam+eta ≤ 1 := by linarith
  have hy0 : 0 ≤ y := ht.trans hy
  have hy1 : y ≤ 1 := by linarith
  have loD : lam+eta ≤ q*(lam+eta) := by nlinarith only [mul_nonneg (sub_nonneg.mpr hq) hd]
  have hiD : q*(lam+eta) ≤ lam+eta+eta/4 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hd'),hq']
  have lob : t ≤ q*y := by nlinarith only [mul_nonneg (sub_nonneg.mpr hq) hy0,hy]
  have hib : q*y ≤ t+eta+eta/4 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hy1),hq',hy']
  refine ⟨by linarith only [hl,loD,he,hz],by linarith only [hcap,hiD,hz',he],
    by linarith only [ha,hiD,hz',lob,he],lt_min ?_ ?_⟩
  · linarith only [hm,hiD,hib,hz',he]
  · linarith only [hc,hiD,hib,hz',hres',he]

/-- Original upper endpoints may move independently. Every chronological
square uses the prefix and two copies of its own slot, including ties. -/
theorem endpoint_square_increase {r : ℕ} (x y : Fin r → ℝ) {delta : ℝ}
    (hdelta : 0 ≤ delta) (hy : ∀ j, y j ≤ x j+delta) (i : Fin r) :
    (∑ j : Fin r with j.val < i.val, y j) + 2*y i ≤
      (∑ j : Fin r with j.val < i.val, x j) + 2*x i + ((r:ℝ)+2)*delta := by
  let S := Finset.univ.filter (fun j : Fin r => j.val < i.val)
  have hh := Finset.sum_le_sum (s:=S) (fun j _ => hy j)
  have hs : (S.card:ℝ) ≤ (r:ℝ) := by
    exact_mod_cast (show S.card ≤ r by simpa only [Finset.card_univ,Fintype.card_fin] using
        (Finset.card_le_card (Finset.subset_univ S)))
  rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hh
  change (∑ j ∈ S, y j) + 2*y i ≤ (∑ j ∈ S, x j) + 2*x i + ((r:ℝ)+2)*delta
  linarith only [hh,hy i,mul_le_mul_of_nonneg_right hs hdelta]

end ImbalancedChen.P5OriginalH430SingletonCoverRescale
