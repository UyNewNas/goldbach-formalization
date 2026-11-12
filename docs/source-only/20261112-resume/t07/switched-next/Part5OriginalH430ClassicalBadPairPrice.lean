import ImbalancedChen.Part5OriginalH430ClassicalBadPairGeometry
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniform

/-! On the rejected Γ5 corner, the true ordinary upper model fits inside
the original K/4 times the converted mass of the very same integers.
This compares prices before summing the tested AP remainders. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalBadPairPrice
noncomputable section
open Set Real Finset Filter Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2OriginalChildPhysicalNormalization (thetaAtom thetaAtom_pair localPrimeFactor localPrimeFactor_pos)
open P2OriginalPositiveSameQMassLift (thetaAtom_nonneg)
open P2EnhancedSwitchedTrueNormalization (thetaConversion rawMainAtom rawMainAtom_to_thetaAtom)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2SeedOmegaLiteralFibre (s0 a0 a2 K)
open Part5OriginalH430SeedPurifiedPrimeFibres (fibre raw_fibre)
open Part5OriginalH430SameQCanonicalMains (model physical_main_sides)
open Part5OriginalH430ClassicalBadPairGeometry
open scoped Classical BigOperators Topology

private theorem actual_rough_lower :
    ∃ X : ℝ, 1<X ∧ ∀ x ≥ X, ∀ y : ℝ, 1<y → log x/log y ∈ Icc (2:ℝ) 100 →
      (49/100)*(x/log y) ≤ ((roughNumbers x y).card:ℝ) := by
  obtain ⟨X,hX,h⟩ := roughCount_uniform_buchstab (by norm_num : (1:ℝ)<2)
    (by norm_num : (0:ℝ)<1/100)
  refine ⟨X,hX,?_⟩
  intro x hx y hy hu
  let u := log x/log y
  have hx1 := hX.trans_le hx
  have hly := log_pos hy
  have hu' : (1:ℝ)≤u := (by norm_num : (1:ℝ)≤2).trans hu.1
  have hxy : y≤x := (log_le_log_iff (zero_lt_one.trans hy) (zero_lt_one.trans hx1)).mp
    (by linarith only [(le_div_iff₀ hly).mp hu'])
  have hpow := NonunitRoughUniform.rpow_inv_log_ratio hy hxy
  obtain ⟨hpos,hclose⟩ := h x hx u hu
  have hmain := rpow_buchstab_main_eq hx1 (zero_lt_one.trans_le hu')
  change x^(1/u)=y at hpow
  rw [hpow] at hmain hclose
  rw [←hmain] at hpos hclose
  have hh := (lt_div_iff₀ hpos).mp (show 99/100 < (roughCount x y:ℝ)/(x*buchstab u/log y) by
    linarith only [(abs_lt.mp hclose).1])
  have hbase := mul_le_mul_of_nonneg_right (one_half_le_buchstab hu') (div_pos (zero_lt_one.trans hx1) hly).le
  change _ ≤ (roughCount x y:ℝ)
  have he : buchstab u*(x/log y)=x*buchstab u/log y := by ring
  rw [he] at hbase
  linarith only [hbase,hh,div_pos (zero_lt_one.trans hx1) hly]

private theorem local_price {d q : ℕ} (hq : 202≤(q:ℝ)) :
    localPrimeFactor d q ≤ (101/100)/(q:ℝ) := by
  have hq0 : (0:ℝ)<q := by linarith
  have hq2 : 0<(q:ℝ)-2 := by linarith
  unfold localPrimeFactor
  split_ifs
  · exact div_le_div_of_nonneg_right (by norm_num) hq0.le
  · rw [div_le_div_iff₀ hq2 hq0]
    linarith

private theorem pair_theta_cost {N p : ℕ} {Q : ℝ} {l : List ℕ}
    (hN : 4≤N) (hF : 202≤floorScale N) (h : Geometry N p Q l) :
    thetaAtom N Q (p*l.prod) ≤ (10/3)*(thetaAtom N Q p/(l.prod:ℝ)) := by
  let a := l.getD 0 0
  let b := l.getD 1 0
  let u := log (a:ℝ)/log (Q/p)
  let v := log (b:ℝ)/log (Q/p)
  have ha := hF.trans h.scale.2.1
  have hb := hF.trans h.scale.2.2
  have h0a : (0:ℝ)<a := Nat.cast_pos.mpr h.first.1.pos
  have h0b : (0:ℝ)<b := Nat.cast_pos.mpr h.second.1.pos
  have ha2 : 2<a := by exact_mod_cast (show (2:ℝ)<a by linarith only [ha])
  have hb2 : 2<b := by exact_mod_cast (show (2:ℝ)<b by linarith only [hb])
  have he : l.prod=a*b := by rw [h.pair]; simp [a,b]
  have hθ := thetaAtom_nonneg hN h.outer.1.pos h.parent
  have hden : 9/29≤1-u-v := by
    have hh := h.coordinates
    norm_num [a2] at hh
    linarith only [hh.1,hh.2]
  have hd : 0<1-u-v := lt_of_lt_of_le (by norm_num) hden
  have hm := mul_le_mul (local_price (d:=p) ha) (local_price (d:=p*a) hb)
    (localPrimeFactor_pos (show (2:ℝ)<b by linarith only [hb])).le (by positivity)
  have hpair : localPrimeFactor p a*localPrimeFactor (p*a) b/(1-u-v) ≤
      (10/3)/((a:ℝ)*(b:ℝ)) := by
    apply (div_le_iff₀ hd).mpr
    apply hm.trans
    calc
      _ = (101/100)^2/((a:ℝ)*(b:ℝ)) := by field_simp [h0a.ne',h0b.ne'] <;> ring
      _ ≤ ((10/3)*(1-u-v))/((a:ℝ)*(b:ℝ)) :=
        div_le_div_of_nonneg_right (by linarith only [hden]) (mul_pos h0a h0b).le
      _ = _ := by ring
  rw [he,←Nat.mul_assoc,thetaAtom_pair (by omega) h.outer.1.pos h.first.1 h.second.1
    ha2 hb2 h.first.2 h.second.2 h.parent,Nat.cast_mul]
  exact (mul_le_mul_of_nonneg_left hpair hθ).trans_eq (by ring)

/-- At every actual rejected Γ5 label, the full true ordinary model at
the lowered upper cutoff is already covered by the original converted
rough-integer K/4 allocation. No prime-test estimate is an input. -/
theorem actual_bad_model_paid :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ (p : ℕ) (Q : ℝ) (l : List ℕ), Geometry N p Q l →
      model true N Q (p*l.prod) (cutoff Q (p*l.prod) 2) ≤
        (K/4)*thetaConversion N p*fibre false N (p*l.prod) (cutoff Q p (227/50)) := by
  obtain ⟨X,hX,hrough⟩ := actual_rough_lower
  obtain ⟨T,hT,hm⟩ := physical_main_sides (by norm_num : (0:ℝ)<1/200)
    (by norm_num : (0:ℝ)<1/100)
  have hf : Tendsto floorScale atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/200)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop T,hf.eventually_ge_atTop (max X 202)] with N hN hF
  intro hEven p Q l h
  let D := p*l.prod
  let y := cutoff Q p (227/50)
  let w := cutoff Q D 2
  let x := (N:ℝ)/(D:ℝ)
  have h4 := hT.trans hN
  have hD := h.big.1
  have hP : 0<l.prod := Nat.pos_of_mul_pos_left hD
  have hmain := (hm N hN hEven Q w 2 D hD h.big.2.1 h.child h.cutoff_order.1
    (P2SameQPhysicalRosserSeed.cutoff_log_coordinate h.child (by norm_num))
    le_rfl (by norm_num)).1
  rw [P5CanonicalUpperCancellation.upperA_eq_one (by norm_num) (by norm_num)] at hmain
  have hθ := pair_theta_cost h4 ((le_max_right _ _).trans hF) h
  have hden := hrough x (((le_max_left _ _).trans hF).trans h.height.1) y h.height.2 h.band
  have hconv := P2EnhancedUnitSourceMass.thetaConversion_nonneg h4 h.outer.1.pos h.parent
  have hcost := mul_le_mul_of_nonneg_left hden hconv
  have hK : (0:ℝ)≤K/4 := by norm_num [K]
  have hKcost := mul_le_mul_of_nonneg_left hcost hK
  have hy : log y=log (Q/p)/(227/50:ℝ) := by
    change log ((Q/(p:ℝ))^(1/(227/50):ℝ))=_
    rw [log_rpow (zero_lt_one.trans h.parent)]; ring
  have htheta : thetaConversion N p * (x/log y) = (227/50)*(thetaAtom N Q p/(l.prod:ℝ)) := by
    have he := rawMainAtom_to_thetaAtom (by omega : 0<N) h.outer.1.pos Q h.parent (fun _ => 1)
    simp only [rawMainAtom,mul_one] at he
    rw [←he,hy]
    dsimp only [x,D]; push_cast
    field_simp [(Nat.cast_pos.mpr h.outer.1.pos : (0:ℝ)<p).ne',
      (Nat.cast_pos.mpr hP : (0:ℝ)<l.prod).ne',(log_pos h.parent).ne'] <;> ring
  have htest := thetaAtom_nonneg h4 h.outer.1.pos h.parent
  have hnon : 0≤thetaAtom N Q p/(l.prod:ℝ) := div_nonneg htest (Nat.cast_nonneg _)
  rw [raw_fibre]
  change _ ≤ (K/4)*thetaConversion N p*((roughNumbers x y).card:ℝ)
  have hlow : ((K/4)*(49/100)*(227/50))*(thetaAtom N Q p/(l.prod:ℝ)) ≤
      (K/4)*thetaConversion N p*((roughNumbers x y).card:ℝ) := by
    calc
      _ = (K/4)*(thetaConversion N p*((49/100)*(x/log y))) := by
        rw [mul_left_comm (thetaConversion N p) (49/100) (x/log y),htheta]; ring
      _ ≤ _ := hKcost.trans_eq (by ring)
  have hpay : (1+1/100:ℝ)*(10/3) ≤ (K/4)*(49/100)*(227/50) := by norm_num [K]
  calc
    _ ≤ _ := hmain
    _ ≤ (1+1/100)*((10/3)*(thetaAtom N Q p/(l.prod:ℝ))) :=
      mul_le_mul_of_nonneg_left hθ (by norm_num)
    _ ≤ _ := (by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right hpay hnon)
    _ ≤ _ := hlow

end
end ImbalancedChen.Part5OriginalH430ClassicalBadPairPrice
