import ImbalancedChen.P4AFull87UnionCompilerPayment

namespace ImbalancedChen.P4AFull87RoughEulerRatio
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler P4AFull87PhysicalReserveFromRate

theorem ratio_eq_interval (N cap : ℕ) (hEven : Even N) (w z : ℝ) (hwz : w≤z) :
    actualSmallEulerProduct N cap w / actualSmallEulerProduct N cap z =
      ∏ p ∈ roughPrimeFinset N cap w z, (1-1/((p:ℝ)-1))⁻¹ := by
  let W := actualSmallPrimeFinset N cap w
  let Z := actualSmallPrimeFinset N cap z
  let P := roughPrimeFinset N cap w z
  let f (p : ℕ) := (1:ℝ)-1/((p:ℝ)-1)
  have union : Z=W∪P := by
    ext p
    simp only [Z,W,P,Finset.mem_union,mem_actualSmallPrimeFinset,mem_roughPrimeFinset]
    constructor
    · rintro ⟨hc,hp,hnd,hz⟩
      by_cases h : (p:ℝ)<w
      · exact Or.inl ⟨hc,hp,hnd,h⟩
      · exact Or.inr ⟨hc,hp,hnd,le_of_not_gt h,hz⟩
    · rintro (⟨hc,hp,hnd,h⟩|⟨hc,hp,hnd,_,h⟩)
      · exact ⟨hc,hp,hnd,h.trans_le hwz⟩
      · exact ⟨hc,hp,hnd,h⟩
  have disj : Disjoint W P := Finset.disjoint_left.mpr (fun p hp hq =>
    (not_lt_of_ge (mem_roughPrimeFinset.mp hq).2.2.2.1) (mem_actualSmallPrimeFinset.mp hp).2.2.2)
  have hW : W.prod f ≠ 0 := (actualSmallEulerProduct_pos N cap w hEven).ne'
  change W.prod f/Z.prod f = ∏ p ∈ P, (f p)⁻¹
  rw [union,Finset.prod_union disj,Finset.prod_inv_distrib]
  rw [div_eq_mul_inv,mul_inv_rev]
  calc
    _ = (W.prod f*(W.prod f)⁻¹)*(P.prod f)⁻¹ := by ring
    _ = _ := by rw [mul_inv_cancel₀ hW,one_mul]

/-- The literal rough-density increment multiplied by V_N(w)/V_N(z).
The pre-omega coarse coefficient is 300 M. All endpoint errors are
explicit at the same N; cap may be the physical target itself. -/
theorem of_wallRate {M : ℕ} {keep : Keep} {tags : Tags} (rate : WallRate M keep tags) :
    ∃ K E : ℝ, 1<K ∧ 1<E ∧ ∀ N cap : ℕ, 2≤N → Even N → ∀ omega v tau : ℝ,
    0<omega → omega≤v → v≤1 → 0<tau → 3≤(N:ℝ)^omega → E≤omega*Real.log (N:ℝ) →
    let w := (N:ℝ)^omega
    let z := (N:ℝ)^v
    let U := universe N cap w z
    let increase := reciprocalTotientDensity U (coefficient (keep N) (tags N) N cap w z tau) -
      reciprocalTotientDensity U (raw (keep N) N cap w z)
    (actualSmallEulerProduct N cap w/actualSmallEulerProduct N cap z)*increase ≤
      ((M:ℝ)*300*tau+(M:ℝ)*20*K/Real.log (N:ℝ))/omega^5 := by
  obtain ⟨K,E,hK,hE,hh⟩ := rate
  obtain ⟨I,hI,hint⟩ := MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K,max E I,hK,hE.trans_le (le_max_left _ _),?_⟩
  intro N cap hN hEven omega v tau hw hv hv1 ht h3 hmax
  let w := (N:ℝ)^omega
  let z := (N:ℝ)^v
  have hn : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hwz : w ≤ z := Real.rpow_le_rpow_of_exponent_le hn.le hv
  have hvl := (le_max_right E I).trans hmax
  have hpow := hint (roughPrimeFinset N cap w z) (fun _ hp => roughPrimeFinset_odd_of_even hEven hp)
    w z (by dsimp only [w]; linarith) hwz (fun _ hp => (mem_roughPrimeFinset.mp hp).2.2.2)
  rw [← ratio_eq_interval N cap hEven w z hwz] at hpow
  have hzlog : Real.log z = v*Real.log (N:ℝ) := Real.log_rpow (zero_lt_one.trans hn) _
  have hwlog : Real.log w = omega*Real.log (N:ℝ) := Real.log_rpow (zero_lt_one.trans hn) _
  rw [hzlog,hwlog] at hpow
  have hlog := Real.log_pos hn
  have hratio : v*Real.log (N:ℝ)/(omega*Real.log (N:ℝ))=v/omega := by field_simp [hw.ne',hlog.ne']
  rw [hratio] at hpow
  have he : 1+I/(omega*Real.log (N:ℝ))≤2 := by
    linarith [(div_le_one (mul_pos hw hlog)).mpr hvl]
  have hco : actualSmallEulerProduct N cap w/actualSmallEulerProduct N cap z≤2/omega := by
    apply hpow.trans
    calc
      _ ≤ (1/omega)*2 := mul_le_mul (div_le_div_of_nonneg_right hv1 hw.le) he
        (by positivity) (by positivity)
      _ = _ := by ring
  have hsum : 0 ≤ changedMass (keep N) (tags N) N cap w z tau := by
    unfold changedMass
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hrate := hh 2 (by norm_num) N cap hN hEven omega v tau hw hv hv1 ht h3 ((le_max_left E I).trans hmax)
  dsimp only
  rw [rough_density_increase_eq_changedMass]
  apply (mul_le_mul_of_nonneg_right hco hsum).trans
  convert hrate using 1 <;> ring

end
end ImbalancedChen.P4AFull87RoughEulerRatio
