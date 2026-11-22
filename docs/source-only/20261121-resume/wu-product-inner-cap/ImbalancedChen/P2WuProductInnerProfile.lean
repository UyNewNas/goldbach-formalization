import ImbalancedChen.P5ActualSingletonLogCollarFamily
import ImbalancedChen.P5zMarkedPrimeFamilyMultiplicity
import Mathlib

/-!
SOURCE ONLY / UNCOMPILED.

One genuine component of the native outer-approximation problem: a smooth
INNER complete-product cutoff. It equals one below N*(1-width), vanishes
at and above N, and has rank-independent polylogarithmic ordered Euler
bounds. The zero/negative-product extension is locally constant one; the
small-N profile is zero.

This is not a smooth replacement for the other sharp indexedWeight masks.
The prime-output loss is paid by the existing literal small-partner mass,
not by a new PP premise or a global H_N error.
-/
namespace ImbalancedChen.P2WuProductInnerProfile

noncomputable section
open Classical Set Filter Topology
open scoped BigOperators
open P5Z.ActualEtaPsiOccurrenceBudget
open P5Z.ActualSingletonPrimeTestFamily
open P5Z.ActualSingletonLogCollarFamily
open P5Z.AllWordAmbientOccurrenceBound
open P5Z.NativeSelectedFourOrderedEuler
open P5Z.AdmissibleAllRankIntegerGeometricFamily

def capLog (width : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  chiLog ((x-Real.log (N:ℝ))/width+Real.log 2)

def capReal (width : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  if 0 < x then capLog width N (Real.log x) else 1

def productProfile {r : ℕ} (width : ℝ) (N : ℕ) (p : Fin r → ℝ) : ℝ :=
  if 2 ≤ N then capReal width N (∏ j, p j) else 0

def innerProfile {r : ℕ} (B N : ℕ) (p : Fin r → ℝ) : ℝ :=
  productProfile (logWidth B N) N p

def innerWeight {r : ℕ} (B N : ℕ) (u : Fin r → Fin (N+1)) : ℝ :=
  innerProfile B N (fun j => ((u j).val:ℝ))

theorem capLog_bounds (width : ℝ) (N : ℕ) (x : ℝ) :
    0 ≤ capLog width N x ∧ capLog width N x ≤ 1 :=
  chi_bounds _

theorem capReal_bounds (width : ℝ) (N : ℕ) (x : ℝ) :
    0 ≤ capReal width N x ∧ capReal width N x ≤ 1 := by
  by_cases hx : 0 < x
  · simpa only [capReal,if_pos hx] using capLog_bounds width N (Real.log x)
  · simp [capReal,hx]

theorem productProfile_bounds {r : ℕ} (width : ℝ) (N : ℕ) (p : Fin r → ℝ) :
    0 ≤ productProfile width N p ∧ productProfile width N p ≤ 1 := by
  by_cases hN : 2 ≤ N
  · simpa only [productProfile,if_pos hN] using capReal_bounds width N (∏ j,p j)
  · simp [productProfile,hN]

theorem innerWeight_bounds {r : ℕ} (B N : ℕ) (u : Fin r → Fin (N+1)) :
    0 ≤ innerWeight B N u ∧ innerWeight B N u ≤ 1 :=
  productProfile_bounds (logWidth B N) N (fun j => ((u j).val:ℝ))

/-- Inserting this cap cannot increase the actual unsifted source mass. -/
theorem inner_mass_le_original {r : ℕ} (B N : ℕ)
    (S : Finset (Fin r → Fin (N+1))) :
    p5z_labelledMass S (innerWeight B N) ≤ p5z_labelledMass S (fun _ => 1) := by
  exact Finset.sum_le_sum (fun u _ => (innerWeight_bounds B N u).2)

theorem inner_primeMass_le_original {r : ℕ} (B N : ℕ)
    (S : Finset (Fin r → Fin (N+1))) :
    p5z_labelledPrimeMass S Part3.labelledProduct (innerWeight B N) N ≤
      p5z_labelledPrimeMass S Part3.labelledProduct (fun _ => 1) N := by
  unfold p5z_labelledPrimeMass
  apply Finset.sum_le_sum
  intro u hu
  split_ifs
  · exact (innerWeight_bounds B N u).2
  · exact le_rfl

private theorem capLog_one {width : ℝ} (hw : 0 < width) (N : ℕ) {x : ℝ}
    (hx : x-Real.log (N:ℝ) ≤ -width*Real.log 2) :
    capLog width N x=1 := by
  have harg : (x-Real.log (N:ℝ))/width+Real.log 2 ≤ 0 := by
    have h : (x-Real.log (N:ℝ))/width ≤ -Real.log 2 :=
      (div_le_iff₀ hw).mpr (by nlinarith only [hx])
    linarith
  exact chi_one (Real.exp_le_one_iff.mpr harg)

theorem capReal_zero_of_ge {width : ℝ} (hw : 0 < width) {N : ℕ}
    (hN : 0 < N) {x : ℝ} (hx : (N:ℝ) ≤ x) : capReal width N x=0 := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hx0 := hNr.trans_le hx
  have hlog := Real.log_le_log hNr hx
  have harg : Real.log 2 ≤ (Real.log x-Real.log (N:ℝ))/width+Real.log 2 :=
    le_add_of_nonneg_left (div_nonneg (sub_nonneg.mpr hlog) hw.le)
  have hexp : (2:ℝ) ≤ Real.exp ((Real.log x-Real.log (N:ℝ))/width+Real.log 2) := by
    calc
      (2:ℝ)=Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr harg
  simp only [capReal,if_pos hx0,capLog,chiLog,chi_zero hexp]

/-- A fixed positive plateau makes the extension across product=0 smooth. -/
theorem capReal_one_below_half {width : ℝ} (hw : 0 < width) (hw1 : width ≤ 1)
    {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : x ≤ (N:ℝ)/2) :
    capReal width N x=1 := by
  by_cases hx0 : 0 < x
  · have hNr : (0:ℝ) < N := by exact_mod_cast hN
    have hlog := Real.log_le_log hx0 hx
    rw [Real.log_div hNr.ne' (by norm_num : (2:ℝ)≠0)] at hlog
    have hlog2 : 0 ≤ Real.log (2:ℝ) := (Real.log_pos (by norm_num)).le
    have hc : Real.log x-Real.log (N:ℝ) ≤ -width*Real.log 2 := by
      nlinarith only [hlog,hw1,hlog2]
    simpa only [capReal,if_pos hx0] using capLog_one hw N hc
  · simp [capReal,hx0]

/-- The safe linear inner plateau; this gives an exact integer collar. -/
theorem capReal_one_of_linear_bound {width : ℝ} (hw : 0 < width)
    {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : 0 < x)
    (hbound : x ≤ (N:ℝ)*(1-width)) : capReal width N x=1 := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hratio : x/(N:ℝ) ≤ 1-width :=
    (div_le_iff₀ hNr).mpr (by simpa only [mul_comm] using hbound)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx hNr)
  rw [Real.log_div hx.ne' hNr.ne'] at hlog
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h
  have hpre : Real.log x-Real.log (N:ℝ) ≤ -width := by linarith
  have hdiv : (Real.log x-Real.log (N:ℝ))/width ≤ -1 :=
    (div_le_iff₀ hw).mpr (by linarith)
  have harg : (Real.log x-Real.log (N:ℝ))/width+Real.log 2 ≤ 0 := by linarith
  simp only [capReal,if_pos hx,capLog,chiLog,chi_one (Real.exp_le_one_iff.mpr harg)]

theorem capLog_smooth (width : ℝ) (N : ℕ) : ContDiff ℝ ∞ (capLog width N) :=
  chiLog_smooth.comp (by fun_prop)

theorem capReal_smooth {width : ℝ} (hw : 0 < width) (hw1 : width ≤ 1)
    {N : ℕ} (hN : 0 < N) : ContDiff ℝ ∞ (capReal width N) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0 < x
  · have hraw := (capLog_smooth width N).contDiffAt.comp x
      (Real.contDiffAt_log hx.ne')
    have heq : capReal width N =ᶠ[𝓝 x] (fun y => capLog width N (Real.log y)) := by
      filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds hx] with y hy
      simp only [capReal,if_pos hy]
    exact hraw.congr_of_eventuallyEq heq
  · have hNr : (0:ℝ) < N := by exact_mod_cast hN
    have hopen : IsOpen {y : ℝ | y < (N:ℝ)/2} :=
      isOpen_lt continuous_id continuous_const
    have heq : capReal width N =ᶠ[𝓝 x] (fun _ => 1) := by
      filter_upwards [hopen.mem_nhds (show x < (N:ℝ)/2 by linarith)] with y hy
      exact capReal_one_below_half hw hw1 hN hy.le
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (1:ℝ)) x).
      congr_of_eventuallyEq heq

theorem productProfile_smooth {r : ℕ} {width : ℝ}
    (hw : 0 < width) (hw1 : width ≤ 1) (N : ℕ) :
    ContDiff ℝ ∞ (productProfile (r:=r) width N) := by
  by_cases hN : 2 ≤ N
  · simp only [productProfile,if_pos hN]
    exact (capReal_smooth hw hw1 (by omega : 0<N)).comp (by fun_prop)
  · simp only [productProfile,if_neg hN]
    exact contDiff_const

theorem multiplicative_product {r : ℕ} (p z : Fin r → ℝ) :
    (∏ j, multiplicativeChart p z j) = (∏ j,p j)*Real.exp (∑ j,z j) := by
  simp only [multiplicativeChart,Finset.prod_mul_distrib,Real.exp_sum]

theorem product_chart_positive {r : ℕ} (width : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (p : Fin r → ℝ) (hp : 0 < ∏ j,p j) :
    (fun z => productProfile width N (multiplicativeChart p z)) =
      scalarLift (Real.log (∏ j,p j)) (capLog width N) := by
  funext z
  have hprod : 0 < (∏ j,p j)*Real.exp (∑ j,z j) := mul_pos hp (Real.exp_pos _)
  simp only [productProfile,if_pos hN,multiplicative_product,capReal,if_pos hprod,
    Real.log_mul hp.ne' (Real.exp_pos _).ne',Real.log_exp,scalarLift]

theorem product_chart_nonpositive {r : ℕ} (width : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (p : Fin r → ℝ) (hp : ∏ j,p j ≤ 0) :
    (fun z => productProfile width N (multiplicativeChart p z)) = fun _ => 1 := by
  funext z
  have hprod : (∏ j,p j)*Real.exp (∑ j,z j) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hp (Real.exp_pos _).le
  simp only [productProfile,if_pos hN,multiplicative_product,capReal,if_neg (not_lt_of_ge hprod)]

theorem capLog_derivative_bound (q : ℕ) {width : ℝ}
    (hw : 0 < width) (hw1 : width ≤ 1) (M : ℝ) (hM : 1 ≤ M)
    (hm : ∀ d ≤ q, ∀ x, |iteratedDeriv d etaLog x| ≤ M)
    (N d : ℕ) (hd : d ≤ q) (x : ℝ) :
    |iteratedDeriv d (capLog width N) x| ≤ M*(width⁻¹)^q := by
  let b := width*Real.log 2-Real.log (N:ℝ)
  have heq : capLog width N = fun y => scaledChi width (b+1*y) := by
    funext y
    unfold capLog scaledChi
    congr 1
    dsimp [b]
    field_simp [hw.ne']
    ring
  rw [heq,P4B.iteratedDeriv_comp_real_affine d (scaledChi width)
    (scaledChi_smooth width) b 1 x]
  simp only [one_pow,one_mul]
  exact scaledChi_order_bound q hw hw1 M hM hm d hd _

/-- Constants precede every rank, target, point and ordered word.
No rank-dependent or BoxIndex-dependent derivative constant is introduced. -/
theorem uniform_product_Euler (q : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (width : ℝ), 0 < width → width ≤ 1 →
      ∀ (N r : ℕ) (w : List (Fin r)) (p : Fin r → ℝ), w.length ≤ q →
        |eulerWord w (productProfile width N) p| ≤ (C:ℝ)*(width⁻¹)^q := by
  obtain ⟨M,hM,hm⟩ := finite_order_constants etaLog exists_etaLog_order_bound q
  refine ⟨Nat.ceil M+1,by omega,?_⟩
  intro width hw hw1 N r w p hwq
  have hceil : M ≤ ((Nat.ceil M+1:ℕ):ℝ) := by
    have h := Nat.le_ceil M
    push_cast
    linarith
  have hinv : 1 ≤ width⁻¹ := by
    rw [←one_div]
    exact (le_div_iff₀ hw).mpr (by simpa using hw1)
  have hpow : 1 ≤ (width⁻¹)^q := by
    simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hinv q
  have hfinal := mul_le_mul_of_nonneg_right hceil (pow_nonneg (inv_nonneg.mpr hw.le) q)
  apply le_trans ?_ hfinal
  by_cases hN : 2 ≤ N
  · have he := orderedEuler_occurrence_dictionary (productProfile (r:=r) width N)
      (productProfile_smooth hw hw1 N) w p 0
    have hid : |eulerWord w (productProfile width N) p| =
        |occWord w (fun z => productProfile width N (multiplicativeChart p z)) 0| := by
      simpa using congrArg abs he
    rw [hid]
    by_cases hp : 0 < ∏ j,p j
    · rw [product_chart_positive width hN p hp,occWord_scalarLift]
      exact capLog_derivative_bound q hw hw1 M hM hm N w.length hwq _
    · rw [product_chart_nonpositive width hN p (le_of_not_gt hp)]
      exact (occurrence_one_bound w 0).trans (by nlinarith only [hM,hpow])
  · have hz : productProfile (r:=r) width N=0 := by
      funext y
      simp only [productProfile,if_neg hN,Pi.zero_apply]
    rw [(eulerWord_eventually_zero w _ p
      (Eventually.of_forall (fun y => congrFun hz y))).eq_of_nhds,abs_zero]
    positivity

theorem innerProfile_smooth (B N r : ℕ) :
    ContDiff ℝ ∞ (innerProfile (r:=r) B N) := by
  by_cases hN : 2 ≤ N
  · exact productProfile_smooth (logWidth_bounds B hN).1 (logWidth_bounds B hN).2 N
  · simp only [innerProfile,productProfile,if_neg hN]
    exact contDiff_const

theorem uniform_inner_mixedEuler (B q : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (N r : ℕ) (w : List (Fin r)) (p : Fin r → ℝ),
      w.length ≤ q →
      |eulerWord w (innerProfile B N) p| ≤
        (C:ℝ)*Real.log ((N:ℝ)+2)^(B*q) := by
  obtain ⟨C0,hC0,hbound⟩ := uniform_product_Euler q
  let K : ℝ := (C0:ℝ)/Real.log 2^(B*q)
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨Nat.ceil K+1,by omega,?_⟩
  intro N r w p hwq
  by_cases hN : 2 ≤ N
  · have hwidth := logWidth_bounds B hN
    have hb := hbound (logWidth B N) hwidth.1 hwidth.2 N r w p hwq
    have hscale : (C0:ℝ)*(logWidth B N)⁻¹^q =
        K*Real.log ((N:ℝ)+2)^(B*q) := by
      dsimp [logWidth,K]
      simp only [inv_pow,inv_div,div_pow,←pow_mul]
      ring
    rw [hscale] at hb
    have hceil : K ≤ ((Nat.ceil K+1:ℕ):ℝ) := by
      have h := Nat.le_ceil K
      push_cast
      linarith
    exact hb.trans (mul_le_mul_of_nonneg_right hceil (by positivity))
  · have hz : innerProfile (r:=r) B N=0 := by
      funext y
      simp only [innerProfile,productProfile,if_neg hN,Pi.zero_apply]
    rw [(eulerWord_eventually_zero w _ p
      (Eventually.of_forall (fun y => congrFun hz y))).eq_of_nhds,abs_zero]
    positivity

/-- The inner cap never creates a product at or above the same target N. -/
theorem innerWeight_zero_at_or_above {r N B : ℕ} (hN : 2 ≤ N)
    (u : Fin r → Fin (N+1)) (hm : N ≤ Part3.labelledProduct u) :
    innerWeight B N u=0 := by
  have hw := (logWidth_bounds B hN).1
  have hmR : (N:ℝ) ≤ ∏ j,((u j).val:ℝ) := by
    exact_mod_cast hm
  simpa only [innerWeight,innerProfile,productProfile,if_pos hN] using
    capReal_zero_of_ge hw (by omega : 0<N) hmR

/-- Exact finite prime-output payment. The existing small-partner theorem
keeps r=0, prime powers and every labelled product representation. -/
theorem finite_inner_cut_loss {r N : ℕ} (hN : 2 ≤ N)
    (S : Finset (Fin r → Fin (N+1))) (hS : S ⊆ Part3.labelledPrimeTuples r N)
    (hcap : ∀ u ∈ S, Part3.labelledProduct u ≤ N)
    {width : ℝ} (hw : 0 < width) (hw1 : width ≤ 1) :
    p5z_labelledPrimeMass S Part3.labelledProduct (fun _ => 1) N ≤
      p5z_labelledPrimeMass S Part3.labelledProduct
        (fun u => productProfile width N (fun j => ((u j).val:ℝ))) N +
      (r^r:ℕ)*(Nat.ceil (width*(N:ℝ)):ℝ) := by
  let z := Nat.ceil (width*(N:ℝ))
  have hfinite :
      p5z_labelledPrimeMass S Part3.labelledProduct (fun _ => 1) N ≤
        p5z_labelledPrimeMass S Part3.labelledProduct
          (fun u => productProfile width N (fun j => ((u j).val:ℝ))) N +
        p5z_labelledSmallPrimeMass S Part3.labelledProduct (fun _ => 1) N z := by
    unfold p5z_labelledPrimeMass p5z_labelledSmallPrimeMass
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u hu
    by_cases hp : Part3.labelledProduct u < N ∧ Nat.Prime (N-Part3.labelledProduct u)
    · by_cases hs : N-Part3.labelledProduct u < z
      · have hpos := (productProfile_bounds width N (fun j => ((u j).val:ℝ))).1
        simp only [if_pos hp,if_pos ⟨hp.1,hp.2,hs⟩]
        linarith
      · have hge : z ≤ N-Part3.labelledProduct u := Nat.le_of_not_gt hs
        have hout : width*(N:ℝ) ≤ ((N-Part3.labelledProduct u:ℕ):ℝ) :=
          (Nat.le_ceil _).trans (by exact_mod_cast hge)
        rw [Nat.cast_sub (hcap u hu)] at hout
        have hm : 0 < Part3.labelledProduct u := by
          exact Finset.prod_pos (fun j _ => ((Finset.mem_filter.mp (hS hu)).2 j).pos)
        have hlin : ((Part3.labelledProduct u:ℕ):ℝ) ≤ (N:ℝ)*(1-width) := by nlinarith
        have hone := capReal_one_of_linear_bound hw (by omega : 0<N)
          (by exact_mod_cast hm) hlin
        have hprofile : productProfile width N (fun j => ((u j).val:ℝ))=1 := by
          simpa only [productProfile,if_pos hN,←Nat.cast_prod,Part3.labelledProduct] using hone
        simp only [if_pos hp,hprofile,if_neg (fun h => hs h.2.2),add_zero,le_refl]
    · have hnot : ¬(Part3.labelledProduct u<N ∧
          Nat.Prime (N-Part3.labelledProduct u) ∧ N-Part3.labelledProduct u<z) :=
        fun h => hp ⟨h.1,h.2.1⟩
      simp only [if_neg hp,if_neg hnot,add_zero,le_refl]
  have hsmall := p5z_markedSmallPrimeMass_le S hS (fun _ => 1) 1 (by norm_num)
    (fun _ _ => le_rfl) hcap z
  simp only [one_mul] at hsmall
  exact hfinite.trans (add_le_add_left hsmall _)

end
end ImbalancedChen.P2WuProductInnerProfile
