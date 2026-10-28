import Mathlib
import ImbalancedChen.P4BSmoothStepDerivativeBudget
import ImbalancedChen.Part3TwoLongLiteralMellinModes

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual fixed-transition interval/endpoint-strip profiles. The derivative
constants are chosen ONCE from the existing genuine smoothTransition
supplier, before delta and every profile argument. This avoids assuming
uniform derivative bounds for an arbitrary variable-radius bump family.
-/
namespace ImbalancedChen.Part3.TwoLongQuantitativeTransitionProfiles
noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators Topology
open ImbalancedChen.P4B
open ImbalancedChen.Part3.TwoLongLiteralMellinModes

def B (k : ℕ) : ℝ := Classical.choose (exists_smoothGateUpperStep_derivative_budget k)

theorem B_one_le (k : ℕ) : 1 ≤ B k :=
  (Classical.choose_spec (exists_smoothGateUpperStep_derivative_budget k)).1

theorem B_nonneg (k : ℕ) : 0 ≤ B k := zero_le_one.trans (B_one_le k)

theorem step_smooth (delta : ℝ) : ContDiff ℝ ∞ (smoothGateUpperStep delta) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.add (contDiff_id.div_const delta))

theorem step_deriv_bound {delta : ℝ} (hd : 0 < delta) (x : ℝ) :
    |deriv (smoothGateUpperStep delta) x| ≤ B 1 / delta := by
  simpa only [iteratedDeriv_one,pow_one] using
    (Classical.choose_spec (exists_smoothGateUpperStep_derivative_budget 1)).2 delta hd x

theorem step_second_bound {delta : ℝ} (hd : 0 < delta) (x : ℝ) :
    |deriv (deriv (smoothGateUpperStep delta)) x| ≤ B 2 / delta^2 := by
  simpa only [iteratedDeriv_succ,iteratedDeriv_one] using
    (Classical.choose_spec (exists_smoothGateUpperStep_derivative_budget 2)).2 delta hd x

/-- Actual upper interval profile, one on [a,b] and zero outside
(a-delta,b+delta), using a FIXED smooth scalar transition. -/
def doubleStep (delta a b x : ℝ) : ℝ :=
  smoothGateUpperStep delta (x-a) * smoothGateUpperStep delta (b-x)

theorem doubleStep_smooth (delta a b : ℝ) : ContDiff ℝ ∞ (doubleStep delta a b) :=
  ((step_smooth delta).comp (contDiff_id.sub contDiff_const)).mul
    ((step_smooth delta).comp (contDiff_const.sub contDiff_id))

theorem doubleStep_range (delta a b x : ℝ) :
    0 ≤ doubleStep delta a b x ∧ doubleStep delta a b x ≤ 1 := by
  have hL := smoothGateUpperStep_bounds delta (x-a)
  have hR := smoothGateUpperStep_bounds delta (b-x)
  exact ⟨mul_nonneg hL.1 hR.1,
    (mul_le_mul hL.2 hR.2 hR.1 zero_le_one).trans_eq (one_mul _)⟩

theorem doubleStep_one {delta a b x : ℝ} (hd : 0 < delta) (hx : x ∈ Icc a b) :
    doubleStep delta a b x = 1 := by
  rw [doubleStep,smoothGateUpperStep_eq_one hd (by linarith [hx.1]),
    smoothGateUpperStep_eq_one hd (by linarith [hx.2]),one_mul]

theorem doubleStep_support {delta a b : ℝ} (hd : 0 < delta) :
    Function.support (doubleStep delta a b) ⊆ Icc (a-delta) (b+delta) := by
  intro x hx
  have h := mul_ne_zero_iff.mp hx
  have hL := smoothGateUpperStep_nonzero_support hd h.1
  have hR := smoothGateUpperStep_nonzero_support hd h.2
  constructor <;> linarith

def firstJet (delta a b x : ℝ) : ℝ :=
  deriv (smoothGateUpperStep delta) (x-a) * smoothGateUpperStep delta (b-x) -
    smoothGateUpperStep delta (x-a) * deriv (smoothGateUpperStep delta) (b-x)

def secondJet (delta a b x : ℝ) : ℝ :=
  deriv (deriv (smoothGateUpperStep delta)) (x-a) * smoothGateUpperStep delta (b-x) -
    2 * deriv (smoothGateUpperStep delta) (x-a) * deriv (smoothGateUpperStep delta) (b-x) +
    smoothGateUpperStep delta (x-a) * deriv (deriv (smoothGateUpperStep delta)) (b-x)

theorem doubleStep_hasDerivAt (delta a b x : ℝ) :
    HasDerivAt (doubleStep delta a b) (firstJet delta a b x) x := by
  have hD := (step_smooth delta).differentiable (by simp)
  have hL := (hD (x-a)).hasDerivAt.comp x ((hasDerivAt_id x).sub_const a)
  have hR := (hD (b-x)).hasDerivAt.comp x ((hasDerivAt_const x b).sub (hasDerivAt_id x))
  convert hL.mul hR using 1 <;> simp only [doubleStep,firstJet] <;> ring

theorem doubleStep_secondDeriv (delta a b x : ℝ) :
    deriv (deriv (doubleStep delta a b)) x = secondJet delta a b x := by
  have hD := (step_smooth delta).differentiable (by simp)
  have hD1 := ((contDiff_infty_iff_deriv.mp (step_smooth delta)).2).differentiable (by simp)
  have hL := (hD (x-a)).hasDerivAt.comp x ((hasDerivAt_id x).sub_const a)
  have hR := (hD (b-x)).hasDerivAt.comp x ((hasDerivAt_const x b).sub (hasDerivAt_id x))
  have hL1 := (hD1 (x-a)).hasDerivAt.comp x ((hasDerivAt_id x).sub_const a)
  have hR1 := (hD1 (b-x)).hasDerivAt.comp x ((hasDerivAt_const x b).sub (hasDerivAt_id x))
  have he : deriv (doubleStep delta a b) = firstJet delta a b :=
    funext (fun y => (doubleStep_hasDerivAt delta a b y).deriv)
  rw [he]
  have hj : HasDerivAt (firstJet delta a b) (secondJet delta a b x) x := by
    convert (hL1.mul hR).sub (hL.mul hR1) using 1 <;>
      simp only [firstJet,secondJet] <;> ring
  exact hj.deriv

def D : ℝ := 2*B 2 + 2*(B 1)^2

theorem D_nonneg : 0 ≤ D := by have h := B_nonneg 2; unfold D; positivity

theorem doubleStep_deriv_bound {delta : ℝ} (hd : 0 < delta) (a b x : ℝ) :
    |deriv (doubleStep delta a b) x| ≤ 2*B 1/delta := by
  rw [(doubleStep_hasDerivAt delta a b x).deriv]
  have hL := smoothGateUpperStep_bounds delta (x-a)
  have hR := smoothGateUpperStep_bounds delta (b-x)
  have hB := B_nonneg 1
  calc
    _ ≤ |deriv (smoothGateUpperStep delta) (x-a) * smoothGateUpperStep delta (b-x)| +
        |smoothGateUpperStep delta (x-a) * deriv (smoothGateUpperStep delta) (b-x)| :=
      abs_sub_le _ _
    _ ≤ (B 1/delta)*1 + 1*(B 1/delta) := by
      rw [abs_mul,abs_mul,abs_of_nonneg hL.1,abs_of_nonneg hR.1]
      gcongr
      · exact step_deriv_bound hd _
      · exact hR.2
      · exact hL.2
      · exact step_deriv_bound hd _
    _ = _ := by ring

theorem doubleStep_second_bound {delta : ℝ} (hd : 0 < delta) (a b x : ℝ) :
    |deriv (deriv (doubleStep delta a b)) x| ≤ D/delta^2 := by
  rw [doubleStep_secondDeriv]
  have hL := smoothGateUpperStep_bounds delta (x-a)
  have hR := smoothGateUpperStep_bounds delta (b-x)
  have hB1 := B_nonneg 1
  have hB2 := B_nonneg 2
  calc
    _ ≤ |deriv (deriv (smoothGateUpperStep delta)) (x-a) * smoothGateUpperStep delta (b-x)| +
        |2 * deriv (smoothGateUpperStep delta) (x-a) * deriv (smoothGateUpperStep delta) (b-x)| +
        |smoothGateUpperStep delta (x-a) * deriv (deriv (smoothGateUpperStep delta)) (b-x)| := by
      exact (abs_add _ _).trans (add_le_add_right (abs_sub_le _ _) _)
    _ ≤ (B 2/delta^2)*1 + 2*(B 1/delta)*(B 1/delta) + 1*(B 2/delta^2) := by
      simp only [abs_mul,abs_of_nonneg hL.1,abs_of_nonneg hR.1,abs_ofNat]
      gcongr
      · exact step_second_bound hd _
      · exact hR.2
      · exact step_deriv_bound hd _
      · exact step_deriv_bound hd _
      · exact hL.2
      · exact step_second_bound hd _
    _ = D/delta^2 := by unfold D; field_simp [hd.ne']; ring

/-- The three original normalized upper/gap profile choices. -/
def upper (delta : ℝ) : ℝ → ℝ := doubleStep delta 1 2

def endpoint (delta a : ℝ) : ℝ → ℝ := doubleStep delta (a-delta) (a+delta)

def gap (delta x : ℝ) : ℝ := endpoint delta 1 x + endpoint delta 2 x

theorem upper_smooth (delta : ℝ) : ContDiff ℝ ∞ (upper delta) := doubleStep_smooth delta 1 2

theorem gap_smooth (delta : ℝ) : ContDiff ℝ ∞ (gap delta) :=
  (doubleStep_smooth delta (1-delta) (1+delta)).add
    (doubleStep_smooth delta (2-delta) (2+delta))

theorem upper_support {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4) :
    Function.support (upper delta) ⊆ Icc (1/2 : ℝ) (5/2) := by
  intro x hx
  have h := doubleStep_support (a := 1) (b := 2) hd hx
  constructor <;> linarith [h.1,h.2]

theorem gap_support {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4) :
    Function.support (gap delta) ⊆ Icc (1/2 : ℝ) (5/2) := by
  intro x hx
  by_cases hL : endpoint delta 1 x = 0
  · have hR : endpoint delta 2 x ≠ 0 := by intro h; exact hx (by simp [gap,hL,h])
    have h := doubleStep_support (a := 2-delta) (b := 2+delta) hd hR
    constructor <;> linarith [h.1,h.2]
  · have h := doubleStep_support (a := 1-delta) (b := 1+delta) hd hL
    constructor <;> linarith [h.1,h.2]

theorem upper_abs_le_one (delta x : ℝ) : |upper delta x| ≤ 1 := by
  rw [abs_of_nonneg (doubleStep_range delta 1 2 x).1]
  exact (doubleStep_range delta 1 2 x).2

theorem gap_abs_le_two (delta x : ℝ) : |gap delta x| ≤ 2 := by
  have hL := doubleStep_range delta (1-delta) (1+delta) x
  have hR := doubleStep_range delta (2-delta) (2+delta) x
  rw [abs_of_nonneg (add_nonneg hL.1 hR.1)]
  unfold gap endpoint
  linarith

theorem gap_second_bound {delta : ℝ} (hd : 0 < delta) (x : ℝ) :
    |deriv (deriv (gap delta)) x| ≤ 2*D/delta^2 := by
  have hL := doubleStep_smooth delta (1-delta) (1+delta)
  have hR := doubleStep_smooth delta (2-delta) (2+delta)
  have he1 : deriv (gap delta) = fun y =>
      deriv (endpoint delta 1) y + deriv (endpoint delta 2) y := by
    funext y
    exact (((hL.differentiable (by simp) y).hasDerivAt).add
      ((hR.differentiable (by simp) y).hasDerivAt)).deriv
  rw [he1]
  have hdL := (contDiff_infty_iff_deriv.mp hL).2
  have hdR := (contDiff_infty_iff_deriv.mp hR).2
  rw [(((hdL.differentiable (by simp) x).hasDerivAt).add
    ((hdR.differentiable (by simp) x).hasDerivAt)).deriv]
  calc
    _ ≤ |deriv (deriv (endpoint delta 1)) x| + |deriv (deriv (endpoint delta 2)) x| := abs_add _ _
    _ ≤ D/delta^2 + D/delta^2 :=
      add_le_add (doubleStep_second_bound hd _ _ _) (doubleStep_second_bound hd _ _ _)
    _ = _ := by ring


def sharp (x : ℝ) : ℝ := if x ∈ Ioc (1 : ℝ) 2 then 1 else 0

theorem sharp_le_upper {delta : ℝ} (hd : 0 < delta) (x : ℝ) :
    0 ≤ sharp x ∧ sharp x ≤ upper delta x := by
  by_cases hx : x ∈ Ioc (1 : ℝ) 2
  · rw [sharp,if_pos hx,doubleStep_one hd ⟨hx.1.le,hx.2⟩]
    exact ⟨by norm_num,le_rfl⟩
  · rw [sharp,if_neg hx]
    exact ⟨le_rfl,(doubleStep_range delta 1 2 x).1⟩

theorem gap_nonneg (delta x : ℝ) : 0 ≤ gap delta x :=
  add_nonneg (doubleStep_range delta (1-delta) (1+delta) x).1
    (doubleStep_range delta (2-delta) (2+delta) x).1

/-- These quantitative profiles are actual upper/gap witnesses for the
original strict-left/closed-right long interval, not arbitrary smooth data. -/
theorem upper_sharp_error {delta : ℝ} (hd : 0 < delta) (x : ℝ) :
    |upper delta x - sharp x| ≤ gap delta x := by
  by_cases hx : x ∈ Ioc (1 : ℝ) 2
  · rw [sharp,if_pos hx,doubleStep_one hd ⟨hx.1.le,hx.2⟩,sub_self,abs_zero]
    exact gap_nonneg delta x
  · rw [sharp,if_neg hx,sub_zero,abs_of_nonneg (doubleStep_range delta 1 2 x).1]
    by_cases hh : upper delta x = 0
    · rw [hh]; exact gap_nonneg delta x
    have hs := doubleStep_support (a := 1) (b := 2) hd hh
    have ho : x ≤ 1 ∨ 2 < x := by
      by_cases h : x ≤ 1
      · exact Or.inl h
      · exact Or.inr (lt_of_not_ge (fun h' => hx ⟨lt_of_not_ge h,h'⟩))
    rcases ho with hleft | hright
    · have he : endpoint delta 1 x = 1 := doubleStep_one hd ⟨hs.1,by linarith⟩
      have hrest := (doubleStep_range delta (2-delta) (2+delta) x).1
      have hu := (doubleStep_range delta 1 2 x).2
      unfold gap
      rw [he]
      linarith
    · have he : endpoint delta 2 x = 1 := doubleStep_one hd ⟨by linarith,hs.2⟩
      have hrest := (doubleStep_range delta (1-delta) (1+delta) x).1
      have hu := (doubleStep_range delta 1 2 x).2
      unfold gap
      rw [he]
      linarith

theorem rectangle_error {delta : ℝ} (hd : 0 < delta) (x y : ℝ) :
    0 ≤ upper delta x * upper delta y - sharp x * sharp y ∧
    upper delta x * upper delta y - sharp x * sharp y ≤
      gap delta x * upper delta y + upper delta x * gap delta y := by
  have hs₁ := sharp_le_upper hd x
  have hs₂ := sharp_le_upper hd y
  have hu₁ := (doubleStep_range delta 1 2 x).1
  have hu₂ := (doubleStep_range delta 1 2 y).1
  have hk₂ := gap_nonneg delta y
  have he₁ := (le_abs_self _).trans (upper_sharp_error hd x)
  have he₂ := (le_abs_self _).trans (upper_sharp_error hd y)
  constructor
  · exact sub_nonneg.mpr (mul_le_mul hs₁.2 hs₂.2 hs₂.1 hu₁)
  · have h1 := mul_le_mul_of_nonneg_right he₁ hu₂
    have h2 := mul_le_mul_of_nonneg_left he₂ hs₁.1
    have h3 := mul_le_mul_of_nonneg_right hs₁.2 hk₂
    nlinarith only [h1,h2,h3]

/-- Compact support gives an actual integral estimate of a bounded
normalized profile; the interval has length exactly two. -/
theorem norm_integral_le_two {f : ℝ → ℂ} (hf : Integrable f)
    (hs : Function.support f ⊆ Icc (1/2 : ℝ) (5/2))
    (M : ℝ) (hM : ∀ x ∈ Icc (1/2 : ℝ) (5/2), ‖f x‖ ≤ M) :
    (∫ x : ℝ, ‖f x‖) ≤ 2*M := by
  let S := Icc (1/2 : ℝ) (5/2)
  have heq : (fun x : ℝ => ‖f x‖) = S.indicator (fun x => ‖f x‖) := by
    funext x
    by_cases hx : x ∈ S
    · simp [hx]
    · have hz : f x = 0 := by by_contra hn; exact hx (hs hn)
      simp [hx,hz]
  rw [heq,integral_indicator measurableSet_Icc]
  calc
    _ ≤ ∫ _x in S, M :=
      setIntegral_mono_on hf.norm.integrableOn continuous_const.integrableOn_Icc measurableSet_Icc hM
    _ = 2*M := by
      unfold S
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (1/2 : ℝ) ≤ 5/2),
        intervalIntegral.integral_const,smul_eq_mul]
      ring

/-- Exact conversion of the actual real second derivative to the complex
profile used in P2; no unrelated N2 bound is a field. -/
theorem ofReal_secondDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    deriv (deriv (fun y => (f y : ℂ))) x = (deriv (deriv f) x : ℂ) := by
  have he : deriv (fun y => (f y : ℂ)) = fun y => (deriv f y : ℂ) := by
    funext y
    exact ((hf.differentiable (by simp) y).hasDerivAt.ofReal_comp).deriv
  rw [he]
  exact ((((contDiff_infty_iff_deriv.mp hf).2).differentiable (by simp) x).
    hasDerivAt.ofReal_comp).deriv

theorem real_N2_le {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : Function.support f ⊆ Icc (1/2 : ℝ) (5/2))
    (M0 M2 : ℝ) (h0 : ∀ x, |f x| ≤ M0)
    (h2 : ∀ x, |deriv (deriv f) x| ≤ M2) :
    N2 (fun x => (f x : ℂ)) ≤ 2*M0 + 2*M2 := by
  have hc : HasCompactSupport f := by
    change IsCompact (closure (Function.support f))
    exact isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc)
  have hfc := Complex.ofRealCLM.contDiff.comp hf
  have hcc : HasCompactSupport (fun x => (f x : ℂ)) :=
    hc.comp_left (g := Complex.ofRealCLM) (map_zero _)
  have hI := hfc.continuous.integrable_of_hasCompactSupport hcc
  have hD1 := (contDiff_infty_iff_deriv.mp hfc).2
  have hD2 := (contDiff_infty_iff_deriv.mp hD1).2
  have hI2 := hD2.continuous.integrable_of_hasCompactSupport hcc.deriv.deriv
  have hsC : Function.support (fun x => (f x : ℂ)) ⊆ Icc (1/2 : ℝ) (5/2) := by
    intro x hx; exact hs (by simpa using hx)
  have htC : tsupport (fun x => (f x : ℂ)) ⊆ Icc (1/2 : ℝ) (5/2) :=
    closure_minimal hsC isClosed_Icc
  have hsD2 : Function.support (deriv (deriv (fun x => (f x : ℂ)))) ⊆
      Icc (1/2 : ℝ) (5/2) :=
    support_deriv_subset.trans (tsupport_deriv_subset.trans htC)
  have hN0 := norm_integral_le_two hI hsC M0 (fun x hx => by simpa using h0 x)
  have hN2 := norm_integral_le_two hI2 hsD2 M2 (fun x hx => by
    rw [ofReal_secondDeriv hf]
    simpa using h2 x)
  exact add_le_add hN0 hN2

def upperCost : ℝ := 2+2*D
def gapCost : ℝ := 4+4*D

theorem gapCost_nonneg : 0 ≤ gapCost := by have h := D_nonneg; unfold gapCost; positivity

theorem upper_N2 {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4) :
    N2 (fun x => (upper delta x : ℂ)) ≤ upperCost/delta^2 := by
  have h := real_N2_le (upper_smooth delta) (upper_support hd hs) 1 (D/delta^2)
    (upper_abs_le_one delta) (fun x => doubleStep_second_bound hd 1 2 x)
  have hd2 : 0 < delta^2 := pow_pos hd 2
  have hs2 : delta^2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (by linarith : 0 ≤ (1/4 : ℝ)+delta)]
  apply h.trans
  apply (le_div_iff₀ hd2).2
  unfold upperCost
  field_simp [hd.ne']
  nlinarith

theorem gap_N2 {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4) :
    N2 (fun x => (gap delta x : ℂ)) ≤ gapCost/delta^2 := by
  have h := real_N2_le (gap_smooth delta) (gap_support hd hs) 2 (2*D/delta^2)
    (gap_abs_le_two delta) (gap_second_bound hd)
  have hd2 : 0 < delta^2 := pow_pos hd 2
  have hs2 : delta^2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (by linarith : 0 ≤ (1/4 : ℝ)+delta)]
  apply h.trans
  apply (le_div_iff₀ hd2).2
  unfold gapCost
  field_simp [hd.ne']
  nlinarith

end
end ImbalancedChen.Part3.TwoLongQuantitativeTransitionProfiles
