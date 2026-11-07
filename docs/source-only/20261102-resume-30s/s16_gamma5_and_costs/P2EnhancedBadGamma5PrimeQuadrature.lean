import ImbalancedChen.P2EnhancedBadGamma5ConstantCutoff
import ImbalancedChen.P2SeedOmegaBadGlobalCost
import MathlibNt.Wu2008DoubleSieve.Gamma5MassQuadrature

/-! SOURCE ONLY / UNCOMPILED.
Actual reciprocal-prime quadrature on the excluded Gamma5 square. The
native feedback kernel gamma5MassH is NOT used as the constant-cutoff
kernel. Only its already proved prime interval and Lipschitz APIs are
reused. Every boundary is closed, including 2u+v=1. -/
namespace ImbalancedChen.P2EnhancedBadGamma5PrimeQuadrature
noncomputable section
open Real Finset Set Filter MeasureTheory Wu2008DoubleSieve
open P2SeedOmegaLiteralFibre (a0 a2 corner badLower roughPairKernel)
open P2SeedOmegaLiteralFunctional (badMassLog)
open scoped Classical BigOperators Topology Interval

def start (t : ℝ) : ℝ := min a2 (max a0 (badLower t))
def section (t : ℝ) : ℝ := ∫ u in start t..a2, (1 : ℝ)/u

def closedPairs (R : ℝ) : Finset (ℕ×ℕ) :=
  (gamma5MassPrimes R corner a2 ×ˢ gamma5MassPrimes R a0 a2).filter
    (fun p => badLower (gamma5MassCoordinate R p.1) ≤ gamma5MassCoordinate R p.2)

def reciprocalMass (R : ℝ) : ℝ :=
  ∑ p ∈ closedPairs R, 1/((p.1 : ℝ)*p.2)

theorem start_bounds (t : ℝ) : a0 ≤ start t ∧ start t ≤ a2 :=
  ⟨le_min (by norm_num [a0,a2]) (le_max_left _ _), min_le_left _ _⟩

theorem start_eq {t : ℝ} (ht : t ∈ Icc corner a2) : start t = badLower t := by
  have hlo : a0 ≤ badLower t := (by norm_num [a0,corner] : a0 ≤ corner).trans
    (ht.1.trans (le_max_left _ _))
  rw [start,max_eq_right hlo,min_eq_right (P2SeedOmegaLiteralFibre.bad_fibre_geometry ht).2.2.1]

theorem lower_lipschitz (x y : ℝ) : |badLower x-badLower y| ≤ 2*|x-y| := by
  have h1 := le_abs_self (x-y)
  have h2 := neg_le_abs (x-y)
  unfold badLower
  rcases le_total x (1-2*x) with hx | hx <;>
    rcases le_total y (1-2*y) with hy | hy
  · rw [max_eq_right hx,max_eq_right hy,abs_le]
    constructor <;> linarith
  · rw [max_eq_right hx,max_eq_left hy,abs_le]
    constructor <;> linarith
  · rw [max_eq_left hx,max_eq_right hy,abs_le]
    constructor <;> linarith
  · rw [max_eq_left hx,max_eq_left hy]
    nlinarith [abs_nonneg (x-y)]

theorem start_lipschitz (x y : ℝ) : |start x-start y| ≤ 2*|x-y| :=
  (gamma5Mass_min_lipschitz a2 _ _).trans
    ((gamma5Mass_max_lipschitz a0 _ _).trans (lower_lipschitz x y))

theorem section_regular :
    (∀ t : ℝ, |section t| ≤ 4) ∧
      ∀ x y : ℝ, |section x-section y| ≤ 20*|x-y| := by
  have ha2 : a2 ∈ Icc (1/10 : ℝ) (1/2) := by norm_num [a2]
  have hm (t : ℝ) : start t ∈ Icc (1/10 : ℝ) (1/2) :=
    ⟨(by norm_num [a0] : (1/10 : ℝ) ≤ a0).trans (start_bounds t).1,
      (start_bounds t).2.trans ha2.2⟩
  have hreg := primeOrdered_moving_integral_lipschitz (H := fun _ _ => (1 : ℝ))
    (M := 1) (K := 0) ha2 (by norm_num) (by norm_num)
    (fun _ _ => continuousOn_const) (fun _ _ _ _ => by norm_num)
    (fun _ _ _ _ _ _ => by simp)
  constructor
  · intro t
    simpa [section] using hreg.1 (start t) (hm t)
  · intro x y
    have hh := hreg.2 (start x) (hm x) (start y) (hm y)
    have hl := start_lipschitz x y
    dsimp [section]
    norm_num at hh
    linarith

theorem section_integral_literal :
    (∫ u in corner..a2, section u/u) = badMassLog := by
  calc
    _ = ∫ u in corner..a2, ∫ v in badLower u..a2, roughPairKernel u v := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (by norm_num [corner,a2])] at hu
      rw [section,start_eq hu,← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro v _
      dsimp [roughPairKernel]
      ring
    _ = _ := by
      rw [P2SeedOmegaLiteralFibre.bad_rough_partition]
      exact P2SeedOmegaLiteralFunctional.badRoughDouble_eq_original_log

theorem closedPairs_rows {R : ℝ} (hR : 1 < R) :
    reciprocalMass R = ∑ p ∈ gamma5MassPrimes R corner a2,
      (∑ q ∈ gamma5MassPrimes R (start (gamma5MassCoordinate R p)) a2, (1 : ℝ)/q)/p := by
  have hrow (p : ℕ) (hp : p ∈ gamma5MassPrimes R corner a2) :
      (gamma5MassPrimes R a0 a2).filter
        (fun q => badLower (gamma5MassCoordinate R p) ≤ gamma5MassCoordinate R q) =
      gamma5MassPrimes R (start (gamma5MassCoordinate R p)) a2 := by
    have ht := (gamma5Mass_coordinate_mem_iff hR p).mp hp
    ext q
    simp only [mem_filter,gamma5Mass_coordinate_mem_iff hR,start_eq ⟨ht.2.1,ht.2.2⟩]
    have hlo : a0 ≤ badLower (gamma5MassCoordinate R p) :=
      (by norm_num [a0,corner] : a0 ≤ corner).trans (ht.2.1.trans (le_max_left _ _))
    constructor
    · rintro ⟨⟨hq,_,hu⟩,hl⟩; exact ⟨hq,hl,hu⟩
    · rintro ⟨hq,hl,hu⟩; exact ⟨⟨hq,hlo.trans hl,hu⟩,hl⟩
  unfold reciprocalMass closedPairs
  rw [sum_filter,sum_product]
  apply sum_congr rfl
  intro p hp
  rw [← sum_filter,hrow p hp,sum_div]
  apply sum_congr rfl
  intro q _
  ring

/-- Uniform in the actual moving scale. The affine equality square and
all prime endpoint atoms remain in the finite upper sum. -/
theorem reciprocal_quadrature {epsilon : ℝ} (he : 0 < epsilon) :
    ∀ᶠ R : ℝ in atTop, |reciprocalMass R-badMassLog| < epsilon := by
  let e := epsilon/12
  have he' : 0 < e := by dsimp [e]; positivity
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    primeOrdered_weighted_uniform 1 0 e (by norm_num) (by norm_num) he',
    primeOrdered_weighted_uniform 4 20 e (by norm_num) (by norm_num) he',
    primeOrdered_reciprocal_uniform 1 (by norm_num)] with R hR hinner houter hmass
  let P := gamma5MassPrimes R corner a2
  have hP : (∑ p ∈ P, 1/(p : ℝ)) ≤ 5 := by
    have hh := (le_abs_self _).trans (hmass corner a2
      (by norm_num [corner]) (by norm_num [corner,a2]) (by norm_num [a2])).le
    have hi := (primeOrdered_exponent_density_bounds
      (show (1/10 : ℝ) ≤ corner by norm_num [corner])
      (show corner ≤ a2 by norm_num [corner,a2]) (show a2 ≤ (1/2 : ℝ) by norm_num [a2])).2
    dsimp [P,gamma5MassPrimes]
    linarith
  have hrows (p : ℕ) :
      |(∑ q ∈ gamma5MassPrimes R (start (gamma5MassCoordinate R p)) a2, (1 : ℝ)/q)-
        section (gamma5MassCoordinate R p)| < e := by
    have hh := hinner (fun _ => (1 : ℝ)) (start (gamma5MassCoordinate R p)) a2
      continuousOn_const (fun _ _ => by norm_num) (fun _ _ _ _ => by simp)
      ((by norm_num [a0] : (1/10 : ℝ) ≤ a0).trans (start_bounds _).1)
      (start_bounds _).2 (by norm_num [a2])
    simpa [primeOrderedClosedSum,gamma5MassPrimes,section] using hh
  have hsum : |reciprocalMass R-
      ∑ p ∈ P, section (gamma5MassCoordinate R p)/p| ≤ 5*e := by
    rw [closedPairs_rows hR,← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ p ∈ P, e/p := by
        apply sum_le_sum
        intro p hp
        rw [← sub_div,abs_div,abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
        exact div_le_div_of_nonneg_right (hrows p).le (Nat.cast_nonneg p)
      _ = e*∑ p ∈ P, 1/(p : ℝ) := by rw [mul_sum]; simp only [mul_one_div]
      _ ≤ 5*e := by nlinarith [mul_le_mul_of_nonneg_left hP he'.le]
  have ho := houter section corner a2
    (primeOrdered_continuous_of_lipschitz (fun x _ y _ => section_regular.2 x y))
    (fun t _ => section_regular.1 t) (fun x _ y _ => section_regular.2 x y)
    (by norm_num [corner]) (by norm_num [corner,a2]) (by norm_num [a2])
  rw [section_integral_literal] at ho
  change |(∑ p ∈ P, section (gamma5MassCoordinate R p)/p)-badMassLog| < e at ho
  have ht := abs_sub_le (reciprocalMass R)
    (∑ p ∈ P, section (gamma5MassCoordinate R p)/p) badMassLog
  dsimp [e] at hsum ho
  linarith

theorem original_log_mass_bound : |badMassLog| ≤ 16 := by
  rw [← section_integral_literal]
  exact primeOrdered_integral_norm_le_four
    (by norm_num [corner]) (by norm_num [a2]) (by norm_num)
    (fun t _ => section_regular.1 t)

theorem reciprocal_mass_coarse : ∀ᶠ R : ℝ in atTop, reciprocalMass R ≤ 625 := by
  filter_upwards [reciprocal_quadrature (show (0 : ℝ) < 1 by norm_num)] with R hR
  have h := (le_abs_self _).trans hR.le
  have hm := (le_abs_self badMassLog).trans original_log_mass_bound
  linarith

end
end ImbalancedChen.P2EnhancedBadGamma5PrimeQuadrature
