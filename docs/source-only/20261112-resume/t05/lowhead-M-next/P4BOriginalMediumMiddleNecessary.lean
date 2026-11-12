import ImbalancedChen.P4BOriginalMediumTriplePowers

/-! A necessary size for the middle dyadic factor of an actual complete
level. This is useful for distinguishing the singleton and W algorithms. -/
namespace ImbalancedChen.P4BOriginalMediumMiddleNecessary
noncomputable section
open P4BOriginalMediumTriplePowers
open P4BOriginalMediumAtomFamily (Index support support_data third_data)
open P4BOriginalMediumOccupiedLengths (firstOwners first_length)
open P4BOriginalCollisionThirdFactor (thirdSupport)
open P5Z.HBRightClosedDyadicRoles (owner owner_owns)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos owns_bounds)

theorem necessary {order : ℕ} {zeta kap0 : ℝ} (I : Index order zeta kap0) (K : ℕ)
    (hx : 1<I.x) (he : 0<I.eta) (hu : I.x^(2*I.eta)≤I.U)
    {a b c : ℕ} (ha : a∈support I.P I.groups.1) (hb : b∈support I.P I.groups.2.1)
    (hc : c∈thirdSupport I.P I.J I.groups.2.2)
    (h2 : I.U^2*(lower (owner b):ℝ)*(lower (owner c):ℝ)^2<I.x^(1-8*(I.eta/2000))) :
    2*power I.x ((a*b*c:ℕ):ℝ) <
      1-10*(I.eta/2000)+power I.x (lower (owner b))+6*power I.x 2 := by
  let Q := fun n : ℕ => (lower (owner n):ℝ)
  have hQ (n : ℕ) : 0<Q n := by exact_mod_cast lower_pos (owner n)
  have hU := (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _).trans_le hu
  have h (n : ℕ) (hn : 0<n) : power I.x n≤power I.x 2+power I.x (Q n) := by
    rw [←power_mul (by norm_num : (0:ℝ)<2) (hQ n)]
    exact power_mono hx (by exact_mod_cast hn) (by exact_mod_cast (owns_bounds (owner_owns hn)).2)
  have hap := (support_data _ _ ha).1
  have hbp := (support_data _ _ hb).1
  have hcp := (third_data _ _ _ hc).1
  have hpos₁ : 0<(a:ℝ) := by exact_mod_cast hap
  have hpos₂ : 0<(b:ℝ) := by exact_mod_cast hbp
  have hpos₃ : 0<(c:ℝ) := by exact_mod_cast hcp
  have h1 := first_length I K (owner a) (owner b) (owner c) (Finset.mem_image_of_mem owner ha) hx he hu
  change Q a<I.U*I.x^(-(I.eta/2000)) at h1
  have hpσ := Real.rpow_pos_of_pos (zero_lt_one.trans hx) (-(I.eta/2000))
  have h1' : power I.x (Q a)<power I.x (I.U*I.x^(-(I.eta/2000))) :=
    lt_of_not_ge (fun h => (not_le_of_gt h1) ((positive_le_iff hx (mul_pos hU hpσ) (hQ a)).mpr h))
  rw [power_mul hU hpσ,power_base hx] at h1'
  have h2' := (strict_iff hx (mul_pos (mul_pos (sq_pos_of_pos hU) (hQ b)) (sq_pos_of_pos (hQ c)))).mp h2
  rw [power_mul (mul_pos (sq_pos_of_pos hU) (hQ b)) (sq_pos_of_pos (hQ c)),
    power_mul (sq_pos_of_pos hU) (hQ b),power_pow,power_pow] at h2'
  rw [Nat.cast_mul,Nat.cast_mul,power_mul (mul_pos hpos₁ hpos₂) hpos₃,power_mul hpos₁ hpos₂]
  change 2*(power I.x a+power I.x b+power I.x c)<1-10*(I.eta/2000)+power I.x (Q b)+6*power I.x 2
  norm_num only [Nat.cast_ofNat] at h2'
  linarith only [h1',h2',h a hap,h b hbp,h c hcp]

end
end ImbalancedChen.P4BOriginalMediumMiddleNecessary
