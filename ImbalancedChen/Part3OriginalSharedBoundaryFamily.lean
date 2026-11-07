import ImbalancedChen.Part3OriginalSharedWeightedBoundary

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26, phase 4.

Concrete original-range family bound AFTER genuine primitive zero/V/U
payment. The extra range Q1^2*(8Q1Q2Q3)^4 <= V^2*x^(-delta) is arithmetic
in ORIGINAL physical parameters. No W/nonzero/spectral bound is assumed.
The existing signedError Cauchy is used as an inequality. This proves a
legal boundary family only; the full retained 7/32 theorem remains OPEN.
-/

namespace ImbalancedChen.Part3.OriginalSharedBoundaryFamily20261026b
noncomputable section
open Classical Finset Filter TransposedPrimitiveUPayment
open OriginalSharedResidualBoundary20261026b OriginalSharedWeightedBoundary20261026b
open scoped BigOperators Topology

theorem original_boundary_weighted_residual_log_payment
    (B : ℕ) (sigma kappa c0 A delta : ℝ) (hsigma : 0 < sigma) (hdelta : 0 < delta) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
      d.Q1^2*d.physicalFactorCap^4 ≤ d.V^2*d.scale^(-delta) →
        originalOutside d * ‖sharedResidual d‖ ≤ d.scale^2/(Real.log d.scale)^A := by
  obtain ⟨C,hC,hbound⟩ := original_weighted_sharedResidual_boundary
  obtain ⟨xL,hxL,hlogs⟩ := eventually_actual_log_cost_le_rpow
    ((2^B)^2-1) 0 sigma hsigma (by linarith : 0 < delta/2)
  obtain ⟨xP,hpay⟩ := eventually_atTop.mp
    (eventually_const_rpow_two_le_logBudget C A hC.le (by linarith : 0 < delta/2))
  refine ⟨max xL xP,hxL.trans_le (le_max_left _ _),fun d hd hx hrange => ?_⟩
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hxpos : 0 < d.scale := by unfold MediumAtom.scale; positivity
  have hlog0 : 0 ≤ originalBetaLogCost B d := by
    unfold originalBetaLogCost
    have hbase : 0 ≤ 1+Real.log (2*d.V) := by
      linarith [Real.log_nonneg (show 1 ≤ 2*d.V by linarith [hd.2.1])]
    exact pow_nonneg hbase _
  have hlog : originalBetaLogCost B d ≤ d.scale^(delta/2) := by
    simpa only [pow_zero,mul_one,originalBetaLogCost] using
      hlogs B kappa c0 d hd ((le_max_left xL xP).trans hx)
  have hparam : d.U^2*d.Q1^2*d.physicalFactorCap^4 ≤ d.scale^2*d.scale^(-delta) := by
    calc
      _ = d.U^2*(d.Q1^2*d.physicalFactorCap^4) := by ring
      _ ≤ d.U^2*(d.V^2*d.scale^(-delta)) :=
        mul_le_mul_of_nonneg_left hrange (sq_nonneg _)
      _ = _ := by unfold MediumAtom.scale; ring
  have hpower : originalOutside d * ‖sharedResidual d‖ ≤ C*d.scale^(2-delta/2) := by
    calc
      _ ≤ C*d.U^2*d.Q1^2*d.physicalFactorCap^4*originalBetaLogCost B d :=
        hbound B sigma kappa c0 d hd
      _ = (C*(d.U^2*d.Q1^2*d.physicalFactorCap^4))*originalBetaLogCost B d := by ring
      _ ≤ (C*(d.scale^2*d.scale^(-delta)))*d.scale^(delta/2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hparam hC.le) hlog hlog0 (by positivity)
      _ = C*d.scale^(2-delta/2) := by
        rw [← Real.rpow_natCast d.scale 2]
        rw [mul_assoc, mul_assoc, ← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
        rw [show (2 : ℝ)+(-delta+delta/2) = 2-delta/2 by ring]
  exact hpower.trans (hpay d.scale ((le_max_right xL xP).trans hx))

/-- Actual squared signed-error conclusion on the displayed original
boundary range. The public parent already paid zero covariance and U/V,
and its uniform error is retained in C. No small-core estimate is assumed. -/
theorem uniformAuxiliarySW_original_shared_boundary_signedError_sq
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 delta : ℝ)
    (hsigma : 0 < sigma) (hsigma_small : sigma < 1/100)
    (hc0 : 0 < c0) (hkappa : 0 ≤ kappa) (hkappa_small : kappa ≤ sigma/100)
    (hdelta : 0 < delta)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i : ι, x0 ≤ (F i).scale →
        (F i).Q1^2*(F i).physicalFactorCap^4 ≤ (F i).V^2*(F i).scale^(-delta) →
        ‖(F i).signedError‖^2 ≤ C*(F i).scale^2/(Real.log (F i).scale)^A := by
  intro A hA
  obtain ⟨CE,hCE,xE,hxE,henergy⟩ :=
    uniformAuxiliarySW_sharedFirstFactor_signedError_sq_le_nonzero_add_log_payment
      F B C0 sigma kappa c0 hsigma hsigma_small hc0 hkappa hkappa_small hadmissible hSW A hA
  obtain ⟨xN,hxN,hnonzero⟩ := original_boundary_weighted_residual_log_payment
    B sigma kappa c0 A delta hsigma hdelta
  refine ⟨CE+1,by linarith,max xE xN,hxE.trans_le (le_max_left _ _),?_⟩
  intro i hx hrange
  have hE := henergy i ((le_max_left xE xN).trans hx)
  have hN := hnonzero (F i) (hadmissible i) ((le_max_right xE xN).trans hx) hrange
  change ‖(F i).signedError‖^2 ≤ originalOutside (F i)*(sharedResidual (F i)).re +
    CE*(F i).scale^2/(Real.log (F i).scale)^A at hE
  have hout : 0 ≤ originalOutside (F i) := by unfold originalOutside; positivity
  calc
    _ ≤ originalOutside (F i)*(sharedResidual (F i)).re +
        CE*(F i).scale^2/(Real.log (F i).scale)^A := hE
    _ ≤ originalOutside (F i)*‖sharedResidual (F i)‖ +
        CE*(F i).scale^2/(Real.log (F i).scale)^A :=
      add_le_add (mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (Complex.abs_re_le_norm _)) hout) le_rfl
    _ ≤ (F i).scale^2/(Real.log (F i).scale)^A +
        CE*(F i).scale^2/(Real.log (F i).scale)^A := add_le_add hN le_rfl
    _ = (CE+1)*(F i).scale^2/(Real.log (F i).scale)^A := by ring

/-- The actual linear medium-error conclusion on this explicit boundary
subrange, using the squared reduction at budget 2*A. -/
theorem uniformAuxiliarySW_original_shared_boundary_signedError
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 delta : ℝ)
    (hsigma : 0 < sigma) (hsigma_small : sigma < 1/100)
    (hc0 : 0 < c0) (hkappa : 0 ≤ kappa) (hkappa_small : kappa ≤ sigma/100)
    (hdelta : 0 < delta)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i : ι, x0 ≤ (F i).scale →
        (F i).Q1^2*(F i).physicalFactorCap^4 ≤ (F i).V^2*(F i).scale^(-delta) →
        ‖(F i).signedError‖ ≤ C*(F i).scale/(Real.log (F i).scale)^A := by
  intro A hA
  obtain ⟨C,hC,x0,hx0,hbound⟩ :=
    uniformAuxiliarySW_original_shared_boundary_signedError_sq F B C0 sigma kappa c0 delta
      hsigma hsigma_small hc0 hkappa hkappa_small hdelta hadmissible hSW (2*A) (by linarith)
  refine ⟨C+1,by linarith,x0,hx0,fun i hx hrange => ?_⟩
  have hx1 : 1 < (F i).scale := hx0.trans_le hx
  have hlog : 0 < Real.log (F i).scale := Real.log_pos hx1
  have hpow : (Real.log (F i).scale)^(2*A) = ((Real.log (F i).scale)^A)^2 := by
    rw [show 2*A = A+A by ring, Real.rpow_add hlog]
    ring
  let L : ℝ := (F i).scale/(Real.log (F i).scale)^A
  have hL : 0 ≤ L := div_nonneg (zero_lt_one.trans hx1).le (Real.rpow_nonneg hlog.le _)
  have hsq : ‖(F i).signedError‖^2 ≤ C*L^2 := by
    have h := hbound i hx hrange
    simpa only [L,hpow,div_pow,mul_div_assoc] using h
  have hCpow : C ≤ (C+1)^2 := by nlinarith
  have hsq' : ‖(F i).signedError‖^2 ≤ ((C+1)*L)^2 := by
    calc
      _ ≤ C*L^2 := hsq
      _ ≤ (C+1)^2*L^2 := mul_le_mul_of_nonneg_right hCpow (sq_nonneg _)
      _ = _ := by ring
  have hlin : ‖(F i).signedError‖ ≤ (C+1)*L :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) hL)).mp hsq'
  simpa only [L,mul_div_assoc] using hlin

end
end ImbalancedChen.Part3.OriginalSharedBoundaryFamily20261026b
