import ImbalancedChen.P5ActualHBAuxiliaryPrefixes

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Auxiliary-k Abel summation for the ORIGINAL group logarithms.  The norm
on the right is K's computed finite prefix maximum, plus the proved
arithmetic k-removal payment; no smallness of that maximum is assumed.
-/
namespace ImbalancedChen.P5Z.ActualHBAuxiliaryGroupLog
noncomputable section
open Classical Finset Set MeasureTheory
open scoped BigOperators Topology
open ImbalancedChen.Part3
open OriginalBetaPrimeSource OriginalBetaPrimeHalfOpenSW
open ActualRoughHeathBrownWords ActualHBGroupLogAbelPrefix ActualHBAuxiliaryPrefixes
open ActualHBGroupLogLine OriginalGroupLogAbelVariation
open PrimeMellinProfileVariation20261026b
open PerGroupIntegerHBAtlasPushforward HBRightClosedDyadicRoles
open ImbalancedChen.P5ActualIndependentUpperPairProfile ActualUpperOrderedHBSource

theorem auxiliary_exact_Abel (c : ℕ → ℂ) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (f : ℝ → ℂ)
    (hfd : ∀ y ∈ Icc u v, DifferentiableAt ℝ f y)
    (hfi : IntegrableOn (deriv f) (Icc u v)) (k q b : ℕ) :
    auxiliarySWError (Finset.Ioc (Nat.floor u) (Nat.floor v))
      (fun n => f n*c n) k q b =
      f v*prefix (coprimeMask c k) u q b (Nat.floor v) -
        ∫ y in Ioc u v, deriv f y*prefix (coprimeMask c k) u q b (Nat.floor y) := by
  rw [auxiliary_eq_mask,mask_mul]
  exact exact_Abel (coprimeMask c k) hu huv f hfd hfi q b

theorem auxiliary_Abel_bound (c : ℕ → ℂ) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (f : ℝ → ℂ)
    (hfd : ∀ y ∈ Icc u v, DifferentiableAt ℝ f y)
    (hfi : IntegrableOn (deriv f) (Icc u v)) (k q b : ℕ) :
    ‖auxiliarySWError (Finset.Ioc (Nat.floor u) (Nat.floor v))
      (fun n => f n*c n) k q b‖ ≤
      auxiliaryPrefixNorm c u v k q b *
        (‖f v‖ + ∫ y in Ioc u v, ‖deriv f y‖) := by
  rw [auxiliary_eq_mask,mask_mul]
  exact Abel_bound_by_actual_prefix (coprimeMask c k) hu huv f hfd hfi q b

theorem normalized_auxiliary_prefix_bound (c : ℕ → ℂ)
    {Phi : ℝ → ℝ} (hPhi : ContDiff ℝ 1 Phi)
    {M D U A H ell u v : ℝ} (hM0 : 0 ≤ M) (hD0 : 0 ≤ D)
    (hM : ∀ x ∈ Icc (1 : ℝ) 2, |Phi x| ≤ M)
    (hD : ∀ x ∈ Icc (1 : ℝ) 2, |deriv Phi x| ≤ D)
    (hU : 0 < U) (hA : 0 < A) (hell : 0 < ell)
    (hlo : U ≤ u) (huv : u ≤ v) (hhi : v ≤ 2*U)
    (hfloor : ell ≤ Real.log (A*U)) (t : ℝ) (k q b : ℕ) :
    ‖auxiliarySWError (Finset.Ioc (Nat.floor u) (Nat.floor v))
      (fun n => normalizedProfile Phi t U A H n*c n) k q b‖ ≤
      auxiliaryPrefixNorm c u v k q b *
        (|H|⁻¹*((M+D)/ell+M/ell^2)*(1+|t|)) := by
  have hfd : ∀ a ∈ Icc u v,
      DifferentiableAt ℝ (normalizedProfile Phi t U A H) a := by
    intro a ha
    exact (normalizedProfile_hasDerivAt hPhi t H hU hA
      (hU.trans_le (hlo.trans ha.1))
      (hell.trans_le (log_floor_on_interval hA hU hlo hfloor a ha)).ne').differentiableAt
  have hcont : ContinuousOn (deriv (normalizedProfile Phi t U A H)) (Icc u v) := by
    intro a ha
    have ha0 := hU.trans_le (hlo.trans ha.1)
    have hl := hell.trans_le (log_floor_on_interval hA hU hlo hfloor a ha)
    have hp : ContDiffAt ℝ 1 (physicalProfile Phi t U) a :=
      (physicalProfile_contDiffOn hPhi t hU).contDiffAt (isOpen_Ioi.mem_nhds ha0)
    have hr := reciprocalGroupLog_contDiffAt hA ha0 hl.ne'
    have hh : ContDiffAt ℝ 1 (normalizedProfile Phi t U A H) a :=
      (contDiffAt_const.mul hp).mul
        (Complex.ofRealCLM.contDiff.contDiffAt.comp a hr)
    exact (hh.derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  exact (auxiliary_Abel_bound c (hU.le.trans hlo) huv _ hfd
    hcont.integrableOn_Icc k q b).trans
      (mul_le_mul_of_nonneg_left
        (normalizedProfile_variation_le hPhi hM0 hD0 hM hD hU hA hell
          hlo huv hhi hfloor t) (auxiliaryPrefixNorm_nonneg _ _ _ _ _ _))

/-- The original group denominator and every other original group log
remain in their original positions.  The error is explicit with tau(k)^1.
This theorem is an arithmetic reduction, not the missing k=1 cancellation. -/
theorem actual_role_auxiliary_groupLog_bound (z y : ℝ) (role : Role)
    {Phi : ℝ → ℝ} (hPhi : ContDiff ℝ 1 Phi)
    {M D U A H ell u v : ℝ} (hM0 : 0 ≤ M) (hD0 : 0 ≤ D)
    (hM : ∀ x ∈ Icc (1 : ℝ) 2, |Phi x| ≤ M)
    (hD : ∀ x ∈ Icc (1 : ℝ) 2, |deriv Phi x| ≤ D)
    (hU : 0 < U) (hA : 0 < A) (hell : 0 < ell)
    (hlo : U ≤ u) (huv : u ≤ v) (hhi : v ≤ 2*U)
    (hfloor : ell ≤ Real.log (A*U)) (hz : 0 < z)
    (t : ℝ) (k q b : ℕ) (hk : 0 < k) (hq : 0 < q) :
    ‖auxiliarySWError (Finset.Ioc (Nat.floor u) (Nat.floor v))
      (fun n => normalizedProfile Phi t U A H n*actual z y role n) k q b‖ ≤
      (prefixNorm (actual z y role) u v q b +
        2*roleAmplitude role (Nat.floor v)*(k.divisors.card : ℝ)*(Nat.floor v : ℝ)/z) *
        (|H|⁻¹*((M+D)/ell+M/ell^2)*(1+|t|)) := by
  refine (normalized_auxiliary_prefix_bound (actual z y role) hPhi hM0 hD0 hM hD
    hU hA hell hlo huv hhi hfloor t k q b).trans ?_
  exact mul_le_mul_of_nonneg_right
    (actual_auxiliaryPrefixNorm_le z y role u v k q b hz hk hq) (by positivity)

/-- K's ACTUAL occupied original upper row supplies the group-log floor.
No new support/floor licence is required from the SW consumer, and no
modulus coefficient is divided by log(e*p). -/
theorem actual_occupied_auxiliary_groupLog_bound
    (D : Parameters) (b : Band D) (N : ℕ) (kappa0 : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (before after : List Row)
    (j : ℕ) (bs : List Block) (left right : List ℕ)
    {n : ℕ} {U u v M E : ℝ} (hU : 0 < U) (hnU : (n : ℝ) ≤ 2*U)
    (hlarge : 2 ≤ (N : ℝ)^(D.theta/2))
    (hn : upperTest D b N kappa0 Q rho
      (rowLine before after j bs left right n) ≠ 0)
    (Phi : ℝ → ℝ) (hPhi : ContDiff ℝ 1 Phi)
    (hM0 : 0 ≤ M) (hE0 : 0 ≤ E)
    (hM : ∀ x ∈ Icc (1 : ℝ) 2, |Phi x| ≤ M)
    (hE : ∀ x ∈ Icc (1 : ℝ) 2, |deriv Phi x| ≤ E)
    (hlo : U ≤ u) (huv : u ≤ v) (hhi : v ≤ 2*U)
    (z y : ℝ) (role : Role) (hz : 0 < z)
    (t : ℝ) (k q residue : ℕ) (hk : 0 < k) (hq : 0 < q) :
    let ell := (D.theta/2)*Real.log (N : ℝ)
    ‖auxiliarySWError (Finset.Ioc (Nat.floor u) (Nat.floor v))
      (fun a => normalizedProfile Phi t U (sameGroupFactor left right)
        (otherGroupLogs before after) a*actual z y role a) k q residue‖ ≤
      (prefixNorm (actual z y role) u v q residue +
        2*roleAmplitude role (Nat.floor v)*(k.divisors.card : ℝ)*(Nat.floor v : ℝ)/z) *
        (|otherGroupLogs before after|⁻¹*((M+E)/ell+M/ell^2)*(1+|t|)) := by
  obtain ⟨hA,hell,hfloor⟩ := actual_occupied_line_floor D b N kappa0 Q rho
    before after j bs left right hU hnU hlarge hn
  exact actual_role_auxiliary_groupLog_bound z y role hPhi hM0 hE0 hM hE
    hU hA hell hlo huv hhi hfloor hz t k q residue hk hq

end
end ImbalancedChen.P5Z.ActualHBAuxiliaryGroupLog
