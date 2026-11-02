import ImbalancedChen.P2LowerFiniteCellRawDensityReserve
import ImbalancedChen.ActualSmallEulerNormalization
import ImbalancedChen.EvenRoughAbsoluteDensity
import ImbalancedChen.NormalizedSmallRosserError

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The ALL/ANY rounded coefficient can have negative support OUTSIDE the
raw retained support. Its absolute mass is therefore proved on its actual
complete divisor carrier, not borrowed from the unrounded even tree.
This supplies a uniform normalized payment of the very beta-loss term
in the original lower finite-cell raw-density reserve. The choice of
small parameter precedes the target, policy and mesh. Rounding itself,
physical support licences and the same-rho signed PP remain separate.
-/

namespace ImbalancedChen.P5OriginalStartsRoundedBetaReserve

noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P2LowerFiniteCellRounding

/-- Actual absolute mass, including outer-rounded negative cells. -/
def roundedMass (retainEven : List ℕ → Bool) (N cap : ℕ) (w z tau : ℝ) : ℝ :=
  reciprocalTotientDensity (universe N cap w z)
    (fun d => |coefficient retainEven N cap w z tau d|)

/-- The complete divisor carrier is the product of the same actual rough
primes, with target primes deleted and a strict upper cutoff. -/
theorem universe_eq_primeProduct_divisors (N cap : ℕ) (w z : ℝ) :
    universe N cap w z = ((roughPrimeFinset N cap w z).prod id).divisors := by
  unfold universe roughProduct
  have hprod : (roughPrimeFinset N cap w z).prod id =
      (roughPrimeUniverse N cap w z).prod := by
    rw [← roughPrimeUniverse_toFinset N cap w z]
    simpa using List.prod_toFinset (fun p : ℕ => p)
      (roughPrimeUniverse_nodup N cap w z)
  rw [hprod]

/-- No retained-support inclusion is required for the rounded coefficient.
The complete absolute mass is bounded by its exact finite Euler product. -/
theorem roundedMass_le_eulerProduct (retainEven : List ℕ → Bool)
    (N cap : ℕ) (w z tau : ℝ) :
    roundedMass retainEven N cap w z tau ≤
      ∏ p ∈ roughPrimeFinset N cap w z, (1+1/((p:ℝ)-1)) := by
  have hprime : ∀ p ∈ roughPrimeFinset N cap w z, Nat.Prime p :=
    fun _ hp => (mem_roughPrimeFinset.mp hp).2.1
  have hcop : ∀ p ∈ roughPrimeFinset N cap w z, Nat.Coprime p N := by
    intro p hp
    have h := mem_roughPrimeFinset.mp hp
    exact h.2.1.coprime_iff_not_dvd.mpr h.2.2.1
  calc
    roundedMass retainEven N cap w z tau ≤
        ∑ d ∈ universe N cap w z, 1/(Nat.totient d:ℝ) := by
      unfold roundedMass reciprocalTotientDensity
      apply Finset.sum_le_sum
      intro d _
      exact div_le_div_of_nonneg_right
        (coefficient_abs_le_one retainEven N cap w z tau d) (Nat.cast_nonneg _)
    _ = _ := by
      rw [universe_eq_primeProduct_divisors]
      exact reciprocalTotient_sum_divisors_primeProduct N _ hprime hcop

/-- One Mertens constant serves every actual rounded history and mesh.
A truncated enumeration cap remains allowed. -/
theorem exists_roundedMass_le_logRatio :
    ∃ Krough : ℝ, 1<Krough ∧
      ∀ (retainEven : List ℕ → Bool) (N cap : ℕ), Even N →
      ∀ w z tau : ℝ, 2≤w → w≤z →
        roundedMass retainEven N cap w z tau ≤
          Real.log z/Real.log w*(1+Krough/Real.log w) := by
  obtain ⟨Krough,hKrough,hinterval⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨Krough,hKrough,?_⟩
  intro retainEven N cap hN w z tau hw hwz
  exact ((roundedMass_le_eulerProduct retainEven N cap w z tau).trans
    (roughPrime_eulerProduct_le_inverseProduct N cap w z hN)).trans
      (hinterval (roughPrimeFinset N cap w z)
        (fun _ hp => roughPrimeFinset_odd_of_even hN hp)
        w z hw hwz (fun _ hp => (mem_roughPrimeFinset.mp hp).2.2.2))

/-- A single top rough exponent controls all smaller starting cutoffs,
without a separate epsilon choice at a and h. -/
theorem exists_roundedMass_le_powerEnvelope :
    ∃ Krough : ℝ, 1<Krough ∧
      ∀ (retainEven : List ℕ → Bool) (N cap : ℕ), Even N →
      ∀ D epsilon r z tau : ℝ, 1<D → 0<epsilon →
        2≤D^(epsilon^2) → D^(epsilon^2)≤z → z≤D^r →
        roundedMass retainEven N cap (D^(epsilon^2)) z tau ≤
          (r/epsilon^2)*(1+Krough/(epsilon^2*Real.log D)) := by
  obtain ⟨Krough,hKrough,hrough⟩ := exists_roundedMass_le_logRatio
  refine ⟨Krough,hKrough,?_⟩
  intro retainEven N cap hN D epsilon r z tau hD he hw hwz hz
  have hDpos : 0<D := zero_lt_one.trans hD
  have hlogw : 0<Real.log (D^(epsilon^2)) :=
    Real.log_pos (by linarith)
  have hzpos : 0<z := (by linarith : 0<D^(epsilon^2)).trans_le hwz
  have hratio : Real.log z/Real.log (D^(epsilon^2)) ≤
      Real.log (D^r)/Real.log (D^(epsilon^2)) :=
    div_le_div_of_nonneg_right (Real.log_le_log hzpos hz) hlogw.le
  have hK0 : 0≤Krough := by linarith
  have hfactor : 0≤1+Krough/Real.log (D^(epsilon^2)) := by positivity
  have h := (hrough retainEven N cap hN _ z tau hw hwz).trans
    (mul_le_mul_of_nonneg_right hratio hfactor)
  rw [roughPower_log_ratio hDpos (Real.log_pos hD).ne' he.ne',
    Real.log_rpow hDpos] at h
  exact h

/-- This is the literal compiler beta reserve, not a proxy for the signed
density and not an assumed final error. C,K are auxiliary beta constants. -/
def betaLoss (C K D epsilon : ℝ) (retainEven : List ℕ → Bool)
    (N cap : ℕ) (z tau : ℝ) : ℝ :=
  (actualSmallEulerProduct N cap (D^(epsilon^2))*
    actualSmallRosserDensityError C K D epsilon)*
      roundedMass retainEven N cap (D^(epsilon^2)) z tau

/-- One epsilon and one large D threshold pay the ACTUAL rounded beta
loss uniformly in the policy, finite mesh and all cutoffs below D^r.
No policy may enter the choice of epsilon or the threshold. -/
theorem exists_betaLoss_le_normalized_reserve
    (C K r eta epsilonMax : ℝ) (hC : 0<C) (hr : 0<r)
    (heta : 0<eta) (hepsilonMax : 0<epsilonMax) :
    ∃ epsilon : ℝ, 0<epsilon ∧ epsilon<1/8 ∧ epsilon<epsilonMax ∧
      epsilon^2≤r ∧ ∃ D0 : ℝ, 2≤D0 ∧
      ∀ D : ℝ, D0≤D → ∀ N cap : ℕ, 0<N → Even N →
        D^(epsilon^2)≤(cap:ℝ) →
        ∀ z tau : ℝ, D^(epsilon^2)≤z → z≤D^r →
        ∀ retainEven : List ℕ → Bool,
          betaLoss C K D epsilon retainEven N cap z tau ≤
            eta*singularSeries N/Real.log D := by
  obtain ⟨B,_hB,hEuler⟩ := exists_actualSmallEulerProduct_le_singularSeries_log
  obtain ⟨Krough,hKrough,hrough⟩ := exists_roundedMass_le_powerEnvelope
  obtain ⟨epsilon,he,he8,hemax,her,hfloor⟩ :=
    exists_normalizedSmallRosser_epsilon_absorbing B C r eta epsilonMax
      hr heta hepsilonMax
  have hlimit := tendsto_normalizedSmallRosserDensityError_mul_roughMassEnvelope
    B C K Krough r epsilon he
  have hsmall : ∀ᶠ D : ℝ in atTop,
      (B/epsilon^2)*actualSmallRosserDensityError C K D epsilon*
        (r/epsilon^2)*(1+Krough/(epsilon^2*Real.log D))<eta :=
    (tendsto_order.1 hlimit).2 eta hfloor
  obtain ⟨Dscalar,hscalar⟩ := eventually_atTop.mp
    (hsmall.and (eventually_four_le_smallRosserPower epsilon he))
  refine ⟨epsilon,he,he8,hemax,her,max 2 Dscalar,le_max_left _ _,?_⟩
  intro D hD N cap hNpos hN hcap z tau hwz hz retainEven
  have hD2 : 2≤D := (le_max_left _ _).trans hD
  have hDs : Dscalar≤D := (le_max_right _ _).trans hD
  have hD1 : 1<D := by linarith
  have hDpos : 0<D := by linarith
  have hlogD : 0<Real.log D := Real.log_pos hD1
  have hwfour := (hscalar D hDs).2
  have hV := actualSmallEulerProduct_pos N cap (D^(epsilon^2)) hN
  have hVbound := hEuler N cap hNpos hN (D^(epsilon^2)) hwfour hcap
  rw [Real.log_rpow hDpos] at hVbound
  have hE : 0≤actualSmallRosserDensityError C K D epsilon := by
    unfold actualSmallRosserDensityError
    positivity
  have hQ : 0≤(r/epsilon^2)*(1+Krough/(epsilon^2*Real.log D)) := by
    have : 0<Krough := by linarith
    positivity
  have hmass := hrough retainEven N cap hN D epsilon r z tau hD1 he
    (by linarith) hwz hz
  have hnorm : 0≤singularSeries N/Real.log D :=
    div_nonneg (singularSeries_pos N).le hlogD.le
  unfold betaLoss
  calc
    _ ≤ (actualSmallEulerProduct N cap (D^(epsilon^2))*
        actualSmallRosserDensityError C K D epsilon)*
          ((r/epsilon^2)*(1+Krough/(epsilon^2*Real.log D))) :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg hV.le hE)
    _ = actualSmallEulerProduct N cap (D^(epsilon^2))*
        (actualSmallRosserDensityError C K D epsilon*
          ((r/epsilon^2)*(1+Krough/(epsilon^2*Real.log D)))) := by ring
    _ ≤ (B*singularSeries N/(epsilon^2*Real.log D))*
        (actualSmallRosserDensityError C K D epsilon*
          ((r/epsilon^2)*(1+Krough/(epsilon^2*Real.log D)))) :=
      mul_le_mul_of_nonneg_right hVbound (mul_nonneg hE hQ)
    _ = (singularSeries N/Real.log D)*
        ((B/epsilon^2)*actualSmallRosserDensityError C K D epsilon*
          (r/epsilon^2)*(1+Krough/(epsilon^2*Real.log D))) := by field_simp
    _ ≤ (singularSeries N/Real.log D)*eta :=
      mul_le_mul_of_nonneg_left (hscalar D hDs).1.le hnorm
    _ = eta*singularSeries N/Real.log D := by ring

end
end ImbalancedChen.P5OriginalStartsRoundedBetaReserve
