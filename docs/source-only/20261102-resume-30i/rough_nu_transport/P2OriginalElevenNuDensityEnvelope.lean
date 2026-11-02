import ImbalancedChen.P2OriginalElevenPaidCoverDensity
import ImbalancedChen.PowerErrorBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The small Rosser scale is D=N^nu, whereas the ORIGINAL rough ceiling is
z=N^r.  In particular the residual logarithmic ratio is r/(nu*epsilon^2),
and the small Euler normalization costs 1/(nu*epsilon^2).  The sieve
coordinate remains 1/epsilon.  No square-root change of epsilon is made.
-/
namespace ImbalancedChen.P2OriginalElevenNuDensityEnvelope
noncomputable section
open Classical Filter
open scoped BigOperators Topology
open Certificates.P2OriginalSixthElevenLogSemantics
open P2OriginalSixthOmittedArithmeticMass P2OriginalElevenFullModulusOmittedCover
open P2OriginalElevenAttachedOmittedDensity

/-- Exact scale identities, including the actual Rosser coordinate. -/
theorem schedule_logs (nu epsilon r : ℝ) {N : ℕ} (hN : 1 < N)
    (hnu : 0 < nu) (he : 0 < epsilon) :
    Real.log ((N : ℝ)^nu) = nu*Real.log (N : ℝ) ∧
    Real.log ((N : ℝ)^(nu*epsilon^2)) = (nu*epsilon^2)*Real.log (N : ℝ) ∧
    Real.log ((N : ℝ)^(nu*epsilon)) /
      Real.log ((N : ℝ)^(nu*epsilon^2)) = 1/epsilon ∧
    Real.log ((N : ℝ)^r) / Real.log ((N : ℝ)^(nu*epsilon^2)) = r/(nu*epsilon^2) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hNl : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  refine ⟨?_,?_,?_,?_⟩
  · rw [Real.log_rpow hNp]
  · rw [Real.log_rpow hNp]
  · rw [Real.log_rpow hNp,Real.log_rpow hNp]
    field_simp [hnu.ne',he.ne',hNl] <;> ring
  · rw [Real.log_rpow hNp,Real.log_rpow hNp]
    field_simp [hnu.ne',he.ne',hNl] <;> ring

/-- These are the true pointwise/source-support conditions.  The display
of small divisors is not claimed to lie below L; only active weights do. -/
theorem schedule_cutoffs (nu epsilon r : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (he : 0 < epsilon) (he8 : epsilon < 1/8) (her : nu*epsilon^2 ≤ r)
    {N cap : ℕ} (hN : 2 ≤ N) (hcap : (N : ℝ)^r ≤ (cap : ℝ)) :
    1 < (N : ℝ)^nu ∧ (N : ℝ)^nu ≤ (N : ℝ) ∧
    1 < (N : ℝ)^(nu*epsilon^2) ∧
    (N : ℝ)^(nu*epsilon^2) ≤ (N : ℝ)^r ∧
    (N : ℝ)^(nu*epsilon^2) ≤ (N : ℝ)^(nu*epsilon) ∧
    (N : ℝ)^(nu*epsilon) < (N : ℝ)^nu ∧
    (N : ℝ)^(nu*epsilon^2) ≤ (cap : ℝ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have he1 : epsilon < 1 := by linarith
  have hesq : epsilon^2 ≤ epsilon := by
    nlinarith [mul_nonneg he.le (sub_nonneg.mpr he1.le)]
  have hwz := Real.rpow_le_rpow_of_exponent_le hNr.le her
  refine ⟨Real.one_lt_rpow hNr hnu,?_,
    Real.one_lt_rpow hNr (mul_pos hnu (sq_pos_of_pos he)),hwz,
    Real.rpow_le_rpow_of_exponent_le hNr.le (mul_le_mul_of_nonneg_left hesq hnu.le),
    Real.rpow_lt_rpow_of_exponent_lt hNr
      (by simpa only [mul_one] using mul_lt_mul_of_pos_left he1 hnu),hwz.trans hcap⟩
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr.le hnu1

/-- The active small coefficient keeps its original strict level. -/
theorem active_small_level (nu epsilon : ℝ) (N cap e : ℕ)
    (h : actualSmallRosserMinus N cap ((N : ℝ)^(nu*epsilon^2))
        ((N : ℝ)^(nu*epsilon)) e ≠ 0 ∨
      actualSmallRosserPlus N cap ((N : ℝ)^(nu*epsilon^2))
        ((N : ℝ)^(nu*epsilon)) e ≠ 0) :
    (e : ℝ) < (N : ℝ)^(nu*epsilon) ∧
      SmallPrimeSupportedAt ((N : ℝ)^(nu*epsilon^2)) e := by
  rcases h with h | h
  · exact (actualSmallRosserMinus_active h).2
  · exact (actualSmallRosserPlus_active h).2

/-- A Rankin loss w^(-s) has saving nu*epsilon^2*s at this schedule.
Thus the precise sublinear-power condition is a-nu*epsilon^2*s<1.
This scalar result does not assert any arithmetic Rankin bound. -/
theorem eventually_rankin_power_log_payment
    (nu epsilon s a C eta : ℝ) (j : ℕ)
    (hgap : a-nu*epsilon^2*s < 1) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      C*(N : ℝ)^a*((N : ℝ)^(nu*epsilon^2))^(-s)*
        (Real.log (N : ℝ))^j ≤ eta*singularNormalization N := by
  filter_upwards [eventually_powerLog_le_singularNormalization C
    (a-nu*epsilon^2*s) j hgap eta heta,eventually_ge_atTop (1 : ℕ)] with N h hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hid : (N : ℝ)^a*((N : ℝ)^(nu*epsilon^2))^(-s) =
      (N : ℝ)^(a-nu*epsilon^2*s) := by
    rw [← Real.rpow_mul hNp.le,← Real.rpow_add hNp]
    congr 1
    ring
  calc
    _ = C*((N : ℝ)^a*((N : ℝ)^(nu*epsilon^2))^(-s))*(Real.log (N : ℝ))^j := by ring
    _ = C*(N : ℝ)^(a-nu*epsilon^2*s)*(Real.log (N : ℝ))^j := by rw [hid]
    _ ≤ _ := h

/-- Full residual-divisor mass, at the ORIGINAL z=N^r, with the actual
nu-dependent denominator and no parameter redefinition. -/
theorem exists_residualMass_nu_envelope :
    ∃ K : ℝ, 1 < K ∧ ∀ (N cap : ℕ), Even N → ∀ nu epsilon r : ℝ,
      1 < N → 0 < nu → 0 < epsilon → nu*epsilon^2 ≤ r →
      2 ≤ (N : ℝ)^(nu*epsilon^2) →
      residualMass N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r) ≤
        (r/(nu*epsilon^2))*(1+K/((nu*epsilon^2)*Real.log (N : ℝ))) := by
  obtain ⟨K,hK,hinterval⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K,hK,?_⟩
  intro N cap hEven nu epsilon r hN hnu he her hw
  have hNp : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hwz := Real.rpow_le_rpow_of_exponent_le hNr.le her
  have hprime : ∀ p ∈ roughPrimeFinset N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r),
      p.Prime ∧ 2 < p := fun p hp => roughPrimeFinset_odd_of_even hEven hp
  have h := hinterval _ hprime ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r) hw hwz
    (fun p hp => (mem_roughPrimeFinset.mp hp).2.2.2)
  rw [residualMass_eq_euler]
  apply (roughPrime_eulerProduct_le_inverseProduct N cap
    ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r) hEven).trans
  rw [(schedule_logs nu epsilon r hN hnu he).2.2.2,Real.log_rpow hNp] at h
  exact h

/-- Rebuild the analytic envelope at D=N^nu.  The exponential error floor
is exp(-1/epsilon), while BOTH Euler costs retain nu.  All analytic
thresholds are combined before target, cap, policy, cell and subcarrier. -/
theorem exists_attached_nu_normalization_envelope (nu epsilon r : ℝ)
    (hnu : 0 < nu) (he : 0 < epsilon) (he8 : epsilon < 1/8)
    (her : nu*epsilon^2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N, N₀ ≤ N → Even N →
      ∀ cap, (N : ℝ)^r ≤ (cap : ℝ) → ∀ (ret : List ℕ → Bool) (c : Cell) (n : ℕ) (S : Finset ℕ),
        S ⊆ omittedRough ret c n N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r) →
        |restrictedDensity ret N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r)
          ((N : ℝ)^(nu*epsilon)) S| ≤
          A*(singularSeries N/Real.log (N : ℝ))*omittedMass c n N := by
  obtain ⟨B,hB,hEuler⟩ := exists_actualSmallEulerProduct_le_singularSeries_log
  obtain ⟨C,K,hC,hK,hsmall⟩ := exists_actualSmallRosser_density_sandwich
  obtain ⟨D₀,hD₀,hsmall⟩ := hsmall epsilon he he8
  obtain ⟨Kr,hKr,hresidual⟩ := exists_residualMass_nu_envelope
  let gamma := nu*epsilon^2
  let E₀ := C*Real.exp (-(1/epsilon))
  let M := E₀+1
  let R := r/gamma+1
  let A := (B/gamma)*(1+M)*R
  have hg : 0 < gamma := mul_pos hnu (sq_pos_of_pos he)
  have hr : 0 < r := hg.trans_le her
  have hM : 0 < M := by dsimp [M,E₀]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hDpower : Tendsto (fun N : ℕ => (N : ℝ)^nu) atTop atTop :=
    (tendsto_rpow_atTop hnu).comp tendsto_natCast_atTop_atTop
  have hE : Tendsto (fun N : ℕ => actualSmallRosserDensityError C K ((N : ℝ)^nu) epsilon)
      atTop (𝓝 E₀) := (tendsto_actualSmallRosserDensityError C K epsilon he).comp hDpower
  have hlog : Tendsto (fun N : ℕ => gamma*Real.log (N : ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hg
  have hQ : Tendsto (fun N : ℕ => (r/gamma)*(1+Kr/(gamma*Real.log (N : ℝ))))
      atTop (𝓝 (r/gamma)) := by
    simpa only [add_zero,mul_one] using ((hlog.const_div_atTop Kr).const_add 1).const_mul (r/gamma)
  have hpower : Tendsto (fun N : ℕ => (N : ℝ)^gamma) atTop atTop :=
    (tendsto_rpow_atTop hg).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ D₀ ≤ (N : ℝ)^nu ∧
      4 ≤ (N : ℝ)^gamma ∧ actualSmallRosserDensityError C K ((N : ℝ)^nu) epsilon < M ∧
      (r/gamma)*(1+Kr/(gamma*Real.log (N : ℝ))) < R := by
    filter_upwards [eventually_ge_atTop (2 : ℕ),
      hDpower.eventually (eventually_ge_atTop D₀),
      hpower.eventually (eventually_ge_atTop (4 : ℝ)),
      hE.eventually (gt_mem_nhds (show E₀ < M by dsimp [M]; linarith)),
      hQ.eventually (gt_mem_nhds (show r/gamma < R by dsimp [R]; linarith))]
      with N hN hD hw hE hQ
    exact ⟨hN,hD,hw,hE,hQ⟩
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨A,hA,max 2 N₀,le_max_left _ _,?_⟩
  intro N hN hEven cap hcap ret c n S hS
  obtain ⟨hN2,hD,hw,hE,hQ⟩ := hN₀ N ((le_max_right _ _).trans hN)
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hlogN := Real.log_pos hNr
  let V := actualSmallEulerProduct N cap ((N : ℝ)^gamma)
  let E := actualSmallRosserDensityError C K ((N : ℝ)^nu) epsilon
  have hV := actualSmallEulerProduct_pos N cap ((N : ℝ)^gamma) hEven
  have hE0 : 0 ≤ E := by dsimp [E,actualSmallRosserDensityError]; positivity
  have hs := hsmall ((N : ℝ)^nu) hD N cap hEven
  dsimp only at hs
  simp only [← Real.rpow_mul hNp.le] at hs
  have hminus : |actualSmallRosserMinusDensity N cap ((N : ℝ)^gamma)
      ((N : ℝ)^(nu*epsilon))| ≤ V*(1+E) := by
    apply abs_le.mpr
    constructor
    · have hlo := hs.1
      change V*(1-E) ≤ _ at hlo
      nlinarith [mul_nonneg hV.le hE0]
    · have hlo := hs.2.1
      change _ ≤ V at hlo
      nlinarith [mul_nonneg hV.le hE0]
  have hplus : |actualSmallRosserPlusDensity N cap ((N : ℝ)^gamma)
      ((N : ℝ)^(nu*epsilon))| ≤ V*(1+E) := by
    apply abs_le.mpr
    constructor
    · have hlo := hs.2.2.1
      change V ≤ _ at hlo
      nlinarith [mul_nonneg hV.le hE0]
    · exact hs.2.2.2.1
  have hbound := abs_restrictedDensity_le ret c n N cap _ _ _ (V*(1+E)) S hS
    (by positivity) hminus hplus
  have hwcap := (Real.rpow_le_rpow_of_exponent_le hNr.le her).trans hcap
  have hVbound := hEuler N cap (by omega) hEven ((N : ℝ)^gamma) hw hwcap
  rw [Real.log_rpow hNp] at hVbound
  have hres := (hresidual N cap hEven nu epsilon r (by omega) hnu he her
    (by linarith)).trans hQ.le
  have hres0 := residualMass_nonneg N cap ((N : ℝ)^gamma) ((N : ℝ)^r)
  have hfactor : V*(1+E)*residualMass N cap ((N : ℝ)^gamma) ((N : ℝ)^r) ≤
      A*(singularSeries N/Real.log (N : ℝ)) := by
    calc
      _ ≤ V*(1+M)*R := mul_le_mul
        (mul_le_mul_of_nonneg_left (by linarith : 1+E ≤ 1+M) hV.le) hres
        hres0 (by positivity)
      _ ≤ (B*singularSeries N/(gamma*Real.log (N : ℝ)))*(1+M)*R :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hVbound (by positivity)) hR.le
      _ = _ := by dsimp [A]; field_simp [hg.ne',hlogN.ne'] <;> ring
  calc
    _ ≤ (V*(1+E))*omittedMass c n N*residualMass N cap ((N : ℝ)^gamma) ((N : ℝ)^r) := hbound
    _ = (V*(1+E)*residualMass N cap ((N : ℝ)^gamma) ((N : ℝ)^r))*omittedMass c n N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (omittedMass_nonneg c n N)

theorem exists_full_attached_nu_density_payment (nu epsilon r eta : ℝ)
    (hnu : 0 < nu) (he : 0 < epsilon) (he8 : epsilon < 1/8)
    (her : nu*epsilon^2 ≤ r) (heta : 0 < eta) :
    ∃ n₀ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n, n₀ ≤ n → ∀ N, N₀ ≤ N → Even N →
      ∀ cap, (N : ℝ)^r ≤ (cap : ℝ) → ∀ (ret : List ℕ → Bool) (c : Cell) (S : Finset ℕ),
        S ⊆ omittedRough ret c n N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r) →
        |restrictedDensity ret N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r)
          ((N : ℝ)^(nu*epsilon)) S| < eta*(singularSeries N/Real.log (N : ℝ)) := by
  obtain ⟨A,hA,M,hM,hbound⟩ := exists_attached_nu_normalization_envelope nu epsilon r hnu he he8 her
  obtain ⟨n₀,T,hT,hmass⟩ := exists_common_omittedMass_rectangle (eta/A) (div_pos heta hA)
  refine ⟨n₀,max M T,hM.trans (le_max_left _ _),?_⟩
  intro n hn N hN hEven cap hcap ret c S hS
  have hNm := (le_max_left _ _).trans hN
  have hNt := (le_max_right _ _).trans hN
  have hN2 := hM.trans hNm
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hnorm := div_pos (singularSeries_pos N) hlog
  have hs := mul_lt_mul_of_pos_left (hmass n hn N hNt c) (mul_pos hA hnorm)
  have heq : (A*(singularSeries N/Real.log (N : ℝ)))*(eta/A) =
      eta*(singularSeries N/Real.log (N : ℝ)) := by field_simp [hA.ne'] <;> ring
  rw [heq] at hs
  exact (hbound N hNm hEven cap hcap ret c n S hS).trans_lt hs

end
end ImbalancedChen.P2OriginalElevenNuDensityEnvelope
