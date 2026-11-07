import ImbalancedChen.ActualNormalizedRhoError

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

One beta pair must serve all later selected-row cutoffs. The existing
power-cutoff reserve fixes z=D^r. Here z varies throughout [w,D^r], while
the choice of epsilon and the threshold precede z, the retained policy,
the target and the enumeration cap. The cap need only cover w. The proof
keeps the actual absolute rough mass and uses its proved log-ratio bound.
-/

namespace ImbalancedChen.P5Z.OriginalCommonBetaVariableCutoffReserve

noncomputable section
open Filter Topology

theorem exists_variable_cutoff_normalized_reserve (r eta epsilonMax : ℝ)
    (hr : 0<r) (heta : 0<eta) (hepsilonMax : 0<epsilonMax) :
    ∃epsilon:ℝ,0<epsilon ∧ epsilon<1/8 ∧ epsilon<epsilonMax ∧ epsilon^2≤r ∧
      ∃D0:ℝ,2≤D0 ∧ ∀D:ℝ,D0≤D → ∀N cap:ℕ,0<N → Even N →
        D^(epsilon^2)≤(cap:ℝ) → ∀z:ℝ,D^(epsilon^2)≤z → z≤D^r →
          ∀retainOdd:List ℕ→Bool,
            let w:=D^(epsilon^2)
            let B:=D^epsilon
            let V:=actualSmallEulerProduct N cap w
            let S:=fixedRoughSupport retainOdd N cap w z
            let c:=fixedRoughCoefficient retainOdd N cap w z
            let density:=physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
              (actualSmallRoughRho retainOdd N cap w z B)
            0≤density-V*reciprocalTotientDensity S c ∧
              density-V*reciprocalTotientDensity S c≤eta*singularSeries N/Real.log D := by
  obtain ⟨CEuler,_hCEuler,hEuler⟩ := exists_actualSmallEulerProduct_le_singularSeries_log
  obtain ⟨C,K,hC,_hK,hsieve⟩ := exists_actualSmallRoughRho_density_error
  obtain ⟨Krough,hKrough,hrough⟩ := exists_fixedRoughAbsoluteDensity_le_logRatio
  obtain ⟨epsilon,hepsilon,hepsilon8,hepsilonMax',hepsilonr,hfloor⟩ :=
    exists_normalizedSmallRosser_epsilon_absorbing CEuler C r eta epsilonMax
      hr heta hepsilonMax
  have hlimit := tendsto_normalizedSmallRosserDensityError_mul_roughMassEnvelope
    CEuler C K Krough r epsilon hepsilon
  have hsmall : ∀ᶠ D:ℝ in atTop,
      (CEuler/epsilon^2)*actualSmallRosserDensityError C K D epsilon *
        (r/epsilon^2)*(1+Krough/(epsilon^2*Real.log D))<eta :=
    (tendsto_order.1 hlimit).2 eta hfloor
  obtain ⟨Dscalar,hDscalar⟩ := eventually_atTop.mp
    (hsmall.and (eventually_four_le_smallRosserPower epsilon hepsilon))
  obtain ⟨Dsieve,hDsieve,hsupply⟩ := hsieve epsilon hepsilon hepsilon8
  refine ⟨epsilon,hepsilon,hepsilon8,hepsilonMax',hepsilonr,
    max Dsieve Dscalar,hDsieve.trans (le_max_left _ _),?_⟩
  intro D hD N cap hNpos hEven hcap z hwz hzmax retainOdd
  have hDs : Dsieve≤D := (le_max_left _ _).trans hD
  have hDt : Dscalar≤D := (le_max_right _ _).trans hD
  have hD1 : 1<D := by linarith
  have hDpos : 0<D := by linarith
  have hlogD : 0<Real.log D := Real.log_pos hD1
  have hw : 1<D^(epsilon^2) :=
    Real.one_lt_rpow hD1 (sq_pos_of_pos hepsilon)
  have hlogw : 0<Real.log (D^(epsilon^2)) := Real.log_pos hw
  have hzpos : 0<z := (zero_lt_one.trans hw).trans_le hwz
  have hlogz : Real.log z≤r*Real.log D := by
    have h := Real.log_le_log hzpos hzmax
    rwa [Real.log_rpow hDpos] at h
  have hratio : Real.log z/Real.log (D^(epsilon^2))≤r/epsilon^2 := by
    calc
      Real.log z/Real.log (D^(epsilon^2))≤
          (r*Real.log D)/Real.log (D^(epsilon^2)) :=
        div_le_div_of_nonneg_right hlogz hlogw.le
      _ = r/epsilon^2 := by
        rw [Real.log_rpow hDpos]
        field_simp [hlogD.ne',hepsilon.ne']
  have hfactor : 0≤1+Krough/Real.log (D^(epsilon^2)) := by
    have hk : 0<Krough := by linarith
    positivity
  have hmass := hrough retainOdd N cap hEven (D^(epsilon^2)) z hw hwz
  have hmass' : reciprocalTotientDensity (fixedRoughSupport retainOdd N cap (D^(epsilon^2)) z)
      (fun d=>|fixedRoughCoefficient retainOdd N cap (D^(epsilon^2)) z d|) ≤
      (r/epsilon^2)*(1+Krough/(epsilon^2*Real.log D)) := by
    have h := hmass.trans (mul_le_mul_of_nonneg_right hratio hfactor)
    simpa only [Real.log_rpow hDpos] using h
  have hV := actualSmallEulerProduct_pos N cap (D^(epsilon^2)) hEven
  have hVbound := hEuler N cap hNpos hEven (D^(epsilon^2)) (hDscalar D hDt).2 hcap
  rw [Real.log_rpow hDpos] at hVbound
  have hE : 0≤actualSmallRosserDensityError C K D epsilon := by
    unfold actualSmallRosserDensityError
    positivity
  have hQ : 0≤(r/epsilon^2)*(1+Krough/(epsilon^2*Real.log D)) := by
    have hk : 0<Krough := by linarith
    positivity
  have herror := hsupply D hDs N cap hEven retainOdd z
  have hscalar := (hDscalar D hDt).1
  have hnorm : 0≤singularSeries N/Real.log D :=
    div_nonneg (singularSeries_pos N).le hlogD.le
  dsimp only at herror ⊢
  refine ⟨herror.1,herror.2.trans ?_⟩
  calc
    (actualSmallEulerProduct N cap (D^(epsilon^2))*actualSmallRosserDensityError C K D epsilon)*
        reciprocalTotientDensity (fixedRoughSupport retainOdd N cap (D^(epsilon^2)) z)
          (fun d=>|fixedRoughCoefficient retainOdd N cap (D^(epsilon^2)) z d|) ≤
      (actualSmallEulerProduct N cap (D^(epsilon^2))*actualSmallRosserDensityError C K D epsilon)*
        ((r/epsilon^2)*(1+Krough/(epsilon^2*Real.log D))) :=
      mul_le_mul_of_nonneg_left hmass' (mul_nonneg hV.le hE)
    _ = actualSmallEulerProduct N cap (D^(epsilon^2)) *
        (actualSmallRosserDensityError C K D epsilon *
          ((r/epsilon^2)*(1+Krough/(epsilon^2*Real.log D)))) := by ring
    _ ≤ (CEuler*singularSeries N/(epsilon^2*Real.log D)) *
        (actualSmallRosserDensityError C K D epsilon *
          ((r/epsilon^2)*(1+Krough/(epsilon^2*Real.log D)))) :=
      mul_le_mul_of_nonneg_right hVbound (mul_nonneg hE hQ)
    _ = (singularSeries N/Real.log D) *
        ((CEuler/epsilon^2)*actualSmallRosserDensityError C K D epsilon *
          (r/epsilon^2)*(1+Krough/(epsilon^2*Real.log D))) := by field_simp
    _ ≤ (singularSeries N/Real.log D)*eta :=
      mul_le_mul_of_nonneg_left hscalar.le hnorm
    _ = eta*singularSeries N/Real.log D := by ring

/-- The common physical beta pair is chosen before every variable row
cutoff and target. Only coverage of its own small cutoff is required. -/
theorem exists_variable_cutoff_target_reserve (nu r eta epsilonMax:ℝ)
    (hnu:0<nu) (hr:0<r) (heta:0<eta) (hepsilonMax:0<epsilonMax) :
    ∃epsilon:ℝ,0<epsilon ∧ epsilon<1/8 ∧ epsilon<epsilonMax ∧ epsilon^2≤r ∧
      ∃N0:ℕ,2≤N0 ∧ ∀N:ℕ,N0≤N → Even N → ∀cap:ℕ,
        (N:ℝ)^(nu*epsilon^2)≤(cap:ℝ) → ∀z:ℝ,
          (N:ℝ)^(nu*epsilon^2)≤z → z≤(N:ℝ)^(nu*r) → ∀retainOdd:List ℕ→Bool,
            let w:=(N:ℝ)^(nu*epsilon^2)
            let B:=(N:ℝ)^(nu*epsilon)
            let V:=actualSmallEulerProduct N cap w
            let S:=fixedRoughSupport retainOdd N cap w z
            let c:=fixedRoughCoefficient retainOdd N cap w z
            let density:=physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
              (actualSmallRoughRho retainOdd N cap w z B)
            0≤density-V*reciprocalTotientDensity S c ∧
              density-V*reciprocalTotientDensity S c≤eta*singularSeries N/Real.log (N:ℝ) := by
  obtain ⟨epsilon,hepsilon,hepsilon8,hepsilonMax',hepsilonr,D0,_hD0,hbound⟩ :=
    exists_variable_cutoff_normalized_reserve r (eta*nu) epsilonMax hr (mul_pos heta hnu) hepsilonMax
  have hpower : Tendsto (fun N:ℕ=>(N:ℝ)^nu) atTop atTop :=
    (tendsto_rpow_atTop hnu).comp tendsto_natCast_atTop_atTop
  obtain ⟨Nlarge,hNlarge⟩ := eventually_atTop.mp (hpower.eventually (eventually_ge_atTop D0))
  refine ⟨epsilon,hepsilon,hepsilon8,hepsilonMax',hepsilonr,
    max Nlarge 2,le_max_right _ _,?_⟩
  intro N hN hEven cap hcap z hwz hzmax retainOdd
  have hNlarge' : Nlarge≤N := (le_max_left _ _).trans hN
  have hN2 : 2≤N := (le_max_right _ _).trans hN
  have hNpos : 0<N := by omega
  have hNposR : (0:ℝ)<N := by exact_mod_cast hNpos
  have hcap' : ((N:ℝ)^nu)^(epsilon^2)≤(cap:ℝ) := by
    simpa only [←Real.rpow_mul hNposR.le] using hcap
  have hwz' : ((N:ℝ)^nu)^(epsilon^2)≤z := by
    simpa only [←Real.rpow_mul hNposR.le] using hwz
  have hzmax' : z≤((N:ℝ)^nu)^r := by
    simpa only [←Real.rpow_mul hNposR.le] using hzmax
  have h := hbound ((N:ℝ)^nu) (hNlarge N hNlarge') N cap hNpos hEven
    hcap' z hwz' hzmax' retainOdd
  dsimp only at h ⊢
  simp only [←Real.rpow_mul hNposR.le,Real.log_rpow hNposR] at h
  have hcancel : (eta*nu)*singularSeries N/(nu*Real.log (N:ℝ))=
      eta*singularSeries N/Real.log (N:ℝ) := by field_simp [hnu.ne']
  rw [hcancel] at h
  exact h

end
end ImbalancedChen.P5Z.OriginalCommonBetaVariableCutoffReserve
