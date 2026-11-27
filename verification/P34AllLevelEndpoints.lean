import ImbalancedChen.Part3AllLevelContinuedMaass

noncomputable section
open Set Filter Topology
open scoped UpperHalfPlane MatrixGroups ContDiff
open ImbalancedChen.Part3.ComplexOrderKBridgeSourceOnly
open ImbalancedChen.Part3.ComplexOrderKQODE
open ImbalancedChen.Part3.ContinuedFourierNonconstantMaass
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.CompletedEisensteinMeromorphic20261025a
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.LevelPrimitiveComplexEisenstein
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.CriticalEisensteinScattering20261025a
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a

example (ν : ℂ) (q : ℝ) (hq : 0 < q) :
    (q : ℂ) ^ 2 * deriv (deriv (complexOrderK ν)) q +
      (q : ℂ) * deriv (complexOrderK ν) q -
      ((q : ℂ) ^ 2 + ν ^ 2) * complexOrderK ν q = 0 :=
  complexOrderK_modifiedBessel_equation ν hq

example (y : ℝ) (hy : 0 < y) (x : ℝ) :
    Meromorphic (fun s : ℂ => completedEisensteinFourier s y x) :=
  completedEisensteinFourier_meromorphic hy x

example (y : ℝ) (hy : 0 < y) (x : ℝ) (s : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => completedEisensteinFourier w y x) s ↔
      s ≠ 0 ∧ s ≠ 1 :=
  completedEisensteinFourier_analyticAt_iff hy x s

example (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    completedActualEisenstein s z = completionFactor s *
      ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic.primitiveComplexEisenstein s z :=
  completedActualEisenstein_eq_initial s hs z

example (N : ℕ) (s : ℂ) (z : UpperHalfPlane) :
    levelPrimitiveComplexEisenstein N s z = (1 / 2 : ℂ) *
      ∑' v : ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a.LevelPrimitiveRow N,
        levelComplexSeed N z v s := rfl

example (N : ℕ) (t : ℝ) (z : UpperHalfPlane) :
    AnalyticAt ℂ (fun s => completedLevelOldform N s z) ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) :=
  completedLevelOldform_analyticAt_critical N t z

example (N : ℕ) : {s : ℂ | 0 < s.re ∧ s.re < 1} ⊆ completedRegularDomain N :=
  criticalStrip_subset_completedRegularDomain N

example : Tendsto completedScattering (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (-1)) :=
  completedScattering_tendsto_half

example : criticalScattering 0 = -1 := criticalScattering_zero

example (t : ℝ) : ‖criticalScattering t‖ = 1 := criticalScattering_norm t

example (y : ℝ) (hy : 0 < y) :
    reflectionHeightQuotient y (1 / 2 : ℂ) =
      (Real.sqrt y : ℂ) * (Real.log y : ℂ) := by
  simpa only [root0_eq_sqrt] using
    ImbalancedChen.Part3.CompletedEisensteinCentralHeight.reflectionHeightQuotient_half y hy

example (N : ℕ) (hN : 0 < N) (t : ℝ)
    (γ : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    completedLevelOldform N (criticalParameter t) ((γ : SL(2, ℤ)) • z) =
      completedLevelOldform N (criticalParameter t) z :=
  completedLevelOldform_Gamma0_invariant N hN _
    (criticalParameter_mem_completedRegularDomain N t) γ z

example (N : ℕ) (t : ℝ) (z : UpperHalfPlane) :
    maassLaplacian (completedLevelChart N (criticalParameter t)) z.re z.im =
      (((1 / 4 : ℝ) + t ^ 2 : ℝ) : ℂ) * completedLevelOldform N (criticalParameter t) z :=
  by simpa only [Complex.ofReal_add, Complex.ofReal_pow] using completedLevelOldform_maass_critical N t z

example (N : ℕ) (z : UpperHalfPlane) :
    maassLaplacian (completedLevelChart N (1 / 2)) z.re z.im =
      (1 / 4 : ℂ) * completedLevelOldform N (1 / 2) z :=
  completedLevelOldform_maass_center N z

example (N : ℕ) (hN : 0 < N) (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    continuedLevelEisenstein N s z = levelPrimitiveComplexEisenstein N s z :=
  continuedLevelEisenstein_eq_initial N hN s hs z

example (N : ℕ) (s : ℂ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => completedLevelOldform N s
      (ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic.horizontalPoint
        (Real.exp p.2) (Real.exp_pos p.2) p.1)) :=
  completedLevelOldform_logHeight_smooth N s
