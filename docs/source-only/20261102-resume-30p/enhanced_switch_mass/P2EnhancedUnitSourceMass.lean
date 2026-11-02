import ImbalancedChen.P2EnhancedUnitSourceGeometry
import ImbalancedChen.P2OriginalPositiveSameQMassLift
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitBoxedLimit

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual enhanced-Q UNSIFTED unit masses reach their two independent unit
integrals. The analytic input is the existing, arbitrary-R and arbitrary-
phi physical prime-fibre theorem, not the classical-Q source receiver.
The threshold precedes Q, d, support and sigma. The genuine log quotient
is used throughout. Only an upper mass is proved for the target-deleted
strict source, since the proved physical envelope has closed endpoints
and drops target deletion. No bilateral source limit or PP is asserted.
-/

namespace ImbalancedChen.P2EnhancedUnitSourceMass
noncomputable section
open Real Filter Finset Wu2008DoubleSieve
open P2EnhancedUnitSourceGeometry P2EnhancedSwitchedUnsiftedSource
open P2EnhancedSwitchedTrueNormalization
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open P2OriginalPositiveSameQMassLift (thetaAtom_nonneg)
open P2EnhancedTwentyOneSameQWeighted (Theta)
open P2SeedOmegaLastUnitIntegrals (unit20Mass unit21Mass)
open P2SeedOmegaLiteralFibre (a2 a3 b)
open scoped Classical BigOperators Topology

/-- Actual residual scale raised to actual alpha is exactly N/d. -/
theorem scale_identity {N d : ℕ} {Q : ℝ}
    (hN : 0<N) (hd : 0<d) (hR : 1<Q/d) :
    (Q/d)^trueAlpha N Q d=(N:ℝ)/d := by
  have hX : (0:ℝ)<(N:ℝ)/d := div_pos (Nat.cast_pos.mpr hN) (Nat.cast_pos.mpr hd)
  rw [trueAlpha,rpow_def_of_pos (zero_lt_one.trans hR)]
  rw [mul_div_cancel₀ _ (log_pos hR).ne',exp_log hX]

/-- Uniform physical prime-fibre limits at the actual enhanced Q.
The two limits are kept separate and each has tolerance epsilon. -/
theorem physical_pair_uniform {eta epsilon : ℝ} (heta : 0<eta) (he : 0<epsilon) :
    ∃T : ℕ,4≤T ∧ ∀N : ℕ,T≤N → ∀Q : ℝ,∀d : ℕ,0<d →
      (N:ℝ)^eta≤Q/d →
      (|log (Q/d)/((N:ℝ)/d)*physical20 N Q d-unit20Mass (trueAlpha N Q d)|<epsilon) ∧
      (|log (Q/d)/((N:ℝ)/d)*physical21 N Q d-unit21Mass (trueAlpha N Q d)|<epsilon) := by
  obtain ⟨R0,hR0,hphysical⟩ := HighUnit.physical_pair_uniform epsilon he
  have ht : Tendsto (fun N : ℕ => (N:ℝ)^eta) atTop atTop :=
    (tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop
  obtain ⟨T,hT⟩ := eventually_atTop.mp (ht.eventually_ge_atTop R0)
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hNT Q d hd hscale
  have hN4 : 4≤N := (le_max_left 4 T).trans hNT
  have hlarge := (hT N ((le_max_right 4 T).trans hNT)).trans hscale
  have hR : 1<Q/d := hR0.trans_le hlarge
  have h := hphysical (Q/d) hlarge a2 a3 b (trueAlpha N Q d)
    (by norm_num [a2]) (by norm_num [a3]) (by norm_num [b])
  rw [scale_identity (by omega : 0<N) hd hR] at h
  simpa only [physical20,physical21,
    P2SeedOmegaUnitChartIdentification.unit20Mass_eq_pinned_J20,
    P2SeedOmegaUnitChartIdentification.unit21Mass_eq_pinned_J21] using h

/-- A real source upper mass, derived from its full-list geometry and
the actual PNT unit-fibre limit. No assumed unit mass/count license. -/
theorem actual_unit_upper_uniform {eta epsilon : ℝ} (heta : 0<eta) (he : 0<epsilon) :
    ∃T : ℕ,4≤T ∧ ∀N : ℕ,T≤N → ∀Q : ℝ,∀d : ℕ,0<d →
      (N:ℝ)^eta≤Q/d →
      unitWordMass N Q d [2,3,3,3,3]≤
        rawMainAtom N Q d unit20Mass+epsilon*((N:ℝ)/((d:ℝ)*log (Q/d))) ∧
      unitWordMass N Q d [3,3,3,3,3,3]≤
        rawMainAtom N Q d unit21Mass+epsilon*((N:ℝ)/((d:ℝ)*log (Q/d))) := by
  obtain ⟨T,hT,hphysical⟩ := physical_pair_uniform heta he
  refine ⟨T,hT,?_⟩
  intro N hNT Q d hd hscale
  have hN4 := hT.trans hNT
  have hN1 : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hR : 1<Q/d := (one_lt_rpow hN1 heta).trans_le hscale
  obtain ⟨h20,h21⟩ := hphysical N hNT Q d hd hscale
  have hu20 := HighUnit.unnormalize (by omega : 0<N) hd hR h20
  have hu21 := HighUnit.unnormalize (by omega : 0<N) hd hR h21
  obtain ⟨hs20,hs21⟩ := actual_unit_masses_le_physical hd hR
  have hb20 := (le_abs_self _).trans hu20.le
  have hb21 := (le_abs_self _).trans hu21.le
  unfold rawMainAtom
  constructor <;> linarith

/-- The algebraic density conversion is positive on actual admitted
marks. This is not a claim that a PP density equals this conversion. -/
theorem thetaConversion_nonneg {N d : ℕ} {Q : ℝ}
    (hN : 4≤N) (hd : 0<d) (hR : 1<Q/d) : 0≤thetaConversion N d := by
  have hc : 0<(N:ℝ)/((d:ℝ)*log (Q/d)) :=
    div_pos (Nat.cast_pos.mpr (by omega)) (mul_pos (Nat.cast_pos.mpr hd) (log_pos hR))
  have he := rawMainAtom_to_thetaAtom (by omega : 0<N) hd Q hR (fun _ => 1)
  simp only [rawMainAtom,mul_one] at he
  have hprod : 0≤thetaConversion N d*((N:ℝ)/((d:ℝ)*log (Q/d))) := by
    rw [he]
    exact thetaAtom_nonneg hN hd hR
  exact nonneg_of_mul_nonneg_right hprod hc

def convertedUnit20 (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑d∈D,sigma d*thetaConversion N d*unitWordMass N Q d [2,3,3,3,3]

def convertedUnit21 (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑d∈D,sigma d*thetaConversion N d*unitWordMass N Q d [3,3,3,3,3,3]

/-- Each original unit surface is lifted with exactly the original sigma
and the original same-Q atom. One epsilon/2 budget is assigned to each.
No division by total mass, no positivity of total mass, and no alpha reset. -/
theorem actual_unit_theta_upper {eta epsilon : ℝ} (heta : 0<eta) (he : 0<epsilon) :
    ∃T : ℕ,4≤T ∧ ∀N : ℕ,T≤N → ∀Q : ℝ,∀D : Finset ℕ,∀sigma : ℕ → ℝ,
      (∀d∈D,0<d) → (∀d∈D,0≤sigma d) → (∀d∈D,(N:ℝ)^eta≤Q/d) →
      (convertedUnit20 N Q D sigma≤thetaPayload N Q D sigma unit20Mass+
        (epsilon/2)*Theta N Q D sigma) ∧
      (convertedUnit21 N Q D sigma≤thetaPayload N Q D sigma unit21Mass+
        (epsilon/2)*Theta N Q D sigma) ∧
      (convertedUnit20 N Q D sigma+convertedUnit21 N Q D sigma≤
        thetaPayload N Q D sigma unit20Mass+thetaPayload N Q D sigma unit21Mass+
        epsilon*Theta N Q D sigma) := by
  obtain ⟨T,hT,hupper⟩ := actual_unit_upper_uniform heta (half_pos he)
  refine ⟨T,hT,?_⟩
  intro N hNT Q D sigma hd hsigma hscale
  have hN4 := hT.trans hNT
  have hR (d : ℕ) (hmem : d∈D) : 1<Q/d :=
    (one_lt_rpow (by exact_mod_cast (show 1<N by omega)) heta).trans_le (hscale d hmem)
  have hpoint (d : ℕ) (hmem : d∈D) :
      sigma d*thetaConversion N d*unitWordMass N Q d [2,3,3,3,3]≤
        sigma d*thetaAtom N Q d*unit20Mass (trueAlpha N Q d)+
          (epsilon/2)*(sigma d*thetaAtom N Q d) ∧
      sigma d*thetaConversion N d*unitWordMass N Q d [3,3,3,3,3,3]≤
        sigma d*thetaAtom N Q d*unit21Mass (trueAlpha N Q d)+
          (epsilon/2)*(sigma d*thetaAtom N Q d) := by
    obtain ⟨h20,h21⟩ := hupper N hNT Q d (hd d hmem) (hscale d hmem)
    have hw := mul_nonneg (hsigma d hmem)
      (thetaConversion_nonneg hN4 (hd d hmem) (hR d hmem))
    have hconvert (F : ℝ → ℝ) := rawMainAtom_to_thetaAtom
      (by omega : 0<N) (hd d hmem) Q (hR d hmem) F
    have hconstant := hconvert (fun _ => 1)
    simp only [rawMainAtom,mul_one] at hconstant
    have hfinish (F : ℝ → ℝ) (mass : ℝ)
        (h : mass≤rawMainAtom N Q d F+(epsilon/2)*((N:ℝ)/((d:ℝ)*log (Q/d)))) :
        sigma d*thetaConversion N d*mass≤
          sigma d*thetaAtom N Q d*F (trueAlpha N Q d)+
            (epsilon/2)*(sigma d*thetaAtom N Q d) := by
      calc
        _ ≤ sigma d*thetaConversion N d*
            (rawMainAtom N Q d F+(epsilon/2)*((N:ℝ)/((d:ℝ)*log (Q/d)))) :=
          mul_le_mul_of_nonneg_left h hw
        _ = sigma d*(thetaConversion N d*rawMainAtom N Q d F)+
            (epsilon/2)*(sigma d*(thetaConversion N d*((N:ℝ)/((d:ℝ)*log (Q/d))))) := by ring
        _ = _ := by rw [hconvert F,hconstant]; ring
    exact ⟨hfinish unit20Mass _ h20,hfinish unit21Mass _ h21⟩
  have h20 := sum_le_sum (s:=D) (fun d hmem => (hpoint d hmem).1)
  have h21 := sum_le_sum (s:=D) (fun d hmem => (hpoint d hmem).2)
  simp only [sum_add_distrib,← mul_sum,← Theta_eq_sum_atoms] at h20 h21
  change convertedUnit20 N Q D sigma≤thetaPayload N Q D sigma unit20Mass+
    (epsilon/2)*Theta N Q D sigma at h20
  change convertedUnit21 N Q D sigma≤thetaPayload N Q D sigma unit21Mass+
    (epsilon/2)*Theta N Q D sigma at h21
  exact ⟨h20,h21,by linarith⟩

/-- Zero total mass is settled absolutely by positivity of the original
normalizer, without any asymptotic threshold or division by the mass. -/
theorem zero_theta_units {N : ℕ} (hN : 4≤N) (Q : ℝ)
    (D : Finset ℕ) (sigma : ℕ → ℝ)
    (hd : ∀d∈D,0<d) (hsigma : ∀d∈D,0≤sigma d) (hR : ∀d∈D,1<Q/d)
    (hzero : Theta N Q D sigma=0) :
    convertedUnit20 N Q D sigma=0 ∧ convertedUnit21 N Q D sigma=0 ∧
      thetaPayload N Q D sigma unit20Mass=0 ∧ thetaPayload N Q D sigma unit21Mass=0 := by
  have hs0 (d : ℕ) (hmem : d∈D) : sigma d=0 := by
    rcases eq_or_lt_of_le (hsigma d hmem) with heq | hpos
    · exact heq.symm
    · have hp := P2EnhancedTwentyOneSameQWeighted.Theta_pos hN Q D sigma hd hsigma hR
        ⟨d,hmem,hpos⟩
      rw [hzero] at hp
      exact (lt_irrefl (0:ℝ) hp).elim
  unfold convertedUnit20 convertedUnit21 thetaPayload
  refine ⟨sum_eq_zero (fun d hmem => ?_),sum_eq_zero (fun d hmem => ?_),
    sum_eq_zero (fun d hmem => ?_),sum_eq_zero (fun d hmem => ?_)⟩ <;>
    simp only [hs0 d hmem,zero_mul]

end
end ImbalancedChen.P2EnhancedUnitSourceMass
