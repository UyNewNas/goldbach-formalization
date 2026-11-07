import ImbalancedChen.P2TwentyOneSmallPartnerOutputFibres
import ImbalancedChen.P2EnhancedCollisionThetaPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Pay the actual ALL-word small-partner count against the original Theta_Q.
The old marked weight may be any nonnegative real weight, including zero.
The power gap kappa+rho<1 and the actual fixed prime cutoff are sufficient;
no convolution model, small-partner estimate, K, PP or J licence is assumed.
The threshold precedes Q, D, sigma and the natural small-partner cap z.
-/
namespace ImbalancedChen.P2TwentyOneSmallPartnerThetaPayment
noncomputable section
open Finset Filter Wu2008DoubleSieve
open scoped Classical Topology BigOperators
open MathlibNt.SieveTheory.SingularSeries
open P2EnhancedTwentyOneSameQWeighted
open P2EnhancedThetaReciprocalMass
open P2EnhancedCollisionThetaPayment (residual_level_le_N)
open P2ActualSameQTwentyOnePositiveSourceBinding
open P2TwentyOneSmallPartnerOutputFibres

/-- The same residual level bounds the old divisor.  This is why the
ordinary marked mass costs N^kappa times its own reciprocal mass. -/
theorem marked_mass_le_reciprocal {N : ℕ} {Q kappa : ℝ}
    (D : Finset ℕ) (sigma : ℕ → ℝ) (hQ : Q≤(N : ℝ)^kappa)
    (hd : ∀ d ∈ D,0<d) (hsigma : ∀ d ∈ D,0≤sigma d)
    (hR : ∀ d ∈ D,1<Q/(d : ℝ)) :
    (∑ d ∈ D,sigma d)≤(N : ℝ)^kappa*(∑ d ∈ D,sigma d/(d : ℝ)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hdD
  have hdreal : (0 : ℝ)<d := Nat.cast_pos.mpr (hd d hdD)
  have hdQ : (d : ℝ)<Q := by
    simpa only [one_mul] using (lt_div_iff₀ hdreal).mp (hR d hdD)
  calc
    sigma d=(d : ℝ)*(sigma d/(d : ℝ)) := by field_simp
    _≤_ := mul_le_mul_of_nonneg_right (hdQ.le.trans hQ)
      (div_nonneg (hsigma d hdD) hdreal.le)

theorem actualSmallPartnerMass_le_power_reciprocal {N z : ℕ} {Q eta kappa rho : ℝ}
    (D : Finset ℕ) (sigma : ℕ → ℝ) (hN : 1<N) (heta : 0<eta)
    (hQ : Q≤(N : ℝ)^kappa) (hz : (z : ℝ)≤(N : ℝ)^rho)
    (hd : ∀ d ∈ D,0<d) (hsigma : ∀ d ∈ D,0≤sigma d)
    (hR : ∀ d ∈ D,1<Q/(d : ℝ))
    (hcut : ∀ d ∈ D,(N : ℝ)^eta≤cutoff Q d (227/50)) :
    actualSmallPartnerMass N Q D sigma z≤
      (22*(max 1 (1/eta))^6*(N : ℝ)^(kappa+rho))*(∑ d ∈ D,sigma d/(d : ℝ)) := by
  have hmass : 0≤∑ d ∈ D,sigma d/(d : ℝ) :=
    Finset.sum_nonneg (fun d hdD => div_nonneg (hsigma d hdD) (Nat.cast_nonneg d))
  have hC : 0≤22*(max 1 (1/eta))^6 := by positivity
  calc
    _≤(22*(max 1 (1/eta))^6*(z : ℝ))*(∑ d ∈ D,sigma d) :=
      actualSmallPartnerMass_le D sigma hN heta hd hsigma hcut
    _≤(22*(max 1 (1/eta))^6*(z : ℝ))*
        ((N : ℝ)^kappa*(∑ d ∈ D,sigma d/(d : ℝ))) :=
      mul_le_mul_of_nonneg_left (marked_mass_le_reciprocal D sigma hQ hd hsigma hR)
        (mul_nonneg hC (Nat.cast_nonneg z))
    _≤(22*(max 1 (1/eta))^6*(N : ℝ)^rho)*
        ((N : ℝ)^kappa*(∑ d ∈ D,sigma d/(d : ℝ))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz hC)
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) hmass)
    _=_ := by
      rw [Real.rpow_add (by exact_mod_cast (show 0<N by omega))]
      ring

/-- Genuine relative payment, including empty/zero-weight marked sources.
No lower bound for their mass, and no division by it, is used. -/
theorem actual_smallPartner_theta_payment {eta kappa rho epsilon : ℝ}
    (heta : 0<eta) (hkappa : kappa≤1) (hgap : kappa+rho<1) (hepsilon : 0<epsilon) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) (z : ℕ),
      Q≤(N : ℝ)^kappa → (z : ℝ)≤(N : ℝ)^rho →
      (∀ d ∈ D,0<d) → (∀ d ∈ D,0≤sigma d) →
      (∀ d ∈ D,1<Q/(d : ℝ)) →
      (∀ d ∈ D,(N : ℝ)^eta≤cutoff Q d (227/50)) →
      actualSmallPartnerMass N Q D sigma z≤epsilon*Theta N Q D sigma := by
  let C : ℝ := 22*(max 1 (1/eta))^6
  have hC : 0<C := by dsimp [C]; positivity
  obtain ⟨T,hT,hpay⟩ := ninth_power_log_error_budget 0
    (C:=C) (α:=1-(kappa+rho)) (ε:=2*liuUniversalProduct*epsilon)
    hC (sub_pos.mpr hgap) (by positivity)
  refine ⟨T,by omega,?_⟩
  intro N hNT Q D sigma z hQ hz hd hsigma hR hcut
  have hN4 : 4≤N := by omega
  have hNpos : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hQN : Q≤(N : ℝ) := hQ.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 hkappa)
  have hmass : 0≤∑ d ∈ D,sigma d/(d : ℝ) :=
    Finset.sum_nonneg (fun d hdD => div_nonneg (hsigma d hdD) (Nat.cast_nonneg d))
  have htheta := Theta_lower hN4 Q D sigma hd hsigma
    (fun d hdD => ⟨hR d hdD,residual_level_le_N (hd d hdD) hQN⟩)
  have hpower : C*(N : ℝ)^(kappa+rho)≤
      (2*liuUniversalProduct*epsilon)*N/Real.log N^2 := by
    have hexp : (N : ℝ)^(kappa+rho)=(N : ℝ)/(N : ℝ)^(1-(kappa+rho)) := by
      calc
        _=(N : ℝ)^(1-(1-(kappa+rho))) := by congr 1; ring
        _=_ := by rw [Real.rpow_sub hNpos,Real.rpow_one]
    calc
      _=C*(N : ℝ)*Real.log N^(0 : ℕ)/(N : ℝ)^(1-(kappa+rho)) := by
        rw [hexp,pow_zero]
        ring
      _≤_ := hpay N hNT
  calc
    _≤(C*(N : ℝ)^(kappa+rho))*(∑ d ∈ D,sigma d/(d : ℝ)) :=
      actualSmallPartnerMass_le_power_reciprocal D sigma (by omega) heta hQ hz hd hsigma hR hcut
    _≤((2*liuUniversalProduct*epsilon)*N/Real.log N^2)*
        (∑ d ∈ D,sigma d/(d : ℝ)) := mul_le_mul_of_nonneg_right hpower hmass
    _=epsilon*((2*liuUniversalProduct*(N : ℝ)/Real.log N^2)*
        (∑ d ∈ D,sigma d/(d : ℝ))) := by ring
    _≤_ := mul_le_mul_of_nonneg_left htheta hepsilon.le

/-- The same-Q G count now has a proved small-partner payment.  The old
floor is used only for G's masked-to-absolute tail decomposition. -/
theorem actual_switched_good_source_paid {eta kappa rho epsilon : ℝ}
    (heta : 0<eta) (hkappa : kappa≤1) (hgap : kappa+rho<1) (hepsilon : 0<epsilon) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) (z : ℕ),
      Q≤(N : ℝ)^kappa → (z : ℝ)≤(N : ℝ)^rho → (z : ℝ)≤(N : ℝ)^eta →
      (∀ d ∈ D,0<d) → (∀ d ∈ D,0≤sigma d) →
      (∀ d ∈ D,1<Q/(d : ℝ)) →
      (∀ d ∈ D,(N : ℝ)^eta≤cutoff Q d (227/50)) →
      (∀ d ∈ D,∀ p : ℕ,p.Prime → p ∣ d → z≤p) →
      P2EnhancedTwentyOneChildCorrection.switchedCount N Q D sigma≤
        actualGoodMass N Q D sigma z+epsilon*Theta N Q D sigma := by
  obtain ⟨T,hT,hpay⟩ := actual_smallPartner_theta_payment heta hkappa hgap hepsilon
  refine ⟨T,hT,?_⟩
  intro N hNT he Q D sigma z hQ hz hzeta hd hsigma hR hcut hold
  exact (actual_sameQ_good_source_bound Q D sigma (hT.trans hNT) he hd hsigma hold
    (fun d hdD => hzeta.trans (hcut d hdD))).trans
      (add_le_add_left (hpay N hNT Q D sigma z hQ hz hd hsigma hR hcut) _)

end
end ImbalancedChen.P2TwentyOneSmallPartnerThetaPayment
