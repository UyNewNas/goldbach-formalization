import ImbalancedChen.P2OriginalW2ComplementAction
import ImbalancedChen.P2EnhancedCollisionThetaPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A genuine o(Theta_Q) payment for the receiver-complement cost in all36
actual W2 actions. The threshold precedes N, Q, sigma, its finite support,
the action and every finite old arithmetic generation. The primitive
residual-power gate N^eta <= Q/d and Q<=N pay the passage from sigma-mass
to sigma/d-mass. The true li(N), singular series, phi(d), and log(Q/d)
normalization are exactly the existing original Theta_Q.

The result is an action count estimate with a proved small source error.
It does not pay the old Rosser AP errors or the positive switched costs,
prove the adopted positive seed, identify an arithmetic state with a
numeric H table, or supply H247 / BankEndpointLicences.
-/
namespace ImbalancedChen.P2OriginalW2CentreThetaPayment

noncomputable section
open Finset Filter Wu2008DoubleSieve
open P2FrozenReceiverCountActions P2OriginalW2CentreIncidence
open P2OriginalW2ComplementAction
open P2EnhancedTwentyOneSameQWeighted (Theta cutoff)
open P2EnhancedThetaReciprocalMass
open P2EnhancedCollisionThetaPayment (residual_level_le_N)
open P5OriginalU5FrozenSource (receiver)
open P5OriginalActionMassBound (originalW2At)
open MathlibNt.SieveTheory.SingularSeries
open scoped Classical BigOperators Topology

def chargeConstant : ℝ := 9 / Real.log 2^3

theorem chargeConstant_pos : 0<chargeConstant := by
  unfold chargeConstant
  exact div_pos (by norm_num) (pow_pos (Real.log_pos (by norm_num)) 3)

theorem W2Charge_le_log_cube {N : ℕ} (hN : 0<N) (hNP : ¬N.Prime)
    (hlog : 1≤Real.log (N:ℝ)) (Q : ℝ) (d : ℕ) (j : Fin 36) :
    W2Charge N Q d j ≤ chargeConstant*Real.log (N:ℝ)^3 := by
  have htwo : 0<Real.log 2 := Real.log_pos (by norm_num)
  have htwo1 : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    exact hh
  have hL : 1≤logRank N :=
    (le_div_iff₀ htwo).mpr (by simpa only [one_mul] using htwo1.trans hlog)
  have hcube : logRank N≤logRank N^3 := by
    have hp := mul_nonneg (sub_nonneg.mpr hL)
      (add_nonneg (sq_nonneg (logRank N)) (logRank_nonnegative N))
    nlinarith only [hp]
  calc
    _ ≤ 5*logRank N+4*logRank N^3 := W2Charge_le hN hNP Q d j
    _ ≤ 9*logRank N^3 := by linarith
    _ = _ := by unfold logRank chargeConstant; rw [div_pow]; ring

/-- This power saving is derived from the same physical residual
level, not supplied as a bound on an error or on a weighted count. -/
theorem prefix_cap_of_residual {N d : ℕ} {Q eta : ℝ}
    (hN : 0<N) (hd : 0<d) (hQ : Q≤(N:ℝ))
    (hres : (N:ℝ)^eta≤Q/(d:ℝ)) : (d:ℝ)≤(N:ℝ)/(N:ℝ)^eta := by
  have hdR : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hpow : 0<(N:ℝ)^eta := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _
  have hm : (N:ℝ)^eta*(d:ℝ)≤(N:ℝ) := ((le_div_iff₀ hdR).mp hres).trans hQ
  exact (le_div_iff₀ hpow).mpr (by simpa only [mul_comm] using hm)

def markedCharge (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (j : Fin 36) : ℝ := ∑ d∈D, sigma d*W2Charge N Q d j

theorem markedCharge_reciprocal_bound {N : ℕ} {eta Q : ℝ}
    (hN : 0<N) (hNP : ¬N.Prime) (hlog : 1≤Real.log (N:ℝ))
    (D : Finset ℕ) (sigma : ℕ → ℝ) (j : Fin 36)
    (hQ : Q≤(N:ℝ)) (hd : ∀d∈D,0<d) (hsigma : ∀d∈D,0≤sigma d)
    (hres : ∀d∈D,(N:ℝ)^eta≤Q/(d:ℝ)) :
    markedCharge N Q D sigma j ≤
      (chargeConstant*(N:ℝ)*Real.log (N:ℝ)^3/(N:ℝ)^eta)*
        ∑ d∈D,sigma d/(d:ℝ) := by
  unfold markedCharge
  rw [mul_sum]
  apply sum_le_sum
  intro d hmem
  have hdR : (0:ℝ)<d := Nat.cast_pos.mpr (hd d hmem)
  have hm : 0≤sigma d/(d:ℝ) := div_nonneg (hsigma d hmem) hdR.le
  have hcap := prefix_cap_of_residual hN (hd d hmem) hQ (hres d hmem)
  have he : (d:ℝ)*(sigma d/(d:ℝ))=sigma d := by field_simp [hdR.ne']
  have hs : sigma d≤((N:ℝ)/(N:ℝ)^eta)*(sigma d/(d:ℝ)) := by
    calc
      sigma d=(d:ℝ)*(sigma d/(d:ℝ)) := he.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hcap hm
  have hcoef : 0≤chargeConstant*Real.log (N:ℝ)^3 :=
    mul_nonneg chargeConstant_pos.le (pow_nonneg (Real.log_natCast_nonneg N) 3)
  calc
    _ ≤ sigma d*(chargeConstant*Real.log (N:ℝ)^3) :=
      mul_le_mul_of_nonneg_left (W2Charge_le_log_cube hN hNP hlog Q d j) (hsigma d hmem)
    _ ≤ (((N:ℝ)/(N:ℝ)^eta)*(sigma d/(d:ℝ)))*
        (chargeConstant*Real.log (N:ℝ)^3) := mul_le_mul_of_nonneg_right hs hcoef
    _ = _ := by ring

/-- A uniform relative payment for the complete action charge, before
the action's division by five. Empty supports and zero weights need no
division by Theta and are covered by the same proof. -/
theorem all36_charge_theta_payment {eta epsilon : ℝ}
    (heta : 0<eta) (hepsilon : 0<epsilon) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → Even N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q≤(N:ℝ) →
      (∀d∈D,0<d) → (∀d∈D,0≤sigma d) →
      (∀d∈D,(N:ℝ)^eta≤Q/(d:ℝ)) → ∀j : Fin 36,
      markedCharge N Q D sigma j≤epsilon*Theta N Q D sigma := by
  obtain ⟨T1,hT1,hpay⟩ := ninth_power_log_error_budget 3
    (C := chargeConstant) (α := eta) (ε := 2*liuUniversalProduct*epsilon)
    chargeConstant_pos heta
    (mul_pos (mul_pos (by norm_num) liuUniversalProduct_pos) hepsilon)
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T2,hlogT⟩ := eventually_atTop.mp
    (hlogTop.eventually (eventually_ge_atTop (1:ℝ)))
  refine ⟨max T1 T2,by omega,?_⟩
  intro N hNT he Q D sigma hQ hd hsigma hres j
  have hN1 := (le_max_left T1 T2).trans hNT
  have hN4 : 4≤N := by omega
  have hNpos : 0<N := by omega
  have hNP := chen_not_prime_of_even_four_le he hN4
  have hlog := hlogT N ((le_max_right T1 T2).trans hNT)
  have hR : ∀d∈D,1<Q/(d:ℝ) := fun d hmem =>
    (Real.one_lt_rpow (by exact_mod_cast (show 1<N by omega)) heta).trans_le (hres d hmem)
  have hmass : 0≤∑d∈D,sigma d/(d:ℝ) :=
    sum_nonneg (fun d hmem => div_nonneg (hsigma d hmem) (Nat.cast_nonneg d))
  have htheta := Theta_lower hN4 Q D sigma hd hsigma
    (fun d hmem => ⟨hR d hmem,residual_level_le_N (hd d hmem) hQ⟩)
  calc
    _ ≤ (chargeConstant*(N:ℝ)*Real.log (N:ℝ)^3/(N:ℝ)^eta)*
        ∑d∈D,sigma d/(d:ℝ) :=
      markedCharge_reciprocal_bound hNpos hNP hlog D sigma j hQ hd hsigma hres
    _ ≤ ((2*liuUniversalProduct*epsilon)*(N:ℝ)/Real.log (N:ℝ)^2)*
        ∑d∈D,sigma d/(d:ℝ) := mul_le_mul_of_nonneg_right (hpay N hN1) hmass
    _ = epsilon*((2*liuUniversalProduct*(N:ℝ)/Real.log (N:ℝ)^2)*
        ∑d∈D,sigma d/(d:ℝ)) := by ring
    _ ≤ epsilon*Theta N Q D sigma := mul_le_mul_of_nonneg_left htheta hepsilon.le

def markedPaidW2 (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (bank : List P2ActualMarkedCountState.Query) (rounds : ℕ) (j : Fin 36) : ℝ :=
  ∑d∈D,sigma d*paidW2 N Q
    (P2AllW2ImmutableCountRecursion.iterate N Q (receiver N) bank rounds) d j

/-- Concrete arithmetic consumer. No source/count enclosure is a
caller premise: the initial signed Rosser polynomials and the joint
old-generation induction supply it. -/
theorem marked_actual_W2_with_charge (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (bank : List P2ActualMarkedCountState.Query)
    (rounds : ℕ) (j : Fin 36) (hd : ∀d∈D,0<d) (hsigma : ∀d∈D,0≤sigma d)
    (hR : ∀d∈D,1<Q/(d:ℝ)) :
    markedPhi N Q D id sigma (fun _ => receiver N) (originalW2At j).s ≤
      markedPaidW2 N Q D sigma bank rounds j+markedCharge N Q D sigma j/5 := by
  calc
    _ ≤ ∑d∈D,sigma d*(paidW2 N Q
        (P2AllW2ImmutableCountRecursion.iterate N Q (receiver N) bank rounds) d j+
          W2Charge N Q d j/5) := by
      apply sum_le_sum
      intro d hmem
      exact mul_le_mul_of_nonneg_left
        (iterate_W2_upper N Q bank rounds j (hd d hmem) (hR d hmem)) (hsigma d hmem)
    _ = _ := by
      simp only [markedPaidW2,markedCharge,mul_add,sum_add_distrib,mul_div_assoc,sum_div]

/-- The original all36 count action with its receiver-complement error
PAID at the same Theta_Q. A single threshold works for every action,
bank and old generation; it does not conflate any numerical histories. -/
theorem all36_actual_W2_paid {eta epsilon : ℝ} (heta : 0<eta) (hepsilon : 0<epsilon) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → Even N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q≤(N:ℝ) →
      (∀d∈D,0<d) → (∀d∈D,0≤sigma d) →
      (∀d∈D,(N:ℝ)^eta≤Q/(d:ℝ)) →
      ∀ (bank : List P2ActualMarkedCountState.Query) (rounds : ℕ) (j : Fin 36),
      markedPhi N Q D id sigma (fun _ => receiver N) (originalW2At j).s ≤
        markedPaidW2 N Q D sigma bank rounds j+epsilon*Theta N Q D sigma := by
  obtain ⟨T,hT,hpaid⟩ := all36_charge_theta_payment heta
    (mul_pos (by norm_num : (0:ℝ)<5) hepsilon)
  refine ⟨T,hT,?_⟩
  intro N hNT he Q D sigma hQ hd hsigma hres bank rounds j
  have hN4 : 4≤N := hT.trans hNT
  have hR : ∀d∈D,1<Q/(d:ℝ) := fun d hmem =>
    (Real.one_lt_rpow (by exact_mod_cast (show 1<N by omega)) heta).trans_le (hres d hmem)
  have hcharge := hpaid N hNT he Q D sigma hQ hd hsigma hres j
  have hdiv : markedCharge N Q D sigma j/5≤epsilon*Theta N Q D sigma := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<5)).mpr
    nlinarith only [hcharge]
  exact (marked_actual_W2_with_charge N Q D sigma bank rounds j hd hsigma hR).trans
    (add_le_add_left hdiv _)

/-- Only equal complete prefixes are grouped, and their weights are
ADDED. The original mark multiplicity is never replaced by one. -/
def groupedSigma {ι : Type*} (L : Finset ι) (B : ι → ℕ) (sigma : ι → ℝ)
    (d : ℕ) : ℝ := ∑a∈L with B a=d,sigma a

theorem weighted_fiber_sum {ι : Type*} (L : Finset ι) (B : ι → ℕ)
    (sigma : ι → ℝ) (F : ℕ → ℝ) :
    (∑d∈L.image B,groupedSigma L B sigma d*F d)=∑a∈L,sigma a*F (B a) := by
  unfold groupedSigma
  simp only [sum_mul]
  calc
    _ = ∑d∈L.image B,∑a∈L with B a=d,sigma a*F (B a) := by
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro a ha
      rw [(mem_filter.mp ha).2]
    _ = _ := sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem B ha) _

/-- The same original normalizer before equal-prefix labels are pooled. -/
def labelledTheta {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) : ℝ :=
  4*AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N*
    ∑a∈L,sigma a*wuSingularSeries (B a*N)/
      ((Nat.totient (B a):ℝ)*Real.log (Q/B a))

theorem Theta_grouped {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) :
    Theta N Q (L.image B) (groupedSigma L B sigma)=labelledTheta N Q L B sigma := by
  unfold Theta labelledTheta
  congr 1
  simpa only [mul_div_assoc] using weighted_fiber_sum L B sigma
    (fun d => wuSingularSeries (d*N)/((Nat.totient d:ℝ)*Real.log (Q/d)))

/-- The original labelled-family consumer, including coincident prefix
products. The threshold is unchanged by the size or multiplicity of the
family. The receiver is still precisely E_N, not an arbitrary extra
history filter. -/
theorem all36_labelled_actual_W2_paid {ι : Type*} {eta epsilon : ℝ}
    (heta : 0<eta) (hepsilon : 0<epsilon) :
    ∃ T : ℕ,4≤T ∧ ∀N : ℕ,T≤N → Even N →
      ∀(Q : ℝ) (L : Finset ι) (B : ι → ℕ) (sigma : ι → ℝ),Q≤(N:ℝ) →
      (∀a∈L,0<B a) → (∀a∈L,0≤sigma a) →
      (∀a∈L,(N:ℝ)^eta≤Q/(B a:ℝ)) →
      ∀(bank : List P2ActualMarkedCountState.Query) (rounds : ℕ) (j : Fin 36),
      markedPhi N Q L B sigma (fun _ => receiver N) (originalW2At j).s ≤
        (∑a∈L,sigma a*paidW2 N Q
          (P2AllW2ImmutableCountRecursion.iterate N Q (receiver N) bank rounds) (B a) j)+
          epsilon*labelledTheta N Q L B sigma := by
  obtain ⟨T,hT,hpaid⟩ := all36_actual_W2_paid heta hepsilon
  refine ⟨T,hT,?_⟩
  intro N hNT he Q L B sigma hQ hB hsigma hres bank rounds j
  have hd : ∀d∈L.image B,0<d := by
    intro d hd
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hd
    exact hB a ha
  have hs : ∀d∈L.image B,0≤groupedSigma L B sigma d := by
    intro d _
    exact sum_nonneg (fun a ha => hsigma a (mem_filter.mp ha).1)
  have hr : ∀d∈L.image B,(N:ℝ)^eta≤Q/(d:ℝ) := by
    intro d hd
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hd
    exact hres a ha
  have hh := hpaid N hNT he Q (L.image B) (groupedSigma L B sigma)
    hQ hd hs hr bank rounds j
  rw [Theta_grouped] at hh
  unfold markedPhi at hh ⊢
  unfold markedPaidW2 at hh
  simp only [id_eq,weighted_fiber_sum] at hh
  exact hh

end
end ImbalancedChen.P2OriginalW2CentreThetaPayment
