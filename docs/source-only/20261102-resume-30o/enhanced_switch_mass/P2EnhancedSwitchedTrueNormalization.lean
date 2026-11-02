import ImbalancedChen.P2EnhancedSwitchedUnsiftedSource
import ImbalancedChen.P2OriginalChildPhysicalNormalization
import ImbalancedChen.P2SeedOmegaFirstThreeLiteralMass
import ImbalancedChen.P2SeedOmegaSwitchedMassFour
import ImbalancedChen.P2SeedOmegaLastFullMassBounds
import ImbalancedChen.P2SeedOmegaUnitChartIdentification

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The physical logarithmic alpha, actual enhanced Q, and true-li Theta are
identified algebraically. No arithmetic source limit is asserted. Unit20
uses its first-coordinate chart and unit21 its last-coordinate chart at
this alpha. A finite theta-weighted continuous envelope is not confused
with an asymptotic for the roughCarrier in the companion source file.
-/

namespace ImbalancedChen.P2EnhancedSwitchedTrueNormalization
noncomputable section
open Real Finset MeasureTheory
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2EnhancedTwentyOneSameQWeighted (Theta)
open P2SeedOmegaLiteralFibre (a0 a1 a2 a3 b s0 omegaCap)
open scoped Classical BigOperators

def prefixExponent (N d : ℕ) : ℝ := log (d:ℝ)/log (N:ℝ)
def residualExponent (N d : ℕ) (nu : ℝ) : ℝ := nu-prefixExponent N d
def trueAlpha (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  log ((N:ℝ)/d)/log (Q/d)

theorem residual_log {N d : ℕ} (hN : 1<N) (hd : 0<d) (nu : ℝ) :
    log ((N:ℝ)^nu/d)=log (N:ℝ)*residualExponent N d nu := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hdr : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hnlog : log (N:ℝ)≠0 := (log_pos (by exact_mod_cast hN)).ne'
  rw [log_div (Real.rpow_pos_of_pos hNr nu).ne' hdr.ne',log_rpow hNr]
  unfold residualExponent prefixExponent
  field_simp [hnlog]
  ring

theorem physical_log {N d : ℕ} (hN : 1<N) (hd : 0<d) :
    log ((N:ℝ)/d)=log (N:ℝ)*(1-prefixExponent N d) := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hdr : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hnlog : log (N:ℝ)≠0 := (log_pos (by exact_mod_cast hN)).ne'
  rw [log_div hNr.ne' hdr.ne']
  unfold prefixExponent
  field_simp [hnlog]
  ring

theorem trueAlpha_eq {N d : ℕ} (hN : 1<N) (hd : 0<d) (nu : ℝ) :
    trueAlpha N ((N:ℝ)^nu) d=
      (1-prefixExponent N d)/residualExponent N d nu := by
  unfold trueAlpha
  rw [physical_log hN hd,residual_log hN hd]
  have hnlog : log (N:ℝ)≠0 := (log_pos (by exact_mod_cast hN)).ne'
  exact mul_div_mul_left _ _ hnlog

/-- At enhanced nu>1/2, alpha>=2 has the nontrivial prefix requirement
2nu<=1+log_N d. Positive residual level alone does not supply it. -/
theorem trueAlpha_ge_two_iff {N d : ℕ} (hN : 1<N) (hd : 0<d) {nu : ℝ}
    (hL : 0<residualExponent N d nu) :
    2≤trueAlpha N ((N:ℝ)^nu) d ↔ 2*nu≤1+prefixExponent N d := by
  rw [trueAlpha_eq hN hd,le_div_iff₀ hL]
  unfold residualExponent
  constructor <;> intro h <;> linarith only [h]

theorem physical_conservation {N d : ℕ} (hN : 1<N) (hd : 0<d) {nu : ℝ}
    (hL : residualExponent N d nu≠0) :
    prefixExponent N d+residualExponent N d nu*trueAlpha N ((N:ℝ)^nu) d=1 := by
  rw [trueAlpha_eq hN hd]
  field_simp [hL]
  ring

/-- The exact enhanced square gate, with equality retained on the bad
side, and the actual unchanged residual level. -/
theorem bad_square_physical {N : ℝ} (hN : 1<N) {beta L u v : ℝ} (hL : 0<L) :
    N^(beta+L)≤N^beta*(N^(L*u))^2*N^(L*v) ↔ 1≤2*u+v := by
  have hN0 : 0<N := zero_lt_one.trans hN
  have hsq : (N^(L*u))^2=N^(2*(L*u)) := by
    rw [mul_comm (2:ℝ),Real.rpow_mul hN0.le]
    norm_num
  rw [hsq,← Real.rpow_add hN0,← Real.rpow_add hN0,
    Real.rpow_le_rpow_left_iff hN]
  constructor
  · intro h
    apply (mul_le_mul_left hL).mp
    nlinarith only [h]
  · intro h
    have hh := mul_le_mul_of_nonneg_left h hL.le
    nlinarith only [hh]

/-- The unsifted continuous main atom still has N/(d log(Q/d)). -/
def rawMainAtom (N : ℕ) (Q : ℝ) (d : ℕ) (F : ℝ → ℝ) : ℝ :=
  (N:ℝ)/((d:ℝ)*log (Q/d))*F (trueAlpha N Q d)

/-- Exact local density conversion. It is d-dependent and uses true li;
there is no assumed PP coefficient and no division by total mass. -/
def thetaConversion (N d : ℕ) : ℝ :=
  4*AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N*
    (d:ℝ)*Wu2008DoubleSieve.wuSingularSeries (d*N)/
      ((N:ℝ)*(Nat.totient d:ℝ))

theorem rawMainAtom_to_thetaAtom {N d : ℕ} (hN : 0<N) (hd : 0<d)
    (Q : ℝ) (hR : 1<Q/d) (F : ℝ → ℝ) :
    thetaConversion N d*rawMainAtom N Q d F=
      thetaAtom N Q d*F (trueAlpha N Q d) := by
  have hNr : (N:ℝ)≠0 := (Nat.cast_pos.mpr hN).ne'
  have hdr : (d:ℝ)≠0 := (Nat.cast_pos.mpr hd).ne'
  have hphi : (Nat.totient d:ℝ)≠0 := (Nat.cast_pos.mpr (Nat.totient_pos.mpr hd)).ne'
  have hlog : log (Q/d)≠0 := (log_pos hR).ne'
  unfold thetaConversion rawMainAtom thetaAtom
  field_simp [hNr,hdr,hphi,hlog] <;> ring

def thetaPayload (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (F : ℝ → ℝ) : ℝ := ∑ d∈D,sigma d*thetaAtom N Q d*F (trueAlpha N Q d)

theorem actual_raw_main_conversion {N : ℕ} (hN : 0<N) (Q : ℝ)
    (D : Finset ℕ) (sigma : ℕ → ℝ) (hd : ∀d∈D,0<d)
    (hR : ∀d∈D,1<Q/d) (F : ℝ → ℝ) :
    (∑ d∈D,sigma d*thetaConversion N d*rawMainAtom N Q d F)=
      thetaPayload N Q D sigma F := by
  apply sum_congr rfl
  intro d hmem
  rw [mul_assoc,rawMainAtom_to_thetaAtom hN (hd d hmem) Q (hR d hmem)]
  ring

theorem constant_thetaPayload (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (c : ℝ) :
    thetaPayload N Q D sigma (fun _ => c)=c*Theta N Q D sigma := by
  rw [P2OriginalChildPhysicalNormalization.Theta_eq_sum_atoms]
  unfold thetaPayload
  rw [mul_sum]
  apply sum_congr rfl
  intro d _
  ring

theorem thetaPayload_zero (N : ℕ) (Q : ℝ) (D : Finset ℕ) (F : ℝ → ℝ) :
    thetaPayload N Q D (fun _ => 0) F=0 := by simp [thetaPayload]

/-- First-coordinate elimination for20 and last-coordinate elimination
for21 conserve the SAME physical exponent 1, for the actual enhanced Q. -/
theorem two_unit_physical_charts {N d : ℕ} (hN : 1<N) (hd : 0<d) {nu : ℝ}
    (hL : residualExponent N d nu≠0) (y20 : Fin 4 → ℝ) (y21 : Fin 5 → ℝ) :
    prefixExponent N d+residualExponent N d nu*
      P2SeedOmegaLastSwitchGeometry.total
        (P2SeedOmegaLastSwitchGeometry.unit20Point (trueAlpha N ((N:ℝ)^nu) d) y20)=1 ∧
    prefixExponent N d+residualExponent N d nu*
      P2SeedOmegaLastSwitchGeometry.total
        (P2SeedOmegaLastSwitchGeometry.unit21Point (trueAlpha N ((N:ℝ)^nu) d) y21)=1 := by
  rw [P2SeedOmegaLastSwitchGeometry.unit20_total,
    P2SeedOmegaLastSwitchGeometry.unit21_total]
  exact ⟨physical_conservation hN hd hL,physical_conservation hN hd hL⟩

theorem enhanced_unit_chart_masses (N d : ℕ) (nu : ℝ) :
    P2SeedOmegaLastUnitIntegrals.unit20Mass (trueAlpha N ((N:ℝ)^nu) d)=
      Wu2008DoubleSieve.HighUnit.J20 a2 a3 b (trueAlpha N ((N:ℝ)^nu) d) ∧
    P2SeedOmegaLastUnitIntegrals.unit21Mass (trueAlpha N ((N:ℝ)^nu) d)=
      Wu2008DoubleSieve.HighUnit.J21 a3 b (trueAlpha N ((N:ℝ)^nu) d) :=
  ⟨P2SeedOmegaUnitChartIdentification.unit20Mass_eq_pinned_J20 _,
    P2SeedOmegaUnitChartIdentification.unit21Mass_eq_pinned_J21 _⟩

/-- This is only the continuous envelope step. The finite rough source
has not been replaced by the integral, and both unit summands survive. -/
theorem enhanced_last_continuous_envelopes (omega : ℝ → ℝ) (hm : Measurable omega)
    (hb : ∀t,1≤t → 0≤omega t ∧ omega t≤1) (N d : ℕ) (nu : ℝ) :
    P2SeedOmegaLastFullMassBounds.full20Mass omega (trueAlpha N ((N:ℝ)^nu) d)≤
      P2SeedOmegaLiteralFunctional.switchedMass (11 : Fin 13) ∧
    P2SeedOmegaLastFullMassBounds.full21Mass omega (trueAlpha N ((N:ℝ)^nu) d)≤
      P2SeedOmegaLiteralFunctional.switchedMass (12 : Fin 13) :=
  P2SeedOmegaLastFullMassBounds.full_masses_le_original omega hm hb _

end
end ImbalancedChen.P2EnhancedSwitchedTrueNormalization
