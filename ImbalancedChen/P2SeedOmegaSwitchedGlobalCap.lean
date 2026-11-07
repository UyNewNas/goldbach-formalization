import ImbalancedChen.P2SeedOmegaGlobalEnvelope

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original switched triples9..15, their literal next-to-last-prime cutoff,
and their seven exact corner minima. This connects the GLOBAL actual
omega envelope to every alpha>=2 on these original closed bands.
The two minima below2 are treated with max(1/x,c), without replacing
the true argument by max(2,x) or asserting omega monotonicity.
No switched integral/mass inequality or final seed lower bound is assumed.
-/

namespace ImbalancedChen.P2SeedOmegaSwitchedGlobalCap
noncomputable section
open Set
open P2SeedOmegaLiteralFibre
open P2SeedOmegaGlobalEnvelope

def lowerU : Fin 7 → ℝ := ![a1,a1,a1,a0,a0,a0,a1]
def upperU : Fin 7 → ℝ := ![a3,a2,a2,a1,a1,a1,a2]
def lowerV : Fin 7 → ℝ := ![a1,a1,a2,a0,a1,a2,a2]
def upperV : Fin 7 → ℝ := ![a3,a2,a3,a1,a2,b,a3]
def lowerW : Fin 7 → ℝ := ![a1,a2,a2,a3,a2,a2,a3]
def upperW : Fin 7 → ℝ := ![a3,b,a3,b,b,b,b]

def originalMinimum : Fin 7 → ℝ :=
  ![47/25,273/110,1478/725,3801/1100,103299/38830,3136/1765,15388/7975]

/-- Same seven parameter formulas as the original envelope certifier. -/
theorem originalMinimum_parameter_dictionary : originalMinimum=
    ![2*phi3-3,2*phi2-2-phi2/s,2*phi3-phi3/phi2-2,
      2*phi1-2-phi1/s,2*phi2-phi2/phi1-1-phi2/s,
      2*s-s/phi1-2,2*phi3-phi3/phi2-1-phi3/s] := by
  funext j
  fin_cases j <;> norm_num [originalMinimum,phi1,phi2,phi3,s]

theorem original_corner_identity (j : Fin 7) :
    originalMinimum j*upperV j=2-upperU j-upperV j-upperW j := by
  fin_cases j <;> norm_num [originalMinimum,upperU,upperV,upperW,a1,a2,a3,b]

theorem original_minima_properties (j : Fin 7) :
    1≤originalMinimum j ∧ 1<originalMinimum j*omegaCap ∧ 0<lowerV j := by
  fin_cases j <;> norm_num [originalMinimum,omegaCap,lowerV,a0,a1,a2]

/-- Literal ordered closed prime bands for domains9..15. -/
def OriginalTriple (j : Fin 7) (u v w : ℝ) : Prop :=
  u ∈ Icc (lowerU j) (upperU j) ∧
  v ∈ Icc (lowerV j) (upperV j) ∧
  w ∈ Icc (lowerW j) (upperW j) ∧ u≤v ∧ v≤w

def actualArgument (alpha u v w : ℝ) : ℝ := (alpha-u-v-w)/v

/-- The physical cutoff is v. Uniformity in alpha is proved by an
inequality, not by a finite-alpha grid or a change of cutoff. -/
theorem original_argument_minimum (j : Fin 7) {alpha u v w : ℝ}
    (ha : 2≤alpha) (hx : OriginalTriple j u v w) :
    originalMinimum j≤actualArgument alpha u v w := by
  have hp := original_minima_properties j
  have hv0 : 0<v := hp.2.2.trans_le hx.2.1.1
  have hm0 : 0≤originalMinimum j := zero_le_one.trans hp.1
  have hmul := mul_le_mul_of_nonneg_left hx.2.1.2 hm0
  rw [original_corner_identity] at hmul
  apply (le_div_iff₀ hv0).mpr
  linarith only [hmul,ha,hx.1.2,hx.2.1.2,hx.2.2.1.2]

/-- The ORIGINAL c_omega cap licenses each actual switched argument,
including the two corner minima between1 and2, for every alpha>=2. -/
theorem actual_omega_cap_on_original_triples (j : Fin 7) {alpha u v w : ℝ}
    (ha : 2≤alpha) (hx : OriginalTriple j u v w) :
    LiLiuPrereqBuchstab.buchstab (actualArgument alpha u v w)≤omegaCap := by
  have hmin := original_argument_minimum j ha hx
  have hp := original_minima_properties j
  have harg : 1≤actualArgument alpha u v w := hp.1.trans hmin
  have harg0 : 0<actualArgument alpha u v w := zero_lt_one.trans_le harg
  have hprod : (1:ℝ)≤omegaCap*actualArgument alpha u v w := by
    have h := mul_le_mul_of_nonneg_left hmin omegaCap_positive.le
    have hcorner := hp.2.1.le
    nlinarith only [h,hcorner]
  have hinv : 1/actualArgument alpha u v w≤omegaCap :=
    (div_le_iff₀ harg0).mpr hprod
  exact (actual_buchstab_original_global_envelope harg).trans (max_le hinv le_rfl)

end
end ImbalancedChen.P2SeedOmegaSwitchedGlobalCap
