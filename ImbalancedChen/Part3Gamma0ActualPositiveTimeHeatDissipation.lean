import ImbalancedChen.Part3Gamma0ActualHeatDirichletDissipation
import ImbalancedChen.Part3GenericHeatPositiveTimeRegularization

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

ALL actual quotient-L2 initial data acquire the genuine actual Friedrichs
operator domain at every positive heat time. The actual operator output
is the constructed bounded heat generator multiplier, with norm <=||f||/t.
Using half-time smoothing and the proved on-domain full derivative gives
full strong differentiability for arbitrary initial data at positive time.

The norm-square derivative is minus twice the ACTUAL completed Dirichlet
energy. This energy is nonnegative and at most ||f||^2/t. No smoothing,
derivative, energy or domain assertion is supplied as a premise. No
geometric C-infinity or minimal differential-domain assertion is made.
-/

namespace ImbalancedChen.Part3.Gamma0ActualPositiveTimeHeatDissipation20261025a

noncomputable section
open Set Filter Topology MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0ActualHeatGenerator20261025a
open Gamma0ActualHeatDirichletDissipation20261025a
open GenericHeatPositiveTimeRegularization20261025a

def actualGammaHeatOutput (N : ℕ) [NeZero N] (t : ℝ) :
    QuotientL2 N→L[ℂ]QuotientL2 N := heatGeneratorOperator (actualGammaHeatData N) t

/-- Genuine graph smoothing for arbitrary initial physical quotient data. -/
theorem actualGammaHeat_positive_graph (N : ℕ) [NeZero N]
    {t : ℝ} (ht : 0<t) (f : QuotientL2 N) :
    (actualGammaHeat N t f,actualGammaHeatOutput N t f)∈(actualGammaFriedrichs N).graph :=
  (actualGammaFriedrichs_mem_graph_iff N).mpr
    (heatOperator_generator_graph (actualGammaHeatData N) ht f)

def actualPositiveHeatPoint (N : ℕ) [NeZero N] (t : ℝ) (ht : 0<t)
    (f : QuotientL2 N) : (actualGammaFriedrichs N).domain :=
  ⟨actualGammaHeat N t f,LinearPMap.mem_domain_of_mem_graph
    (actualGammaHeat_positive_graph N ht f)⟩

theorem actualGammaFriedrichs_positiveHeatPoint (N : ℕ) [NeZero N]
    {t : ℝ} (ht : 0<t) (f : QuotientL2 N) :
    actualGammaFriedrichs N (actualPositiveHeatPoint N t ht f)=actualGammaHeatOutput N t f :=
  (actualGammaFriedrichs N).mem_graph_snd_inj
    ((actualGammaFriedrichs N).mem_graph (actualPositiveHeatPoint N t ht f))
    (actualGammaHeat_positive_graph N ht f) rfl

theorem actualGammaHeatOutput_norm_le (N : ℕ) [NeZero N]
    {t : ℝ} (ht : 0<t) (f : QuotientL2 N) :
    ‖actualGammaHeatOutput N t f‖≤‖f‖/t :=
  heatGeneratorOperator_norm_le (actualGammaHeatData N) ht f

/-- Full strong derivative for arbitrary actual quotient-L2 data,
derived from genuine half-time domain smoothing, not a derivative premise. -/
theorem actualGammaHeat_hasDerivAt (N : ℕ) [NeZero N]
    (f : QuotientL2 N) {t : ℝ} (ht : 0<t) :
    HasDerivAt (fun s : ℝ => actualGammaHeat N s f) (-actualGammaHeatOutput N t f) t := by
  let b : ℝ := t/2
  have hb : 0<b := by dsimp [b]; positivity
  have htb : 0<t-b := by dsimp [b]; linarith
  let u : (actualGammaFriedrichs N).domain := actualPositiveHeatPoint N b hb f
  have hsem := actualGammaHeat_add N htb.le hb.le
  have htime : t-b+b=t := by ring
  rw [htime] at hsem
  have hpoint : actualHeatDomainPoint N (t-b) u=actualPositiveHeatPoint N t ht f := by
    apply Subtype.ext
    change actualGammaHeat N (t-b) (actualGammaHeat N b f)=actualGammaHeat N t f
    exact (congrArg (fun A : QuotientL2 N→L[ℂ]QuotientL2 N => A f) hsem).symm
  have houtput : actualGammaHeat N (t-b) (actualGammaFriedrichs N u)=
      actualGammaHeatOutput N t f := by
    rw [← actualGammaFriedrichs_heat_commute,hpoint,actualGammaFriedrichs_positiveHeatPoint]
  have hd := (actualGammaHeat_hasDerivAt_on_domain N u htb).scomp t
    ((hasDerivAt_id t).sub_const b)
  have hder : HasDerivAt (fun s : ℝ => actualGammaHeat N (s-b) (u:QuotientL2 N))
      (-actualGammaHeatOutput N t f) t := by
    simpa only [Function.comp_def,one_smul,houtput] using hd
  apply hder.congr_of_eventuallyEq
  have hbt : b<t := sub_pos.mp htb
  filter_upwards [gt_mem_nhds hbt] with s hs
  have hadd := actualGammaHeat_add N (sub_pos.mpr hs).le hb.le
  have hst : s-b+b=s := by ring
  rw [hst] at hadd
  exact congrArg (fun A : QuotientL2 N→L[ℂ]QuotientL2 N => A f) hadd

/-- Total auxiliary scalar pairing. At every positive time the theorem
below identifies it with the genuine canonical completed Dirichlet form. -/
def actualGammaHeatPhysicalEnergy (N : ℕ) [NeZero N] (t : ℝ) (f : QuotientL2 N) : ℝ :=
  (inner ℂ (actualGammaHeat N t f) (actualGammaHeatOutput N t f)).re

theorem actualGammaHeatPhysicalEnergy_eq_Dirichlet (N : ℕ) [NeZero N]
    {t : ℝ} (ht : 0<t) (f : QuotientL2 N) :
    actualGammaHeatPhysicalEnergy N t f=
      (actualDirichletPair N
        (actualOperatorEnergyLift N (actualPositiveHeatPoint N t ht f))
        (actualOperatorEnergyLift N (actualPositiveHeatPoint N t ht f))).re := by
  rw [actualOperatorEnergyLift_pair,actualGammaFriedrichs_positiveHeatPoint]

theorem actualGammaHeatPhysicalEnergy_nonneg (N : ℕ) [NeZero N]
    {t : ℝ} (ht : 0<t) (f : QuotientL2 N) :
    0≤actualGammaHeatPhysicalEnergy N t f := by
  rw [actualGammaHeatPhysicalEnergy_eq_Dirichlet N ht f]
  exact actualDirichletPair_nonneg N _

/-- Quantitative actual positive-time form-energy bound for EVERY
initial quotient vector, using genuine generator and heat bounds. -/
theorem actualGammaHeatPhysicalEnergy_le (N : ℕ) [NeZero N]
    {t : ℝ} (ht : 0<t) (f : QuotientL2 N) :
    actualGammaHeatPhysicalEnergy N t f≤‖f‖^2/t := by
  calc
    _ ≤ ‖actualGammaHeat N t f‖*‖actualGammaHeatOutput N t f‖ := re_inner_le_norm _ _
    _ ≤ ‖f‖*(‖f‖/t) := mul_le_mul
      (actualGammaHeat_apply_norm_le N t f) (actualGammaHeatOutput_norm_le N ht f)
      (norm_nonneg _) (norm_nonneg _)
    _ = ‖f‖^2/t := by ring

/-- Actual completed-Dirichlet dissipation for ALL physical initial data
at positive times, from the genuine strong derivative just proved. -/
theorem actualGammaHeat_norm_sq_hasDerivAt_all (N : ℕ) [NeZero N]
    (f : QuotientL2 N) {t : ℝ} (ht : 0<t) :
    HasDerivAt (fun s : ℝ => ‖actualGammaHeat N s f‖^2)
      (-2*actualGammaHeatPhysicalEnergy N t f) t := by
  have hd := (actualGammaHeat_hasDerivAt N f ht).norm_sq
  simpa only [real_inner_eq_re_inner (𝕜:=ℂ),inner_neg_right,Complex.neg_re,
    actualGammaHeatPhysicalEnergy,mul_neg,neg_mul] using hd

end
end ImbalancedChen.Part3.Gamma0ActualPositiveTimeHeatDissipation20261025a
