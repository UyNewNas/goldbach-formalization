import ImbalancedChen.Part3ActualNonzeroSourceCore
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Original actual-mode coefficients and their one-boundedness

This is the minimal declaration-preserving recovery from the original
Part3ActualSeparatedRowFiniteMatcher, Part3ActualSeparatedRowLogModeSupplier,
Part3ActualM2FinitePoissonAdapter and Part3ActualModeJointBetaPositiveCount.
Exact donor identities and byte ranges are recorded in
COEFFICIENT_SOURCE_INTAKE.json under the P3.1 actual-mass-budget audit.
Only imports, namespace/open context and this header are new here.

The original gamma2 coefficient remains outside branch conjugation.
The original shortened signed h block and residue indicator are retained,
as is the period-64 Fourier basis. Existing actual carrier definitions are
imported from their accepted owner rather than redeclared.

These coefficient bounds do not reconstruct the original row, sum the
outer Fourier modes, or establish a uniform original-family tail budget.
-/

noncomputable section

namespace ImbalancedChen.Part3.GeneralDActivePairCountSourceOnly
open Classical Finset

theorem factorCarrier_bounds {N : ℝ} (hN : 1 ≤ N) {n : ℕ}
    (hn : n ∈ factorCarrier N) :
    0 < n ∧ N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N := by
  obtain ⟨hlo, hhi⟩ := mem_Icc.mp hn
  have hloR : N ≤ (n : ℝ) :=
    (Nat.le_ceil N).trans (by exact_mod_cast hlo)
  have hnOne : 1 ≤ n := by exact_mod_cast hN.trans hloR
  exact ⟨by omega, hloR,
    (show (n : ℝ) ≤ (Nat.floor (2 * N) : ℝ) by exact_mod_cast hhi).trans
      (Nat.floor_le (by linarith))⟩

end ImbalancedChen.Part3.GeneralDActivePairCountSourceOnly

namespace ImbalancedChen.Part3.GeneralDRootResidueCostSourceOnly

variable (A : ℕ) [NeZero A]

/-- Once u=zeta^{-1} and k=[h] are fixed, this depends only on inner t. -/
def rootT (a : ZMod A) (u : (ZMod A)ˣ) (k : ZMod A)
    (t : (ZMod A)ˣ) : ℂ :=
  ZMod.stdAddChar (-a * k * ((u : ZMod A) * (↑(t⁻¹) : ZMod A)))

end ImbalancedChen.Part3.GeneralDRootResidueCostSourceOnly

namespace ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly
open Classical Finset GeneralDRootResidueCostSourceOnly

def natUnit (A n : ℕ) : (ZMod A)ˣ :=
  if hn : n.Coprime A then ZMod.unitOfCoprime n hn else 1

def branch (negative : Bool) (z : ℂ) : ℂ := if negative then (starRingEnd ℂ) z else z

def commonLambda (D delta g l : ℕ) [NeZero (g * l)] (a : ℤ) (negative : Bool)
    (u : (ZMod (g * l))ˣ) (k : ZMod (g * l)) (W : ℕ → ℂ) (t : ℕ) : ℂ :=
  W (D / delta * t) * branch negative
    (rootT (g * l) (a : ZMod (g * l)) u k (natUnit (g * l) t))

def commonOmega (g l : ℕ) (k : ZMod (g * l)) (omega : ℤ → ℂ) (h : ℤ) : ℂ :=
  if (h : ZMod (g * l)) = k then omega h else 0

end ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly

namespace P3TwoLogMixed22SourceOnly
open Complex

local instance period_pos : Fact (0 < (32 : ℝ) - (-32)) := ⟨by norm_num⟩

def basis (n : ℤ) (x : ℝ) : ℂ :=
  fourier n (x : AddCircle ((32 : ℝ) - (-32)))

lemma norm_basis (n : ℤ) (x : ℝ) : ‖basis n x‖ = 1 := Circle.norm_coe _

end P3TwoLogMixed22SourceOnly

namespace P3ActualLogAdapterSourceOnly
open ImbalancedChen.Part3 ImbalancedChen.Part3.CommonSmoothCutoff
open P3TwoLogMixed22SourceOnly

def Hnat (j : ℕ) : ℕ := 2 ^ j
def Hreal (j : ℕ) : ℝ := (Hnat j : ℝ)

def Uu (d : MediumAtom) (s : ℕ) : ℝ := (s : ℝ) / d.Q2

/- EXACT finite signed dyadic fibres. No final block is enlarged. -/
def window (d : MediumAtom) (D : ℕ) (Z : ℝ) : Finset ℤ :=
  poissonNonzeroFrequencyWindow (d.sharedSmoothFrequencyBound Z D)
def dyadicKey (h : ℤ) : ℕ × Bool := (Nat.log 2 h.natAbs, decide (h < 0))
def block (d : MediumAtom) (D : ℕ) (Z : ℝ) (a : ℕ × Bool) : Finset ℤ :=
  (window d D Z).filter (fun h => dyadicKey h = a)

def innerPhase (d : MediumAtom) (s : ℕ) (n : ℤ) : ℂ := basis (-n) (Real.log (Uu d s))
def hPhase (j : ℕ) (h n : ℤ) : ℂ := basis n (Real.log (|(h : ℝ)| / Hreal j))

def innerMultiplier (d : MediumAtom) (s : ℕ) (n : ℤ) : ℂ :=
  ((Uu d s)⁻¹ : ℝ) * innerPhase d s n
def hMode (d : MediumAtom) (D : ℕ) (Z : ℝ) (a : ℕ × Bool) (h n : ℤ) : ℂ :=
  if h ∈ block d D Z a then hPhase a.1 h n else 0

lemma norm_innerPhase (d : MediumAtom) (s : ℕ) (n : ℤ) : ‖innerPhase d s n‖ = 1 := norm_basis _ _
lemma norm_hPhase (j : ℕ) (h n : ℤ) : ‖hPhase j h n‖ = 1 := norm_basis _ _

lemma norm_hMode_le (d : MediumAtom) (D : ℕ) (Z : ℝ) (a : ℕ × Bool) (h n : ℤ) :
    ‖hMode d D Z a h n‖ ≤ 1 := by
  unfold hMode
  split_ifs
  · exact (norm_hPhase _ _ _).le
  · simp only [norm_zero, zero_le_one]

end P3ActualLogAdapterSourceOnly

namespace ImbalancedChen.Part3.ActualLogModePacketInstanceSourceOnly
open ActualSeparatedRowPacketMatchSourceOnly

def modeW (e : MediumAtom) (m : ℤ × ℤ) (negative : Bool) (s : ℕ) : ℂ :=
  e.gamma2 s * branch negative (_root_.P3ActualLogAdapterSourceOnly.innerMultiplier e s m.2)

def modeOmega (e : MediumAtom) (D : ℕ) (Z : ℝ) (tag : ℕ × Bool)
    (m : ℤ × ℤ) (negative : Bool) (h : ℤ) : ℂ :=
  branch negative (_root_.P3ActualLogAdapterSourceOnly.hMode e D Z tag h m.2)

end ImbalancedChen.Part3.ActualLogModePacketInstanceSourceOnly

namespace ImbalancedChen.Part3.ActualM2FinitePoissonAdapterSourceOnly
open ActualSeparatedRowPacketMatchSourceOnly

/-- In particular gamma2(q*t) is NOT a newly independent coefficient.
The root phase and the actual log multiplier are fixed on this u,k,m fibre. -/
def actualModeLambda (e : MediumAtom) (D delta g l : ℕ) [NeZero (g*l)]
    (m : ℤ × ℤ) (negative : Bool) (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) : ℕ → ℂ :=
  commonLambda D delta g l e.residue negative u k
    (ActualLogModePacketInstanceSourceOnly.modeW e m negative)

/-- The final shortened signed dyadic block and the actual residue class
are BOTH in one common h coefficient. There is no b,c or completed-m argument. -/
def actualModeOmega (e : MediumAtom) (D g l : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool) (k : ZMod (g*l)) (h : ℤ) : ℂ :=
  if h ∈ _root_.P3ActualLogAdapterSourceOnly.block e D Z tag then
    commonOmega g l k (ActualLogModePacketInstanceSourceOnly.modeOmega e D Z tag m negative) h
  else 0

end ImbalancedChen.Part3.ActualM2FinitePoissonAdapterSourceOnly

namespace ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly
open Classical Finset
open GeneralDActivePairCountSourceOnly GeneralDRootResidueCostSourceOnly
open ActualSeparatedRowPacketMatchSourceOnly ActualM2FinitePoissonAdapterSourceOnly
attribute [local instance] Classical.propDecidable

private theorem norm_branch_eq (negative : Bool) (z : ℂ) :
    ‖branch negative z‖ = ‖z‖ := by
  cases negative <;> simp [branch]

private theorem norm_rootT_eq (A : ℕ) [NeZero A] (a : ZMod A)
    (u : (ZMod A)ˣ) (k : ZMod A) (t : (ZMod A)ˣ) :
    ‖rootT A a u k t‖ = 1 := by
  rw [rootT, ZMod.stdAddChar_apply, Circle.norm_coe]

/-- This uses the actual image-of-divisible-s carrier, even when q=0. -/
private theorem baseCarrier_original_window {e : MediumAtom} {q t : ℕ}
    (ht : t ∈ baseCarrier e q) : q*t ∈ factorCarrier e.Q2 := by
  obtain ⟨s, hs, rfl⟩ := mem_image.mp ht
  obtain ⟨hs, hd⟩ := mem_filter.mp hs
  have he : q*(s/q) = s := by
    simpa only [Nat.mul_comm] using Nat.div_mul_cancel hd
  rwa [he]

private theorem original_innerMultiplier_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e) {s : ℕ}
    (hs : s ∈ factorCarrier e.Q2) (n : ℤ) :
    ‖_root_.P3ActualLogAdapterSourceOnly.innerMultiplier e s n‖ ≤ 1 := by
  have hQ : 1 ≤ e.Q2 := he.2.2.2.1
  have hQ0 : 0 < e.Q2 := zero_lt_one.trans_le hQ
  have hslo := (factorCarrier_bounds hQ hs).2.1
  have hU : 1 ≤ _root_.P3ActualLogAdapterSourceOnly.Uu e s := by
    change 1 ≤ (s : ℝ)/e.Q2
    exact (le_div_iff₀ hQ0).mpr (by simpa only [one_mul] using hslo)
  have hU0 := zero_lt_one.trans_le hU
  have hi : (_root_.P3ActualLogAdapterSourceOnly.Uu e s)⁻¹ ≤ (1 : ℝ) := by
    simpa only [one_div] using (div_le_one hU0).mpr hU
  simpa only [_root_.P3ActualLogAdapterSourceOnly.innerMultiplier, norm_mul,
    _root_.P3ActualLogAdapterSourceOnly.norm_innerPhase, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hU0.le)] using hi

/-- Original gamma2(q*t) remains outside the branch conjugation. -/
theorem actualModeLambda_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e)
    (D delta g l : ℕ) [NeZero (g*l)] (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) {t : ℕ}
    (ht : t ∈ baseCarrier e (D/delta)) :
    ‖actualModeLambda e D delta g l m negative u k t‖ ≤ 1 := by
  have hs := baseCarrier_original_window ht
  have hg : ‖e.gamma2 (D/delta*t)‖ ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h2, _⟩ := he
    exact (h2 _ hs).1
  have hi := original_innerMultiplier_norm_le he hs m.2
  simp only [actualModeLambda, commonLambda,
    ActualLogModePacketInstanceSourceOnly.modeW, norm_mul,
    norm_branch_eq, norm_rootT_eq, mul_one]
  exact (mul_le_mul hg hi (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- Includes the shortened signed h block AND root residue indicator. -/
theorem actualModeOmega_norm_le (e : MediumAtom) (D g l : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (k : ZMod (g*l)) (h : ℤ) :
    ‖actualModeOmega e D g l Z tag m negative k h‖ ≤ 1 := by
  unfold actualModeOmega commonOmega
  split_ifs
  · simpa only [ActualLogModePacketInstanceSourceOnly.modeOmega, norm_branch_eq] using
      _root_.P3ActualLogAdapterSourceOnly.norm_hMode_le e D Z tag h m.2
  all_goals simp only [norm_zero, zero_le_one]

end ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly

end
