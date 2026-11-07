import ImbalancedChen.Part3ActualCompletedGamma0SideCancellation
import ImbalancedChen.Part3Gamma0FiniteMeasureCarrier
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Finite Green-current trace over the ACTUAL finite SL(2,Z)/Gamma0(N)
class space. The inverse representatives are the same ones used by the
actual finite-measure carrier. Under a in SL(2,Z), the exact class
permutation is q |-> a^(-1)*q. The relative matrix is proved to lie in
Gamma0 from quotient equality, so actual function invariance identifies
the pulled-back one-forms. Finite reindexing gives full SL(2,Z) covariance,
in particular the genuine S and T chart relations. The actual completed
fields supply all regularity and Gamma0 invariance inputs.
No arbitrary polygon pairing or target trace-invariance premise occurs.
-/

noncomputable section
open Set Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups BigOperators
open ImbalancedChen.Part3.SLRealGreenCurrent20261026b
open ImbalancedChen.Part3.Gamma0PairedEdgeGreen20261026b
open ImbalancedChen.Part3.ActualCompletedGamma0Sides20261026b
open ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a
open ImbalancedChen.Part3.FrickeNormalizer

namespace ImbalancedChen.Part3.Gamma0FiniteCosetGreenTrace20261026b

local instance (N : ℕ) [NeZero N] : Fintype (gamma0Classes N) :=
  (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex

def classShift (N : ℕ) (a : SL(2, ℤ)) : gamma0Classes N ≃ gamma0Classes N where
  toFun q := a⁻¹ • q
  invFun q := a • q
  left_inv q := by simp
  right_inv q := by simp

/-- The actual Gamma0 matrix implementing the change of inverse section. -/
def reindexGamma (N : ℕ) (a : SL(2, ℤ)) (q : gamma0Classes N) :
    CongruenceSubgroup.Gamma0 N :=
  ⟨(Quotient.out q)⁻¹ * a * Quotient.out (classShift N a q), by
    have hm : (QuotientGroup.mk (a⁻¹ * Quotient.out q) : gamma0Classes N) =
        QuotientGroup.mk (Quotient.out (classShift N a q)) := by
      calc
        _ = a⁻¹ • q := by
          simpa only [smul_eq_mul] using MulAction.Quotient.mk_smul_out (a⁻¹) q
        _ = _ := (Quotient.out_eq' (classShift N a q)).symm
    have h := QuotientGroup.eq.mp hm
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using h⟩

theorem reindexGamma_mul_inverseClassRep (N : ℕ) [NeZero N]
    (a : SL(2, ℤ)) (q : gamma0Classes N) :
    (reindexGamma N a q : SL(2, ℤ)) * inverseClassRep N (classShift N a q) =
      inverseClassRep N q * a := by
  unfold reindexGamma inverseClassRep
  group

def pulledField (g : SL(2, ℤ)) (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  F (slMap (realSL g) w)

theorem pulledField_differentiableAt (g : SL(2, ℤ)) (F : ℂ → ℂ)
    (hF : ∀ z : UpperHalfPlane, DifferentiableAt ℝ F (z : ℂ)) (z : UpperHalfPlane) :
    DifferentiableAt ℝ (pulledField g F) (z : ℂ) := by
  have hFm : DifferentiableAt ℝ F (slMap (realSL g) z) := by
    simpa only [slMap_eq_action, realSL_action_int] using hF (g • z)
  exact hFm.comp (z : ℂ) (slMap_hasFDerivAt (realSL g) z).differentiableAt

/-- This local identity is produced by the actual coset relation and
actual Gamma0 invariance, before taking any derivatives. -/
theorem reindex_pulledField_eventually (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (q : gamma0Classes N) (F : ℂ → ℂ)
    (hFI : ∀ δ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      F ((δ • z : UpperHalfPlane) : ℂ) = F z) (z : UpperHalfPlane) :
    (fun w => pulledField (inverseClassRep N q) F (slMap (realSL a) w)) =ᶠ[𝓝 (z : ℂ)]
      pulledField (inverseClassRep N (classShift N a q)) F := by
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  let W : UpperHalfPlane := ⟨w, hw⟩
  have ha : slMap (realSL a) w = ((a • W : UpperHalfPlane) : ℂ) := by
    change slMap (realSL a) (W : ℂ) = _
    rw [slMap_eq_action, realSL_action_int]
  have hr : slMap (realSL (inverseClassRep N (classShift N a q))) w =
      ((inverseClassRep N (classShift N a q) • W : UpperHalfPlane) : ℂ) := by
    change slMap _ (W : ℂ) = _
    rw [slMap_eq_action, realSL_action_int]
  unfold pulledField
  rw [ha, slMap_eq_action, realSL_action_int, hr]
  have h := hFI (reindexGamma N a q) (inverseClassRep N (classShift N a q) • W)
  change F (((reindexGamma N a q : SL(2, ℤ)) •
    (inverseClassRep N (classShift N a q) • W) : UpperHalfPlane) : ℂ) = _ at h
  rw [← mul_smul, reindexGamma_mul_inverseClassRep, mul_smul] at h
  exact h

def traceTerm (N : ℕ) [NeZero N] (F G : ℂ → ℂ) (q : gamma0Classes N)
    (z : UpperHalfPlane) (v : ℂ) : ℂ :=
  greenOneForm (pulledField (inverseClassRep N q) F)
    (pulledField (inverseClassRep N q) G) z v

def greenTrace (N : ℕ) [NeZero N] (F G : ℂ → ℂ) (z : UpperHalfPlane) (v : ℂ) : ℂ :=
  ∑ q : gamma0Classes N, traceTerm N F G q z v

/-- A trace summand is the pullback of the genuine physical current with
the exact Mobius tangent factor. -/
theorem traceTerm_eq_physical (N : ℕ) [NeZero N] (F G : ℂ → ℂ)
    (hF : ∀ z : UpperHalfPlane, DifferentiableAt ℝ F (z : ℂ))
    (hG : ∀ z : UpperHalfPlane, DifferentiableAt ℝ G (z : ℂ))
    (q : gamma0Classes N) (z : UpperHalfPlane) (v : ℂ) :
    traceTerm N F G q z v =
      greenOneForm F G ((inverseClassRep N q • z : UpperHalfPlane) : ℂ)
        (slFactor (realSL (inverseClassRep N q)) z * v) := by
  have hFm : DifferentiableAt ℝ F (slMap (realSL (inverseClassRep N q)) z) := by
    simpa only [slMap_eq_action, realSL_action_int] using hF (inverseClassRep N q • z)
  have hGm : DifferentiableAt ℝ G (slMap (realSL (inverseClassRep N q)) z) := by
    simpa only [slMap_eq_action, realSL_action_int] using hG (inverseClassRep N q • z)
  simpa only [traceTerm, pulledField, slMap_eq_action, realSL_action_int] using
    greenOneForm_slMap_pullback (realSL (inverseClassRep N q)) z F G hFm hGm v

theorem traceTerm_reindex (N : ℕ) [NeZero N] (F G : ℂ → ℂ)
    (hF : ∀ z : UpperHalfPlane, DifferentiableAt ℝ F (z : ℂ))
    (hG : ∀ z : UpperHalfPlane, DifferentiableAt ℝ G (z : ℂ))
    (hFI : ∀ δ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      F ((δ • z : UpperHalfPlane) : ℂ) = F z)
    (hGI : ∀ δ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      G ((δ • z : UpperHalfPlane) : ℂ) = G z)
    (a : SL(2, ℤ)) (q : gamma0Classes N) (z : UpperHalfPlane) (v : ℂ) :
    traceTerm N F G q (a • z) (slFactor (realSL a) z * v) =
      traceTerm N F G (classShift N a q) z v := by
  have hPF : DifferentiableAt ℝ (pulledField (inverseClassRep N q) F) (slMap (realSL a) z) := by
    simpa only [slMap_eq_action, realSL_action_int] using
      pulledField_differentiableAt (inverseClassRep N q) F hF (a • z)
  have hPG : DifferentiableAt ℝ (pulledField (inverseClassRep N q) G) (slMap (realSL a) z) := by
    simpa only [slMap_eq_action, realSL_action_int] using
      pulledField_differentiableAt (inverseClassRep N q) G hG (a • z)
  have hcov := greenOneForm_slMap_pullback (realSL a) z _ _ hPF hPG v
  have heq := greenOneForm_congr_of_eventuallyEq _ _ _ _ (z : ℂ) v
    (reindex_pulledField_eventually N a q F hFI z)
    (reindex_pulledField_eventually N a q G hGI z)
  simpa only [traceTerm, slMap_eq_action, realSL_action_int] using hcov.symm.trans heq

/-- Full modular covariance is proved by the ACTUAL finite coset reindex. -/
theorem greenTrace_SL_invariant (N : ℕ) [NeZero N] (F G : ℂ → ℂ)
    (hF : ∀ z : UpperHalfPlane, DifferentiableAt ℝ F (z : ℂ))
    (hG : ∀ z : UpperHalfPlane, DifferentiableAt ℝ G (z : ℂ))
    (hFI : ∀ δ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      F ((δ • z : UpperHalfPlane) : ℂ) = F z)
    (hGI : ∀ δ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      G ((δ • z : UpperHalfPlane) : ℂ) = G z)
    (a : SL(2, ℤ)) (z : UpperHalfPlane) (v : ℂ) :
    greenTrace N F G (a • z) (slFactor (realSL a) z * v) = greenTrace N F G z v := by
  unfold greenTrace
  calc
    _ = ∑ q : gamma0Classes N, traceTerm N F G (classShift N a q) z v := by
      apply Finset.sum_congr rfl
      intro q hq
      exact traceTerm_reindex N F G hF hG hFI hGI a q z v
    _ = _ := (classShift N a).sum_comp (fun q => traceTerm N F G q z v)

def actualCompletedGreenTrace (N : ℕ) [NeZero N] (s u : ℂ)
    (z : UpperHalfPlane) (v : ℂ) : ℂ :=
  greenTrace N (completedComplexField N s) (completedComplexField N u) z v

/-- Actual continued fields discharge the regularity and invariance
inputs; the conclusion has no trace-covariance supplier among its premises. -/
theorem actualCompletedGreenTrace_SL_invariant (N : ℕ) [NeZero N]
    (s u : ℂ) (hs : s ∈ completedRegularDomain N) (hu : u ∈ completedRegularDomain N)
    (a : SL(2, ℤ)) (z : UpperHalfPlane) (v : ℂ) :
    actualCompletedGreenTrace N s u (a • z) (slFactor (realSL a) z * v) =
      actualCompletedGreenTrace N s u z v :=
  greenTrace_SL_invariant N _ _
    (fun z => (completedComplexField_contDiffAt N s z).differentiableAt (by simp))
    (fun z => (completedComplexField_contDiffAt N u z).differentiableAt (by simp))
    (completedComplexField_Gamma0_invariant N (Nat.pos_of_ne_zero (NeZero.ne N)) s hs)
    (completedComplexField_Gamma0_invariant N (Nat.pos_of_ne_zero (NeZero.ne N)) u hu) a z v

theorem slFactor_T (w : ℂ) : slFactor (realSL ModularGroup.T) w = 1 := by
  simp [slFactor, realGL, realSL, UpperHalfPlane.denom, ModularGroup.coe_T]

theorem slFactor_S (w : ℂ) : slFactor (realSL ModularGroup.S) w = 1 / w ^ 2 := by
  simp [slFactor, realGL, realSL, UpperHalfPlane.denom, ModularGroup.coe_S]

/-- Exact translation-side trace relation with its actual tangent. -/
theorem actualCompletedGreenTrace_T (N : ℕ) [NeZero N]
    (s u : ℂ) (hs : s ∈ completedRegularDomain N) (hu : u ∈ completedRegularDomain N)
    (z : UpperHalfPlane) (v : ℂ) :
    actualCompletedGreenTrace N s u (ModularGroup.T • z) v =
      actualCompletedGreenTrace N s u z v := by
  simpa only [slFactor_T, one_mul] using
    actualCompletedGreenTrace_SL_invariant N s u hs hu ModularGroup.T z v

/-- Exact inversion-side trace relation; the derivative 1/z^2 is retained. -/
theorem actualCompletedGreenTrace_S (N : ℕ) [NeZero N]
    (s u : ℂ) (hs : s ∈ completedRegularDomain N) (hu : u ∈ completedRegularDomain N)
    (z : UpperHalfPlane) (v : ℂ) :
    actualCompletedGreenTrace N s u (ModularGroup.S • z) ((1 / (z : ℂ) ^ 2) * v) =
      actualCompletedGreenTrace N s u z v := by
  simpa only [slFactor_S] using
    actualCompletedGreenTrace_SL_invariant N s u hs hu ModularGroup.S z v

end ImbalancedChen.Part3.Gamma0FiniteCosetGreenTrace20261026b
