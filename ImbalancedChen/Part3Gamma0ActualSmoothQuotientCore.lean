import ImbalancedChen.Part3Gamma0SmoothCompactTensorCore
import ImbalancedChen.Part3Gamma0QuotientCoreRepresentativeFaithfulness

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

An actual typed smooth core inside the EXISTING canonical Gamma0 quotient
L2 space. Its generators are exactly the already constructed quotient L2
vectors of finite smooth compact-tensor Poincare seeds. Finite span
membership proves existence of a continuous, C-infinity chart representative;
it is not an hDomain input. The actual conull-tiling faithfulness theorem
proves that representative unique. Consequently the canonical H-valued
representative map is an injective complex linear map.

The existing upperMaass expression is then defined on this typed core and
proved independent of representative choice. This does NOT claim that its
output is quotient L2, or that it equals the Poincare sum of seed Laplacians.
Those require the separate actual Mobius chain/equivariance and L2 suppliers.
-/

namespace ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorQuotientL2Core20261025a
open ImbalancedChen.Part3.Gamma0SmoothCompactTensorCore20261025a
open ImbalancedChen.Part3.Gamma0QuotientCoreRepresentativeFaithfulness20261025a

abbrev QuotientL2 (N : ℕ) [NeZero N] := Lp ℂ 2 (carrierPushforward N)
abbrev SmoothSeed := Σ n : ℕ, Fin n → SmoothCompactTensor

def seedVector (N : ℕ) [NeZero N] (s : SmoothSeed) : QuotientL2 N :=
  smoothQuotientPoincareL2 N Finset.univ s.2

/-- The actual finite smooth compact-seed quotient L2 span. -/
def smoothCore (N : ℕ) [NeZero N] : Submodule ℂ (QuotientL2 N) :=
  Submodule.span ℂ (range (seedVector N))

/-- A representative PROPERTY, later derived for every member of the
actual seed span. The input and measure are the original quotient L2. -/
def HasSmoothRepresentative (N : ℕ) [NeZero N] (u : QuotientL2 N) : Prop :=
  ∃ F : Gamma0OrbitSpace N → ℂ,
    (u : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] F ∧
    Continuous (F ∘ orbitProjection N) ∧
    ContDiffOn ℝ ∞ (extendUpper (F ∘ orbitProjection N)) positiveChart

theorem extendUpper_add (F G : UpperHalfPlane → ℂ) :
    extendUpper (F+G) = extendUpper F + extendUpper G := by
  funext p
  by_cases hp : 0 < p.2 <;> simp [extendUpper,hp]

theorem extendUpper_smul (c : ℂ) (F : UpperHalfPlane → ℂ) :
    extendUpper (c • F) = c • extendUpper F := by
  funext p
  by_cases hp : 0 < p.2 <;> simp [extendUpper,hp]

def representableSubmodule (N : ℕ) [NeZero N] : Submodule ℂ (QuotientL2 N) where
  carrier := {u | HasSmoothRepresentative N u}
  zero_mem' := by
    refine ⟨0,Lp.coeFn_zero ℂ 2 (carrierPushforward N),continuous_const,?_⟩
    have heq : extendUpper ((0 : Gamma0OrbitSpace N → ℂ) ∘ orbitProjection N) = 0 := by
      funext p
      by_cases hp : 0 < p.2 <;> simp [extendUpper,hp]
    rw [heq]
    exact contDiffOn_const
  add_mem' := by
    intro u v hu hv
    obtain ⟨F,hFu,hFc,hFs⟩ := hu
    obtain ⟨G,hGv,hGc,hGs⟩ := hv
    refine ⟨F+G,?_,hFc.add hGc,?_⟩
    · filter_upwards [Lp.coeFn_add u v,hFu,hGv] with q hsum hf hg
      simpa only [Pi.add_apply,hf,hg] using hsum
    · change ContDiffOn ℝ ∞ (extendUpper ((F ∘ orbitProjection N)+(G ∘ orbitProjection N))) positiveChart
      rw [extendUpper_add]
      exact hFs.add hGs
  smul_mem' := by
    intro c u hu
    obtain ⟨F,hFu,hFc,hFs⟩ := hu
    refine ⟨c • F,?_,continuous_const.smul hFc,?_⟩
    · filter_upwards [Lp.coeFn_smul c u,hFu] with q hsmul hf
      simpa only [Pi.smul_apply,hf] using hsmul
    · change ContDiffOn ℝ ∞ (extendUpper (c • (F ∘ orbitProjection N))) positiveChart
      rw [extendUpper_smul]
      exact contDiffOn_const.smul hFs

theorem seedVector_hasSmoothRepresentative (N : ℕ) [NeZero N] (s : SmoothSeed) :
    HasSmoothRepresentative N (seedVector N s) := by
  let T : Fin s.1 → CompactTensor := fun i => (s.2 i).toCompactTensor
  refine ⟨quotientTensorPoincare N Finset.univ T,
    (quotientTensorPoincare_memLp_two N Finset.univ T).coeFn_toLp,?_,?_⟩
  · simpa only [Function.comp_def,quotientTensorPoincare_projection] using
      finiteCompactTensorPoincare_continuous N Finset.univ T
  · exact smoothQuotientPoincare_pullback_cinfty N Finset.univ s.2

/-- Actual span membership supplies the smooth representative; no domain
membership or target representative contract is assumed. -/
theorem smoothCore_le_representable (N : ℕ) [NeZero N] :
    smoothCore N ≤ representableSubmodule N := by
  apply Submodule.span_le.mpr
  rintro u ⟨s,rfl⟩
  exact seedVector_hasSmoothRepresentative N s

theorem smoothCore_hasSmoothRepresentative (N : ℕ) [NeZero N] (u : smoothCore N) :
    HasSmoothRepresentative N (u : QuotientL2 N) :=
  smoothCore_le_representable N u.property

def chosenQuotientRepresentative (N : ℕ) [NeZero N] (u : smoothCore N) : Gamma0OrbitSpace N → ℂ :=
  Classical.choose (smoothCore_hasSmoothRepresentative N u)

theorem chosenRepresentative_spec (N : ℕ) [NeZero N] (u : smoothCore N) :
    ((u : QuotientL2 N) : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
        chosenQuotientRepresentative N u ∧
    Continuous (chosenQuotientRepresentative N u ∘ orbitProjection N) ∧
    ContDiffOn ℝ ∞ (extendUpper (chosenQuotientRepresentative N u ∘ orbitProjection N)) positiveChart :=
  Classical.choose_spec (smoothCore_hasSmoothRepresentative N u)

def coreRepresentative (N : ℕ) [NeZero N] (u : smoothCore N) : UpperHalfPlane → ℂ :=
  chosenQuotientRepresentative N u ∘ orbitProjection N

theorem coreRepresentative_continuous (N : ℕ) [NeZero N] (u : smoothCore N) :
    Continuous (coreRepresentative N u) := (chosenRepresentative_spec N u).2.1

theorem coreRepresentative_cinfty (N : ℕ) [NeZero N] (u : smoothCore N) :
    ContDiffOn ℝ ∞ (extendUpper (coreRepresentative N u)) positiveChart :=
  (chosenRepresentative_spec N u).2.2

theorem coreRepresentative_gamma0_invariant (N : ℕ) [NeZero N] (u : smoothCore N)
    (gamma : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    coreRepresentative N u (gamma • z) = coreRepresentative N u z := by
  change chosenQuotientRepresentative N u (orbitProjection N (gamma • z)) = _
  rw [orbitProjection_smul]

/-- The chosen representative equals ANY continuous representative of
the same actual quotient L2 vector, by the true full-H faithfulness proof. -/
theorem coreRepresentative_eq (N : ℕ) [NeZero N] (u : smoothCore N)
    (F : Gamma0OrbitSpace N → ℂ)
    (hF : ((u : QuotientL2 N) : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] F)
    (hFc : Continuous (F ∘ orbitProjection N)) :
    coreRepresentative N u = F ∘ orbitProjection N :=
  quotient_ae_continuous_pullback_eq N ((chosenRepresentative_spec N u).1.symm.trans hF)
    (coreRepresentative_continuous N u) hFc

theorem coreRepresentative_add (N : ℕ) [NeZero N] (u v : smoothCore N) :
    coreRepresentative N (u+v) = coreRepresentative N u + coreRepresentative N v := by
  apply coreRepresentative_eq N (u+v)
    (chosenQuotientRepresentative N u + chosenQuotientRepresentative N v)
  · filter_upwards [Lp.coeFn_add (u : QuotientL2 N) (v : QuotientL2 N),
      (chosenRepresentative_spec N u).1,(chosenRepresentative_spec N v).1] with q hsum hu hv
    simpa only [Pi.add_apply,hu,hv] using hsum
  · exact (coreRepresentative_continuous N u).add (coreRepresentative_continuous N v)

theorem coreRepresentative_smul (N : ℕ) [NeZero N] (c : ℂ) (u : smoothCore N) :
    coreRepresentative N (c • u) = c • coreRepresentative N u := by
  apply coreRepresentative_eq N (c • u) (c • chosenQuotientRepresentative N u)
  · filter_upwards [Lp.coeFn_smul c (u : QuotientL2 N),(chosenRepresentative_spec N u).1]
      with q hsmul hu
    simpa only [Pi.smul_apply,hu] using hsmul
  · exact continuous_const.smul (coreRepresentative_continuous N u)

/-- A genuine complex-linear faithful realization of the actual quotient
smooth compact-seed core as smooth automorphic H-functions. -/
def coreRepresentativeLinearMap (N : ℕ) [NeZero N] :
    smoothCore N →ₗ[ℂ] (UpperHalfPlane → ℂ) where
  toFun := coreRepresentative N
  map_add' := coreRepresentative_add N
  map_smul' := coreRepresentative_smul N

theorem coreRepresentative_injective (N : ℕ) [NeZero N] :
    Function.Injective (coreRepresentativeLinearMap N) := by
  intro u v huv
  have hQ : chosenQuotientRepresentative N u = chosenQuotientRepresentative N v := by
    funext q
    exact Quotient.inductionOn q (fun z => congrFun huv z)
  apply Subtype.ext
  apply Lp.ext
  exact (chosenRepresentative_spec N u).1.trans
    ((Filter.Eventually.of_forall (fun q => congrFun hQ q)).trans
      (chosenRepresentative_spec N v).1.symm)

def seedCoreElement (N : ℕ) [NeZero N] (s : SmoothSeed) : smoothCore N :=
  ⟨seedVector N s,Submodule.subset_span ⟨s,rfl⟩⟩

/-- On every literal generating seed the canonical realization is its
actual locally finite Gamma0 Poincare function, not a substitute vector. -/
theorem coreRepresentative_seed (N : ℕ) [NeZero N] (s : SmoothSeed) :
    coreRepresentative N (seedCoreElement N s) = smoothFinitePoincare N Finset.univ s.2 := by
  let T : Fin s.1 → CompactTensor := fun i => (s.2 i).toCompactTensor
  have heq := coreRepresentative_eq N (seedCoreElement N s)
    (quotientTensorPoincare N Finset.univ T)
    (quotientTensorPoincare_memLp_two N Finset.univ T).coeFn_toLp
    (by simpa only [Function.comp_def,quotientTensorPoincare_projection] using
      finiteCompactTensorPoincare_continuous N Finset.univ T)
  simpa only [Function.comp_def,quotientTensorPoincare_projection] using heq

/-- The true coordinate Maass expression is now typed on this actual
quotient input core. Its quotient-L2 output supplier is still separate. -/
def smoothCoreMaass (N : ℕ) [NeZero N] (u : smoothCore N) : UpperHalfPlane → ℂ :=
  upperMaass (coreRepresentative N u)

theorem smoothCoreMaass_representation_independent (N : ℕ) [NeZero N] (u : smoothCore N)
    (F : Gamma0OrbitSpace N → ℂ)
    (hF : ((u : QuotientL2 N) : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] F)
    (hFc : Continuous (F ∘ orbitProjection N)) :
    smoothCoreMaass N u = upperMaass (F ∘ orbitProjection N) :=
  congrArg upperMaass (coreRepresentative_eq N u F hF hFc)

end
end ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
