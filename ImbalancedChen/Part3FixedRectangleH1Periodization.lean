import ImbalancedChen.Part3FixedRectangleH1EnergyLift
import ImbalancedChen.Part3GammaCompactWeakSeedL2Continuity
import ImbalancedChen.Part3GammaSmoothMultiplierPeriodization

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The fixed-positive-rectangle H1 model is a genuine closed linear subspace
of three ordinary planar L2 classes. Its actual compact-seed Poincare
periodization lifts to a BOUNDED COMPLEX-LINEAR map into the existing
Gamma EnergyCompletion. Both linearity and the norm bound are proved:
compact weak-seed subtraction/scaling and physicalProjection injectivity
supply linearity; genuine finite H1 approximants supply the norm bound.
There is no assumed linear extension, limit, form membership, or output.
-/
namespace ImbalancedChen.Part3.FixedRectangleH1Periodization20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open CompactC2ProductMollifier20261026a ProductKernelL2TranslationAverage20261026a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open GammaCompactSeedL2Transport20261026a GammaCompactWeakSeedPoincareL220261026b
open GammaCompactWeakSeedL2Continuity20261026b GammaSmoothMultiplierPeriodization20261026a
open Gamma0WholeChartCoordinateWeakEquation20261026b CanonicalPlanarL2UnitarySourceOnly
open UpperRectangleMollifierGeometry20261026b LocalH1Tests20261026b
open CompactH1CanonicalSeedL220261026b FixedRectangleH1JetSpace20261026b
open FixedRectangleH1EnergyLift20261026b

instance rectangleJet_complete (L R a b : ℝ) : CompleteSpace (RectangleJet L R a b) :=
  (rectangleH1Jets_isClosed L R a b).completeSpace_coe

/-- AE seed congruence is derived quantitatively from the actual compact
weak-seed bound, not by changing pointwise orbit sums on a null set. -/
theorem weakSeedL2_congr_ae (N : ℕ) [NeZero N]
    (f g : UpperHalfPlane → ℂ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (K : Set UpperHalfPlane) (hK : IsCompact K)
    (hfs : Function.support f ⊆ K) (hgs : Function.support g ⊆ K)
    (hfg : f =ᵐ[volume] g) :
    weakSeedL2 N f hf K hK hfs = weakSeedL2 N g hg K hK hgs := by
  have hin : hf.toLp f = hg.toLp g := by
    apply Lp.ext
    exact hf.coeFn_toLp.trans (hfg.trans hg.coeFn_toLp.symm)
  have hb := weakSeedL2_difference_norm_sq_le N f g hf hg K hK hfs hgs
  rw [hin,sub_self,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero] at hb
  have hz : ‖weakSeedL2 N f hf K hK hfs - weakSeedL2 N g hg K hK hgs‖ = 0 := by
    nlinarith [norm_nonneg (weakSeedL2 N f hf K hK hfs - weakSeedL2 N g hg K hK hgs)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem weakSeedL2_smul (N : ℕ) [NeZero N]
    (c : ℂ) (f : UpperHalfPlane → ℂ) (hf : MemLp f 2 volume)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hfs : Function.support f ⊆ K) :
    ∀ hcs : Function.support (c • f) ⊆ K,
    weakSeedL2 N (c • f) (hf.const_smul c) K hK hcs = c • weakSeedL2 N f hf K hK hfs := by
  intro hcs
  have htrace : complexPoincare N (c • f) = c • complexPoincare N f := by
    have hh := complexPoincare_mul_invariant N (fun _ => c) f (fun _ _ => rfl)
    have hquot : quotientMultiplier N (fun _ => c) (fun _ _ => rfl) = fun _ => c := by
      funext q
      induction q using Quotient.inductionOn with | h z => rfl
    simpa only [hquot,Pi.mul_apply,Pi.smul_apply,smul_eq_mul] using hh
  apply Lp.ext
  filter_upwards [weakSeedL2_ae N (c • f) (hf.const_smul c) K hK hcs,
    weakSeedL2_ae N f hf K hK hfs,
    Lp.coeFn_smul c (weakSeedL2 N f hf K hK hfs)] with q hcf hfq hsm
  rw [hcf,hsm,hfq]
  exact congrFun htrace q

/-- A literal, compact representative of the value component. -/
def seed {L R a b : ℝ} (v : RectangleJet L R a b) : UpperHalfPlane → ℂ :=
  upperSeed (representative v 0)

theorem seed_memLp {L R a b : ℝ} (ha : 0 < a) (v : RectangleJet L R a b) :
    MemLp (seed v) 2 (volume : Measure UpperHalfPlane) := by
  apply upperSeed_memLp (representative_memLp v 0) ha
  intro p hp
  have hn : p ∉ rect L R a b := fun h => not_lt_of_ge h.2.1 hp
  simp only [representative,indicator_of_notMem hn]

theorem seed_support {L R a b : ℝ} (v : RectangleJet L R a b) :
    Function.support (seed v) ⊆ upperRectangle L R a b := by
  intro z hz
  exact representative_support v 0 (subset_tsupport hz)

theorem seed_sub_ae {L R a b : ℝ} (v w : RectangleJet L R a b) :
    seed (v-w) =ᵐ[(volume : Measure UpperHalfPlane)] seed v - seed w := by
  have hp : representative (v-w) 0 =ᵐ[(volume : Measure Plane)]
      representative v 0 - representative w 0 := by
    filter_upwards [representative_ae (v-w) 0,representative_ae v 0,representative_ae w 0,
      Lp.coeFn_sub (v.val 0) (w.val 0)] with p hvw hv hw hsub
    rw [hvw,Pi.sub_apply,hv,hw]
    exact hsub
  simpa only [seed,upperSeed,coordinateSeed,chartMap,
    Complex.measurableEquivRealProd_apply,Pi.sub_apply] using
      chartMap_quasiMeasurePreserving.ae_eq hp

theorem seed_smul_ae {L R a b : ℝ} (c : ℂ) (v : RectangleJet L R a b) :
    seed (c • v) =ᵐ[(volume : Measure UpperHalfPlane)] c • seed v := by
  have hp : representative (c • v) 0 =ᵐ[(volume : Measure Plane)] c • representative v 0 := by
    filter_upwards [representative_ae (c • v) 0,representative_ae v 0,
      Lp.coeFn_smul c (v.val 0)] with p hcv hv hsm
    rw [hcv,Pi.smul_apply,hv]
    exact hsm
  simpa only [seed,upperSeed,coordinateSeed,chartMap,
    Complex.measurableEquivRealProd_apply,Pi.smul_apply] using
      chartMap_quasiMeasurePreserving.ae_eq hp

def periodizedSeed (N : ℕ) [NeZero N] {L R a b : ℝ} (ha : 0 < a)
    (v : RectangleJet L R a b) : QuotientL2 N :=
  weakSeedL2 N (seed v) (seed_memLp ha v) (upperRectangle L R a b)
    (upperRectangle_isCompact L R a b ha) (seed_support v)

theorem periodizedSeed_ae (N : ℕ) [NeZero N] {L R a b : ℝ}
    (ha : 0 < a) (v : RectangleJet L R a b) :
    (periodizedSeed N ha v : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (seed v) := weakSeedL2_ae N _ _ _ _ _

theorem periodizedSeed_sub (N : ℕ) [NeZero N] {L R a b : ℝ}
    (ha : 0 < a) (v w : RectangleJet L R a b) :
    periodizedSeed N ha (v-w) = periodizedSeed N ha v - periodizedSeed N ha w := by
  calc
    _ = weakSeedL2 N (seed v-seed w) ((seed_memLp ha v).sub (seed_memLp ha w))
        (upperRectangle L R a b) (upperRectangle_isCompact L R a b ha)
        (sub_support_subset (seed_support v) (seed_support w)) :=
      weakSeedL2_congr_ae N _ _ _ _ _ _ _ _ (seed_sub_ae v w)
    _ = _ := weakSeedL2_sub N _ _ _ _ _ _ _ _

theorem periodizedSeed_smul (N : ℕ) [NeZero N] {L R a b : ℝ}
    (ha : 0 < a) (c : ℂ) (v : RectangleJet L R a b) :
    periodizedSeed N ha (c • v) = c • periodizedSeed N ha v := by
  have hs : Function.support (c • seed v) ⊆ upperRectangle L R a b := by
    intro z hz
    apply seed_support v
    intro hzero
    exact hz (by simp only [Pi.smul_apply,hzero,smul_zero])
  calc
    _ = weakSeedL2 N (c • seed v) ((seed_memLp ha v).const_smul c)
        (upperRectangle L R a b) (upperRectangle_isCompact L R a b ha) hs :=
      weakSeedL2_congr_ae N _ _ _ _ _ _ _ _ (seed_smul_ae c v)
    _ = _ := weakSeedL2_smul N c _ _ _ _ _ hs

/-- Chosen only after existence and the quantitative bound have been
proved. Its physical value uniquely determines the energy vector. -/
def energyLift (N : ℕ) [NeZero N] (L R a b : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b) (v : RectangleJet L R a b) : EnergyCompletion N :=
  Classical.choose (exists_bounded_energy_lift N L R a b hLR ha hab v)

theorem energyLift_norm_le (N : ℕ) [NeZero N] (L R a b : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b) (v : RectangleJet L R a b) :
    ‖energyLift N L R a b hLR ha hab v‖ ≤ fixedEnergyBound N L R a b * ‖v‖ :=
  (Classical.choose_spec (exists_bounded_energy_lift N L R a b hLR ha hab v)).1

theorem energyLift_physical (N : ℕ) [NeZero N] (L R a b : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b) (v : RectangleJet L R a b) :
    physicalProjection N (energyLift N L R a b hLR ha hab v) = periodizedSeed N ha v := by
  apply Lp.ext
  exact (Classical.choose_spec (exists_bounded_energy_lift N L R a b hLR ha hab v)).2.trans
    (periodizedSeed_ae N ha v).symm

theorem energyLift_sub (N : ℕ) [NeZero N] (L R a b : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b) (v w : RectangleJet L R a b) :
    energyLift N L R a b hLR ha hab (v-w) =
      energyLift N L R a b hLR ha hab v - energyLift N L R a b hLR ha hab w := by
  apply physicalProjection_injective N
  rw [map_sub,energyLift_physical,energyLift_physical,energyLift_physical,periodizedSeed_sub]

theorem energyLift_smul (N : ℕ) [NeZero N] (L R a b : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b) (c : ℂ) (v : RectangleJet L R a b) :
    energyLift N L R a b hLR ha hab (c • v) = c • energyLift N L R a b hLR ha hab v := by
  apply physicalProjection_injective N
  rw [map_smul,energyLift_physical,energyLift_physical,periodizedSeed_smul]

def periodizationLinear (N : ℕ) [NeZero N] (L R a b : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b) :
    RectangleJet L R a b →ₗ[ℂ] EnergyCompletion N where
  toFun := energyLift N L R a b hLR ha hab
  map_add' := by
    intro v w
    have h := energyLift_sub N L R a b hLR ha hab (v+w) w
    rw [add_sub_cancel_right] at h
    exact (eq_sub_iff_add_eq.mp h).symm
  map_smul' := energyLift_smul N L R a b hLR ha hab

/-- Actual bounded complex-linear compact-H1 periodization into the
already existing Gamma energy completion. -/
def periodization (N : ℕ) [NeZero N] (L R a b : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b) :
    RectangleJet L R a b →L[ℂ] EnergyCompletion N :=
  (periodizationLinear N L R a b hLR ha hab).mkContinuous (fixedEnergyBound N L R a b)
    (energyLift_norm_le N L R a b hLR ha hab)

theorem periodization_norm_le (N : ℕ) [NeZero N] (L R a b : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b) :
    ‖periodization N L R a b hLR ha hab‖ ≤ fixedEnergyBound N L R a b := by
  apply ContinuousLinearMap.opNorm_le_bound (fixedEnergyBound_pos N L R a b).le
  exact energyLift_norm_le N L R a b hLR ha hab

theorem periodization_physical_ae (N : ℕ) [NeZero N] (L R a b : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b) (v : RectangleJet L R a b) :
    ((physicalProjection N (periodization N L R a b hLR ha hab v) : QuotientL2 N) :
      Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] complexPoincare N (seed v) := by
  change (physicalProjection N (energyLift N L R a b hLR ha hab v) : Gamma0OrbitSpace N → ℂ) =ᵐ[_] _
  rw [energyLift_physical]
  exact periodizedSeed_ae N ha v

/-- Any physical representative with this raw periodization is therefore
in the actual form range; it is not assumed to be a smooth core vector. -/
theorem periodization_physical_unique (N : ℕ) [NeZero N] (L R a b : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b) (v : RectangleJet L R a b)
    (e : EnergyCompletion N)
    (he : (physicalProjection N e : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (seed v)) : e = periodization N L R a b hLR ha hab v := by
  apply physicalProjection_injective N
  apply Lp.ext
  exact he.trans (periodization_physical_ae N L R a b hLR ha hab v).symm

end
end ImbalancedChen.Part3.FixedRectangleH1Periodization20261026b
