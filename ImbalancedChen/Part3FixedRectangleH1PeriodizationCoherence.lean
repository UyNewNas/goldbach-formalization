import ImbalancedChen.Part3FixedRectangleH1Periodization

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Enlarging a fixed positive source rectangle gives a genuine norm-preserving
complex-linear inclusion of its closed H1 jet spaces. The actual bounded
energy periodization maps COMMUTE with that inclusion. The pointwise
indicator representatives may change; canonical seed AE congruence and
the proved compact weak-Poincare bound pay that change before physical
projection injectivity is used. No chosen-lift compatibility is assumed.
-/
namespace ImbalancedChen.Part3.FixedRectangleH1PeriodizationCoherence20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open CompactC2ProductMollifier20261026a ProductKernelL2TranslationAverage20261026a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open GammaCompactWeakSeedPoincareL220261026b CanonicalPlanarL2UnitarySourceOnly
open Gamma0WholeChartCoordinateWeakEquation20261026b UpperRectangleMollifierGeometry20261026b
open LocalH1Tests20261026b CompactH1CanonicalSeedL220261026b
open FixedRectangleH1JetSpace20261026b FixedRectangleH1EnergyLift20261026b
open FixedRectangleH1Periodization20261026b

def inclusionLinear {L R a b L' R' a' b' : ℝ}
    (hK : rect L R a b ⊆ rect L' R' a' b') :
    RectangleJet L R a b →ₗ[ℂ] RectangleJet L' R' a' b' where
  toFun v := ⟨v.val,⟨by
    intro i
    filter_upwards [v.property.1 i] with p hp
    intro hp'
    exact hp (fun hpK => hp' (hK hpK)),v.property.2⟩⟩
  map_add' := by intro v w; rfl
  map_smul' := by intro c v; rfl

/-- The input norm remains the original ordinary three-component L2
norm, with no rectangle-dependent renormalization. -/
def inclusion {L R a b L' R' a' b' : ℝ}
    (hK : rect L R a b ⊆ rect L' R' a' b') :
    RectangleJet L R a b →ₗᵢ[ℂ] RectangleJet L' R' a' b' where
  toLinearMap := inclusionLinear hK
  norm_map' := by intro v; rfl

@[simp] theorem inclusion_val {L R a b L' R' a' b' : ℝ}
    (hK : rect L R a b ⊆ rect L' R' a' b') (v : RectangleJet L R a b) :
    (inclusion hK v).val = v.val := rfl

@[simp] theorem inclusion_refl {L R a b : ℝ} (v : RectangleJet L R a b) :
    inclusion (Subset.refl (rect L R a b)) v = v := by apply Subtype.ext; rfl

@[simp] theorem inclusion_trans {L R a b L' R' a' b' L'' R'' a'' b'' : ℝ}
    (h12 : rect L R a b ⊆ rect L' R' a' b')
    (h23 : rect L' R' a' b' ⊆ rect L'' R'' a'' b'') (v : RectangleJet L R a b) :
    inclusion h23 (inclusion h12 v) = inclusion (h12.trans h23) v := by
  apply Subtype.ext
  rfl

theorem inclusion_norm {L R a b L' R' a' b' : ℝ}
    (hK : rect L R a b ⊆ rect L' R' a' b') (v : RectangleJet L R a b) :
    ‖inclusion hK v‖ = ‖v‖ := rfl

theorem inclusion_representative_ae {L R a b L' R' a' b' : ℝ}
    (hK : rect L R a b ⊆ rect L' R' a' b') (v : RectangleJet L R a b) (i : Fin 3) :
    representative (inclusion hK v) i =ᵐ[(volume : Measure Plane)] representative v i :=
  (representative_ae (inclusion hK v) i).trans (representative_ae v i).symm

theorem inclusion_seed_ae {L R a b L' R' a' b' : ℝ}
    (hK : rect L R a b ⊆ rect L' R' a' b') (v : RectangleJet L R a b) :
    seed (inclusion hK v) =ᵐ[(volume : Measure UpperHalfPlane)] seed v := by
  simpa only [seed,upperSeed,coordinateSeed,chartMap,
    Complex.measurableEquivRealProd_apply] using
      chartMap_quasiMeasurePreserving.ae_eq (inclusion_representative_ae hK v 0)

/-- AE changes of indicator representatives are transported through the
actual Poincare operator using a single genuine compact support bound. -/
theorem inclusion_seed_Poincare_ae (N : ℕ) [NeZero N]
    {L R a b L' R' a' b' : ℝ} (ha : 0 < a) (ha' : 0 < a')
    (hK : rect L R a b ⊆ rect L' R' a' b') (v : RectangleJet L R a b) :
    complexPoincare N (seed (inclusion hK v)) =ᵐ[carrierPushforward N]
      complexPoincare N (seed v) := by
  have hsource : Function.support (seed v) ⊆ upperRectangle L' R' a' b' :=
    fun z hz => hK (seed_support v hz)
  have heq := weakSeedL2_congr_ae N (seed (inclusion hK v)) (seed v)
    (seed_memLp ha' (inclusion hK v)) (seed_memLp ha v)
    (upperRectangle L' R' a' b') (upperRectangle_isCompact L' R' a' b' ha')
    (seed_support (inclusion hK v)) hsource (inclusion_seed_ae hK v)
  have hg := weakSeedL2_ae N (seed v) (seed_memLp ha v)
    (upperRectangle L' R' a' b') (upperRectangle_isCompact L' R' a' b' ha') hsource
  rw [← heq] at hg
  exact (weakSeedL2_ae N (seed (inclusion hK v)) (seed_memLp ha' (inclusion hK v))
    (upperRectangle L' R' a' b') (upperRectangle_isCompact L' R' a' b' ha')
    (seed_support (inclusion hK v))).symm.trans hg

/-- Pointwise compatibility of two independently constructed actual
energy maps, with both positive-rectangle hypotheses explicit. -/
theorem periodization_inclusion (N : ℕ) [NeZero N]
    (L R a b L' R' a' b' : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b)
    (hLR' : L' ≤ R') (ha' : 0 < a') (hab' : a' ≤ b')
    (hK : rect L R a b ⊆ rect L' R' a' b') (v : RectangleJet L R a b) :
    periodization N L' R' a' b' hLR' ha' hab' (inclusion hK v) =
      periodization N L R a b hLR ha hab v := by
  apply physicalProjection_injective N
  apply Lp.ext
  exact (periodization_physical_ae N L' R' a' b' hLR' ha' hab' (inclusion hK v)).trans
    ((inclusion_seed_Poincare_ae N ha ha' hK v).trans
      (periodization_physical_ae N L R a b hLR ha hab v).symm)

/-- Equality of bounded operators: the source-rectangle system commutes
with its genuine linear-isometric enlargement maps. -/
theorem periodization_comp_inclusion (N : ℕ) [NeZero N]
    (L R a b L' R' a' b' : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b)
    (hLR' : L' ≤ R') (ha' : 0 < a') (hab' : a' ≤ b')
    (hK : rect L R a b ⊆ rect L' R' a' b') :
    (periodization N L' R' a' b' hLR' ha' hab').comp (inclusion hK).toContinuousLinearMap =
      periodization N L R a b hLR ha hab := by
  ext v
  exact periodization_inclusion N L R a b L' R' a' b' hLR ha hab hLR' ha' hab' hK v

/-- Enlarged-map evaluation retains the SMALLER source norm bound; the
coarser rectangle's overlap constant is not silently substituted. -/
theorem periodization_inclusion_norm_le (N : ℕ) [NeZero N]
    (L R a b L' R' a' b' : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b)
    (hLR' : L' ≤ R') (ha' : 0 < a') (hab' : a' ≤ b')
    (hK : rect L R a b ⊆ rect L' R' a' b') (v : RectangleJet L R a b) :
    ‖periodization N L' R' a' b' hLR' ha' hab' (inclusion hK v)‖ ≤
      fixedEnergyBound N L R a b * ‖v‖ := by
  rw [periodization_inclusion N L R a b L' R' a' b' hLR ha hab hLR' ha' hab' hK v]
  exact energyLift_norm_le N L R a b hLR ha hab v

end
end ImbalancedChen.Part3.FixedRectangleH1PeriodizationCoherence20261026b
