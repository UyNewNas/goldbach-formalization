import ImbalancedChen.Part3CompactUpperWeakJetModel

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
One canonical COMPLEX-LINEAR actual energy periodization on the algebraic
compact upper-chart weak-jet model. A source rectangle is chosen only to
evaluate an already constructed bounded map. Actual enlargement coherence
proves independence of that choice and then proves linearity on common
source rectangles. Every fixed-rectangle restriction is exactly the
previous bounded operator, with its explicit LOCAL norm bound and actual
raw Poincare physical value. No global continuity is claimed or assumed.
-/
namespace ImbalancedChen.Part3.CompactUpperWeakJetPeriodization20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open FixedRectangleH1JetSpace20261026b FixedRectangleH1EnergyLift20261026b
open FixedRectangleH1Periodization20261026b FixedRectangleH1PeriodizationCoherence20261026b
open CompactUpperWeakJetModel20261026b

def evaluateInSource (N : ℕ) [NeZero N] (v : CompactUpperJet) (Q : SourceRectangle)
    (hs : v.val ∈ supportedJets Q.container) : EnergyCompletion N :=
  periodization N Q.left Q.right Q.floor Q.ceiling Q.horizontal_order Q.floor_pos Q.vertical_order
    (toRectangle v Q hs)

/-- Different source rectangles give the SAME energy vector. The common
rectangle is explicitly constructed and its two model inclusions preserve
the original three L2 classes exactly. -/
theorem evaluateInSource_independent (N : ℕ) [NeZero N] (v : CompactUpperJet)
    (Q S : SourceRectangle) (hQ : v.val ∈ supportedJets Q.container)
    (hS : v.val ∈ supportedJets S.container) :
    evaluateInSource N v Q hQ = evaluateInSource N v S hS := by
  let T := Q.common S
  have hi : inclusion (Q.subset_common_left S) (toRectangle v Q hQ) =
      inclusion (Q.subset_common_right S) (toRectangle v S hS) := by
    apply Subtype.ext
    rfl
  have hleft := periodization_inclusion N Q.left Q.right Q.floor Q.ceiling
    T.left T.right T.floor T.ceiling Q.horizontal_order Q.floor_pos Q.vertical_order
    T.horizontal_order T.floor_pos T.vertical_order (Q.subset_common_left S) (toRectangle v Q hQ)
  have hright := periodization_inclusion N S.left S.right S.floor S.ceiling
    T.left T.right T.floor T.ceiling S.horizontal_order S.floor_pos S.vertical_order
    T.horizontal_order T.floor_pos T.vertical_order (Q.subset_common_right S) (toRectangle v S hS)
  exact hleft.symm.trans ((congrArg
    (periodization N T.left T.right T.floor T.ceiling T.horizontal_order T.floor_pos T.vertical_order) hi).trans hright)

def periodizationValue (N : ℕ) [NeZero N] (v : CompactUpperJet) : EnergyCompletion N :=
  evaluateInSource N v (chosenSource v) (chosenSource_support v)

theorem periodizationValue_eq_source (N : ℕ) [NeZero N] (v : CompactUpperJet)
    (Q : SourceRectangle) (hQ : v.val ∈ supportedJets Q.container) :
    periodizationValue N v = evaluateInSource N v Q hQ :=
  evaluateInSource_independent N v _ _ _ _

theorem periodizationValue_add (N : ℕ) [NeZero N] (v w : CompactUpperJet) :
    periodizationValue N (v+w) = periodizationValue N v + periodizationValue N w := by
  let Q := (chosenSource v).common (chosenSource w)
  have hv : v.val ∈ supportedJets Q.container :=
    supportedJets_mono ((chosenSource v).subset_common_left (chosenSource w)) (chosenSource_support v)
  have hw : w.val ∈ supportedJets Q.container :=
    supportedJets_mono ((chosenSource v).subset_common_right (chosenSource w)) (chosenSource_support w)
  have hsum : (v+w).val ∈ supportedJets Q.container := (supportedJets Q.container).add_mem hv hw
  rw [periodizationValue_eq_source N (v+w) Q hsum,
    periodizationValue_eq_source N v Q hv,periodizationValue_eq_source N w Q hw]
  have heq : toRectangle (v+w) Q hsum = toRectangle v Q hv + toRectangle w Q hw := by
    apply Subtype.ext
    rfl
  simp only [evaluateInSource,heq,map_add]

theorem periodizationValue_smul (N : ℕ) [NeZero N] (c : ℂ) (v : CompactUpperJet) :
    periodizationValue N (c • v) = c • periodizationValue N v := by
  let Q := chosenSource v
  have hv : v.val ∈ supportedJets Q.container := chosenSource_support v
  have hcv : (c • v).val ∈ supportedJets Q.container := (supportedJets Q.container).smul_mem c hv
  rw [periodizationValue_eq_source N (c • v) Q hcv,periodizationValue_eq_source N v Q hv]
  have heq : toRectangle (c • v) Q hcv = c • toRectangle v Q hv := by
    apply Subtype.ext
    rfl
  simp only [evaluateInSource,heq,map_smul]

/-- Algebraic compact-source periodization. Its local boundedness is
proved below; no single global bound is asserted for this union. -/
def compactPeriodization (N : ℕ) [NeZero N] : CompactUpperJet →ₗ[ℂ] EnergyCompletion N where
  toFun := periodizationValue N
  map_add' := periodizationValue_add N
  map_smul' := periodizationValue_smul N

/-- The canonical map restricts EXACTLY to the original bounded operator
on each fixed rectangle. -/
theorem compactPeriodization_includeRectangle (N : ℕ) [NeZero N] (Q : SourceRectangle)
    (v : RectangleJet Q.left Q.right Q.floor Q.ceiling) :
    compactPeriodization N (includeRectangle Q v) =
      periodization N Q.left Q.right Q.floor Q.ceiling Q.horizontal_order Q.floor_pos Q.vertical_order v := by
  change periodizationValue N (includeRectangle Q v) = _
  rw [periodizationValue_eq_source N _ Q v.property.1]
  rfl

theorem compactPeriodization_comp_includeRectangle (N : ℕ) [NeZero N] (Q : SourceRectangle) :
    (compactPeriodization N).comp (includeRectangle Q).toLinearMap =
      (periodization N Q.left Q.right Q.floor Q.ceiling Q.horizontal_order Q.floor_pos Q.vertical_order).toLinearMap := by
  ext v
  exact compactPeriodization_includeRectangle N Q v

theorem compactPeriodization_local_norm_le (N : ℕ) [NeZero N] (v : CompactUpperJet)
    (Q : SourceRectangle) (hQ : v.val ∈ supportedJets Q.container) :
    ‖compactPeriodization N v‖ ≤ fixedEnergyBound N Q.left Q.right Q.floor Q.ceiling * ‖v‖ := by
  change ‖periodizationValue N v‖ ≤ _
  rw [periodizationValue_eq_source N v Q hQ]
  exact energyLift_norm_le N Q.left Q.right Q.floor Q.ceiling Q.horizontal_order Q.floor_pos Q.vertical_order
    (toRectangle v Q hQ)

/-- Literal raw Poincare physical value in ANY valid source rectangle;
its choice does not enter the actual energy vector. -/
theorem compactPeriodization_physical_ae (N : ℕ) [NeZero N] (v : CompactUpperJet)
    (Q : SourceRectangle) (hQ : v.val ∈ supportedJets Q.container) :
    (physicalProjection N (compactPeriodization N v) : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (seed (toRectangle v Q hQ)) := by
  change (physicalProjection N (periodizationValue N v) : Gamma0OrbitSpace N → ℂ) =ᵐ[_] _
  rw [periodizationValue_eq_source N v Q hQ]
  exact periodization_physical_ae N Q.left Q.right Q.floor Q.ceiling
    Q.horizontal_order Q.floor_pos Q.vertical_order (toRectangle v Q hQ)

/-- The geometric-choice-free map is uniquely determined by its true
fixed-source restrictions, rather than by an assumed global extension. -/
theorem compactPeriodization_unique (N : ℕ) [NeZero N]
    (T : CompactUpperJet →ₗ[ℂ] EnergyCompletion N)
    (hT : ∀ Q : SourceRectangle, ∀ v : RectangleJet Q.left Q.right Q.floor Q.ceiling,
      T (includeRectangle Q v) =
        periodization N Q.left Q.right Q.floor Q.ceiling Q.horizontal_order Q.floor_pos Q.vertical_order v) :
    T = compactPeriodization N := by
  ext v
  let Q := chosenSource v
  let u := toRectangle v Q (chosenSource_support v)
  have hu : includeRectangle Q u = v := include_toRectangle v Q (chosenSource_support v)
  calc
    T v = T (includeRectangle Q u) := congrArg T hu.symm
    _ = periodization N Q.left Q.right Q.floor Q.ceiling Q.horizontal_order Q.floor_pos Q.vertical_order u := hT Q u
    _ = compactPeriodization N (includeRectangle Q u) := (compactPeriodization_includeRectangle N Q u).symm
    _ = compactPeriodization N v := congrArg (compactPeriodization N) hu

end
end ImbalancedChen.Part3.CompactUpperWeakJetPeriodization20261026b

