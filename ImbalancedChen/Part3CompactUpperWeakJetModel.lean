import ImbalancedChen.Part3FixedRectangleH1PeriodizationCoherence

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A genuine complex submodule of native three-component ordinary planar L2
jets with literal weak derivatives and SOME compact positive rectangle
source support. Explicit common min/max rectangles prove addition stays
in the model. Fixed-rectangle inclusions are linear isometries. This
algebraic compact-support union is not claimed to be closed or to admit
a uniform periodization bound independent of its source rectangle.
-/
namespace ImbalancedChen.Part3.CompactUpperWeakJetModel20261026b
noncomputable section
open Set Filter MeasureTheory
open CompactC2ProductMollifier20261026a ProductKernelL2TranslationAverage20261026a
open LocalH1Tests20261026b FixedRectangleH1JetSpace20261026b FixedRectangleH1EnergyLift20261026b

structure SourceRectangle where
  left : ℝ
  right : ℝ
  floor : ℝ
  ceiling : ℝ
  horizontal_order : left ≤ right
  floor_pos : 0 < floor
  vertical_order : floor ≤ ceiling

def SourceRectangle.container (Q : SourceRectangle) : Set Plane :=
  rect Q.left Q.right Q.floor Q.ceiling

def SourceRectangle.common (Q S : SourceRectangle) : SourceRectangle where
  left := min Q.left S.left
  right := max Q.right S.right
  floor := min Q.floor S.floor
  ceiling := max Q.ceiling S.ceiling
  horizontal_order := (min_le_left _ _).trans (Q.horizontal_order.trans (le_max_left _ _))
  floor_pos := lt_min Q.floor_pos S.floor_pos
  vertical_order := (min_le_left _ _).trans (Q.vertical_order.trans (le_max_left _ _))

theorem SourceRectangle.subset_common_left (Q S : SourceRectangle) :
    Q.container ⊆ (Q.common S).container := by
  intro p hp
  exact ⟨⟨(min_le_left _ _).trans hp.1.1,hp.1.2.trans (le_max_left _ _)⟩,
    ⟨(min_le_left _ _).trans hp.2.1,hp.2.2.trans (le_max_left _ _)⟩⟩

theorem SourceRectangle.subset_common_right (Q S : SourceRectangle) :
    S.container ⊆ (Q.common S).container := by
  intro p hp
  exact ⟨⟨(min_le_right _ _).trans hp.1.1,hp.1.2.trans (le_max_right _ _)⟩,
    ⟨(min_le_right _ _).trans hp.2.1,hp.2.2.trans (le_max_right _ _)⟩⟩

theorem supportedJets_mono {K K' : Set Plane} (hK : K ⊆ K') :
    supportedJets K ≤ supportedJets K' := by
  intro v hv i
  filter_upwards [hv i] with p hp
  intro hp'
  exact hp (fun hpK => hp' (hK hpK))

/-- Genuine compact upper-chart weak H1 jets. The source support is an
existential geometric condition, not a chosen representative/limit. -/
def compactUpperWeakJets : Submodule ℂ JetSpace where
  carrier := {v | v ∈ weakJets ∧ ∃ Q : SourceRectangle, v ∈ supportedJets Q.container}
  zero_mem' := ⟨weakJets.zero_mem,⟨⟨-1,1,1,2,by norm_num,by norm_num,by norm_num⟩,
    (supportedJets _).zero_mem⟩⟩
  add_mem' := by
    intro v w hv hw
    obtain ⟨Q,hQ⟩ := hv.2
    obtain ⟨S,hS⟩ := hw.2
    refine ⟨weakJets.add_mem hv.1 hw.1,⟨Q.common S,?_⟩⟩
    exact (supportedJets (Q.common S).container).add_mem
      (supportedJets_mono (Q.subset_common_left S) hQ)
      (supportedJets_mono (Q.subset_common_right S) hS)
  smul_mem' := by
    intro c v hv
    obtain ⟨Q,hQ⟩ := hv.2
    exact ⟨weakJets.smul_mem c hv.1,⟨Q,(supportedJets Q.container).smul_mem c hQ⟩⟩

abbrev CompactUpperJet := compactUpperWeakJets

/-- The norm is exactly the inherited native L2 triple norm. -/
def includeRectangle (Q : SourceRectangle) :
    RectangleJet Q.left Q.right Q.floor Q.ceiling →ₗᵢ[ℂ] CompactUpperJet where
  toLinearMap := {
    toFun := fun v => ⟨v.val,⟨v.property.2,⟨Q,v.property.1⟩⟩⟩
    map_add' := by intro v w; rfl
    map_smul' := by intro c v; rfl }
  norm_map' := by intro v; rfl

@[simp] theorem includeRectangle_val (Q : SourceRectangle)
    (v : RectangleJet Q.left Q.right Q.floor Q.ceiling) :
    (includeRectangle Q v).val = v.val := rfl

def toRectangle (v : CompactUpperJet) (Q : SourceRectangle)
    (hs : v.val ∈ supportedJets Q.container) :
    RectangleJet Q.left Q.right Q.floor Q.ceiling := ⟨v.val,⟨hs,v.property.1⟩⟩

@[simp] theorem include_toRectangle (v : CompactUpperJet) (Q : SourceRectangle)
    (hs : v.val ∈ supportedJets Q.container) : includeRectangle Q (toRectangle v Q hs) = v := by
  apply Subtype.ext
  rfl

@[simp] theorem toRectangle_val (v : CompactUpperJet) (Q : SourceRectangle)
    (hs : v.val ∈ supportedJets Q.container) : (toRectangle v Q hs).val = v.val := rfl

/-- A choice of source geometry only; no value, gradient, approximation
or energy vector is chosen by this operation. -/
def chosenSource (v : CompactUpperJet) : SourceRectangle := Classical.choose v.property.2

theorem chosenSource_support (v : CompactUpperJet) :
    v.val ∈ supportedJets (chosenSource v).container := Classical.choose_spec v.property.2

def chosenRectangleJet (v : CompactUpperJet) :
    RectangleJet (chosenSource v).left (chosenSource v).right
      (chosenSource v).floor (chosenSource v).ceiling :=
  toRectangle v (chosenSource v) (chosenSource_support v)

@[simp] theorem chosenRectangleJet_val (v : CompactUpperJet) :
    (chosenRectangleJet v).val = v.val := rfl

end
end ImbalancedChen.Part3.CompactUpperWeakJetModel20261026b
