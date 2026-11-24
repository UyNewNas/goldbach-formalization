import ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Winner9 regular lifting and physical support ownership

Supporting planes of a common finite lifting give null intersections of
the closed physical simplices. A finite strict sign check for each face
supplies the supporting inequalities.
-/

namespace ImbalancedChen.P2Winner9LiftingGeometry

open Set Filter MeasureTheory
open P2Winner9BarycentricMixedDegreeOne (affine)
open P2Winner9PhysicalAffineTransfer
open P2Winner9PhysicalVertexInterpolation
open P2Winner9SelectedRowAnalyticCaps (affine_lower affine_upper)
open P2Winner9SelectedRowRealJacobian (RationalVertices realVertices sourceSupport)

/-- A rational affine row on the eight physical coordinates. -/
structure LiftingPlane where
  offset : ℚ
  coeff : Fin 8 → ℚ

def LiftingPlane.evalQ (p : LiftingPlane) (x : Fin 8 → ℚ) : ℚ :=
  p.offset + ∑ j, p.coeff j * x j

noncomputable def LiftingPlane.eval (p : LiftingPlane) (x : Ambient) : ℝ :=
  (p.offset : ℝ) + ∑ j, (p.coeff j : ℝ) * x j

@[simp] theorem LiftingPlane.eval_cast (p : LiftingPlane) (x : Fin 8 → ℚ) :
    p.eval (fun j => (x j : ℝ)) = (p.evalQ x : ℝ) := by
  simp [LiftingPlane.eval, LiftingPlane.evalQ]

theorem LiftingPlane.eval_vertexMap (p : LiftingPlane) (v : Fin 9 → Ambient) (x : Ambient) :
    p.eval (vertexMap v x) = affine (fun k => p.eval (v k)) x := by
  simp only [LiftingPlane.eval, vertexMap_coordinate, affine_add, affine_constant, affine_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [affine, Finset.mul_sum, mul_assoc]

private noncomputable def LiftingPlane.linear (p : LiftingPlane) : Ambient →ₗ[ℝ] ℝ :=
  ∑ j, (p.coeff j : ℝ) • LinearMap.proj j

private theorem LiftingPlane.linear_apply (p : LiftingPlane) (z : Ambient) :
    p.linear z = ∑ j, (p.coeff j : ℝ) * z j := by
  simp only [LiftingPlane.linear, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul]

private noncomputable def LiftingPlane.wall (p q : LiftingPlane) : AffineSubspace ℝ Ambient where
  carrier := {z | (p.linear - q.linear) z = (q.offset : ℝ) - p.offset}
  smul_vsub_vadd_mem' := by
    intro a x y z hx hy hz
    change (p.linear - q.linear) (a • (x - y) + z) = _
    change (p.linear - q.linear) x = _ at hx
    change (p.linear - q.linear) y = _ at hy
    change (p.linear - q.linear) z = _ at hz
    simp only [map_add, map_smul, map_sub, hx, hy, hz, sub_self, smul_zero, zero_add]

private theorem LiftingPlane.mem_wall (p q : LiftingPlane) (z : Ambient) :
    z ∈ p.wall q ↔ p.eval z = q.eval z := by
  change (p.linear - q.linear) z = _ ↔ _
  simp only [LinearMap.sub_apply, LiftingPlane.linear_apply, LiftingPlane.eval]
  constructor <;> intro h <;> linarith

/-- The equal-value set of two affine rows which differ at some physical point is null. -/
theorem LiftingPlane.eq_null {p q : LiftingPlane} (h : ∃ z, p.eval z ≠ q.eval z) :
    volume {z | p.eval z = q.eval z} = 0 := by
  have he : {z | p.eval z = q.eval z} = (p.wall q : Set Ambient) := by
    ext z
    exact (p.mem_wall q z).symm
  have hwall : p.wall q ≠ ⊤ := by
    obtain ⟨z, hz⟩ := h
    intro hh
    apply hz
    apply (p.mem_wall q z).mp
    rw [hh]
    trivial
  rw [he]
  exact Measure.addHaar_affineSubspace volume (p.wall q) hwall

section Ownership

variable {ι : Type*} {n : ℕ}

def cellVertices (points : Fin n → Fin 8 → ℚ) (ids : ι → Fin 9 → Fin n)
    (i : ι) : RationalVertices :=
  fun k => points (ids i k)

def cellSupport (points : Fin n → Fin 8 → ℚ) (ids : ι → Fin 9 → Fin n)
    (i : ι) : Set Ambient :=
  sourceSupport (cellVertices points ids i)

theorem cellSupport_measurable (points : Fin n → Fin 8 → ℚ)
    (ids : ι → Fin 9 → Fin n) (i : ι) : MeasurableSet (cellSupport points ids i) := by
  unfold cellSupport sourceSupport
  apply IsClosed.measurableSet
  apply IsCompact.isClosed
  apply canonicalSupport_compact.image
  unfold vertexMap
  fun_prop

def vertexSet (ids : Fin 9 → Fin n) : Finset (Fin n) :=
  Finset.univ.image ids

@[simp] theorem mem_vertexSet {ids : Fin 9 → Fin n} {v : Fin n} :
    v ∈ vertexSet ids ↔ ∃ k, ids k = v := by
  simp [vertexSet]

private theorem plane_le_on_cell (points : Fin n → Fin 8 → ℚ) (ids : ι → Fin 9 → Fin n)
    (i : ι) (p q : LiftingPlane) (h : ∀ k, p.evalQ (points (ids i k)) ≤ q.evalQ (points (ids i k)))
    {z : Ambient} (hz : z ∈ cellSupport points ids i) : p.eval z ≤ q.eval z := by
  obtain ⟨x, hx, rfl⟩ := hz
  rw [LiftingPlane.eval_vertexMap, LiftingPlane.eval_vertexMap]
  have hd : affine (fun k => (q.eval (realVertices (cellVertices points ids i) k) -
      p.eval (realVertices (cellVertices points ids i) k))) x ≥ 0 := by
    apply affine_lower hx
    intro k
    rw [sub_nonneg]
    change p.eval (fun j => (points (ids i k) j : ℝ)) ≤
      q.eval (fun j => (points (ids i k) j : ℝ))
    simpa only [LiftingPlane.eval_cast, Rat.cast_le] using h k
  rw [affine_sub] at hd
  exact sub_nonneg.mp hd

/-- A common lifting reduces geometric overlap checks to the supporting
plane inequalities at the finite table and injectivity of the vertex sets. -/
theorem cell_overlap_null (points : Fin n → Fin 8 → ℚ) (ids : ι → Fin 9 → Fin n)
    (height : Fin n → ℚ) (planes : ι → LiftingPlane)
    (own : ∀ i k, (planes i).evalQ (points (ids i k)) = height (ids i k))
    (below : ∀ i v, v ∉ vertexSet (ids i) → (planes i).evalQ (points v) < height v)
    (distinct : Function.Injective (fun i => vertexSet (ids i))) :
    Pairwise fun i j => volume (cellSupport points ids i ∩ cellSupport points ids j) = 0 := by
  have hle (i : ι) (v : Fin n) : (planes i).evalQ (points v) ≤ height v := by
    by_cases hv : v ∈ vertexSet (ids i)
    · obtain ⟨k, rfl⟩ := mem_vertexSet.mp hv
      exact (own i k).le
    · exact (below i v hv).le
  intro i j hij
  have hne : vertexSet (ids i) ≠ vertexSet (ids j) := fun he => hij (distinct he)
  have hplanes : ∃ z, (planes i).eval z ≠ (planes j).eval z := by
    classical
    have hex : ∃ v, (v ∈ vertexSet (ids i) ∧ v ∉ vertexSet (ids j)) ∨
        (v ∈ vertexSet (ids j) ∧ v ∉ vertexSet (ids i)) := by
      by_contra h
      apply hne
      ext v
      by_cases hi : v ∈ vertexSet (ids i) <;>
        by_cases hj : v ∈ vertexSet (ids j) <;>
        simp_all only [iff_true, iff_false]
      · exact False.elim (h ⟨v, Or.inl ⟨hi, hj⟩⟩)
      · exact False.elim (h ⟨v, Or.inr ⟨hj, hi⟩⟩)
    obtain ⟨v, hv | hv⟩ := hex
    · obtain ⟨k, rfl⟩ := mem_vertexSet.mp hv.1
      refine ⟨fun z => (points (ids i k) z : ℝ), ?_⟩
      rw [LiftingPlane.eval_cast, LiftingPlane.eval_cast, own]
      exact_mod_cast (below j (ids i k) hv.2).ne'
    · obtain ⟨k, rfl⟩ := mem_vertexSet.mp hv.1
      refine ⟨fun z => (points (ids j k) z : ℝ), ?_⟩
      rw [LiftingPlane.eval_cast, LiftingPlane.eval_cast, own]
      exact_mod_cast (below i (ids j k) hv.2).ne
  apply measure_mono_null _ (LiftingPlane.eq_null hplanes)
  rintro z ⟨hi, hj⟩
  exact le_antisymm
    (plane_le_on_cell points ids j (planes i) (planes j)
      (fun k => (hle i _).trans_eq (own j k).symm) hj)
    (plane_le_on_cell points ids i (planes j) (planes i)
      (fun k => (hle j _).trans_eq (own i k).symm) hi)

variable [DecidableEq ι]

/-- Remove the original source walls and all intersections from every cell
using a single measurable exceptional set. -/
def exceptionalSet (s : ι → Set Ambient) (walls : Set Ambient) : Set Ambient :=
  walls ∪ ⋃ i, ⋃ j, if i = j then ∅ else s i ∩ s j

def ownedSupport (s : ι → Set Ambient) (walls : Set Ambient) (i : ι) : Set Ambient :=
  s i \ exceptionalSet s walls

theorem exceptionalSet_null [Countable ι] (s : ι → Set Ambient) (walls : Set Ambient)
    (hw : volume walls = 0) (h : Pairwise fun i j => volume (s i ∩ s j) = 0) :
    volume (exceptionalSet s walls) = 0 := by
  apply measure_union_null hw
  apply measure_iUnion_null
  intro i
  apply measure_iUnion_null
  intro j
  by_cases hij : i = j
  · simp [hij]
  · simpa only [if_neg hij] using h hij

theorem exceptionalSet_measurable [Countable ι] (s : ι → Set Ambient)
    (walls : Set Ambient) (hw : MeasurableSet walls) (h : ∀ i, MeasurableSet (s i)) :
    MeasurableSet (exceptionalSet s walls) := by
  apply hw.union
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  by_cases hij : i = j
  · simp [hij]
  · simpa only [if_neg hij] using (h i).inter (h j)

theorem ownedSupport_disjoint (s : ι → Set Ambient) (walls : Set Ambient) :
    Pairwise fun i j => Disjoint (ownedSupport s walls i) (ownedSupport s walls j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨hi, he⟩ ⟨hj, _⟩
  apply he
  right
  apply mem_iUnion.mpr
  refine ⟨i, mem_iUnion.mpr ⟨j, ?_⟩⟩
  rw [if_neg hij]
  exact ⟨hi, hj⟩

theorem ownedSupport_ae_eq [Countable ι] (s : ι → Set Ambient) (walls : Set Ambient)
    (hw : volume walls = 0) (h : Pairwise fun i j => volume (s i ∩ s j) = 0) (i : ι) :
    ownedSupport s walls i =ᵐ[volume] s i := by
  have hn : ∀ᵐ z ∂volume, z ∉ exceptionalSet s walls := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using exceptionalSet_null s walls hw h
  filter_upwards [hn] with z hz
  apply propext
  change z ∈ ownedSupport s walls i ↔ z ∈ s i
  simp [ownedSupport, hz]

/-- Removing null overlaps and source walls preserves every summand. -/
theorem integral_owned_union [Fintype ι] (s : ι → Set Ambient) (walls : Set Ambient)
    (hs : ∀ i, MeasurableSet (s i)) (hw : MeasurableSet walls) (hwn : volume walls = 0)
    (ho : Pairwise fun i j => volume (s i ∩ s j) = 0) {f : Ambient → ℝ}
    (hf : ∀ i, IntegrableOn f (s i)) :
    (∫ z in ⋃ i, ownedSupport s walls i, f z) = ∑ i, ∫ z in s i, f z := by
  rw [integral_iUnion_fintype (s := fun i => ownedSupport s walls i)
    (fun i => (hs i).diff (exceptionalSet_measurable s walls hw hs))
    (ownedSupport_disjoint s walls)
    (fun i => (hf i).mono_set sdiff_subset)]
  exact Finset.sum_congr rfl fun i _ => setIntegral_congr_set (ownedSupport_ae_eq s walls hwn ho i)

theorem sum_cell_integrals_le_source [Fintype ι] (s : ι → Set Ambient) (walls target : Set Ambient)
    (hs : ∀ i, MeasurableSet (s i)) (hw : MeasurableSet walls) (hwn : volume walls = 0)
    (ho : Pairwise fun i j => volume (s i ∩ s j) = 0)
    (inside : ∀ i, s i \ walls ⊆ target) {f : Ambient → ℝ}
    (hf : IntegrableOn f target) (hf0 : 0 ≤ᵐ[volume.restrict target] f) :
    (∑ i, ∫ z in s i, f z) ≤ ∫ z in target, f z := by
  have hord (i : ι) : ownedSupport s walls i ⊆ target := by
    rintro z ⟨hz, hn⟩
    exact inside i ⟨hz, fun hwz => hn (Or.inl hwz)⟩
  have hfi (i : ι) : IntegrableOn f (s i) :=
    (hf.mono_set (hord i)).congr_set_ae (ownedSupport_ae_eq s walls hwn ho i).symm
  rw [← integral_owned_union s walls hs hw hwn ho hfi]
  apply setIntegral_mono_set hf hf0
  exact Filter.Eventually.of_forall (fun z hz => by
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact hord i hi)

end Ownership

section Pulling

variable {κ : Type*} {n : ℕ}

/-- The two operands are the remaining face and the zero set of a gate
that misses the current apex. Each next apex is maximal in their intersection. -/
inductive PullingFace (zeroes : κ → Finset (Fin n)) :
    Finset (Fin n) → Fin n → List (Fin n) → List κ → Prop
  | singleton {face apex} (mem : apex ∈ face) (maximal : ∀ v ∈ face, v ≤ apex) :
      PullingFace zeroes face apex [] []
  | cone {face apex next tail g gs}
      (mem : apex ∈ face) (maximal : ∀ v ∈ face, v ≤ apex) (positive : apex ∉ zeroes g)
      (rest : PullingFace zeroes (face ∩ zeroes g) next tail gs) :
      PullingFace zeroes face apex (next :: tail) (g :: gs)

theorem PullingFace.vertices_mem {zeroes : κ → Finset (Fin n)}
    {face : Finset (Fin n)} {apex : Fin n} {tail : List (Fin n)} {gs : List κ}
    (h : PullingFace zeroes face apex tail gs) :
    ∀ v ∈ apex :: tail, v ∈ face := by
  induction h with
  | singleton hm _ => simpa using hm
  | cone hm _ _ _ ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | ht
    · exact hm
    · exact Finset.mem_inter.mp (ih _ ht) |>.1

private def height (b : ℚ) (v : Fin n) : ℚ := -(b ^ v.val)

private def constantPlane (a : ℚ) : LiftingPlane := ⟨a, fun _ => 0⟩

private def extendPlane (p g : LiftingPlane) (anchor : Fin 8 → ℚ) (value : ℚ) :
    LiftingPlane :=
  let scale := (value - p.evalQ anchor) / g.evalQ anchor
  ⟨p.offset + scale * g.offset, fun j => p.coeff j + scale * g.coeff j⟩

private theorem extendPlane_evalQ (p g : LiftingPlane) (anchor x : Fin 8 → ℚ) (value : ℚ) :
    (extendPlane p g anchor value).evalQ x =
      p.evalQ x + (value - p.evalQ anchor) * (g.evalQ x / g.evalQ anchor) := by
  simp only [extendPlane, LiftingPlane.evalQ, add_mul, Finset.sum_add_distrib, mul_assoc,
    ← Finset.mul_sum]
  ring

private theorem extendPlane_anchor (p g : LiftingPlane) (anchor : Fin 8 → ℚ)
    (value : ℚ) (hne : g.evalQ anchor ≠ 0) :
    (extendPlane p g anchor value).evalQ anchor = value := by
  rw [extendPlane_evalQ, div_self hne, mul_one]
  ring

private theorem eventually_mul_pow_lt (c r : ℚ) (hr : 0 < r) {m k : ℕ} (hm : m < k) :
    ∀ᶠ b : ℚ in atTop, c * b ^ m < r * b ^ k := by
  filter_upwards [eventually_ge_atTop (1 : ℚ), eventually_gt_atTop (c / r)] with b hb hbig
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have hcb : c < r * b := by
    simpa only [mul_comm] using (div_lt_iff₀ hr).mp hbig
  have hpow : b ^ (m + 1) ≤ b ^ k := pow_le_pow_right₀ hb (Nat.succ_le_of_lt hm)
  calc
    c * b ^ m < (r * b) * b ^ m := mul_lt_mul_of_pos_right hcb (pow_pos hbpos _)
    _ = r * b ^ (m + 1) := by rw [pow_succ', mul_assoc]
    _ ≤ r * b ^ k := mul_le_mul_of_nonneg_left hpow hr.le

private theorem abs_extendPlane_bound (p g : LiftingPlane) (anchor x : Fin 8 → ℚ)
    {base lead A B : ℚ} (hA : |p.evalQ x| ≤ A * base)
    (hB : |p.evalQ anchor| ≤ B * base) (hl : |lead| = base) :
    |(extendPlane p g anchor lead).evalQ x| ≤
      (A + (1+B)*|g.evalQ x / g.evalQ anchor|) * base := by
  rw [extendPlane_evalQ]
  calc
    |p.evalQ x + (lead - p.evalQ anchor) * (g.evalQ x / g.evalQ anchor)| ≤
      |p.evalQ x| + |lead - p.evalQ anchor| * |g.evalQ x / g.evalQ anchor| := by
        simpa only [abs_mul] using
          abs_add_le (p.evalQ x) ((lead - p.evalQ anchor) * (g.evalQ x / g.evalQ anchor))
    _ ≤ A * base + (base + B * base) * |g.evalQ x / g.evalQ anchor| := by
      refine add_le_add hA (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
      have hsub : |lead - p.evalQ anchor| ≤ |lead| + |p.evalQ anchor| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le lead (-p.evalQ anchor)
      rw [hl] at hsub
      exact hsub.trans (add_le_add_right hB _)
    _ = _ := by ring

private structure LiftData (points : Fin n → Fin 8 → ℚ)
    (face : Finset (Fin n)) (apex : Fin n) (tail : List (Fin n))
    (p : ℚ → LiftingPlane) : Prop where
  own : ∀ b, ∀ v ∈ apex :: tail, (p b).evalQ (points v) = height b v
  below : ∀ v ∈ face, v ∉ apex :: tail →
    ∀ᶠ b : ℚ in atTop, (p b).evalQ (points v) < height b v
  bound : ∀ x, ∃ A : ℚ, 0 ≤ A ∧
    ∀ b : ℚ, 1 ≤ b → |(p b).evalQ x| ≤ A * b ^ apex.val

private theorem pulling_liftData (points : Fin n → Fin 8 → ℚ)
    (gates : κ → LiftingPlane) (zeroes : κ → Finset (Fin n))
    (hzero : ∀ g v, v ∈ zeroes g ↔ (gates g).evalQ (points v) = 0)
    (hnonneg : ∀ g v, 0 ≤ (gates g).evalQ (points v))
    {face : Finset (Fin n)} {apex : Fin n} {tail : List (Fin n)} {gs : List κ}
    (h : PullingFace zeroes face apex tail gs) :
    ∃ p, LiftData points face apex tail p := by
  induction h with
  | @singleton face apex hmem hmax =>
    refine ⟨fun b => constantPlane (height b apex), ?_, ?_, ?_⟩
    · intro b v hv
      have he : v = apex := by simpa only [List.mem_singleton] using hv
      subst v
      simp [constantPlane, LiftingPlane.evalQ]
    · intro v hv hvout
      have hlt : v < apex := lt_of_le_of_ne (hmax v hv) (by simpa using hvout)
      filter_upwards [eventually_mul_pow_lt 1 1 (by norm_num) hlt] with b hb
      simpa [constantPlane, LiftingPlane.evalQ, height] using hb
    · intro x
      refine ⟨1, by norm_num, ?_⟩
      intro b hb
      have hn : 0 ≤ b := zero_le_one.trans hb
      simp [constantPlane, LiftingPlane.evalQ, height, abs_of_nonneg (pow_nonneg hn _)]
  | @cone face apex next tail g gs hmem hmax hpos hrest ih =>
    obtain ⟨p, hp⟩ := ih
    have hgA : 0 < (gates g).evalQ (points apex) :=
      lt_of_le_of_ne (hnonneg g apex) (fun h => hpos ((hzero g apex).mpr h.symm))
    have hnextmem := Finset.mem_inter.mp (hrest.vertices_mem next List.mem_cons_self)
    have hnext : next < apex := lt_of_le_of_ne (hmax next hnextmem.1)
      (fun h => hpos (h ▸ hnextmem.2))
    let lifted : ℚ → LiftingPlane :=
      fun b => extendPlane (p b) (gates g) (points apex) (height b apex)
    refine ⟨lifted, ?_, ?_, ?_⟩
    · intro b v hv
      rcases List.mem_cons.mp hv with rfl | hvt
      · exact extendPlane_anchor _ _ _ _ hgA.ne'
      · have hz : (gates g).evalQ (points v) = 0 :=
          (hzero g v).mp (Finset.mem_inter.mp (hrest.vertices_mem v hvt)).2
        change (extendPlane _ _ _ _).evalQ _ = _
        rw [extendPlane_evalQ, hz, zero_div, mul_zero, add_zero]
        exact hp.own b v hvt
    · intro v hv hvout
      by_cases hgv : (gates g).evalQ (points v) = 0
      · have hvf : v ∈ face ∩ zeroes g :=
          Finset.mem_inter.mpr ⟨hv, (hzero g v).mpr hgv⟩
        have hvout' : v ∉ next :: tail := fun hh => hvout (List.mem_cons_of_mem _ hh)
        filter_upwards [hp.below v hvf hvout'] with b hb
        change (extendPlane _ _ _ _).evalQ _ < _
        rw [extendPlane_evalQ, hgv, zero_div, mul_zero, add_zero]
        exact hb
      · have hlt : v < apex := lt_of_le_of_ne (hmax v hv) (fun hh => hvout (hh ▸ List.mem_cons_self))
        have hpA : 0 < (gates g).evalQ (points v) :=
          lt_of_le_of_ne (hnonneg g v) (fun hh => hgv hh.symm)
        let r := (gates g).evalQ (points v) / (gates g).evalQ (points apex)
        have hr : 0 < r := div_pos hpA hgA
        obtain ⟨A, hAn, hA⟩ := hp.bound (points v)
        obtain ⟨B, hBn, hB⟩ := hp.bound (points apex)
        let m := max next.val v.val
        have hm : m < apex.val := max_lt hnext hlt
        filter_upwards [eventually_ge_atTop (1 : ℚ),
          eventually_mul_pow_lt (A+B*r+1) r hr hm] with b hb hbig
        have hpn : b ^ next.val ≤ b ^ m := pow_le_pow_right₀ hb (le_max_left _ _)
        have hpv : b ^ v.val ≤ b ^ m := pow_le_pow_right₀ hb (le_max_right _ _)
        have hAx : (p b).evalQ (points v) ≤ A * b ^ m :=
          (le_abs_self _).trans ((hA b hb).trans (mul_le_mul_of_nonneg_left hpn hAn))
        have hBx : -(p b).evalQ (points apex) ≤ B * b ^ m :=
          (neg_le_abs _).trans ((hB b hb).trans (mul_le_mul_of_nonneg_left hpn hBn))
        have hBxr := mul_le_mul_of_nonneg_right hBx hr.le
        change (extendPlane _ _ _ _).evalQ _ < _
        rw [extendPlane_evalQ]
        change (p b).evalQ (points v) + (-(b^apex.val) - (p b).evalQ (points apex)) * r <
          -(b^v.val)
        linarith only [hAx, hBxr, hpv, hbig]
    · intro x
      obtain ⟨A, hAn, hA⟩ := hp.bound x
      obtain ⟨B, hBn, hB⟩ := hp.bound (points apex)
      refine ⟨A + (1+B)*|(gates g).evalQ x / (gates g).evalQ (points apex)|, by positivity, ?_⟩
      intro b hb
      have hb0 : 0 ≤ b := zero_le_one.trans hb
      have hpow : b ^ next.val ≤ b ^ apex.val := pow_le_pow_right₀ hb hnext.le
      exact abs_extendPlane_bound _ _ _ _
        ((hA b hb).trans (mul_le_mul_of_nonneg_left hpow hAn))
        ((hB b hb).trans (mul_le_mul_of_nonneg_left hpow hBn))
        (by simp [height, abs_of_nonneg (pow_nonneg hb0 _)])

/-- Interpret the finite set of vertices represented by a natural-number bitmask. -/
def maskVertices (n : ℕ) (mask : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => mask.testBit v.val

@[simp] theorem mem_maskVertices {mask : ℕ} {v : Fin n} :
    v ∈ maskVertices n mask ↔ mask.testBit v.val = true := by
  simp [maskVertices]

theorem maskVertices_full (n : ℕ) : maskVertices n (2^n - 1) = Finset.univ := by
  ext v
  simp [v.isLt]

theorem maskVertices_inter (n a b : ℕ) :
    maskVertices n (a &&& b) = maskVertices n a ∩ maskVertices n b := by
  ext v
  simp

/-- Test membership and maximality in a face with two bit operations. -/
def maskMax (mask : ℕ) (apex : Fin n) : Bool :=
  mask.testBit apex.val && decide (mask >>> (apex.val + 1) = 0)

theorem maskMax_sound {mask : ℕ} {apex : Fin n} (h : maskMax mask apex = true) :
    apex ∈ maskVertices n mask ∧ ∀ v ∈ maskVertices n mask, v ≤ apex := by
  have ⟨ha, hshift⟩ : mask.testBit apex.val = true ∧ mask >>> (apex.val + 1) = 0 := by
    simpa only [maskMax, Bool.and_eq_true, decide_eq_true_eq] using h
  refine ⟨mem_maskVertices.mpr ha, ?_⟩
  intro v hv
  apply le_of_not_gt
  intro hvbig
  have hvval : apex.val < v.val := hvbig
  have ho : apex.val + 1 + (v.val - (apex.val + 1)) = v.val := by omega
  have he := congrArg (fun m : ℕ => m.testBit (v.val - (apex.val + 1))) hshift
  have hf : mask.testBit v.val = false := by
    simpa only [Nat.testBit_shiftRight, ho, Nat.zero_testBit] using he
  exact Bool.false_ne_true (hf.symm.trans (mem_maskVertices.mp hv))

/-- Validate one pulling flag using only cached zero masks and vertex ordinals. -/
def pullingCheck (zeroMask : κ → ℕ) :
    ℕ → Fin n → List (Fin n) → List κ → Bool :=
  fun face apex tail flags =>
    (List.rec (motive := fun _ => ℕ → Fin n → List κ → Bool)
      (fun current top remaining =>
        match remaining with
        | [] => maskMax current top
        | _ :: _ => false)
      (fun next _ checkTail current top remaining =>
        match remaining with
        | g :: gs => maskMax current top && !(zeroMask g).testBit top.val &&
            checkTail (current &&& zeroMask g) next gs
        | [] => false)
      tail) face apex flags

theorem pullingCheck_sound (zeroMask : κ → ℕ) {face : ℕ} {apex : Fin n}
    {tail : List (Fin n)} {gs : List κ}
    (h : pullingCheck zeroMask face apex tail gs = true) :
    PullingFace (fun g => maskVertices n (zeroMask g)) (maskVertices n face) apex tail gs := by
  induction tail generalizing face apex gs with
  | nil =>
    cases gs with
    | nil =>
      have ⟨hm, hmax⟩ := maskMax_sound h
      exact .singleton hm hmax
    | cons g gs =>
      simp [pullingCheck] at h
  | cons next tail ih =>
    cases gs with
    | nil =>
      simp [pullingCheck] at h
    | cons g gs =>
      have ⟨⟨hmax, hnot⟩, hrest⟩ :
          (maskMax face apex = true ∧ (!(zeroMask g).testBit apex.val) = true) ∧
          pullingCheck zeroMask (face &&& zeroMask g) next tail gs = true := by
        simpa only [pullingCheck, Bool.and_eq_true] using h
      have ⟨hm, hmax⟩ := maskMax_sound hmax
      refine .cone hm hmax (by simp only [mem_maskVertices]; simpa using hnot) ?_
      simpa only [maskVertices_inter] using ih hrest

def rowTail (ids : Fin 9 → Fin n) : List (Fin n) :=
  List.ofFn fun k : Fin 8 => ids k.succ

theorem mem_row_vertices (ids : Fin 9 → Fin n) (v : Fin n) :
    v ∈ ids 0 :: rowTail ids ↔ v ∈ vertexSet ids := by
  change v ∈ ids 0 :: List.ofFn (fun k : Fin 8 => ids k.succ) ↔ _
  rw [← List.ofFn_succ]
  simp only [List.mem_ofFn, mem_vertexSet]

/-- All finite checked pulling flags admit simultaneous supporting planes at a common lift. -/
theorem pulling_supporting_planes {ι : Type*} [Finite ι]
    (points : Fin n → Fin 8 → ℚ) (gates : κ → LiftingPlane) (zeroMask : κ → ℕ)
    (ids : ι → Fin 9 → Fin n) (flags : ι → List κ)
    (hzero : ∀ g v, (zeroMask g).testBit v.val = true ↔ (gates g).evalQ (points v) = 0)
    (hnonneg : ∀ g v, 0 ≤ (gates g).evalQ (points v))
    (hcheck : ∀ i, pullingCheck zeroMask (2^n-1) (ids i 0) (rowTail (ids i)) (flags i) = true) :
    ∃ (height : Fin n → ℚ) (planes : ι → LiftingPlane),
      (∀ i k, (planes i).evalQ (points (ids i k)) = height (ids i k)) ∧
      (∀ i v, v ∉ vertexSet (ids i) → (planes i).evalQ (points v) < height v) := by
  classical
  have hp (i : ι) : ∃ p, LiftData points Finset.univ (ids i 0) (rowTail (ids i)) p := by
    have hface := pullingCheck_sound zeroMask (hcheck i)
    rw [maskVertices_full] at hface
    exact pulling_liftData points gates _ (fun g v => mem_maskVertices.trans (hzero g v))
      hnonneg hface
  choose p hp using hp
  have hB : ∀ᶠ b : ℚ in atTop, ∀ (i : ι) (v : Fin n),
      v ∉ vertexSet (ids i) → (p i b).evalQ (points v) < height b v := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro v
    by_cases hv : v ∈ vertexSet (ids i)
    · exact Eventually.of_forall (fun _ h => (h hv).elim)
    · have hout : v ∉ ids i 0 :: rowTail (ids i) :=
        fun he => hv ((mem_row_vertices (ids i) v).mp he)
      filter_upwards [(hp i).below v (Finset.mem_univ v) hout] with b hb
      exact fun _ => hb
  obtain ⟨b, hb⟩ := hB.exists
  refine ⟨height b, fun i => p i b, ?_, hb⟩
  intro i k
  apply (hp i).own
  exact (mem_row_vertices (ids i) _).mpr (mem_vertexSet.mpr ⟨k, rfl⟩)

theorem checked_pulling_overlap_null {ι : Type*} [Finite ι]
    (points : Fin n → Fin 8 → ℚ) (gates : κ → LiftingPlane) (zeroMask : κ → ℕ)
    (ids : ι → Fin 9 → Fin n) (flags : ι → List κ)
    (hzero : ∀ g v, (zeroMask g).testBit v.val = true ↔ (gates g).evalQ (points v) = 0)
    (hnonneg : ∀ g v, 0 ≤ (gates g).evalQ (points v))
    (hcheck : ∀ i, pullingCheck zeroMask (2^n-1) (ids i 0) (rowTail (ids i)) (flags i) = true)
    (distinct : Function.Injective (fun i => vertexSet (ids i))) :
    Pairwise fun i j => volume (cellSupport points ids i ∩ cellSupport points ids j) = 0 := by
  obtain ⟨height, planes, own, below⟩ :=
    pulling_supporting_planes points gates zeroMask ids flags hzero hnonneg hcheck
  exact cell_overlap_null points ids height planes own below distinct

/-- One canonical key for a geometric vertex set of a cell. -/
def vertexKey (ids : Fin 9 → Fin n) : ℕ :=
  ∑ v ∈ vertexSet ids, 2 ^ v.val

end Pulling

end ImbalancedChen.P2Winner9LiftingGeometry
