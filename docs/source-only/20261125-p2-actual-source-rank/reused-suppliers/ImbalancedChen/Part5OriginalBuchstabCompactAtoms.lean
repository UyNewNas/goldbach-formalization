import ImbalancedChen.Part5OriginalCompactParameterSandwich
import ImbalancedChen.P2OriginalClosedCellProfileAtoms

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Two independent moving parameters are fixed only after the threshold:
physical residual L and the Buchstab start c. The 401 closed/open atoms
are literal table atoms. Their reciprocal pullbacks have six proper
fixed affine normals, including the opposed normals of a knot.
-/
namespace ImbalancedChen.Part5OriginalBuchstabCompactAtoms

noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology Pointwise
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalCompactMovingGateMass
open P2OriginalCompactScaledPrimeMass P2OriginalAffineProfilePassage
open P2OriginalClosedCellProfileAtoms
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables

/-- Reboxing an arbitrary supported selector, not just its strict interior. -/
theorem scaled_sum_rebox {d N : ℕ} (hN : 1 < N)
    {Lmin Lmax L : ℝ} (hmin : 0 < Lmin) (hL : L ∈ Icc Lmin Lmax)
    (D : Set (Coord d)) (hD : D ⊆ cube d) (f : Coord d → ℝ) :
    scaledPrimeSum N L D f =
      Part5OriginalCompactParameterSandwich.testSum N (Lmin/20) Lmax
        {x | L⁻¹ • x ∈ D} (fun x => f (L⁻¹ • x)) := by
  have hpos : 0 < L := hmin.trans_le hL.1
  unfold scaledPrimeSum Part5OriginalCompactParameterSandwich.testSum actualPrimeBoxTestSum
  have hind (x : Coord d) : D.indicator f (L⁻¹ • x) =
      ({y | L⁻¹ • y ∈ D} : Set (Coord d)).indicator (fun y => f (L⁻¹ • y)) x := by
    by_cases hx : L⁻¹ • x ∈ D <;> simp only [Set.indicator, mem_setOf_eq, hx, ↓reduceIte]
  simp_rw [hind]
  apply Finset.sum_subset (moving_box_subset_ambient hN hmin hL)
  intro p hp hnot
  have hx : L⁻¹ • actualPrimeTupleLog N p ∉ D := by
    intro hx
    have hc := hD hx
    apply hnot
    apply (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
    refine ⟨((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).1,
      mem_logPrimeBox.mpr ?_⟩
    intro i
    have hi := mem_logPrimeBox.mp hc i
    simp only [Pi.smul_apply, smul_eq_mul, ← div_eq_inv_mul] at hi
    have hl := (le_div_iff₀ hpos).mp hi.1
    have hh := (div_lt_iff₀ hpos).mp hi.2
    constructor <;> nlinarith
  simp only [mem_setOf_eq, indicator_of_notMem hx, mul_zero]

theorem scaled_integral_rebox {d : ℕ} {Lmin Lmax L : ℝ}
    (hmin : 0 < Lmin) (hL : L ∈ Icc Lmin Lmax)
    (D : Set (Coord d)) (hD : D ⊆ cube d) (f : Coord d → ℝ) :
    Part5OriginalCompactParameterSandwich.testIntegral (Lmin/20) Lmax
      {x | L⁻¹ • x ∈ D} (fun x => f (L⁻¹ • x)) =
      ∫ x in D, f x * ∏ i, 1/x i := by
  have hpos : 0 < L := hmin.trans_le hL.1
  have hset : logPrimeBox (fun _ : Fin d => Lmin/20) (fun _ => Lmax) ∩
      {x | L⁻¹ • x ∈ D} = L • D := by
    ext x
    rw [mem_smul_set_iff_inv_smul_mem₀ hpos.ne', mem_inter_iff, mem_setOf_eq]
    constructor
    · exact And.right
    · intro hx
      refine ⟨mem_logPrimeBox.mpr ?_, hx⟩
      intro i
      have hh := mem_logPrimeBox.mp (hD hx) i
      simp only [Pi.smul_apply, smul_eq_mul, ← div_eq_inv_mul] at hh
      have hlo := (le_div_iff₀ hpos).mp hh.1
      have hhi := (div_lt_iff₀ hpos).mp hh.2
      constructor <;> nlinarith only [hlo,hhi,hmin,hL.1,hL.2]
  unfold Part5OriginalCompactParameterSandwich.testIntegral
  rw [hset, integral_log_density_dilation hpos]

/-- Exact positive dilation of an affine sandwich. -/
theorem scaled_sandwich {d r : ℕ} {L : ℝ} (hL : 0 < L)
    (A : Fin r → Coord d →L[ℝ] ℝ) (c : Fin r → ℝ)
    {D : Set (Coord d)} (hD : AffineSandwich A c D) :
    AffineSandwich A (fun j => L*c j) {x | L⁻¹ • x ∈ D} := by
  constructor
  · intro x hx
    exact hD.1 ((affine_dilation_mem hL A c x).mp hx)
  · intro x hx j
    have hh := hD.2 hx j
    rw [map_smul, smul_eq_mul, ← div_eq_inv_mul, div_le_iff₀ hL] at hh
    simpa only [mul_comm] using hh

/-- A compact parameter family of normalized selectors, uniformly in L.
The target integer remains N throughout; N^L is not an integer target. -/
theorem compact_uniform_scaled_sandwich {P : Type*} [MetricSpace P]
    {d r : ℕ} {K : Set P} (hK : IsCompact K)
    {Lmin Lmax B epsilon : ℝ} (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax)
    (hB : 0 ≤ B) (he : 0 < epsilon)
    (A : Fin r → Coord d →L[ℝ] ℝ) (hA : ∀ j, A j ≠ 0)
    (c : P → Fin r → ℝ) (hc : ∀ j, Continuous (fun q => c q j))
    (D : P → Set (Coord d)) (hD : ∀ q ∈ K, AffineSandwich A (c q) (D q))
    (hbox : ∀ q ∈ K, D q ⊆ cube d)
    (f : Coord d → ℝ) (hf : Continuous f) (hb : ∀ x, |f x| ≤ B) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax, ∀ q ∈ K,
      |scaledPrimeSum N L (D q) f - (∫ x in D q, f x * ∏ i, 1/x i)| < epsilon := by
  let E (z : ℝ × P) : Set (Coord d) := {x | z.1⁻¹ • x ∈ D z.2}
  let C (z : ℝ × P) (j : Fin r) : ℝ := z.1*c z.2 j
  let F (z : (ℝ × P) × Coord d) : ℝ :=
    f ((max (Lmin/2) z.1.1)⁻¹ • z.2)
  have hC (j : Fin r) : Continuous (fun z : ℝ × P => C z j) :=
    continuous_fst.mul ((hc j).comp continuous_snd)
  have hF : Continuous F := by
    apply hf.comp
    apply Continuous.smul
    · apply (continuous_const.max (continuous_fst.comp continuous_fst)).inv₀
      intro z
      exact (lt_of_lt_of_le (by positivity : (0:ℝ) < Lmin/2) (le_max_left _ _)).ne'
    · exact continuous_snd
  obtain ⟨T,hT⟩ := Part5OriginalCompactParameterSandwich.compact_uniform_sandwich
    (isCompact_Icc.prod hK) (a := Lmin/20) (b := Lmax)
    (by positivity) (by linarith) hB A hA C hC E
    (fun z hz => scaled_sandwich (hmin.trans_le hz.1.1) A (c z.2) (hD z.2 hz.2))
    F hF (fun z hz x hx => hb _) he
  refine ⟨max 2 T, ?_⟩
  intro N hN L hL q hq
  have hh := hT N (by omega) (L,q) ⟨hL,hq⟩
  have hFq : (fun x => F ((L,q),x)) = (fun x => f (L⁻¹ • x)) := by
    funext x
    simp only [F, max_eq_right (show Lmin/2 ≤ L by linarith [hL.1])]
  rw [hFq] at hh
  change |Part5OriginalCompactParameterSandwich.testSum N (Lmin/20) Lmax
      {x | L⁻¹ • x ∈ D q} (fun x => f (L⁻¹ • x)) -
    Part5OriginalCompactParameterSandwich.testIntegral (Lmin/20) Lmax
      {x | L⁻¹ • x ∈ D q} (fun x => f (L⁻¹ • x))| < epsilon at hh
  rw [← scaled_sum_rebox (by omega : 1 < N) hmin hL (D q) (hbox q hq) f,
    scaled_integral_rebox hmin hL (D q) (hbox q hq) f] at hh
  exact hh

/-- Globally continuous extension, equal to 1/(c+1) for c >= 1. -/
def reciprocalTop (c : ℝ) : ℝ := 1/(max 1 c+1)
def query (x : Coord 1) : ℝ := 1/x 0-1
def baseDomain (c : ℝ) : Set (Coord 1) :=
  {x | (1/6:ℝ) ≤ x 0 ∧ x 0 ≤ reciprocalTop c}
def atomDomain (up : Bool) (b : FloorAtom) (c : ℝ) : Set (Coord 1) :=
  baseDomain c ∩ tablePullback up query b

def atomForms (up : Bool) (b : FloorAtom) :=
  enumForms (combinedForms singleForms (coord 0) (coord 0) up b)
def atomBounds (up : Bool) (b : FloorAtom) (c : ℝ) :=
  enumBounds (combinedBounds (singleBounds (1/6) (reciprocalTop c)) 1 0 up b)

theorem reciprocalTop_continuous : Continuous reciprocalTop := by
  apply continuous_const.div
    ((continuous_const.max continuous_id).add continuous_const)
  intro c
  have h : (1:ℝ) ≤ max 1 c := le_max_left _ _
  linarith

theorem reciprocalTop_bounds (c : ℝ) :
    0 < reciprocalTop c ∧ reciprocalTop c ≤ (1/2:ℝ) := by
  have h : (1:ℝ) ≤ max 1 c := le_max_left _ _
  refine ⟨one_div_pos.mpr (by linarith), ?_⟩
  exact one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) (by linarith)

theorem base_sandwich (c : ℝ) :
    AffineSandwich singleForms (singleBounds (1/6) (reciprocalTop c)) (baseDomain c) := by
  constructor
  · intro x hx
    have hh : (1/6:ℝ) < x 0 ∧ x 0 < reciprocalTop c := by
      simpa only [← single_as_affine, singleDomain, mem_setOf_eq] using hx
    exact ⟨hh.1.le,hh.2.le⟩
  · intro x hx j
    fin_cases j <;> simp only [singleForms,singleBounds,coord,
      Matrix.cons_val_zero,Matrix.cons_val_one,ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.proj_apply] <;> linarith [hx.1,hx.2]

theorem atom_sandwich (up : Bool) (b : FloorAtom) (c : ℝ) :
    AffineSandwich (atomForms up b) (atomBounds up b c) (atomDomain up b c) := by
  apply combined_sandwich singleForms _ (base_sandwich c) (coord 0) (coord 0) 1 0 query
  · intro x hx
    have hx0 : x 0 ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1)
    simp only [query,coord,ContinuousLinearMap.proj_apply,zero_add]
    field_simp [hx0] <;> ring
  · intro x hx
    simpa only [coord,ContinuousLinearMap.proj_apply,zero_add] using
      (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/6) hx.1)

/-- Only the finitely used grid coefficients need be nonzero. The false
stronger assertion coord+t*coord != 0 for every real t is NOT used. -/
theorem atomForms_nonzero (up : Bool) (b : FloorAtom) :
    ∀ j, atomForms up b j ≠ 0 := by
  have hgrid (n : ℕ) : 0 ≤ floorGrid n := by
    unfold floorGrid
    positivity
  have hlo : 0 ≤ atomLowerGrid b := by cases b <;> exact hgrid _
  have hhi : 0 ≤ atomUpperGrid b := by cases b <;> exact hgrid _
  have hs : 0 ≤ supportLower up := by cases up <;> norm_num [supportLower]
  have hform (t : ℝ) (ht : 0 ≤ t) : coord (d:=1) 0+t • coord 0 ≠ 0 := by
    intro he
    have hh := congrArg (fun F : Coord 1 →L[ℝ] ℝ => F (fun _ => 1)) he
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul,coord,ContinuousLinearMap.proj_apply,ContinuousLinearMap.zero_apply,
      mul_one] at hh
    linarith
  intro j
  change combinedForms singleForms (coord 0) (coord 0) up b
    ((Fintype.equivFin (Fin 2 ⊕ Fin 4)).symm j) ≠ 0
  rcases (Fintype.equivFin (Fin 2 ⊕ Fin 4)).symm j with i | i
  · exact singleForms_ne i
  · fin_cases i <;> simp only [combinedForms,Sum.elim_inr,profileForms,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
    · exact hform _ hs
    · exact neg_ne_zero.mpr (hform _ (by norm_num))
    · exact hform _ hlo
    · exact neg_ne_zero.mpr (hform _ hhi)

theorem atomBounds_continuous (up : Bool) (b : FloorAtom) :
    ∀ j, Continuous (fun c => atomBounds up b c j) := by
  intro j
  change Continuous (fun c => combinedBounds
    (singleBounds (1/6) (reciprocalTop c)) 1 0 up b
      ((Fintype.equivFin (Fin 2 ⊕ Fin 4)).symm j))
  rcases (Fintype.equivFin (Fin 2 ⊕ Fin 4)).symm j with i | i
  · fin_cases i
    · exact continuous_const
    · exact reciprocalTop_continuous
  · exact continuous_const

theorem atom_in_cube (up : Bool) (b : FloorAtom) (c : ℝ) : atomDomain up b c ⊆ cube 1 := by
  intro x hx
  apply mem_logPrimeBox.mpr
  intro i
  have hhi := hx.1.2.trans (reciprocalTop_bounds c).2
  fin_cases i
  constructor <;> linarith [hx.1.1]

/-- The actual reciprocal query; both the support guards and closed knots
are in the domain, rather than inferred from a table value. -/
theorem atomDomain_query {up : Bool} {b : FloorAtom} {c : ℝ} (hc : 1 ≤ c)
    (x : Coord 1) :
    x ∈ atomDomain up b c ↔
      0 < x 0 ∧ query x ∈ Icc c 5 ∧ query x ∈ tableAtomSet up b := by
  have hc0 : 0 < c+1 := by linarith
  have ht : reciprocalTop c = 1/(c+1) := by simp [reciprocalTop,max_eq_right hc]
  constructor
  · rintro ⟨⟨hl,hh⟩,hb⟩
    have hx : 0 < x 0 := lt_of_lt_of_le (by norm_num) hl
    refine ⟨hx, ⟨?_,?_⟩, hb⟩
    · rw [ht,le_div_iff₀ hc0] at hh
      have hq : c+1 ≤ 1/x 0 := (le_div_iff₀ hx).mpr (by nlinarith)
      dsimp [query]; linarith
    · have hq : 1/x 0 ≤ 6 := (div_le_iff₀ hx).mpr (by nlinarith)
      dsimp [query]; linarith
  · rintro ⟨hx,⟨hlo,hhi⟩,hb⟩
    refine ⟨⟨?_,?_⟩,hb⟩
    · have hq : 1/x 0 ≤ 6 := by dsimp [query] at hhi; linarith
      have hh := (div_le_iff₀ hx).mp hq
      nlinarith
    · rw [ht,le_div_iff₀ hc0]
      have hq : c+1 ≤ 1/x 0 := by dsimp [query] at hlo; linarith
      have hh := (le_div_iff₀ hx).mp hq
      nlinarith

def normalizedAtomIntegral (up : Bool) (b : FloorAtom) (c : ℝ) : ℝ :=
  ∫ x in atomDomain up b c, residualSingle x * ∏ i, 1/x i

/-- Full closed/knot atom estimate, uniformly before BOTH L and c. -/
theorem compact_uniform_buchstab_atoms {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax,
      ∀ c ∈ Icc (1:ℝ) 6, ∀ up : Bool, ∀ b : FloorAtom,
      |scaledPrimeSum N L (atomDomain up b c) residualSingle -
        normalizedAtomIntegral up b c| < epsilon := by
  have hfixed (q : Bool × FloorAtom) : ∀ᶠ N : ℕ in atTop,
      ∀ L ∈ Icc Lmin Lmax, ∀ c ∈ Icc (1:ℝ) 6,
      |scaledPrimeSum N L (atomDomain q.1 q.2 c) residualSingle -
        normalizedAtomIntegral q.1 q.2 c| < epsilon := by
    obtain ⟨T,hT⟩ := compact_uniform_scaled_sandwich isCompact_Icc hmin hmax
      (by norm_num : (0:ℝ) ≤ 10) he
      (atomForms q.1 q.2) (atomForms_nonzero q.1 q.2)
      (atomBounds q.1 q.2) (atomBounds_continuous q.1 q.2)
      (atomDomain q.1 q.2) (fun c hc => atom_sandwich q.1 q.2 c)
      (fun c hc => atom_in_cube q.1 q.2 c)
      residualSingle residualSingle_continuous (fun x => by
        rw [abs_of_nonneg (residualSingle_bounds x).1]
        exact (residualSingle_bounds x).2)
    exact (eventually_ge_atTop T).mono (fun N hN => hT N hN)
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_all.mpr hfixed)
  exact ⟨T, fun N hN L hL c hc up b => hT N hN (up,b) L hL c hc⟩

end
end ImbalancedChen.Part5OriginalBuchstabCompactAtoms
