import ImbalancedChen.P2OriginalAffineProfilePassage

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The exact 200 open-cell/201 knot atom dictionary. A knot is encoded by
two opposite weak affine gates, whose strict interior is empty. Its
finite arithmetic contribution is nevertheless present in every sum.
-/
namespace ImbalancedChen.P2OriginalClosedCellProfileAtoms

noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology
open P2OriginalBankChildPrimeMass P2OriginalHalfOpenProfileCarrier
open P2OriginalAffineProfilePassage
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables

def finiteGates {d : ℕ} {κ : Type*} [Fintype κ]
    (A : κ → Coord d →L[ℝ] ℝ) (c : κ → ℝ) : Set (Coord d) := {x | ∀ i, A i x < c i}

def finiteClosedGates {d : ℕ} {κ : Type*} [Fintype κ]
    (A : κ → Coord d →L[ℝ] ℝ) (c : κ → ℝ) : Set (Coord d) := {x | ∀ i, A i x ≤ c i}

def enumForms {d : ℕ} {κ : Type*} [Fintype κ] (A : κ → Coord d →L[ℝ] ℝ) :
    Fin (Fintype.card κ) → Coord d →L[ℝ] ℝ := fun i => A ((Fintype.equivFin κ).symm i)
def enumBounds {κ : Type*} [Fintype κ] (c : κ → ℝ) : Fin (Fintype.card κ) → ℝ :=
  fun i => c ((Fintype.equivFin κ).symm i)

theorem finiteGates_enum {d : ℕ} {κ : Type*} [Fintype κ]
    (A : κ → Coord d →L[ℝ] ℝ) (c : κ → ℝ) :
    finiteGates A c = primeAffineGateRegion (enumForms A) (enumBounds c) := by
  ext x
  constructor
  · exact fun hx i => hx _
  · intro hx i
    simpa only [enumForms,enumBounds,Equiv.symm_apply_apply] using hx (Fintype.equivFin κ i)

theorem finiteClosedGates_enum {d : ℕ} {κ : Type*} [Fintype κ]
    (A : κ → Coord d →L[ℝ] ℝ) (c : κ → ℝ) :
    finiteClosedGates A c = closedGates (enumForms A) (enumBounds c) := by
  ext x
  constructor
  · exact fun hx i => hx _
  · intro hx i
    simpa only [enumForms,enumBounds,Equiv.symm_apply_apply] using hx (Fintype.equivFin κ i)

def controlForms (d : ℕ) : (Fin d × Bool) → Coord d →L[ℝ] ℝ :=
  fun q => if q.2 then coord q.1 else -coord q.1
def controlBounds {d : ℕ} : (Fin d × Bool) → ℝ :=
  fun q => if q.2 then 11/20 else -(3/20)
def control (d : ℕ) : Set (Coord d) := finiteGates (controlForms d) controlBounds

theorem control_membership {d : ℕ} (x : Coord d) :
    x ∈ control d ↔ ∀ i, (3/20:ℝ) < x i ∧ x i < 11/20 := by
  constructor
  · intro hx i
    have hl := hx (i,false)
    have hh := hx (i,true)
    simp only [controlForms,controlBounds,if_false,if_true,
      ContinuousLinearMap.neg_apply,coord,ContinuousLinearMap.proj_apply] at hl hh
    exact ⟨by linarith,hh⟩
  · intro hx q
    rcases q with ⟨i,b⟩
    cases b <;> simp only [controlForms,controlBounds,if_false,if_true,
      ContinuousLinearMap.neg_apply,coord,ContinuousLinearMap.proj_apply] <;>
      linarith [(hx i).1,(hx i).2]

theorem control_nonzero {d : ℕ} (q : Fin d × Bool) : controlForms d q ≠ 0 := by
  intro h
  have hh := congrArg (fun F : Coord d →L[ℝ] ℝ => F (fun _ => 1)) h
  rcases q with ⟨i,b⟩
  cases b <;> norm_num [controlForms,coord] at hh

theorem control_in_cube (d : ℕ) : control d ⊆ cube d := by
  intro x hx
  apply mem_logPrimeBox.mpr
  intro i
  have hi := (control_membership x).mp hx i
  constructor <;> linarith

theorem control_contains_box {d : ℕ} {x : Coord d}
    (hx : ∀ i, (1/5:ℝ) ≤ x i ∧ x i ≤ 1/2) : x ∈ control d := by
  apply (control_membership x).mpr
  intro i
  constructor <;> linarith [(hx i).1,(hx i).2]

def atomLowerGrid : FloorAtom → ℝ
  | .inl i => floorGrid i.val
  | .inr j => floorGrid j.val
def atomUpperGrid : FloorAtom → ℝ
  | .inl i => floorGrid (i.val+1)
  | .inr j => floorGrid j.val
def supportLower (lower : Bool) : ℝ := if lower then 2 else 1

def profileForms {d : ℕ} (F G : Coord d →L[ℝ] ℝ) (lower : Bool)
    (b : FloorAtom) : Fin 4 → Coord d →L[ℝ] ℝ :=
  ![F + supportLower lower • G, -(F + (5:ℝ) • G),
    F + atomLowerGrid b • G, -(F + atomUpperGrid b • G)]
def profileBounds (B g : ℝ) (lower : Bool) (b : FloorAtom) : Fin 4 → ℝ :=
  ![B-supportLower lower*g, -(B-5*g), B-atomLowerGrid b*g, -(B-atomUpperGrid b*g)]

theorem quotient_lower_lt {d : ℕ} (F G : Coord d →L[ℝ] ℝ) (B g t : ℝ)
    {x : Coord d} (hd : 0 < g+G x) :
    (F+t • G) x < B-t*g ↔ t < (B-F x)/(g+G x) := by
  rw [lt_div_iff₀ hd]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  nlinarith

theorem quotient_lower_le {d : ℕ} (F G : Coord d →L[ℝ] ℝ) (B g t : ℝ)
    {x : Coord d} (hd : 0 < g+G x) :
    (F+t • G) x ≤ B-t*g ↔ t ≤ (B-F x)/(g+G x) := by
  rw [le_div_iff₀ hd]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  nlinarith

theorem quotient_upper_lt {d : ℕ} (F G : Coord d →L[ℝ] ℝ) (B g t : ℝ)
    {x : Coord d} (hd : 0 < g+G x) :
    (-(F+t • G)) x < -(B-t*g) ↔ (B-F x)/(g+G x) < t := by
  rw [div_lt_iff₀ hd]
  simp only [ContinuousLinearMap.neg_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  nlinarith

theorem quotient_upper_le {d : ℕ} (F G : Coord d →L[ℝ] ℝ) (B g t : ℝ)
    {x : Coord d} (hd : 0 < g+G x) :
    (-(F+t • G)) x ≤ -(B-t*g) ↔ (B-F x)/(g+G x) ≤ t := by
  rw [div_le_iff₀ hd]
  simp only [ContinuousLinearMap.neg_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  nlinarith

theorem table_atom_closed_bounds (lower : Bool) (b : FloorAtom) {s : ℝ}
    (hs : s ∈ tableAtomSet lower b) :
    supportLower lower ≤ s ∧ s ≤ 5 ∧ atomLowerGrid b ≤ s ∧ s ≤ atomUpperGrid b := by
  cases lower <;> cases b with
  | inl i => exact ⟨hs.1.1,hs.1.2,hs.2.1.le,hs.2.2.le⟩
  | inr j => exact ⟨hs.1.1,hs.1.2,hs.2.ge,hs.2.le⟩

theorem table_atom_of_open_bounds (lower : Bool) (b : FloorAtom) {s : ℝ}
    (hs0 : supportLower lower < s) (hs5 : s < 5)
    (hlo : atomLowerGrid b < s) (hhi : s < atomUpperGrid b) :
    s ∈ tableAtomSet lower b := by
  cases lower <;> cases b with
  | inl i => exact ⟨⟨hs0.le,hs5.le⟩,hlo,hhi⟩
  | inr j => exact False.elim ((not_lt_of_ge hlo.le) hhi)

/-- Only the four affine comparisons are needed, also for the moving
rho=(1-u-v)/u. No max-two substitution is introduced. -/
theorem profile_atom_sandwich {d : ℕ} (F G : Coord d →L[ℝ] ℝ) (B g : ℝ)
    (lower : Bool) (b : FloorAtom) {x : Coord d} (hd : 0 < g+G x) :
    (x ∈ primeAffineGateRegion (profileForms F G lower b) (profileBounds B g lower b) →
      (B-F x)/(g+G x) ∈ tableAtomSet lower b) ∧
    ((B-F x)/(g+G x) ∈ tableAtomSet lower b →
      x ∈ closedGates (profileForms F G lower b) (profileBounds B g lower b)) := by
  constructor
  · intro hx
    have h0 : (F+supportLower lower • G) x < B-supportLower lower*g := hx 0
    have h1 : (-(F+(5:ℝ) • G)) x < -(B-5*g) := hx 1
    have h2 : (F+atomLowerGrid b • G) x < B-atomLowerGrid b*g := hx 2
    have h3 : (-(F+atomUpperGrid b • G)) x < -(B-atomUpperGrid b*g) := hx 3
    exact table_atom_of_open_bounds lower b
      ((quotient_lower_lt F G B g _ hd).mp h0)
      ((quotient_upper_lt F G B g _ hd).mp h1)
      ((quotient_lower_lt F G B g _ hd).mp h2)
      ((quotient_upper_lt F G B g _ hd).mp h3)
  · intro hx i
    obtain ⟨h0,h1,h2,h3⟩ := table_atom_closed_bounds lower b hx
    fin_cases i
    · exact (quotient_lower_le F G B g _ hd).mpr h0
    · exact (quotient_upper_le F G B g _ hd).mpr h1
    · exact (quotient_lower_le F G B g _ hd).mpr h2
    · exact (quotient_upper_le F G B g _ hd).mpr h3

def combinedForms {d r : ℕ} (A : Fin r → Coord d →L[ℝ] ℝ)
    (F G : Coord d →L[ℝ] ℝ) (lower : Bool) (b : FloorAtom) :
    (Fin r ⊕ Fin 4) → Coord d →L[ℝ] ℝ := Sum.elim A (profileForms F G lower b)
def combinedBounds {r : ℕ} (c : Fin r → ℝ) (B g : ℝ) (lower : Bool) (b : FloorAtom) :
    (Fin r ⊕ Fin 4) → ℝ := Sum.elim c (profileBounds B g lower b)

theorem combined_sandwich {d r : ℕ}
    (A : Fin r → Coord d →L[ℝ] ℝ) (c : Fin r → ℝ)
    {D : Set (Coord d)} (hD : AffineSandwich A c D)
    (F G : Coord d →L[ℝ] ℝ) (B g : ℝ) (rho : Coord d → ℝ)
    (hrho : ∀ x ∈ D, rho x = (B-F x)/(g+G x))
    (hden : ∀ x ∈ D, 0 < g+G x) (lower : Bool) (b : FloorAtom) :
    AffineSandwich (enumForms (combinedForms A F G lower b))
      (enumBounds (combinedBounds c B g lower b)) (D ∩ tablePullback lower rho b) := by
  unfold AffineSandwich
  rw [← finiteGates_enum,← finiteClosedGates_enum]
  constructor
  · intro x hx
    have hd : x ∈ D := hD.1 (fun i => hx (Sum.inl i))
    refine ⟨hd,?_⟩
    change rho x ∈ tableAtomSet lower b
    rw [hrho x hd]
    exact (profile_atom_sandwich F G B g lower b (hden x hd)).1
      (fun i => hx (Sum.inr i))
  · rintro x ⟨hd,hb⟩ i
    rcases i with i | i
    · exact hD.2 hd i
    · have hb' : (B-F x)/(g+G x) ∈ tableAtomSet lower b := by
        change rho x ∈ tableAtomSet lower b at hb
        simpa only [hrho x hd] using hb
      exact ((profile_atom_sandwich F G B g lower b (hden x hd)).2 hb') i

theorem combined_nonzero {d r : ℕ}
    (A : Fin r → Coord d →L[ℝ] ℝ) (hA : ∀ i, A i ≠ 0)
    (F G : Coord d →L[ℝ] ℝ) (hFG : ∀ t : ℝ, F+t • G ≠ 0)
    (lower : Bool) (b : FloorAtom) :
    ∀ i, enumForms (combinedForms A F G lower b) i ≠ 0 := by
  intro i
  change combinedForms A F G lower b ((Fintype.equivFin _).symm i) ≠ 0
  rcases (Fintype.equivFin (Fin r ⊕ Fin 4)).symm i with i | i
  · exact hA i
  · fin_cases i <;> simp only [combinedForms,Sum.elim_inr,profileForms,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] <;>
      first | exact hFG _ | exact neg_ne_zero.mpr (hFG _)

/-- The generic theorem is specialized to each ACTUAL arithmetic table
atom, with an implemented proper-wall supplier and original finite grid. -/
theorem compact_uniform_profile_atom {d r : ℕ} {Lmin Lmax C epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (hC : 0 ≤ C) (he : 0 < epsilon)
    (A : Fin r → Coord d →L[ℝ] ℝ) (c : Fin r → ℝ) (hA : ∀ i, A i ≠ 0)
    {D : Set (Coord d)} (hD : AffineSandwich A c D)
    (hbox : ∀ x ∈ D, ∀ i, (1/5:ℝ) ≤ x i ∧ x i ≤ 1/2)
    (F G : Coord d →L[ℝ] ℝ) (B g : ℝ) (rho : Coord d → ℝ)
    (hFG : ∀ t : ℝ, F+t • G ≠ 0)
    (hrho : ∀ x ∈ D, rho x = (B-F x)/(g+G x))
    (hden : ∀ x ∈ D, 0 < g+G x)
    (f : Coord d → ℝ) (hf : Continuous f) (hbound : ∀ x, |f x| ≤ C)
    (lower : Bool) (b : FloorAtom) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax,
      |scaledPrimeSum N L (D ∩ tablePullback lower rho b) f -
        (∫ x in D ∩ tablePullback lower rho b,f x * ∏ i,1/x i)| < epsilon := by
  apply compact_uniform_sandwich hmin hmax hC he
    (enumForms (combinedForms A F G lower b)) (enumBounds (combinedBounds c B g lower b))
    (combined_nonzero A hA F G hFG lower b)
    (enumForms (controlForms d)) (enumBounds controlBounds)
    (fun i => control_nonzero ((Fintype.equivFin _).symm i))
    (by rw [← finiteGates_enum]; exact control_in_cube d)
    (combined_sandwich A c hD F G B g rho hrho hden lower b)
    (fun x hx => by rw [← finiteGates_enum]; exact control_contains_box (hbox x hx.1))
    f hf hbound

end
end ImbalancedChen.P2OriginalClosedCellProfileAtoms
