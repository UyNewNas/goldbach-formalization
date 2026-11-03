import ImbalancedChen.Part5OriginalH430BuchstabMaskedIntervals
import ImbalancedChen.Part5OriginalH430NativeBuchstabMeasure

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Every actual closed table atom, including all 201 knots, is bracketed by
an open and a closed interval in u = 1/(w+1). The moving physical ceiling
is retained in start. Empty and over-ceiling rows are included. Endpoint
primes are paid by the preceding arithmetic theorem; only in the REAL
integral are finite endpoints removed by a proved AE equality.
-/

namespace ImbalancedChen.Part5OriginalH430BuchstabAtomIntervalGeometry

noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open Part5OriginalH430PhysicalMassPerturbation
open Part5OriginalH430BuchstabPhysicalBudget
open Part5OriginalH430NativeBuchstabMeasure
open Part5OriginalH430BuchstabInteriorPrimeLimit
open Part5OriginalH430BuchstabMaskedIntervals

/-- This reciprocal coordinate does not change the original integer target. -/
def inversePoint (w : ℝ) : ℝ := 1/(w+1)
def reciprocalQuery (u : ℝ) : ℝ := 1/u-1
def atomGuard (lower : Bool) : ℝ := if lower then 2 else 1

def relativeAtomDomain (lower : Bool) (start : ℝ) (b : FloorAtom) : Set ℝ :=
  {u | 0 < u ∧ reciprocalQuery u ∈ Icc start 5 ∩ tableAtomSet lower b}

def lowerEndpoint (_lower : Bool) (_start : ℝ) : FloorAtom → ℝ
  | .inl i => inversePoint (floorGrid (i.val+1))
  | .inr j => inversePoint (floorGrid j.val)

def upperEndpoint (lower : Bool) (start : ℝ) : FloorAtom → ℝ
  | .inl i => inversePoint (min 5 (max start (max (atomGuard lower) (floorGrid i.val))))
  | .inr j => inversePoint (floorGrid j.val)

theorem atomGuard_bounds (lower : Bool) : 1 ≤ atomGuard lower ∧ atomGuard lower ≤ 5 := by
  cases lower <;> norm_num [atomGuard]

theorem cell_atom_set (lower : Bool) (i : Fin 200) :
    tableAtomSet lower (.inl i) =
      Icc (atomGuard lower) 5 ∩ Ioo (floorGrid i.val) (floorGrid (i.val+1)) := by
  cases lower <;> rfl

theorem knot_atom_set (lower : Bool) (j : Fin 201) :
    tableAtomSet lower (.inr j) = Icc (atomGuard lower) 5 ∩ {floorGrid j.val} := by
  cases lower <;> rfl

theorem atom_subset_ambient (lower : Bool) (b : FloorAtom) :
    tableAtomSet lower b ⊆ Icc (1:ℝ) 5 := by
  cases b with
  | inl i =>
      rw [cell_atom_set]
      intro w hw
      exact ⟨(atomGuard_bounds lower).1.trans hw.1.1, hw.1.2⟩
  | inr j =>
      rw [knot_atom_set]
      intro w hw
      exact ⟨(atomGuard_bounds lower).1.trans hw.1.1, hw.1.2⟩

theorem inversePoint_bounds {w : ℝ} (hw : w ∈ Icc (1:ℝ) 5) :
    inversePoint w ∈ Icc (1/6:ℝ) (1/2) := by
  have hd : 0 < w+1 := by linarith [hw.1]
  constructor
  · apply (le_div_iff₀ hd).mpr
    linarith [hw.2]
  · apply (div_le_iff₀ hd).mpr
    linarith [hw.1]

theorem query_inversePoint {w : ℝ} (hw : 1 ≤ w) :
    reciprocalQuery (inversePoint w) = w := by
  unfold reciprocalQuery inversePoint
  field_simp [show w+1 ≠ 0 by linarith] <;> ring

theorem inversePoint_query {u : ℝ} (hu : 0 < u) :
    inversePoint (reciprocalQuery u) = u := by
  unfold reciprocalQuery inversePoint
  field_simp [hu.ne'] <;> ring

theorem query_lt_iff {u w : ℝ} (hu : 0 < u) (hw : 1 ≤ w) :
    reciprocalQuery u < w ↔ inversePoint w < u := by
  rw [reciprocalQuery, sub_lt_iff_lt_add, div_lt_iff₀ hu,
    inversePoint, div_lt_iff₀ (by linarith : 0 < w+1)]
  simp only [mul_comm]

theorem query_le_iff {u w : ℝ} (hu : 0 < u) (hw : 1 ≤ w) :
    reciprocalQuery u ≤ w ↔ inversePoint w ≤ u := by
  rw [reciprocalQuery, sub_le_iff_le_add, div_le_iff₀ hu,
    inversePoint, div_le_iff₀ (by linarith : 0 < w+1)]
  simp only [mul_comm]

theorem lt_query_iff {u w : ℝ} (hu : 0 < u) (hw : 1 ≤ w) :
    w < reciprocalQuery u ↔ u < inversePoint w := by
  rw [reciprocalQuery, lt_sub_iff_add_lt, lt_div_iff₀ hu,
    inversePoint, lt_div_iff₀ (by linarith : 0 < w+1)]
  simp only [mul_comm]

theorem le_query_iff {u w : ℝ} (hu : 0 < u) (hw : 1 ≤ w) :
    w ≤ reciprocalQuery u ↔ u ≤ inversePoint w := by
  rw [reciprocalQuery, le_sub_iff_add_le, le_div_iff₀ hu,
    inversePoint, le_div_iff₀ (by linarith : 0 < w+1)]
  simp only [mul_comm]

theorem endpoints_mem (lower : Bool) (start : ℝ) (b : FloorAtom) :
    lowerEndpoint lower start b ∈ Icc (1/6:ℝ) (1/2) ∧
      upperEndpoint lower start b ∈ Icc (1/6:ℝ) (1/2) := by
  cases b with
  | inl i =>
      refine ⟨inversePoint_bounds (Renewal.grid_bounds (by omega)), inversePoint_bounds ?_⟩
      exact ⟨le_min (by norm_num)
        ((atomGuard_bounds lower).1.trans ((le_max_left _ _).trans (le_max_right _ _))),
        min_le_left _ _⟩
  | inr j =>
      exact ⟨inversePoint_bounds (Renewal.grid_bounds (by omega)),
        inversePoint_bounds (Renewal.grid_bounds (by omega))⟩

/-- A knot is empty or a singleton; a cell is a mixed-endpoint interval.
Neither case assumes that an arithmetic endpoint fibre is empty. -/
theorem relativeAtomDomain_sandwich (lower : Bool) (start : ℝ) (b : FloorAtom) :
    Ioo (lowerEndpoint lower start b) (upperEndpoint lower start b) ⊆
      relativeAtomDomain lower start b ∧
    relativeAtomDomain lower start b ⊆
      Icc (lowerEndpoint lower start b) (upperEndpoint lower start b) := by
  cases b with
  | inl i =>
      let l := floorGrid i.val
      let r := floorGrid (i.val+1)
      let c := min 5 (max start (max (atomGuard lower) l))
      have hl : 1 ≤ l ∧ l ≤ 5 := Renewal.grid_bounds (by omega)
      have hr : 1 ≤ r ∧ r ≤ 5 := Renewal.grid_bounds (by omega)
      have hc : 1 ≤ c ∧ c ≤ 5 :=
        ⟨le_min (by norm_num)
          ((atomGuard_bounds lower).1.trans ((le_max_left _ _).trans (le_max_right _ _))),
          min_le_left _ _⟩
      change Ioo (inversePoint r) (inversePoint c) ⊆ relativeAtomDomain lower start (.inl i) ∧ _
      constructor
      · intro u hu
        have hu0 : 0 < u := (by linarith [(inversePoint_bounds hr).1] : 0 < inversePoint r).trans hu.1
        have hqr := (query_lt_iff hu0 hr.1).mpr hu.1
        have hcq := (lt_query_iff hu0 hc.1).mpr hu.2
        have hmax : max start (max (atomGuard lower) l) < reciprocalQuery u := by
          rcases (min_lt_iff.mp hcq) with h5 | hm
          · linarith [hr.2]
          · exact hm
        have hs := (lt_of_le_of_lt (le_max_left _ _) hmax)
        have hg := lt_of_le_of_lt (le_max_left _ _)
          (lt_of_le_of_lt (le_max_right _ _) hmax)
        have hlq := lt_of_le_of_lt (le_max_right _ _)
          (lt_of_le_of_lt (le_max_right _ _) hmax)
        refine ⟨hu0, ⟨hs.le, hqr.le.trans hr.2⟩, ?_⟩
        rw [cell_atom_set]
        exact ⟨⟨hg.le,hqr.le.trans hr.2⟩,hlq,hqr⟩
      · intro u hu
        rcases hu with ⟨hu0, hstart, hatom⟩
        rw [cell_atom_set] at hatom
        have hcq : c ≤ reciprocalQuery u :=
          (min_le_right _ _).trans
            (max_le hstart.1 (max_le hatom.1.1 hatom.2.1.le))
        exact ⟨((query_lt_iff hu0 hr.1).mp hatom.2.2).le,
          (le_query_iff hu0 hc.1).mp hcq⟩
  | inr j =>
      constructor
      · simp only [lowerEndpoint, upperEndpoint, Ioo_self, empty_subset]
      · intro u hu
        rcases hu with ⟨hu0,hstart,hatom⟩
        rw [knot_atom_set] at hatom
        have he : reciprocalQuery u = floorGrid j.val := hatom.2
        have hu' : u = inversePoint (floorGrid j.val) := by
          rw [← he]
          exact (inversePoint_query hu0).symm
        simpa only [lowerEndpoint,upperEndpoint,hu',mem_Icc,le_refl,true_and]

/-- In particular the FULL Buchstab atom stays inside [1/6,1/2]. -/
theorem relativeAtomDomain_bounds {lower : Bool} {start : ℝ} {b : FloorAtom} {u : ℝ}
    (hu : u ∈ relativeAtomDomain lower start b) : u ∈ Icc (1/6:ℝ) (1/2) := by
  have hs := (relativeAtomDomain_sandwich lower start b).2 hu
  have he := endpoints_mem lower start b
  exact ⟨he.1.1.trans hs.1, hs.2.trans he.2.2⟩

theorem relativeAtomDomain_measurable (lower : Bool) (start : ℝ) (b : FloorAtom) :
    MeasurableSet (relativeAtomDomain lower start b) :=
  measurableSet_Ioi.inter
    ((measurableSet_Icc.inter (measurableSet_tableAtomSet lower b)).preimage
      ((measurable_const.div measurable_id).sub measurable_const))

theorem relativeAtomDomain_eq_image (lower : Bool) (start : ℝ) (b : FloorAtom) :
    relativeAtomDomain lower start b =
      inversePoint '' (Icc start 5 ∩ tableAtomSet lower b) := by
  ext u
  constructor
  · rintro ⟨hu,hq⟩
    exact ⟨reciprocalQuery u,hq,inversePoint_query hu⟩
  · rintro ⟨w,hw,rfl⟩
    have ha := atom_subset_ambient lower b hw.2
    refine ⟨by exact div_pos zero_lt_one (by linarith [ha.1]), ?_⟩
    simpa only [query_inversePoint ha.1] using hw

theorem inversePoint_derivative {w : ℝ} (hw : 1 ≤ w) :
    HasDerivAt inversePoint (-(1/(w+1)^2)) w := by
  have hd := (hasDerivAt_const w (1:ℝ)).div ((hasDerivAt_id w).add_const 1)
    (by linarith : w+1 ≠ 0)
  convert hd using 1 <;> simp [inversePoint] <;> ring

theorem inversePoint_injOn : InjOn inversePoint (Icc (1:ℝ) 5) := by
  intro u hu v hv he
  have h := congrArg reciprocalQuery he
  simpa only [query_inversePoint hu.1,query_inversePoint hv.1] using h

theorem reciprocal_Jacobian {w : ℝ} (hw : w ∈ Icc (1:ℝ) 5) :
    |-(1/(w+1)^2)| * (1/(inversePoint w*(1-inversePoint w))) = 1/w := by
  have hw0 : w ≠ 0 := by linarith [hw.1]
  have hd : w+1 ≠ 0 := by linarith [hw.1]
  rw [abs_neg,abs_of_nonneg (div_nonneg zero_le_one (sq_nonneg _))]
  unfold inversePoint
  have he : 1-1/(w+1) = w/(w+1) := by field_simp [hd]; ring
  rw [he]
  field_simp [hw0,hd] <;> ring

/-- AE equality is used ONLY for real integration. The arithmetic
singleton error is established in BuchstabMaskedIntervals. -/
theorem sandwich_integral_eq {lo hi : ℝ} {D : Set ℝ} (hD : MeasurableSet D)
    (hinner : Ioo lo hi ⊆ D) (houter : D ⊆ Icc lo hi) :
    (∫ u in D, 1/(u*(1-u))) = intervalIntegral lo hi := by
  have hn (t : ℝ) : ∀ᵐ u : ℝ ∂volume, u ≠ t := by
    rw [ae_iff]
    simpa only [not_not] using (measure_singleton t : volume {t} = 0)
  unfold intervalIntegral
  rw [← integral_indicator hD, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [hn lo,hn hi] with u hlo hhi
  have hm : u ∈ D ↔ u ∈ Ioo lo hi := by
    constructor
    · intro hu
      have h := houter hu
      exact ⟨lt_of_le_of_ne h.1 (Ne.symm hlo),lt_of_le_of_ne h.2 hhi⟩
    · exact hinner
  by_cases hu : u ∈ D
  · simp only [indicator_of_mem hu, indicator_of_mem (hm.mp hu)]
  · simp only [indicator_of_notMem hu, indicator_of_notMem (mt hm.mpr hu)]

/-- The main term is the existing atomMass, not a newly fitted integral. -/
theorem atomMass_eq_interval (lower : Bool) (start : ℝ) (b : FloorAtom) :
    atomMass lower b start =
      intervalIntegral (lowerEndpoint lower start b) (upperEndpoint lower start b) := by
  let S := Icc start 5 ∩ tableAtomSet lower b
  have hS : MeasurableSet S := measurableSet_Icc.inter (measurableSet_tableAtomSet lower b)
  have hsub : S ⊆ Icc (1:ℝ) 5 := fun w hw => atom_subset_ambient lower b hw.2
  have hchange := integral_image_eq_integral_abs_deriv_smul hS
    (fun w hw => (inversePoint_derivative (hsub hw).1).hasDerivWithinAt)
    (inversePoint_injOn.mono hsub) (fun u : ℝ => 1/(u*(1-u)))
  have he : (∫ u in relativeAtomDomain lower start b, 1/(u*(1-u))) =
      atomMass lower b start := by
    rw [relativeAtomDomain_eq_image]
    calc
      _ = ∫ w in S, |-(1/(w+1)^2)| • (1/(inversePoint w*(1-inversePoint w))) := hchange
      _ = ∫ w in S, buchstabKernel w := by
        apply setIntegral_congr_fun hS
        intro w hw
        rw [smul_eq_mul, reciprocal_Jacobian (hsub hw), buchstabKernel_eq_raw (hsub hw)]
      _ = _ := by
        simp only [atomMass, Part5OriginalH430MovingBuchstabAtoms.startAtomDensity,
          integral_indicator hS]
  rw [← he]
  exact sandwich_integral_eq (relativeAtomDomain_measurable lower start b)
    (relativeAtomDomain_sandwich lower start b).1 (relativeAtomDomain_sandwich lower start b).2

/-- The exact existing native integral retains the full parent physical
weight. It is NOT identified directly with arithmetic parent Theta. -/
theorem nativeAtom_eq_weight_interval {up : Bool} {p : PhysicalNode}
    (hL : 0 < residual p) (hC : 0 < p.ceiling) (hg : directionGuard up p) (b : FloorAtom) :
    nativeAtomCoefficient up p b = physicalWeight p *
      intervalIntegral (lowerEndpoint up (physicalStart up p) b)
        (upperEndpoint up (physicalStart up p) b) := by
  rw [nativeAtomCoefficient_eq hL hC hg, coefficient, atomMass_eq_interval]

/-- The normalized domain is exactly the original physical LocalDomain,
not a newly chosen geometric surrogate. -/
theorem local_relative_atom_iff {up : Bool} {p : PhysicalNode}
    (hL : 0 < residual p) (hC : 0 < p.ceiling) (hg : directionGuard up p)
    {u : ℝ} (hu : 0 < u) (b : FloorAtom) :
    (LocalDomain p (buchstabShape up) (nativePoint (residual p*u)) ∧
      reciprocalQuery u ∈ tableAtomSet up b) ↔
      u ∈ relativeAtomDomain up (physicalStart up p) b := by
  have hpoint : buchstabPoint p (reciprocalQuery u) = nativePoint (residual p*u) := by
    rw [← nativePoint_nativeMap]
    congr 1
    unfold nativeMap reciprocalQuery
    field_simp [hu.ne'] <;> ring
  have hq : buchstabArgument p (nativePoint (residual p*u)) = reciprocalQuery u := by
    simp only [buchstabArgument,nativePoint_zero,reciprocalQuery]
    field_simp [hL.ne',hu.ne'] <;> ring
  constructor
  · rintro ⟨hd,hb⟩
    have hw := (native_local_query_bounds hd).2
    rw [hq] at hw
    have hlocal : LocalDomain p (buchstabShape up) (buchstabPoint p (reciprocalQuery u)) := by
      rwa [hpoint]
    exact ⟨hu,(actual_buchstab_domain hL hC hg hw.1).mp hlocal,hb⟩
  · rintro ⟨_,hw,hb⟩
    have hw1 := (atom_subset_ambient up b hb).1
    have hd := (actual_buchstab_domain hL hC hg hw1).mpr hw
    exact ⟨by simpa only [hpoint] using hd,hb⟩

/-- This is the actual same-target d*N prime atom; all knots are included. -/
theorem compact_uniform_masked_atom {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax,
      ∀ d : ℕ, 0 < d → d ≤ N → ∀ lower : Bool, ∀ start : ℝ, ∀ b : FloorAtom,
      |windowMass N L d (relativeAtomDomain lower start b)-atomMass lower b start| < epsilon := by
  obtain ⟨T,hT⟩ := compact_uniform_masked_interval hmin hmax he
  refine ⟨T, ?_⟩
  intro N hN L hL d hd hdN lower start b
  have hb := endpoints_mem lower start b
  have h := hT N hN L hL _ hb.1 _ hb.2 d hd hdN _
    (relativeAtomDomain_sandwich lower start b).1 (relativeAtomDomain_sandwich lower start b).2
  rwa [← atomMass_eq_interval] at h

end
end ImbalancedChen.Part5OriginalH430BuchstabAtomIntervalGeometry
