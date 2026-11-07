import ImbalancedChen.P2SeedOmegaAffineClipArea

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact finite partition semantics of the ACTUAL sampled bad integral.
Option.none is the genuine top-endpoint singleton; it is retained in the
pointwise partition and its zero area is separately proved. No numerical
sample or area is evaluated. This is a finite-sum identity, not a PASS.
-/

namespace ImbalancedChen.P2SeedOmegaFiniteCellSum
noncomputable section
open Set MeasureTheory Classical
open scoped BigOperators Interval
open P2SeedOmegaLiteralFibre
open P2SeedOmegaBadCellSemantics (actualBadKernel)
open P2SeedOmegaBadSpatialModulus
open P2SeedOmegaBadUniformIntegralError
open P2SeedOmegaFiniteMesh
open P2SeedOmegaMeshAdmissibility
open P2SeedOmegaFiniteMeshLimit (meshCost)

abbrev BandIndex (n : ℕ) := Option (Fin (n+1))
def band (n : ℕ) : BandIndex n → Set ℝ
  | none => {a2}
  | some j => scalarCell n j
def bandNode (n : ℕ) : BandIndex n → ℝ
  | none => a2
  | some j => node n j

theorem band_measurable (n : ℕ) (i : BandIndex n) : MeasurableSet (band n i) := by
  cases i <;> exacts [measurableSet_singleton _,measurableSet_Ico]

theorem band_mem_range {n : ℕ} {i : BandIndex n} {x : ℝ}
    (hx : x ∈ band n i) : x ∈ Icc corner a2 := by
  cases i with
  | none =>
      have he : x=a2 := hx
      subst x
      exact ⟨by norm_num [corner,a2],le_rfl⟩
  | some j =>
      have h := logPrimeMeshLoHi_bounds (d:=1) (by norm_num [corner,a2] : corner<a2)
        n (fun _ => j) 0
      exact ⟨h.1.trans hx.1,hx.2.le.trans h.2.2⟩

theorem band_unique {n : ℕ} {i j : BandIndex n} {x : ℝ}
    (hi : x ∈ band n i) (hj : x ∈ band n j) : i=j := by
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some k =>
          have he : x=a2 := hi
          have h := logPrimeMeshLoHi_bounds (d:=1) (by norm_num [corner,a2] : corner<a2)
            n (fun _ => k) 0
          have ht : x<a2 := hj.2.trans_le h.2.2
          exact (ht.ne he).elim
  | some k =>
      cases j with
      | none =>
          have he : x=a2 := hj
          have h := logPrimeMeshLoHi_bounds (d:=1) (by norm_num [corner,a2] : corner<a2)
            n (fun _ => k) 0
          have ht : x<a2 := hi.2.trans_le h.2.2
          exact (ht.ne he).elim
      | some l => exact congrArg some (scalar_cell_unique hi hj)

theorem exists_band (n : ℕ) {x : ℝ} (hx : x ∈ Icc corner a2) :
    ∃ i : BandIndex n,x ∈ band n i := by
  by_cases ht : x=a2
  · exact ⟨none,ht⟩
  · obtain ⟨j,hj⟩ := exists_logPrimeMeshInterval corner a2 n ⟨hx.1,lt_of_le_of_ne hx.2 ht⟩
    exact ⟨some j,hj⟩

theorem scalarSnap_on_band {n : ℕ} {i : BandIndex n} {x : ℝ}
    (hx : x ∈ band n i) : scalarSnap n x=bandNode n i := by
  cases i with
  | none =>
      have he : x=a2 := hx
      simp only [scalarSnap,he,if_true,bandNode]
  | some j => exact scalarSnap_eq_node hx

def cell (n : ℕ) (i j : BandIndex n) : Set (ℝ×ℝ) :=
  badClosed ∩ (band n i ×ˢ band n j)
def coefficient (alpha : ℝ) (n : ℕ) (i j : BandIndex n) : ℝ :=
  actualBadKernel alpha (bandNode n i) (bandNode n j)
def weight (n : ℕ) (i j : BandIndex n) : ℝ := (volume (cell n i j)).toReal
def jointSample (alpha : ℝ) (n : ℕ) : ℝ×ℝ → ℝ :=
  badClosed.indicator (fun p =>sampledKernel alpha (meshSample n) p.1 p.2)

theorem cell_measurable (n : ℕ) (i j : BandIndex n) : MeasurableSet (cell n i j) :=
  badClosed_measurable.inter ((band_measurable n i).prod (band_measurable n j))

theorem cell_constant_integrable (n : ℕ) (i j : BandIndex n) (c : ℝ) :
    Integrable ((cell n i j).indicator (fun _ : ℝ×ℝ =>c)) := by
  have hc : IntegrableOn (fun _ : ℝ×ℝ =>c) primeRectangle :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  exact (hc.mono_set (fun _ hx =>hx.1.1)).integrable_indicator (cell_measurable n i j)

/-- Exact pointwise finite partition, including both top singleton bands. -/
theorem jointSample_finite_partition (alpha : ℝ) (n : ℕ) (p : ℝ×ℝ) :
    jointSample alpha n p=
      ∑ i : BandIndex n,∑ j : BandIndex n,
        (cell n i j).indicator (fun _ =>coefficient alpha n i j) p := by
  by_cases hp : p ∈ badClosed
  · have hrect := hp.1
    obtain ⟨i,hi⟩ := exists_band n (show p.1 ∈ Icc corner a2 from ⟨hrect.1.1,hrect.2.1⟩)
    obtain ⟨j,hj⟩ := exists_band n (show p.2 ∈ Icc corner a2 from ⟨hrect.1.2,hrect.2.2⟩)
    have hcell : p ∈ cell n i j := ⟨hp,hi,hj⟩
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · rw [indicator_of_mem hcell]
        simp only [jointSample,indicator_of_mem hp,sampledKernel,meshSample,
          scalarSnap_on_band hi,scalarSnap_on_band hj,coefficient]
      · intro k hk hkj
        exact indicator_of_notMem (fun h =>hkj (band_unique h.2.2 hj)) _
      · intro hjfalse
        exact (hjfalse (Finset.mem_univ j)).elim
    · intro k hk hki
      apply Finset.sum_eq_zero
      intro l hl
      exact indicator_of_notMem (fun h =>hki (band_unique h.2.1 hi)) _
    · intro hifalse
      exact (hifalse (Finset.mem_univ i)).elim
  · rw [jointSample,indicator_of_notMem hp]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    exact indicator_of_notMem (fun h =>hp h.1) _

theorem jointSample_integrable (alpha : ℝ) (n : ℕ) : Integrable (jointSample alpha n) := by
  have he : jointSample alpha n=(fun p =>∑ i : BandIndex n,∑ j : BandIndex n,
      (cell n i j).indicator (fun _ =>coefficient alpha n i j) p) := funext (jointSample_finite_partition alpha n)
  rw [he]
  exact integrable_finsetSum _ (fun i _ =>integrable_finsetSum _
    (fun j _ =>cell_constant_integrable n i j _))

theorem integral_cell_constant (n : ℕ) (i j : BandIndex n) (c : ℝ) :
    (∫ p : ℝ×ℝ,(cell n i j).indicator (fun _ =>c) p)=c*weight n i j := by
  rw [integral_indicator (cell_measurable n i j),setIntegral_const,smul_eq_mul]
  exact mul_comm _ _

theorem jointSample_integral_finite_sum (alpha : ℝ) (n : ℕ) :
    (∫ p : ℝ×ℝ,jointSample alpha n p)=
      ∑ i : BandIndex n,∑ j : BandIndex n,coefficient alpha n i j*weight n i j := by
  simp_rw [jointSample_finite_partition alpha n]
  rw [integral_finsetSum _ (fun i _ =>integrable_finsetSum _
    (fun j _ =>cell_constant_integrable n i j _))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ =>cell_constant_integrable n i j _)]
  exact Finset.sum_congr rfl (fun j _ =>integral_cell_constant n i j _)

theorem jointSample_integral_eq_meshCost (alpha : ℝ) (n : ℕ) :
    (∫ p : ℝ×ℝ,jointSample alpha n p)=meshCost n alpha := by
  rw [integral_prod _ (jointSample_integrable alpha n)]
  have hf (u : ℝ) : (∫ v : ℝ,jointSample alpha n (u,v))=
      (Icc corner a2).indicator
        (fun u =>∫ v in badLower u..a2,sampledKernel alpha (meshSample n) u v) u := by
    by_cases hu : u ∈ Icc corner a2
    · rw [indicator_of_mem hu]
      have he (v : ℝ) : jointSample alpha n (u,v)=
          (Icc (badLower u) a2).indicator (sampledKernel alpha (meshSample n) u) v := by
        by_cases hv : v ∈ Icc (badLower u) a2
        · simp only [jointSample,indicator_of_mem ((badClosed_dictionary u v).mpr ⟨hu,hv⟩),indicator_of_mem hv]
        · have hp : (u,v) ∉ badClosed := fun h =>hv ((badClosed_dictionary u v).mp h).2
          simp only [jointSample,indicator_of_notMem hp,indicator_of_notMem hv]
      simp_rw [he]
      rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (bad_fibre_geometry hu).2.2.1]
    · rw [indicator_of_notMem hu]
      have he : (fun v : ℝ =>jointSample alpha n (u,v))=0 := by
        funext v
        exact indicator_of_notMem (fun h =>hu ((badClosed_dictionary u v).mp h).1) _
      rw [he]
      simp
  simp_rw [hf]
  rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num [corner,a2])]
  rfl

/-- Actual concrete mesh integral is an explicit finite weighted sum. -/
theorem meshCost_eq_finite_sum (alpha : ℝ) (n : ℕ) :
    meshCost n alpha=
      ∑ i : BandIndex n,∑ j : BandIndex n,coefficient alpha n i j*weight n i j := by
  rw [←jointSample_integral_eq_meshCost,jointSample_integral_finite_sum]

/-- Top singleton ownership is paid geometrically before its zero
weight is used; no arithmetic boundary is removed by a null-set claim. -/
theorem top_band_weights_zero (n : ℕ) (i : BandIndex n) :
    weight n none i=0 ∧ weight n i none=0 := by
  have hu : volume (cell n none i)=0 := by
    apply measure_mono_null (t:={a2} ×ˢ Icc corner a2) _ ?_
    · intro p hp
      exact ⟨hp.2.1,⟨hp.1.1.1.2,hp.1.1.2.2⟩⟩
    · rw [Measure.prod_prod]
      simp
  have hv : volume (cell n i none)=0 := by
    apply measure_mono_null (t:=Icc corner a2 ×ˢ {a2}) _ ?_
    · intro p hp
      exact ⟨⟨hp.1.1.1.1,hp.1.1.2.1⟩,hp.2.2⟩
    · rw [Measure.prod_prod]
      simp
  simp only [weight,hu,hv,ENNReal.toReal_zero,and_self]

end
end ImbalancedChen.P2SeedOmegaFiniteCellSum
