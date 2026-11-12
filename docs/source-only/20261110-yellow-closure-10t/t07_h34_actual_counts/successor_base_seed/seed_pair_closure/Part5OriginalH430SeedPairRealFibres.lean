import ImbalancedChen.P2SeedOmegaLiteralFunctional
import ImbalancedChen.AffinePrimeGates
import ImbalancedChen.Part5OriginalH430OrdinaryPairCounts

/-! Ordinary double integrals of the actual seed. Fubini uses a single
compact rectangle separated from all three poles. All four ordinary windows
and the bad fifth window lie in this rectangle. -/
namespace ImbalancedChen.Part5OriginalH430SeedPairRealFibres
noncomputable section
open Set MeasureTheory Filter
open P2SeedOmegaLiteralFibre
open P5OriginalActionMassBound (Point)
open scoped Classical Interval

def raw (x : Point) : ℝ := pairKernel (x 0) (x 1)
def box : Set Point := Icc ![a0,a0] ![a2,a3]

theorem box_mem {x : Point} :
    x∈box ↔ a0≤x 0 ∧ x 0≤a2 ∧ a0≤x 1 ∧ x 1≤a3 := by
  constructor
  · intro h
    exact ⟨h.1 0,h.2 0,h.1 1,h.2 1⟩
  · rintro ⟨h0,h1,h2,h3⟩
    constructor <;> intro i <;> fin_cases i <;> assumption

theorem integrable_raw_box : IntegrableOn raw box := by
  have hc : ContinuousOn raw box := by
    unfold raw pairKernel
    apply continuousOn_const.div
    · fun_prop
    · intro x hx
      obtain ⟨h0,h1,h2,h3⟩ := box_mem.mp hx
      have hpos : 0<a0 := by norm_num [a0]
      have hgap : a2+a3<1 := by norm_num [a2,a3]
      exact (mul_pos (mul_pos (hpos.trans_le h0) (hpos.trans_le h2))
        (by linarith only [h1,h3,hgap])).ne'
  exact hc.integrableOn_compact isCompact_Icc

def strip (a b : ℝ) (lo hi : ℝ → ℝ) : Set Point :=
  {x | x 0∈Ioo a b ∧ x 1∈Ioo (lo (x 0)) (hi (x 0))}

theorem strip_measurable (a b : ℝ) {lo hi : ℝ → ℝ}
    (hl : Continuous lo) (hr : Continuous hi) : MeasurableSet (strip a b lo hi) := by
  exact (measurableSet_Ioo.preimage (measurable_pi_apply 0)).inter
    ((measurableSet_lt (hl.measurable.comp (measurable_pi_apply 0)) (measurable_pi_apply 1)).inter
      (measurableSet_lt (measurable_pi_apply 1) (hr.measurable.comp (measurable_pi_apply 0))))

/-- The open cells are integrated first. Endpoints enter only when changing
one-dimensional Lebesgue integrals to interval integrals. -/
theorem strip_integral {a b : ℝ} {lo hi : ℝ → ℝ} (hl : Continuous lo)
    (hr : Continuous hi) (hab : a≤b) (hle : ∀ u∈Ioo a b,lo u≤hi u)
    (hbox : strip a b lo hi⊆box) :
    (∫ x in strip a b lo hi,raw x)=∫ u in a..b,∫ v in lo u..hi u,pairKernel u v := by
  let S := strip a b lo hi
  let F := S.indicator raw
  have hm : MeasurableSet S := strip_measurable a b hl hr
  have hF : Integrable F := (integrable_raw_box.mono_set hbox).integrable_indicator hm
  have htwo : (∫ x : Point,F x)=∫ u : ℝ,∫ v : ℝ,F ![u,v] := by
    calc
      _ = ∫ u : ℝ,∫ v : ℝ,∫ z : Fin 0 → ℝ,F (Fin.cons u (Fin.cons v z)) :=
        integral_fin_pair F hF
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with u
        apply integral_congr_ae
        filter_upwards [] with v
        rw [integral_fin_zero]
        rfl
  have hv (u v : ℝ) : F ![u,v]=(Ioo a b).indicator
      (fun u => (Ioo (lo u) (hi u)).indicator (fun v => pairKernel u v) v) u := by
    have hmuv : (![u,v] : Point)∈S ↔ u∈Ioo a b ∧ v∈Ioo (lo u) (hi u) := Iff.rfl
    by_cases hu : u∈Ioo a b <;> by_cases hv : v∈Ioo (lo u) (hi u) <;>
      simp only [F,Set.indicator_apply,hmuv,hu,hv,raw,Matrix.cons_val_zero,
        Matrix.cons_val_one,if_true,if_false,and_true,and_false,true_and,false_and]
  calc
    _ = ∫ x : Point,F x := (integral_indicator hm).symm
    _ = ∫ u : ℝ,∫ v : ℝ,F ![u,v] := htwo
    _ = ∫ u : ℝ,(Ioo a b).indicator
        (fun u => ∫ v in Ioo (lo u) (hi u),pairKernel u v) u := by
      apply integral_congr_ae
      filter_upwards [] with u
      by_cases hu : u∈Ioo a b
      · rw [indicator_of_mem hu]
        simp_rw [hv,indicator_of_mem hu]
        exact integral_indicator measurableSet_Ioo
      · rw [indicator_of_notMem hu]
        simp_rw [hv,indicator_of_notMem hu]
        simp only [integral_zero]
    _ = ∫ u in Ioo a b,∫ v in Ioo (lo u) (hi u),pairKernel u v :=
      integral_indicator measurableSet_Ioo
    _ = ∫ u in Ioo a b,∫ v in lo u..hi u,pairKernel u v := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      rw [intervalIntegral.integral_of_le (hle u hu),integral_Ioo_eq_integral_Ioc]
    _ = _ := by rw [intervalIntegral.integral_of_le hab,integral_Ioo_eq_integral_Ioc]

def triangle (h : ℝ) : Set Point := strip a0 h id (fun _ => h)
def rectangle (l r : ℝ) : Set Point := strip a0 a1 (fun _ => l) (fun _ => r)
def bad : Set Point := strip corner a2 badLower (fun _ => a2)

theorem triangle_subset {h : ℝ} (ht : h≤a2) : triangle h⊆box := by
  rintro x ⟨⟨hx,hx'⟩,hv,hv'⟩
  apply box_mem.mpr
  exact ⟨hx.le,hx'.le.trans ht,hx.le.trans hv.le,hv'.le.trans (ht.trans (by norm_num [a2,a3]))⟩

theorem triangle_integral {h : ℝ} (ha : a0≤h) (ht : h≤a2) :
    (∫ x in triangle h,raw x)=ordinaryTriangle h :=
  strip_integral continuous_id continuous_const ha (fun _ hu => hu.2.le) (triangle_subset ht)

theorem rectangle_integral {l r : ℝ} (hl : a0≤l) (hlr : l≤r) (hr : r≤a3) :
    (∫ x in rectangle l r,raw x)=ordinaryRectangle l r := by
  apply strip_integral continuous_const continuous_const (by norm_num [a0,a1])
    (fun _ _ => hlr)
  rintro x ⟨⟨hx,hx'⟩,hv,hv'⟩
  exact box_mem.mpr ⟨hx.le,hx'.le.trans (by norm_num [a1,a2]),hl.trans hv.le,hv'.le.trans hr⟩

theorem bad_dictionary (x : Point) : x∈bad ↔ (x 0,x 1)∈badDomain := by
  rw [badDomain_dictionary]
  change (corner<x 0 ∧ x 0<a2) ∧ max (x 0) (1-2*x 0)<x 1 ∧ x 1<a2 ↔ _
  tauto

theorem bad_subset : bad⊆box := by
  intro x hx
  obtain ⟨h0,hu,hv,_⟩ := (bad_dictionary x).mp hx
  exact (triangle_subset (le_refl a2)) ⟨⟨h0,hu.trans hv⟩,hu,hv⟩

theorem bad_integral : (∫ x in bad,raw x)=P2SeedOmegaLiteralFunctional.badOrdinaryDouble := by
  have hb : Continuous badLower := by unfold badLower; fun_prop
  have hf := strip_integral hb continuous_const (by norm_num [corner,a2] : corner≤a2)
    (fun u hu => (bad_fibre_geometry (u:=u) ⟨hu.1.le,hu.2.le⟩).2.2.1) bad_subset
  exact hf.trans bad_pair_partition

end
end ImbalancedChen.Part5OriginalH430SeedPairRealFibres
