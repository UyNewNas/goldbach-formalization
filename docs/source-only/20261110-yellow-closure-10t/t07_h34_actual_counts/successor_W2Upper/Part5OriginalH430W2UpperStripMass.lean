import ImbalancedChen.Part5OriginalH430W2UpperPolygons

namespace ImbalancedChen.Part5OriginalH430W2UpperStripMass

open Set MeasureTheory
open scoped Interval
open Part5OriginalH430W2UpperKernel Part5OriginalH430W2UpperQuadrature
open Part5OriginalH430W2UpperPolygons
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5OriginalH430LiteralBankBudget
open P5OriginalActualTableFeedback

def native (p : Parameters) (k : Fin 4) (i : Fin 200) : Set Point :=
  W2PairDomain (physical p) k ∩ tablePullback false (pairProfile (physical p) k) (.inl i)

theorem native_integrable {p : Parameters} (hp : W2Geometry (physical p)) (k : Fin 4) (i : Fin 200) :
    IntegrableOn pairKernel (native p k i) :=
  (integrableOn_pairKernel (W2PairDomain_subset hp k)).mono_set inter_subset_left

/-- Change variables on the genuine strict fibre. Vertical cuts and affine boundaries
are excluded; this gives a direct lower comparison with the table's specified open atom. -/
theorem strip_integral {p : Parameters} {k : Fin 4} {i : Fin 200} {s : Strip}
    (hp : W2Geometry (physical p)) (hf : Fit p k i.val s) :
    (∫ x in carrier s, pairKernel x) = ∫ u in (s.l : ℝ)..(s.r : ℝ), s.density u := by
  let F := (carrier s).indicator pairKernel
  let A := Ioo (s.l : ℝ) (s.r : ℝ)
  let B := fun u => Ioo (s.low.atR u) (s.high.atR u)
  have hF : Integrable F :=
    ((native_integrable hp k i).mono_set (carrier_native hp hf)).integrable_indicator (carrier_measurable s)
  have htwo : (∫ x : Point,F x) = ∫ u : ℝ,∫ v : ℝ,F ![u,v] := by
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
  have hvec (u v : ℝ) : (![u,v] : Point)∈carrier s ↔ u∈A ∧ v∈B u := Iff.rfl
  have hfun (u v : ℝ) :
      F ![u,v] = A.indicator (fun u => (B u).indicator (fun v => 1/(u*v*(1-u-v))) v) u := by
    by_cases hu : u∈A
    · by_cases hv : v∈B u
      · have hmem := (hvec u v).2 ⟨hu,hv⟩
        have hdom := (carrier_native hp hf hmem).1
        have hgeo := W2PairDomain_geometry hp k hdom
        rw [F,indicator_of_mem hmem,indicator_of_mem hu,indicator_of_mem hv]
        exact pairKernel_eq_raw hgeo.1 hgeo.2
      · have ht : (![u,v] : Point) ∉ carrier s := fun hm => hv ((hvec u v).1 hm).2
        simp only [F,indicator_of_notMem ht,indicator_of_mem hu,indicator_of_notMem hv]
    · have ht : (![u,v] : Point) ∉ carrier s := fun hm => hu ((hvec u v).1 hm).1
      simp only [F,indicator_of_notMem ht,indicator_of_notMem hu]
  calc
    _ = ∫ x : Point,F x := (integral_indicator (carrier_measurable s)).symm
    _ = ∫ u : ℝ,∫ v : ℝ,F ![u,v] := htwo
    _ = ∫ u : ℝ,A.indicator s.density u := by
      apply integral_congr_ae
      filter_upwards [] with u
      by_cases hu : u∈A
      · simp_rw [hfun,indicator_of_mem hu]
        rw [integral_indicator measurableSet_Ioo]
        have hs := fit_safe hf (show u∈Icc (s.l : ℝ) (s.r : ℝ) from ⟨hu.1.le,hu.2.le⟩)
        exact original_inner_primitive s hs.u hs.low hs.order hs.upper
      · simp_rw [hfun,indicator_of_notMem hu]
        simp
    _ = ∫ u in Ioo (s.l : ℝ) (s.r : ℝ),s.density u := integral_indicator measurableSet_Ioo
    _ = _ := by
      rw [integral_Ioo_eq_integral_Ioc,intervalIntegral.integral_of_le (by exact_mod_cast hf.1.le)]

def covered : List Strip → Set Point
  | [] => ∅
  | s::ss => carrier s ∪ covered ss

theorem covered_mem (ss : List Strip) (x : Point) : x∈covered ss ↔ ∃ s∈ss, x∈carrier s := by
  induction ss with
  | nil => simp [covered]
  | cons a ss ih => simp [covered,ih]

theorem covered_measurable (ss : List Strip) : MeasurableSet (covered ss) := by
  induction ss with
  | nil => exact MeasurableSet.empty
  | cons a ss ih => exact (carrier_measurable a).union ih

theorem covered_subset {p : Parameters} {k : Fin 4} {i : Fin 200} (hp : W2Geometry (physical p))
    {ss : List Strip} (hf : ∀ s∈ss, Fit p k i.val s) : covered ss ⊆ native p k i := by
  intro x hx
  obtain ⟨s,hs,ht⟩ := (covered_mem ss x).1 hx
  exact carrier_native hp (hf s hs) ht

/-- Separate strips within one Gamma and one input cell cannot share open u-length. -/
def Separated (ss : List Strip) : Prop := ss.Pairwise (fun a b => a.r≤b.l)
instance (ss : List Strip) : Decidable (Separated ss) := by unfold Separated; infer_instance

theorem disjoint_next {s : Strip} {ss : List Strip} (hd : ∀ t∈ss, s.r≤t.l) :
    Disjoint (carrier s) (covered ss) := by
  refine Set.disjoint_left.2 ?_
  intro x hx hy
  obtain ⟨t,ht,hxt⟩ := (covered_mem ss x).1 hy
  have hsep : (s.r : ℝ)≤t.l := by exact_mod_cast hd t ht
  exact (not_lt_of_ge hsep) (hxt.1.1.trans hx.1.2)

theorem sum_strip_lower {p : Parameters} {k : Fin 4} {i : Fin 200} (hp : W2Geometry (physical p))
    (mid : Bool) (ss : List Strip) (hf : ∀ s∈ss, Fit p k i.val s) (hd : Separated ss) :
    (((ss.map (stripLower mid)).sum : ℚ) : ℝ) ≤ ∫ x in covered ss, pairKernel x := by
  induction ss with
  | nil => simp [covered]
  | cons a ss ih =>
    have ha := hf a (by simp)
    have ht : ∀ s∈ss, Fit p k i.val s := fun s hs => hf s (List.mem_cons_of_mem _ hs)
    obtain ⟨hd0,hdt⟩ := List.pairwise_cons.mp hd
    have hnat := native_integrable hp k i
    have hi := strip_sound mid a ha.1.le (fun x hx => fit_safe ha hx)
    rw [← strip_integral hp ha] at hi
    rw [covered,setIntegral_union (disjoint_next hd0) (covered_measurable ss)
      (hnat.mono_set (carrier_native hp ha)) (hnat.mono_set (covered_subset hp ht))]
    simpa only [List.map_cons,List.sum_cons,Rat.cast_add] using add_le_add hi (ih ht hdt)

theorem actual_pair_atom_lower {p : Parameters} {k : Fin 4} {i : Fin 200} (hp : W2Geometry (physical p))
    (mid : Bool) (hf : ∀ s∈pieces p k i.val, Fit p k i.val s) (hd : Separated (pieces p k i.val)) :
    ((((pieces p k i.val).map (stripLower mid)).sum : ℚ) : ℝ) ≤
      pairIntegralAtom (physical p) k (.inl i) :=
  (sum_strip_lower hp mid _ hf hd).trans (setIntegral_mono_set (native_integrable hp k i)
    (Filter.Eventually.of_forall pairKernel_nonneg)
    (Filter.Eventually.of_forall (fun _ hx => covered_subset hp hf hx)))

end ImbalancedChen.Part5OriginalH430W2UpperStripMass
