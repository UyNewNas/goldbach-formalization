import ImbalancedChen.Part3OriginalMediumCompleteWOneDifference
import Mathlib.Analysis.Calculus.MeanValue

/-!
SOURCE ONLY / NOT COMPILED / ZERO FORMAL CREDIT.
Iterated mean-value (equivalently the norm consequence of FTC) transfer
for the actual complete W. The induction proves the derivative of every
mixed finite difference before bounding it. It never treats a difference
or an integrated variation bound as a premise. Coordinate words are nodup.
-/

noncomputable section
open Classical
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumSmoothWeightInput
open ImbalancedChen.Part3.OriginalMediumCompleteWAllSubsetSteps
open ImbalancedChen.Part3.OriginalMediumCompleteWOneDifference
open ImbalancedChen.Part3.OriginalMediumSubsetLeibnizStep

namespace ImbalancedChen.Part3.OriginalRetainedPhaseMixedDifference20261102

def InRectangle (lo hi : Coordinate → ℝ) (v : Vector5) : Prop :=
  ∀ i, v i ∈ Set.Icc (lo i) (hi i)

def mixedDifference : List Coordinate → (Coordinate → ℝ) →
    (Coordinate → ℝ) → (Vector5 → ℂ) → Vector5 → ℂ
  | [], _, _, F, v => F v
  | i :: is, lo, hi, F, v =>
      mixedDifference is lo hi F (Function.update v i (lo i)) -
        mixedDifference is lo hi F (Function.update v i (hi i))

def widths (is : List Coordinate) (lo hi : Coordinate → ℝ) : ℝ :=
  (is.map (fun i => hi i - lo i)).prod

theorem update_mem_rectangle (lo hi : Coordinate → ℝ) (v : Vector5)
    (hv : InRectangle lo hi v) (i : Coordinate) (t : ℝ)
    (ht : t ∈ Set.Icc (lo i) (hi i)) :
    InRectangle lo hi (Function.update v i t) := by
  intro j
  by_cases hji : j = i
  · subst j; simpa using ht
  · simpa [Function.update_noteq hji] using hv j

/-- Differentiation commutes with the finitely many endpoint differences
in OTHER coordinates. The derivative is the literal next W allocation. -/
theorem mixedDifference_deriv
    (B : FixedBlock) (Smooth : SmoothInput B) (L A : ℝ)
    (lo hi : Coordinate → ℝ) (hordered : ∀ i, lo i ≤ hi i)
    (hbox : ∀ v, InRectangle lo hi v → NormBox v)
    (is : List Coordinate) :
    ∀ (S : Finset Coordinate) (i : Coordinate), i ∉ S → i ∉ is →
    ∀ (v : Vector5), InRectangle lo hi v →
    HasDerivAt
      (fun t => mixedDifference is lo hi (fullWFace B L A S)
        (Function.update v i t))
      (mixedDifference is lo hi (fullWFace B L A (insert i S)) v) (v i) := by
  induction is with
  | nil =>
      intro S i hiS hiis v hv
      obtain ⟨hq,h1,h2,hn,hh⟩ := hbox v hv
      simpa only [mixedDifference] using fullWFace_step_all B Smooth L A S i hiS v
        (zero_lt_one.trans_le hq) (zero_lt_one.trans_le h1)
        (zero_lt_one.trans_le h2) (zero_lt_one.trans_le hn)
  | cons j js ih =>
      intro S i hiS hiis v hv
      have hij : i ≠ j := by
        intro he; subst i; exact hiis (by simp)
      have hijs : i ∉ js := by intro hm; exact hiis (by simp [hm])
      have hlo := update_mem_rectangle lo hi v hv j (lo j) ⟨le_rfl,hordered j⟩
      have hhi := update_mem_rectangle lo hi v hv j (hi j) ⟨hordered j,le_rfl⟩
      have hdlo := ih S i hiS hijs (Function.update v j (lo j)) hlo
      have hdhi := ih S i hiS hijs (Function.update v j (hi j)) hhi
      simp only [Function.update_noteq hij] at hdlo hdhi
      have hd := hdlo.sub hdhi
      convert hd using 1 <;>
        simp only [mixedDifference, Function.update_comm hij]

/-- Each distinct coordinate consumes one segment length. The complete
W fifth-degree envelope is used once after ALL differentiations. -/
theorem mixedDifference_bound
    (B : FixedBlock) (Smooth : SmoothInput B) (L A : ℝ)
    (lo hi : Coordinate → ℝ) (hordered : ∀ i, lo i ≤ hi i)
    (hbox : ∀ v, InRectangle lo hi v → NormBox v)
    (is : List Coordinate) :
    is.Nodup → ∀ (S : Finset Coordinate), (∀ i ∈ is, i ∉ S) →
    ∀ (v : Vector5), InRectangle lo hi v →
    ‖mixedDifference is lo hi (fullWFace B L A S) v‖ ≤
      fifthEnvelope B Smooth L A * widths is lo hi := by
  induction is with
  | nil =>
      intro hnd S hdisj v hv
      simpa [mixedDifference,widths] using fullWFace_box_bound B Smooth L A S v (hbox v hv)
  | cons i is ih =>
      intro hnd S hdisj v hv
      have hiis := (List.nodup_cons.mp hnd).1
      have hnd' := (List.nodup_cons.mp hnd).2
      have hiS : i ∉ S := hdisj i (by simp)
      let f : ℝ → ℂ := fun t => mixedDifference is lo hi
        (fullWFace B L A S) (Function.update v i t)
      let g : ℝ → ℂ := fun t => mixedDifference is lo hi
        (fullWFace B L A (insert i S)) (Function.update v i t)
      have hder : ∀ t ∈ Set.Icc (lo i) (hi i),
          HasDerivWithinAt f (g t) (Set.Icc (lo i) (hi i)) t := by
        intro t ht
        have hvt := update_mem_rectangle lo hi v hv i t ht
        have hd := mixedDifference_deriv B Smooth L A lo hi hordered hbox
          is S i hiS hiis (Function.update v i t) hvt
        have hd' : HasDerivAt f (g t) t := by
          simpa only [f,g,Function.update_same,Function.update_idem] using hd
        exact hd'.hasDerivWithinAt
      have hbound : ∀ t ∈ Set.Icc (lo i) (hi i),
          ‖g t‖ ≤ fifthEnvelope B Smooth L A * widths is lo hi := by
        intro t ht
        apply ih hnd' (insert i S)
        · intro j hj
          have hji : j ≠ i := by intro he; subst j; exact hiis hj
          simp only [Finset.mem_insert, not_or]
          exact ⟨hji,hdisj j (by simp [hj])⟩
        · exact update_mem_rectangle lo hi v hv i t ht
      have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
        (convex_Icc (lo i) (hi i))
        (show lo i ∈ Set.Icc (lo i) (hi i) from ⟨le_rfl,hordered i⟩)
        (show hi i ∈ Set.Icc (lo i) (hi i) from ⟨hordered i,le_rfl⟩)
      simpa [mixedDifference,f,widths,Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (hordered i)),
        norm_sub_rev,mul_assoc,mul_left_comm,mul_comm] using hmean

end ImbalancedChen.Part3.OriginalRetainedPhaseMixedDifference20261102
