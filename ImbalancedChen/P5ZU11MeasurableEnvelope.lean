import ImbalancedChen.P5ZU11AdaptiveMinimum
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
Measurable finite minima and their common disjoint winner partition on
the original four-dimensional logarithmic U11 domain.

Only measurable policy gates and kernels are needed; step-table seams do
not have to be continuous. Integrability of the envelope follows from
its proved nonnegative domination by the switched candidate. No policy
license, Rosser bound, distribution estimate, or whole-U11 mean is assumed
as a theorem here. Those analytic inputs and numerical quadrature remain
open. Status: source_written / uncompiled.
-/

namespace ImbalancedChen.P5Z.U11Integral

open scoped BigOperators
open Set MeasureTheory
open Classical

noncomputable section

def tags (bank : Finset ℕ) : Finset ℕ := insert 0 (bank.image Nat.succ)

theorem tags_nonempty (bank : Finset ℕ) : (tags bank).Nonempty :=
  ⟨0, Finset.mem_insert_self _ _⟩

section FiniteEnvelope

variable {X : Type*} [MeasurableSpace X]

/-- The infimum is over a nonempty finite set, so it is an attained
ordinary real minimum, rather than an empty-infimum convention. -/
def envelope (bank : Finset ℕ) (f : ℕ → X → ℝ) (x : X) : ℝ :=
  sInf ((fun c => f c x) '' (tags bank : Set ℕ))

theorem envelope_eq_min (bank : Finset ℕ) (f : ℕ → X → ℝ) (x : X) :
    envelope bank f x = ((tags bank).image (fun c => f c x)).min'
      ((tags_nonempty bank).image _) := by
  simpa only [envelope, Finset.coe_image] using
    ((tags_nonempty bank).image (fun c => f c x)).csInf_eq_min'

theorem measurable_envelope (bank : Finset ℕ) (f : ℕ → X → ℝ)
    (hf : ∀ c ∈ tags bank, Measurable (f c)) : Measurable (envelope bank f) :=
  Measurable.sInf (tags bank).countable_toSet hf

theorem envelope_le (bank : Finset ℕ) (f : ℕ → X → ℝ) (x : X)
    (c : ℕ) (hc : c ∈ tags bank) : envelope bank f x ≤ f c x := by
  rw [envelope_eq_min]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨c, hc, rfl⟩)

theorem envelope_nonneg (bank : Finset ℕ) (f : ℕ → X → ℝ) (x : X)
    (hf : ∀ c ∈ tags bank, 0 ≤ f c x) : 0 ≤ envelope bank f x := by
  rw [envelope_eq_min]
  apply Finset.le_min'
  intro v hv
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hv
  exact hf c hc

/-- The unique winner is the least tag attaining the real finite minimum. -/
def winner (D : Set X) (bank : Finset ℕ) (f : ℕ → X → ℝ) (c : ℕ) : Set X :=
  {x | x ∈ D ∧ f c x = envelope bank f x ∧
    ∀ d ∈ tags bank, d < c → f d x ≠ envelope bank f x}

theorem measurableSet_winner (D : Set X) (hD : MeasurableSet D)
    (bank : Finset ℕ) (f : ℕ → X → ℝ)
    (hf : ∀ c ∈ tags bank, Measurable (f c)) (c : ℕ) (hc : c ∈ tags bank) :
    MeasurableSet (winner D bank f c) := by
  have he := measurable_envelope bank f hf
  have hsmall : MeasurableSet {x | ∀ d ∈ tags bank,
      d < c → f d x ≠ envelope bank f x} := by
    have hm : MeasurableSet (⋂ d ∈ (tags bank).filter (fun d => d < c),
        {x | f d x ≠ envelope bank f x}) := by
      apply Finset.measurableSet_biInter
      intro d hd
      exact (measurableSet_eq_fun (hf d (Finset.mem_filter.mp hd).1) he).compl
    convert hm using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_filter]
    tauto
  exact hD.inter ((measurableSet_eq_fun (hf c hc) he).inter hsmall)

theorem winner_disjoint (D : Set X) (bank : Finset ℕ) (f : ℕ → X → ℝ)
    {c d : ℕ} (hc : c ∈ tags bank) (hd : d ∈ tags bank) (hcd : c ≠ d) :
    Disjoint (winner D bank f c) (winner D bank f d) := by
  apply Set.disjoint_left.mpr
  intro x hxc hxd
  rcases lt_or_gt_of_ne hcd with hlt | hgt
  · exact hxd.2.2 c hc hlt hxc.2.1
  · exact hxc.2.2 d hd hgt hxd.2.1

theorem exists_winner (D : Set X) (bank : Finset ℕ) (f : ℕ → X → ℝ)
    (x : X) (hx : x ∈ D) : ∃ c ∈ tags bank, x ∈ winner D bank f c := by
  let M := (tags bank).filter (fun c => f c x = envelope bank f x)
  have hM : M.Nonempty := by
    have hm := Finset.min'_mem ((tags bank).image (fun c => f c x))
      ((tags_nonempty bank).image _)
    obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp hm
    refine ⟨c, Finset.mem_filter.mpr ⟨hc, ?_⟩⟩
    exact heq.trans (envelope_eq_min bank f x).symm
  let c := M.min' hM
  have hcM : c ∈ M := Finset.min'_mem M hM
  obtain ⟨hc, heq⟩ := Finset.mem_filter.mp hcM
  refine ⟨c, hc, hx, heq, ?_⟩
  intro d hd hdc hdeq
  have hdM : d ∈ M := Finset.mem_filter.mpr ⟨hd, hdeq⟩
  exact (not_lt_of_ge (Finset.min'_le M d hdM)) hdc

theorem iUnion_winner (D : Set X) (bank : Finset ℕ) (f : ℕ → X → ℝ) :
    (⋃ c ∈ tags bank, winner D bank f c) = D := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨c, hc, hx⟩
    exact hx.1
  · intro hx
    exact exists_winner D bank f x hx

/-- Genuine domination: ordinary candidates need not themselves be
integrable when the switched option already gives an integrable ceiling. -/
theorem integrableOn_envelope (D : Set X) (hD : MeasurableSet D)
    (bank : Finset ℕ) (f : ℕ → X → ℝ) (μ : Measure X)
    (hf : ∀ c ∈ tags bank, Measurable (f c))
    (hn : ∀ x ∈ D, ∀ c ∈ tags bank, 0 ≤ f c x)
    (h0 : IntegrableOn (f 0) D μ) : IntegrableOn (envelope bank f) D μ := by
  apply h0.mono_nonneg (measurable_envelope bank f hf).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hD] with x hx
    exact envelope_nonneg bank f x (hn x hx)
  · filter_upwards [ae_restrict_mem hD] with x hx
    exact envelope_le bank f x 0 (Finset.mem_insert_self _ _)

/-- The envelope integral is exactly the sum over one measurable disjoint
partition. There is no addition of alternative estimates on overlaps. -/
theorem integral_envelope_eq_sum_winner (D : Set X) (hD : MeasurableSet D)
    (bank : Finset ℕ) (f : ℕ → X → ℝ) (μ : Measure X)
    (hf : ∀ c ∈ tags bank, Measurable (f c))
    (hi : IntegrableOn (envelope bank f) D μ) :
    (∫ x in D, envelope bank f x ∂μ) =
      ∑ c ∈ tags bank, ∫ x in winner D bank f c, f c x ∂μ := by
  calc
    _ = ∫ x in ⋃ c ∈ tags bank, winner D bank f c, envelope bank f x ∂μ := by
      rw [iUnion_winner]
    _ = ∑ c ∈ tags bank, ∫ x in winner D bank f c, envelope bank f x ∂μ := by
      apply integral_biUnion_finset
      · exact fun c hc => measurableSet_winner D hD bank f hf c hc
      · intro c hc d hd hcd
        exact winner_disjoint D bank f hc hd hcd
      · intro c hc
        exact hi.mono_set (fun x hx => hx.1)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      apply setIntegral_congr_fun (measurableSet_winner D hD bank f hf c hc)
      intro x hx
      exact hx.2.1.symm

/-- Ineligible policies are replaced by the always available switched
option, preserving both the finite minimum and its measurability. -/
def guarded (eligible : ℕ → X → Prop) (switched : X → ℝ)
    (ordinary : ℕ → X → ℝ) (c : ℕ) (x : X) : ℝ :=
  if c = 0 then switched x else if eligible c.pred x then ordinary c.pred x else switched x

theorem measurable_guarded (bank : Finset ℕ) (eligible : ℕ → X → Prop)
    (switched : X → ℝ) (ordinary : ℕ → X → ℝ)
    (he : ∀ j ∈ bank, MeasurableSet {x | eligible j x})
    (hs : Measurable switched) (ho : ∀ j ∈ bank, Measurable (ordinary j)) :
    ∀ c ∈ tags bank, Measurable (guarded eligible switched ordinary c) := by
  intro c hc
  rcases Finset.mem_insert.mp hc with rfl | hc
  · simpa only [guarded, if_pos rfl] using hs
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    simpa only [guarded, Nat.succ_ne_zero, if_false, Nat.pred_succ] using
      (ho j hj).piecewise (he j hj) hs

theorem guarded_nonneg (D : Set X) (bank : Finset ℕ)
    (eligible : ℕ → X → Prop) (switched : X → ℝ) (ordinary : ℕ → X → ℝ)
    (hs : ∀ x ∈ D, 0 ≤ switched x)
    (ho : ∀ j ∈ bank, ∀ x ∈ D, eligible j x → 0 ≤ ordinary j x) :
    ∀ x ∈ D, ∀ c ∈ tags bank, 0 ≤ guarded eligible switched ordinary c x := by
  intro x hx c hc
  rcases Finset.mem_insert.mp hc with rfl | hc
  · simpa only [guarded, if_pos rfl] using hs x hx
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    by_cases he : eligible j x
    · simpa [guarded, he] using ho j hj x hx he
    · simpa [guarded, he] using hs x hx

theorem guarded_envelope_le_switched (bank : Finset ℕ)
    (eligible : ℕ → X → Prop) (switched : X → ℝ) (ordinary : ℕ → X → ℝ)
    (x : X) : envelope bank (guarded eligible switched ordinary) x ≤ switched x := by
  simpa only [guarded, if_pos rfl] using
    envelope_le bank (guarded eligible switched ordinary) x 0 (Finset.mem_insert_self _ _)

theorem guarded_envelope_bounds (D : Set X) (bank : Finset ℕ)
    (eligible : ℕ → X → Prop) (switched : X → ℝ) (ordinary : ℕ → X → ℝ)
    (hs : ∀ x ∈ D, 0 ≤ switched x)
    (ho : ∀ j ∈ bank, ∀ x ∈ D, eligible j x → 0 ≤ ordinary j x)
    (x : X) (hx : x ∈ D) :
    0 ≤ envelope bank (guarded eligible switched ordinary) x ∧
      envelope bank (guarded eligible switched ordinary) x ≤ switched x := by
  exact ⟨envelope_nonneg bank _ x (guarded_nonneg D bank eligible switched ordinary hs ho x hx),
    guarded_envelope_le_switched bank eligible switched ordinary x⟩

/-- An ordinary winner is eligible: otherwise it ties the switched tag 0
and loses by the deterministic least-tag convention. -/
theorem ordinary_winner_eligible (D : Set X) (bank : Finset ℕ)
    (eligible : ℕ → X → Prop) (switched : X → ℝ) (ordinary : ℕ → X → ℝ)
    (j : ℕ) (x : X)
    (hx : x ∈ winner D bank (guarded eligible switched ordinary) j.succ) :
    eligible j x := by
  by_contra he
  have h0 := hx.2.2 0 (Finset.mem_insert_self _ _) (Nat.succ_pos j)
  apply h0
  have hh : guarded eligible switched ordinary j.succ x =
      guarded eligible switched ordinary 0 x := by simp [guarded, he]
  exact hh.symm.trans hx.2.1

/-- The fallback disappears on every ordinary winner cell, so each cell
integrates the actual switched or ordinary kernel which won there. -/
theorem integral_guarded_envelope_eq_raw (D : Set X) (hD : MeasurableSet D)
    (bank : Finset ℕ) (eligible : ℕ → X → Prop)
    (switched : X → ℝ) (ordinary : ℕ → X → ℝ) (μ : Measure X)
    (he : ∀ j ∈ bank, MeasurableSet {x | eligible j x})
    (hs : Measurable switched) (ho : ∀ j ∈ bank, Measurable (ordinary j))
    (hi : IntegrableOn (envelope bank (guarded eligible switched ordinary)) D μ) :
    (∫ x in D, envelope bank (guarded eligible switched ordinary) x ∂μ) =
      ∑ c ∈ tags bank,
        ∫ x in winner D bank (guarded eligible switched ordinary) c,
          (if c = 0 then switched x else ordinary c.pred x) ∂μ := by
  have hg := measurable_guarded bank eligible switched ordinary he hs ho
  rw [integral_envelope_eq_sum_winner D hD bank _ μ hg hi]
  apply Finset.sum_congr rfl
  intro c hc
  apply setIntegral_congr_fun (measurableSet_winner D hD bank _ hg c hc)
  intro x hx
  by_cases hc0 : c = 0
  · simp only [guarded, hc0, if_pos rfl]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc0
    have hj := ordinary_winner_eligible D bank eligible switched ordinary j x hx
    simp [guarded, hj]

end FiniteEnvelope

abbrev LogFour := Fin 4 → ℝ

/-- Original U11 logarithmic walls. The last pair is (x,y), and the
fourth-prime interval remains the complete [19/125,59/250). -/
def originalDomain (mask : Set (ℝ × ℝ)) : Set LogFour :=
  {v | (417 / 5000 : ℝ) ≤ v 3 ∧ v 3 < v 2 ∧ v 2 < v 1 ∧
    v 1 < (19 / 125 : ℝ) ∧ (19 / 125 : ℝ) ≤ v 0 ∧
    v 0 < (59 / 250 : ℝ) ∧ (v 0, v 1) ∉ mask}

theorem originalDomain_denominators_pos (mask : Set (ℝ × ℝ))
    (v : LogFour) (hv : v ∈ originalDomain mask) : 0 < v 3 ∧ 0 < v 2 := by
  obtain ⟨ha, h32, h21, h1, h0lo, h0hi, hm⟩ := hv
  constructor <;> linarith

/-- Even the complete last-prime range keeps the switched Buchstab
argument above the original 77/38 wall; no mask crop is used here. -/
theorem originalDomain_buchstab_argument_gt (mask : Set (ℝ × ℝ))
    (v : LogFour) (hv : v ∈ originalDomain mask) :
    (77 / 38 : ℝ) < (1 - (v 0 + v 1 + v 2 + v 3)) / v 2 := by
  have hz := (originalDomain_denominators_pos mask v hv).2
  obtain ⟨ha, h32, h21, h1, h0lo, h0hi, hm⟩ := hv
  apply (lt_div_iff₀ hz).2
  linarith

theorem measurableSet_originalDomain (mask : Set (ℝ × ℝ))
    (hm : MeasurableSet mask) : MeasurableSet (originalDomain mask) := by
  have h0 : Measurable (fun v : LogFour => v 0) := measurable_pi_apply 0
  have h1 : Measurable (fun v : LogFour => v 1) := measurable_pi_apply 1
  have h2 : Measurable (fun v : LogFour => v 2) := measurable_pi_apply 2
  have h3 : Measurable (fun v : LogFour => v 3) := measurable_pi_apply 3
  exact (measurableSet_le measurable_const h3).inter
    ((measurableSet_lt h3 h2).inter ((measurableSet_lt h2 h1).inter
      ((measurableSet_lt h1 measurable_const).inter
        ((measurableSet_le measurable_const h0).inter
          ((measurableSet_lt h0 measurable_const).inter
            (hm.preimage (h0.prodMk h1)).compl)))))

def switchedKernel (K : ℝ) (omega : ℝ → ℝ) (v : LogFour) : ℝ :=
  K * omega ((1 - (v 0 + v 1 + v 2 + v 3)) / v 2) / v 2

def ordinaryKernel (H : ℝ → ℝ) (L : ℕ → LogFour → ℝ)
    (j : ℕ) (v : LogFour) : ℝ :=
  4 * (1 - H (max 2 (L j v / v 3))) / L j v

theorem measurable_switchedKernel (K : ℝ) (omega : ℝ → ℝ)
    (ho : Measurable omega) : Measurable (switchedKernel K omega) := by
  have h0 : Measurable (fun v : LogFour => v 0) := measurable_pi_apply 0
  have h1 : Measurable (fun v : LogFour => v 1) := measurable_pi_apply 1
  have h2 : Measurable (fun v : LogFour => v 2) := measurable_pi_apply 2
  have h3 : Measurable (fun v : LogFour => v 3) := measurable_pi_apply 3
  exact (measurable_const.mul (ho.comp
    ((measurable_const.sub (((h0.add h1).add h2).add h3)).div h2))).div h2

theorem measurable_ordinaryKernel (H : ℝ → ℝ) (L : ℕ → LogFour → ℝ)
    (j : ℕ) (hH : Measurable H) (hL : Measurable (L j)) :
    Measurable (ordinaryKernel H L j) := by
  have h3 : Measurable (fun v : LogFour => v 3) := measurable_pi_apply 3
  exact (measurable_const.mul (measurable_const.sub
    (hH.comp (measurable_const.max (hL.div h3))))).div hL

/-- Dedicated original-domain integrability prerequisite, using only the
proved domination by the switched density on this very same masked domain. -/
theorem integrableOn_original_envelope (mask : Set (ℝ × ℝ))
    (hm : MeasurableSet mask) (bank : Finset ℕ)
    (eligible : ℕ → LogFour → Prop) (K : ℝ) (omega H : ℝ → ℝ)
    (L : ℕ → LogFour → ℝ) (μ : Measure LogFour)
    (he : ∀ j ∈ bank, MeasurableSet {v | eligible j v})
    (homega : Measurable omega) (hH : Measurable H)
    (hL : ∀ j ∈ bank, Measurable (L j))
    (hs : ∀ v ∈ originalDomain mask, 0 ≤ switchedKernel K omega v)
    (ho : ∀ j ∈ bank, ∀ v ∈ originalDomain mask,
      eligible j v → 0 ≤ ordinaryKernel H L j v)
    (hi : IntegrableOn (switchedKernel K omega) (originalDomain mask) μ) :
    IntegrableOn (envelope bank
      (guarded eligible (switchedKernel K omega) (ordinaryKernel H L)))
      (originalDomain mask) μ := by
  apply integrableOn_envelope (originalDomain mask) (measurableSet_originalDomain mask hm)
    bank _ μ
  · exact measurable_guarded bank eligible _ _ he (measurable_switchedKernel K omega homega)
      (fun j hj => measurable_ordinaryKernel H L j hH (hL j hj))
  · exact guarded_nonneg _ bank eligible _ _ hs ho
  · simpa only [guarded, if_pos rfl] using hi

/-- Exact set-integral accounting on the complete original U11 masked
log-domain. Kernels with measurable table seams are fully admitted. -/
theorem integral_original_envelope_eq_sum (mask : Set (ℝ × ℝ))
    (hm : MeasurableSet mask) (bank : Finset ℕ)
    (eligible : ℕ → LogFour → Prop) (K : ℝ) (omega H : ℝ → ℝ)
    (L : ℕ → LogFour → ℝ) (μ : Measure LogFour)
    (he : ∀ j ∈ bank, MeasurableSet {v | eligible j v})
    (homega : Measurable omega) (hH : Measurable H)
    (hL : ∀ j ∈ bank, Measurable (L j))
    (hs : ∀ v ∈ originalDomain mask, 0 ≤ switchedKernel K omega v)
    (ho : ∀ j ∈ bank, ∀ v ∈ originalDomain mask,
      eligible j v → 0 ≤ ordinaryKernel H L j v)
    (hi : IntegrableOn (switchedKernel K omega) (originalDomain mask) μ) :
    (∫ v in originalDomain mask,
        envelope bank (guarded eligible (switchedKernel K omega) (ordinaryKernel H L)) v ∂μ) =
      ∑ c ∈ tags bank,
        ∫ v in winner (originalDomain mask) bank
            (guarded eligible (switchedKernel K omega) (ordinaryKernel H L)) c,
          (if c = 0 then switchedKernel K omega v else ordinaryKernel H L c.pred v) ∂μ := by
  exact integral_guarded_envelope_eq_raw (originalDomain mask)
    (measurableSet_originalDomain mask hm) bank eligible (switchedKernel K omega)
    (ordinaryKernel H L) μ he (measurable_switchedKernel K omega homega)
    (fun j hj => measurable_ordinaryKernel H L j hH (hL j hj))
    (integrableOn_original_envelope mask hm bank eligible K omega H L μ he
      homega hH hL hs ho hi)

end

end ImbalancedChen.P5Z.U11Integral
