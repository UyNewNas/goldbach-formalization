import ImbalancedChen.Part5OriginalH430MixedNativeL1
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.MvPolynomial

/-! A finite rational expression, with totalized division and piecewise
comparisons, has locally constant comparison predicates almost everywhere.
Every identically zero polynomial is kept with its actual comparison. -/
namespace ImbalancedChen.Part5OriginalH430PrimeRegularGerms
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical

abbrev Space (d : ℕ) := Fin d → ℝ
abbrev Poly (d : ℕ) := MvPolynomial (Fin d) ℝ
abbrev ev {d} (p : Poly d) (x : Space d) := MvPolynomial.eval x p

theorem ae_poly_ne {d : ℕ} (p : Poly d) (hp : p ≠ 0) : ∀ᵐ x : Space d, ev p x ≠ 0 := by
  induction d with
  | zero =>
    let e := MvPolynomial.isEmptyAlgEquiv ℝ (Fin 0)
    have h := e.symm_apply_apply p
    rw [MvPolynomial.isEmptyAlgEquiv_symm_apply] at h
    apply Eventually.of_forall
    intro x hx
    have he : e p = 0 := by
      calc
        e p = ev (MvPolynomial.C (e p)) x := by simp [ev]
        _ = 0 := by rw [h]; exact hx
    exact hp (e.injective (he.trans (map_zero e).symm))
  | succ d ih =>
    let P := MvPolynomial.finSuccEquiv ℝ d p
    have hP : P ≠ 0 := fun h => hp ((MvPolynomial.finSuccEquiv ℝ d).injective
      (h.trans (map_zero _).symm))
    obtain ⟨j,hj⟩ : ∃ j, P.coeff j ≠ 0 := by
      by_contra! he
      exact hP (Polynomial.ext (fun j => by simp [he]))
    have htail := ih (P.coeff j) hj
    have hslice : ∀ᵐ y : Space d, ∀ᵐ t : ℝ, ev p (Fin.cases t y) ≠ 0 := by
      filter_upwards [htail] with y hy
      let Q := P.map (MvPolynomial.eval y)
      have hQ : Q ≠ 0 := fun h => hy (by
        have he := congrArg (fun q : Polynomial ℝ => q.coeff j) h
        simpa [Q,Polynomial.coeff_map] using he)
      have hn : ∀ᵐ t : ℝ, ¬Q.IsRoot t := by
        rw [ae_iff]
        simpa only [not_not] using (Polynomial.finite_setOfPred_isRoot hQ).measure_zero volume
      filter_upwards [hn] with t ht
      have he := MvPolynomial.eval_polynomial_eval_finSuccEquiv (x := y) p (MvPolynomial.C t)
      change ev p (Fin.cases t y) ≠ 0
      intro hzero
      apply ht
      change (P.map (MvPolynomial.eval y)).eval t = 0
      calc
        _ = (P.map (MvPolynomial.eval y)).eval (MvPolynomial.eval y (MvPolynomial.C t)) := by simp
        _ = MvPolynomial.eval y (P.eval (MvPolynomial.C t)) := Polynomial.eval_map_apply ..
        _ = ev p (Fin.cases t y) := by simpa only [P,MvPolynomial.eval_C] using he
        _ = 0 := hzero
    let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0
    have hm : MeasurableSet {z : ℝ × Space d | ev p (E.symm z) ≠ 0} :=
      (measurableSet_eq_fun (p.continuous_eval.measurable.comp E.symm.measurable) measurable_const).compl
    have hcons (t : ℝ) (y : Space d) : E.symm (t,y) = Fin.cases t y := by
      change Fin.insertNth 0 t y = Fin.cases t y
      exact (Fin.insertNth_zero' t y).trans (funext (fun i => Fin.cases rfl (fun _ => rfl) i))
    have hp' : ∀ᵐ z : ℝ × Space d, ev p (E.symm z) ≠ 0 := by
      rw [Measure.volume_eq_prod]
      apply (Measure.ae_prod_iff_ae_ae hm).mpr
      apply (Measure.ae_ae_comm hm).mpr
      simpa only [hcons] using hslice
    have hz := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).quasiMeasurePreserving.ae hp'
    exact hz.mono (fun x h => by
      change ev p (E.symm (E x)) ≠ 0 at h
      simpa using h)

def Stable {d} (P : Space d → Prop) := ∀ᵐ x, ∀ᶠ y in 𝓝 x, P y ↔ P x
def PW {d} (f : Space d → ℝ) : Prop :=
  ∃ S : Finset (Poly d × Poly d), ∀ᵐ x, ∃ v ∈ S, ev v.2 x ≠ 0 ∧
    ∀ᶠ y in 𝓝 x, f y = ev v.1 y / ev v.2 y

theorem st_const {d} (P : Prop) : Stable (fun _ : Space d => P) :=
  .of_forall (fun _ => .of_forall (fun _ => Iff.rfl))
theorem Stable.and {d} {P Q : Space d → Prop} (p : Stable P) (q : Stable Q) :
    Stable (fun x => P x ∧ Q x) := by
  filter_upwards [p,q] with x hp hq
  filter_upwards [hp,hq] with y hp hq
  exact and_congr hp hq
theorem Stable.not {d} {P : Space d → Prop} (h : Stable P) : Stable (fun x => ¬P x) :=
  h.mono fun _ hx => hx.mono fun _ hy => not_congr hy
theorem Stable.or {d} {P Q : Space d → Prop} (p : Stable P) (q : Stable Q) :
    Stable (fun x => P x ∨ Q x) := by
  filter_upwards [p,q] with x hp hq
  filter_upwards [hp,hq] with y hp hq
  exact or_congr hp hq

theorem pw_const {d} (c : ℝ) : PW (fun _ : Space d => c) := by
  exact ⟨{(MvPolynomial.C c,1)},.of_forall (fun _ =>
    ⟨_,Finset.mem_singleton_self _,by simp [ev],.of_forall (fun _ => by simp [ev])⟩)⟩
theorem pw_coord {d} (i : Fin d) : PW (fun x : Space d => x i) := by
  exact ⟨{(MvPolynomial.X i,1)},.of_forall (fun _ =>
    ⟨_,Finset.mem_singleton_self _,by simp [ev],.of_forall (fun _ => by simp [ev])⟩)⟩

private theorem binary {d} {f g : Space d → ℝ} (hf : PW f) (hg : PW g) (op : ℝ → ℝ → ℝ)
    (num : (Poly d × Poly d) → (Poly d × Poly d) → Poly d)
    (halg : ∀ v w x, ev v.2 x ≠ 0 → ev w.2 x ≠ 0 →
      op (ev v.1 x / ev v.2 x) (ev w.1 x / ev w.2 x) =
        ev (num v w) x / ev (v.2*w.2) x) : PW (fun x => op (f x) (g x)) := by
  obtain ⟨S,hS⟩ := hf
  obtain ⟨T,hT⟩ := hg
  let combine := fun v w : Poly d × Poly d => (num v w,v.2*w.2)
  refine ⟨Finset.image₂ combine S T,?_⟩
  filter_upwards [hS,hT] with x hv hw
  obtain ⟨v,hv,hvx,hv'⟩ := hv
  obtain ⟨w,hw,hwx,hw'⟩ := hw
  refine ⟨combine v w,Finset.mem_image₂.mpr ⟨v,hv,w,hw,rfl⟩,by
    simpa [combine,ev] using mul_ne_zero hvx hwx,?_⟩
  filter_upwards [hv',hw',v.2.continuous_eval.continuousAt.eventually_ne hvx,
    w.2.continuous_eval.continuousAt.eventually_ne hwx] with y h1 h2 h3 h4
  rw [h1,h2]
  exact halg v w y h3 h4

theorem PW.add {d} {f g : Space d → ℝ} (hf : PW f) (hg : PW g) : PW (fun x => f x + g x) :=
  binary hf hg (·+·) (fun v w => v.1*w.2+w.1*v.2) (by
    intro v w x hv hw
    simp only [ev,map_add,map_mul] at *
    field_simp [hv,hw] <;> ring)
theorem PW.sub {d} {f g : Space d → ℝ} (hf : PW f) (hg : PW g) : PW (fun x => f x - g x) :=
  binary hf hg (·-·) (fun v w => v.1*w.2-w.1*v.2) (by
    intro v w x hv hw
    simp only [ev,map_sub,map_mul] at *
    field_simp [hv,hw] <;> ring)
theorem PW.mul {d} {f g : Space d → ℝ} (hf : PW f) (hg : PW g) : PW (fun x => f x * g x) :=
  binary hf hg (·*·) (fun v w => v.1*w.1) (by intro v w x _ _; simp [ev,div_mul_div_comm])
theorem PW.neg {d} {f : Space d → ℝ} (hf : PW f) : PW (fun x => -f x) := by
  simpa only [zero_sub] using (pw_const 0).sub hf

private theorem avoid_num {d} (S : Finset (Poly d × Poly d)) :
    ∀ᵐ x, ∀ v ∈ S, v.1 ≠ 0 → ev v.1 x ≠ 0 := by
  have each (v : ↥S) : ∀ᵐ x, v.val.1 ≠ 0 → ev v.val.1 x ≠ 0 := by
    by_cases h : v.val.1 = 0
    · exact .of_forall (fun _ hn => (hn h).elim)
    · exact (ae_poly_ne _ h).mono (fun _ hn _ => hn)
  exact (Filter.eventually_all.mpr each).mono fun _ h v hv => h ⟨v,hv⟩

theorem PW.inv {d} {f : Space d → ℝ} (hf : PW f) : PW (fun x => (f x)⁻¹) := by
  obtain ⟨S,hS⟩ := hf
  refine ⟨insert (0,1) (S.image Prod.swap),?_⟩
  filter_upwards [hS,avoid_num S] with x hv hx
  obtain ⟨v,hv,_,h⟩ := hv
  by_cases he : v.1 = 0
  · refine ⟨(0,1),Finset.mem_insert_self ..,by simp [ev],?_⟩
    filter_upwards [h] with y hy
    simp [hy,he,ev]
  · refine ⟨v.swap,Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hv),hx v hv he,?_⟩
    filter_upwards [h] with y hy
    simp [hy,inv_div]
theorem PW.div {d} {f g : Space d → ℝ} (hf : PW f) (hg : PW g) : PW (fun x => f x / g x) := by
  simpa only [div_eq_mul_inv] using hf.mul hg.inv

theorem PW.nonneg {d} {f : Space d → ℝ} (hf : PW f) : Stable (fun x => 0 ≤ f x) := by
  obtain ⟨S,hS⟩ := hf
  filter_upwards [hS,avoid_num S] with x hv hx
  obtain ⟨v,hv,hden,h⟩ := hv
  have he := h.self_of_nhds
  by_cases hz : v.1 = 0
  · filter_upwards [h] with y hy
    simp [hy,he,hz,ev]
  · let r := fun y => ev v.1 y / ev v.2 y
    have hc : ContinuousAt r x := v.1.continuous_eval.continuousAt.div v.2.continuous_eval.continuousAt hden
    have hn : r x ≠ 0 := div_ne_zero (hx v hv hz) hden
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · filter_upwards [h,hc.eventually (eventually_lt_nhds hneg)] with y hy h'
      exact iff_of_false (not_le.mpr (hy.trans_lt h')) (not_le.mpr (he.trans_lt hneg))
    · filter_upwards [h,hc.eventually (eventually_gt_nhds hpos)] with y hy h'
      exact iff_of_true (h'.le.trans_eq hy.symm) (hpos.le.trans_eq he.symm)
theorem PW.le {d} {f g : Space d → ℝ} (hf : PW f) (hg : PW g) : Stable (fun x => f x ≤ g x) := by
  simpa only [sub_nonneg] using (hg.sub hf).nonneg
theorem PW.lt {d} {f g : Space d → ℝ} (hf : PW f) (hg : PW g) : Stable (fun x => f x < g x) := by
  simpa only [not_le] using (hg.le hf).not
theorem PW.eq {d} {f g : Space d → ℝ} (hf : PW f) (hg : PW g) : Stable (fun x => f x = g x) := by
  simpa only [le_antisymm_iff] using (hf.le hg).and (hg.le hf)
theorem PW.piece {d} {P : Space d → Prop} [DecidablePred P] {f g : Space d → ℝ}
    (hc : Stable P) (hf : PW f) (hg : PW g) : PW (fun x => if P x then f x else g x) := by
  obtain ⟨S,hS⟩ := hf
  obtain ⟨T,hT⟩ := hg
  refine ⟨S ∪ T,?_⟩
  filter_upwards [hc,hS,hT] with x he hs ht
  by_cases hx : P x
  · obtain ⟨v,hv,hd,h⟩ := hs
    refine ⟨v,Finset.mem_union_left _ hv,hd,?_⟩
    filter_upwards [he,h] with y hy h'
    simpa only [if_pos (hy.mpr hx)] using h'
  · obtain ⟨v,hv,hd,h⟩ := ht
    refine ⟨v,Finset.mem_union_right _ hv,hd,?_⟩
    filter_upwards [he,h] with y hy h'
    simpa only [if_neg (fun H => hx (hy.mp H))] using h'
theorem PW.min {d} {f g : Space d → ℝ} (hf : PW f) (hg : PW g) : PW (fun x => min (f x) (g x)) := by
  simpa only [min_def] using PW.piece (hf.le hg) hf hg
theorem PW.max {d} {f g : Space d → ℝ} (hf : PW f) (hg : PW g) : PW (fun x => max (f x) (g x)) := by
  simpa only [max_def] using PW.piece (hf.le hg) hg hf

end
end ImbalancedChen.Part5OriginalH430PrimeRegularGerms
