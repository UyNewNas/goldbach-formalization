import ImbalancedChen.Part3OriginalInversePairDisplacement
import ImbalancedChen.Part3SignedIntervalResidueOccupancy
import ImbalancedChen.Part3IntervalHarmonicPairBound

/-! Quantitative integer matrix counting within one signed lower-left-entry
fibre. The determinant and the actual left translation supply the modulus
of the upper-left progression. -/
namespace ImbalancedChen.Part3.OriginalInversePairFibres20261113
noncomputable section
open Finset Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups BigOperators
open SignedIntervalResidueOccupancy20261026b Gamma0ParabolicBottomRow20261025a
open IntervalHarmonicPairBoundSourceOnly

private theorem interval_card (S : Finset ℤ) (x A : ℝ) (p : ℤ) (hp : 0<p)
    (hA : 0≤A) (hs : ∀ a ∈ S, |(a:ℝ)-x|≤A)
    (hm : ∀ a ∈ S, ∀ b ∈ S, Int.ModEq p a b) :
    (S.card:ℝ) ≤ 1+2*A/(p:ℝ) := by
  by_cases ne : S.Nonempty
  · let L := S.min' ne
    let U := S.max' ne
    have Ls := min'_mem S ne
    have Us := max'_mem S ne
    have bound := signed_progression_card_le S L U p
      (min'_le S U Us) hp (fun a ha => ⟨min'_le S a ha,le_max' S a ha⟩) hm
    have d : (U:ℝ)-(L:ℝ) ≤ 2*A := by
      have hl := (abs_le.mp (hs _ Ls)).1
      have hu := (abs_le.mp (hs _ Us)).2
      dsimp [L,U]
      linarith
    exact bound.trans (by gcongr)
  · rw [not_nonempty_iff_eq_empty.mp ne,card_empty,Nat.cast_zero]
    positivity

private theorem compare_upper (g h : SL(2,ℤ)) {c d : ℤ} (cg : g 1 0=c) (ch : h 1 0=c)
    (dg : g 1 1=d) (dh : h 1 1=d) :
    ∃ k : ℤ, h=ModularGroup.T^k*g ∧ h 0 0=g 0 0+k*c := by
  have row : bottomRow h=bottomRow g := by
    funext j
    fin_cases j <;> simp [bottomRow,cg,ch,dg,dh]
  obtain ⟨k,he⟩ := (bottomRow_eq_iff_left_translation g h).mp row
  refine ⟨k,he,?_⟩
  simp [he,coe_mul,ModularGroup.coe_T_zpow,Matrix.mul_fin_two,cg]

private theorem one_row (S : Finset (SL(2,ℤ))) {c d : ℤ} (hc : c≠0)
    (cg : ∀ g ∈ S, g 1 0=c) (dg : ∀ g ∈ S, g 1 1=d)
    (x A : ℝ) (hA : 0≤A) (hs : ∀ g ∈ S, |(g 0 0:ℝ)-x|≤A) :
    (S.card:ℝ) ≤ 1+2*A/|(c:ℝ)| := by
  classical
  let f (g : SL(2,ℤ)) := g 0 0
  have hinj : Set.InjOn f ↑S := by
    intro g hg h hh he
    obtain ⟨k,e,ha⟩ := compare_upper g h (cg _ hg) (cg _ hh) (dg _ hg) (dg _ hh)
    have hk : k*c = 0 := by change g 0 0=h 0 0 at he; omega
    have hzero := (mul_eq_zero.mp hk).resolve_right hc
    simpa [hzero] using e.symm
  have b := interval_card (S.image f) x A |c| (abs_pos.mpr hc) hA
    (fun a ha => by obtain ⟨g,hg,rfl⟩ := mem_image.mp ha; exact hs _ hg)
    (by
      intro a ha b hb
      obtain ⟨g,hg,rfl⟩ := mem_image.mp ha
      obtain ⟨h,hh,rfl⟩ := mem_image.mp hb
      obtain ⟨k,_,e⟩ := compare_upper g h (cg _ hg) (cg _ hh) (dg _ hg) (dg _ hh)
      apply Int.modEq_iff_dvd.mpr
      change |c| ∣ h 0 0-g 0 0
      rcases le_total 0 c with hpos | hneg
      · exact ⟨k,by rw [abs_of_nonneg hpos,e]; ring⟩
      · exact ⟨-k,by rw [abs_of_nonpos hneg,e]; ring⟩)
  simpa only [card_image_of_injOn hinj,Int.cast_abs] using b

/-- For a fixed signed c≠0, count d in its true translated interval and
then a in one class modulo |c|. For unequal heights one may exchange the
two points and invert every matrix before applying this statement. -/
theorem fixed_nonzero_c (S : Finset (SL(2,ℤ))) {c : ℤ} (hc : c≠0)
    (hC : ∀ g ∈ S, g 1 0=c) {A D : ℝ} (hA : 0≤A) (hD : 0≤D) (x y : ℝ)
    (hleft : ∀ g ∈ S, |(g 0 0:ℝ)-x|≤A) (hright : ∀ g ∈ S, |(g 1 1:ℝ)-y|≤D) :
    (S.card:ℝ) ≤ (1+2*D)*(1+2*A/|(c:ℝ)|) := by
  classical
  let f (g : SL(2,ℤ)) := g 1 1
  let keys := S.image f
  have hd : (keys.card:ℝ) ≤ 1+2*D := by
    have h := interval_card keys y D 1 (by norm_num) hD
      (by intro d hd; obtain ⟨g,hg,rfl⟩ := mem_image.mp hd; exact hright g hg)
      (fun _ _ _ _ => Int.modEq_iff_dvd.mpr (one_dvd _))
    simpa only [Int.cast_one,div_one] using h
  have hcSum := card_eq_sum_card_fiberwise (fun g (hg : g ∈ S) => mem_image_of_mem f hg)
  have each (d) (hd' : d ∈ keys) : (((S.filter (fun g => f g=d)).card):ℝ) ≤
      1+2*A/|(c:ℝ)| :=
    one_row _ hc (fun g hg => hC g (mem_filter.mp hg).1)
      (fun _ hg => (mem_filter.mp hg).2) x A hA (fun g hg => hleft g (mem_filter.mp hg).1)
  calc
    (S.card:ℝ) = ∑ d ∈ keys, (((S.filter (fun g => f g=d)).card):ℝ) := by exact_mod_cast hcSum
    _ ≤ ∑ _ ∈ keys, (1+2*A/|(c:ℝ)|) := sum_le_sum each
    _ = (keys.card:ℝ)*(1+2*A/|(c:ℝ)|) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hd (by positivity)

/-- Sum one sign of the lower-left entry. Both interval centers may vary
with c. The translation spacing is still |c|, including at c=±1. -/
theorem signed_fibres (S : Finset (SL(2,ℤ))) (negative : Bool) (H : ℕ) {A D : ℝ}
    (hA : 0≤A) (hD : 0≤D) (x y : ℤ → ℝ)
    (sign : ∀ g ∈ S, (if negative then -(g 1 0) else g 1 0) > 0)
    (cap : ∀ g ∈ S, (g 1 0).natAbs ≤ H)
    (ha : ∀ g ∈ S, |(g 0 0:ℝ)-x (g 1 0)|≤A)
    (hd : ∀ g ∈ S, |(g 1 1:ℝ)-y (g 1 0)|≤D) :
    (S.card:ℝ) ≤ (1+2*D)*((H:ℝ)+2*A*(harmonic H:ℝ)) := by
  classical
  let f (g : SL(2,ℤ)) := (g 1 0).natAbs
  have mapTo (g) (hg : g ∈ S) : f g ∈ Icc 1 H := by
    apply mem_Icc.mpr
    refine ⟨?_,cap g hg⟩
    have e := sign g hg
    have ne : g 1 0 ≠ 0 := by intro z; simp [z] at e
    exact Int.natAbs_pos.mpr ne
  have counts := card_eq_sum_card_fiberwise mapTo
  have each (n : ℕ) (hn : n∈Icc 1 H) :
      (((S.filter (fun g => f g=n)).card):ℝ) ≤ (1+2*D)*(1+2*A/(n:ℝ)) := by
    let c : ℤ := if negative then -(n:ℤ) else (n:ℤ)
    have hn0 : 0<n := (mem_Icc.mp hn).1
    have hc : c ≠ 0 := by cases negative <;> simp [c,hn0.ne']
    have val (g) (hg : g∈S.filter (fun g => f g=n)) : g 1 0=c := by
      have h := congrArg (fun k : ℕ => (k:ℤ)) (mem_filter.mp hg).2
      change (((g 1 0).natAbs:ℕ):ℤ) = (n:ℤ) at h
      rw [Int.natCast_natAbs] at h
      have s := sign g (mem_filter.mp hg).1
      cases negative
      · change 0 < g 1 0 at s
        change g 1 0 = (n:ℤ)
        exact (abs_of_pos s).symm.trans h
      · change 0 < -(g 1 0) at s
        change g 1 0 = -(n:ℤ)
        rw [abs_of_neg (by omega : g 1 0 < 0)] at h
        omega
    have B := fixed_nonzero_c (S.filter (fun g => f g=n)) hc val hA hD (x c) (y c)
      (fun g hg => by simpa only [val _ hg] using ha g (mem_filter.mp hg).1)
      (fun g hg => by simpa only [val _ hg] using hd g (mem_filter.mp hg).1)
    cases negative <;> simpa [c,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n)] using B
  calc
    (S.card:ℝ) = ∑ n ∈ Icc 1 H, (((S.filter (fun g => f g=n)).card):ℝ) := by exact_mod_cast counts
    _ ≤ ∑ n ∈ Icc 1 H, (1+2*D)*(1+2*A/(n:ℝ)) := sum_le_sum each
    _ = _ := by
      rw [← mul_sum,sum_add_distrib,← real_reciprocal_sum_eq_harmonic]
      congr 1
      have q : (∑ _n ∈ Icc 1 H, (1:ℝ))=(H:ℝ) := by simp [Nat.card_Icc]
      rw [q, mul_sum]
      congr 1
      exact sum_congr rfl (fun n _ => by ring)

/-- The c=0 matrices have a=d=±1. With a fixed sign only the upper-right
integer varies, over an interval of length 2B independently of both centers. -/
theorem parabolic_fibre (S : Finset (SL(2,ℤ))) {e : ℤ} (he : e=1 ∨ e= -1)
    (hC : ∀ g ∈ S, g 1 0=0) (hD : ∀ g ∈ S, g 1 1=e)
    (x : ℝ) {B : ℝ} (hB : 0≤B) (hb : ∀ g ∈ S, |(g 0 1:ℝ)-x|≤B) :
    (S.card:ℝ) ≤ 1+2*B := by
  classical
  let f (g : SL(2,ℤ)) := g 0 1
  have a (g) (hg : g∈S) : g 0 0=e := by
    have H : g 0 0*e=1 := by simpa [Matrix.det_fin_two,hC g hg,hD g hg] using g.det_coe
    rcases he with h|h
    · simpa [h] using H
    · rw [h,mul_neg_one] at H
      omega
  have hi : Set.InjOn f ↑S := by
    intro g hg h hh hf
    ext i j
    fin_cases i <;> fin_cases j
    · exact (a g hg).trans (a h hh).symm
    · exact hf
    · exact (hC g hg).trans (hC h hh).symm
    · exact (hD g hg).trans (hD h hh).symm
  have bound := interval_card (S.image f) x B 1 (by norm_num) hB
    (by intro t ht; obtain ⟨g,hg,rfl⟩ := mem_image.mp ht; exact hb _ hg)
    (fun _ _ _ _ => Int.modEq_iff_dvd.mpr (one_dvd _))
  simpa only [card_image_of_injOn hi,Int.cast_one,div_one] using bound

end
end ImbalancedChen.Part3.OriginalInversePairFibres20261113
