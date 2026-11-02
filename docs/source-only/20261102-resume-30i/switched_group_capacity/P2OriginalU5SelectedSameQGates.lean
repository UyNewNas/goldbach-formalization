import ImbalancedChen.P2OriginalU5WholeGroupCapacity
import ImbalancedChen.P2EnhancedSelectedSortedDwellMerge

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

All four choices of original selected subset pass at the actual U5 Q.
In particular selecting the SMALLER old prime requires p*q^2<Q, which
is stronger than either of the two usual full-prefix squares. It is
proved from the original U5 triangle here, not inferred from full support.
The sorted-union consumer is for residual MODULUS atoms at Q/(p*q).
It is not a claim that the complete switched source word is D-well.
-/
namespace ImbalancedChen.P2OriginalU5SelectedSameQGates
noncomputable section
open scoped Classical
open P5OriginalU5CausalFinite (pairSupport coordinates)
open P2OriginalU5SmallPartnerRootPayment
open P2EnhancedSortedDwellMerge P2EnhancedSelectedSortedDwellMerge

/-- The additional selected-complement square when the smaller original
prime is selected. The original root's entire triangle satisfies it. -/
theorem root_smaller_selected_square {N : ℕ} (hN : 2≤N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) : (t.1 : ℝ)*(t.2 : ℝ)^2<rootQ N t := by
  have hg := P5OriginalU5CausalFinite.coordinates_mem_triangle hN ht
  obtain ⟨hu,hut,hthi⟩ := Part5OriginalUpsilon5CausalDictionary.mem_triangle.mp hg
  have hlevel := (Part5OriginalUpsilon5CausalDictionary.level_bounds hu hut.le hthi.le).1
  have hexp : coordinates N t 0+2*coordinates N t 1<
      Part5OriginalUpsilon5CausalDictionary.level (coordinates N t 0) (coordinates N t 1) := by
    dsimp [Part5OriginalUpsilon5CausalDictionary.h] at hthi
    linarith
  have hpos : ∀ j : Fin 2,0<(![t.1,t.2] : Fin 2 → ℕ) j := by
    intro j
    fin_cases j
    · exact (pair_primes ht).1.pos
    · exact (pair_primes ht).2.pos
  have hp := actualPrimeTupleLog_rpow (by omega : 1<N) ![t.1,t.2] hpos
  have hp0 : (N : ℝ)^coordinates N t 0=(t.1 : ℝ) := hp 0
  have hp1 : (N : ℝ)^coordinates N t 1=(t.2 : ℝ) := hp 1
  have hNreal : (1 : ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hpower : (N : ℝ)^(coordinates N t 0+2*coordinates N t 1)=
      (t.1 : ℝ)*(t.2 : ℝ)^2 := by
    rw [show coordinates N t 0+2*coordinates N t 1=
      coordinates N t 0+(coordinates N t 1+coordinates N t 1) by ring,
      Real.rpow_add (zero_lt_one.trans hNreal),Real.rpow_add (zero_lt_one.trans hNreal),hp0,hp1]
    ring
  rw [← hpower]
  exact Real.rpow_lt_rpow_of_exponent_lt hNreal hexp

theorem root_all_square_bounds {N : ℕ} (hN : 2≤N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) :
    (t.2 : ℝ)^2<rootQ N t ∧
      (t.2 : ℝ)*(t.1 : ℝ)^2<rootQ N t ∧
      (t.1 : ℝ)*(t.2 : ℝ)^2<rootQ N t := by
  have hp : (1 : ℝ)≤t.1 := by exact_mod_cast (pair_primes ht).1.pos
  have hp0 : (0 : ℝ)≤t.1 := Nat.cast_nonneg _
  have hq0 : (0 : ℝ)≤t.2 := Nat.cast_nonneg _
  have hpq : (t.1 : ℝ)≤t.2 := by exact_mod_cast (Finset.mem_filter.mp ht).2.2.1.le
  have hs := root_smaller_selected_square hN ht
  have hfirst : (t.2 : ℝ)^2≤(t.1 : ℝ)*(t.2 : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg (t.2 : ℝ))]
  have hsecond : (t.2 : ℝ)*(t.1 : ℝ)^2≤(t.1 : ℝ)*(t.2 : ℝ)^2 := by
    nlinarith [mul_nonneg (mul_nonneg hp0 hq0) (sub_nonneg.mpr hpq)]
  exact ⟨hfirst.trans_lt hs,hsecond.trans_lt hs,hs⟩

theorem root_full_squares {N : ℕ} (hN : 2≤N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) : actualDwellSupport (rootQ N t) [t.2,t.1] := by
  have hs := root_all_square_bounds hN ht
  intro i hi
  have hi' : i=0 ∨ i=1 := by simp only [List.length_cons,List.length_nil] at hi; omega
  rcases hi' with rfl | rfl
  · simpa using hs.1.le
  · simpa using hs.2.1.le

/-- Every original selected subset, including empty and full selections,
is checked. No assumption on residual ordering is added to this root fact. -/
theorem root_selected_complement_squares {N : ℕ} (hN : 2≤N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) (S : ℕ → Prop) :
    RemainingSquares (rootQ N t) [t.2,t.1] S := by
  have hs := root_all_square_bounds hN ht
  by_cases hq : S t.2
  · by_cases hp : S t.1
    · simp [RemainingSquares,selected,remaining,hq,hp]
    · intro i hi
      have hi0 : i=0 := by simp [remaining,hq,hp] at hi; omega
      subst i
      simpa [selected,remaining,hq,hp] using hs.2.1.le
  · by_cases hp : S t.1
    · intro i hi
      have hi0 : i=0 := by simp [remaining,hq,hp] at hi; omega
      subst i
      simpa [selected,remaining,hq,hp,mul_comm] using hs.2.2.le
    · simpa [RemainingSquares,selected,remaining,hq,hp,actualDwellSupport,
        MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation.PrefixSquareBound] using
        root_full_squares hN ht

/-- The concrete root discharges the old full AND all selected gates of
the existing genuine sorted-union theorem. The parent Q is unchanged.
Residual primes may interleave; they are not the positive source quotient. -/
theorem root_modulus_sameQ_transport {N : ℕ} (hN : 2≤N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) (residual : List ℕ) (S : ℕ → Prop)
    (hres : actualDwellSupport (rootQ N t/((t.1*t.2 : ℕ) : ℝ)) residual)
    (hresOne : ∀ q ∈ residual,1≤q) (hresNo : ∀ q ∈ residual,¬S q) :
    actualDwellSupport (rootQ N t) (sortedUnion [t.2,t.1] residual) ∧
      selected (sortedUnion [t.2,t.1] residual) S=selected [t.2,t.1] S ∧
      actualDwellSupport (rootQ N t/((selected [t.2,t.1] S).prod : ℝ))
        (remaining (sortedUnion [t.2,t.1] residual) S) ∧
      (remaining (sortedUnion [t.2,t.1] residual) S).prod=
        (remaining [t.2,t.1] S).prod*residual.prod := by
  have hp := pair_primes ht
  have hone : ∀ p ∈ [t.2,t.1],1≤p := by
    intro p hmem
    simp only [List.mem_cons,List.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact hp.2.pos
    · exact hp.1.pos
  have hsort : ([t.2,t.1] : List ℕ).Pairwise (· ≥ ·) := by
    simpa using (Finset.mem_filter.mp ht).2.2.1.le
  apply full_and_selected_sortedUnion [t.2,t.1] residual S
    (by simpa using mul_pos hp.2.pos hp.1.pos)
    (root_full_squares hN ht) hsort hone (root_selected_complement_squares hN ht S)
    _ hresOne hresNo
  simpa only [List.prod_cons,List.prod_nil,mul_one,Nat.mul_comm] using hres

end
end ImbalancedChen.P2OriginalU5SelectedSameQGates
