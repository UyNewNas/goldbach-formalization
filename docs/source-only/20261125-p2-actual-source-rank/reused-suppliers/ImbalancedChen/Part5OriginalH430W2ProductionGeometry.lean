import ImbalancedChen.Part5OriginalH430W2DiscardedCarriers
import ImbalancedChen.Part5OriginalH430W1WindowDictionary

/-!
SOURCE ONLY / UNCOMPILED.

Manuscript-local geometry needed to identify the already-paid W2 fresh
interiors with the EXISTING production prime-child carriers. No external
prime-distribution theorem is implemented. The extra a3<=1/s fact is
proved for the original 36 parameter records, not assumed from W2Geometry
(which does not contain that inequality). No numerical table is replayed.
-/
namespace ImbalancedChen.Part5OriginalH430W2ProductionGeometry

noncomputable section
open Set Classical
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2OriginalHalfOpenProfileCarrier P2OriginalBankThetaMassLimits
open P2OriginalChildPhysicalNormalization P2OriginalBankChildPrimeMass
open Part5OriginalH430W1WindowDictionary Part5OriginalH430W2DiscardedCarriers

/-- This is a finite rational fact about the original parameter records.
It is not an external analytic input and is not a new parent licence. -/
theorem original_a3_le_target_recip (j : Fin 36) :
    a3 (originalW2At j) ≤ b (originalW2At j) := by
  fin_cases j <;>
    norm_num [originalW2At, originalRepairedW2Bank, a3, b]

theorem singleton_lt_target_recip (j : Fin 36) (k : Fin 3) {u : ℝ}
    (hu : u ∈ W2SingletonDomain (originalW2At j) k) :
    u < b (originalW2At j) := by
  have h3 := original_a3_le_target_recip j
  rcases originalRepairedW2Bank_geometry _ (originalW2At_mem j) with
    ⟨h0,h01,h12,h23,hhalf,hb,hg6,hg7,hg8⟩
  fin_cases k
  · exact hu.2
  · exact hu.2.trans_le (h23.trans h3)
  · exact hu.2.trans_le h3

/-- Both coordinates, including the LARGER prime, stay below the target
cutoff. Checking only the smaller coordinate would not suffice. -/
theorem pair_lt_target_recip (j : Fin 36) (k : Fin 4) {x : Point}
    (hx : x ∈ W2PairDomain (originalW2At j) k) :
    ∀ i, x i < b (originalW2At j) := by
  have h3 := original_a3_le_target_recip j
  rcases originalRepairedW2Bank_geometry _ (originalW2At_mem j) with
    ⟨h0,h01,h12,h23,hhalf,hb,hg6,hg7,hg8⟩
  fin_cases k
  · rcases hx with ⟨hu,huv,hv,hgate⟩
    intro i
    fin_cases i <;> linarith
  · rcases hx with ⟨hu,hu',hv,hv'⟩
    intro i
    fin_cases i <;> linarith
  · rcases hx with ⟨hu,huv,hv⟩
    intro i
    fin_cases i <;> linarith
  · rcases hx with ⟨hu,hu',hv,hv'⟩
    intro i
    fin_cases i <;> linarith

theorem normalized_eq_relative {r N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (q : Fin r → ℕ) (i : Fin r) :
    normalizedLog N (physicalLevel N Q old) q i = relativePrime Q old (q i) := by
  calc
    _ = normalizedLog N (physicalLevel N Q old) (fun _ : Fin 1 => q i) 0 := by
      simp only [normalizedLog_coordinate]
    _ = _ := (Part5OriginalH430W1WindowDictionary.relative_eq_normalized hw).symm

theorem relative_lt_iff {N small large : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (hs : 0 < small) (hl : 0 < large) :
    relativePrime Q old small < relativePrime Q old large ↔ small < large := by
  have hR := Real.log_pos (parentWindow_logs hw).2.1
  constructor
  · intro h
    have hh : Real.log (small:ℝ) < Real.log (large:ℝ) :=
      (div_lt_div_iff_of_pos_right hR).mp h
    have hr := (Real.log_lt_log_iff (Nat.cast_pos.mpr hs) (Nat.cast_pos.mpr hl)).mp hh
    exact_mod_cast hr
  · intro h
    exact div_lt_div_of_pos_right
      (Real.log_lt_log (Nat.cast_pos.mpr hs) (by exact_mod_cast h)) hR

/-- The original finite box is derived from actual domain coordinates;
it is not an additional truncation condition on the production carrier. -/
theorem mem_box_of_relative_bounds {r N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (q : Fin r → ℕ)
    (hp : ∀ i, (q i).Prime ∧ (q i).Coprime (N*parentProduct old))
    (hx : ∀ i, (1/5:ℝ) ≤ relativePrime Q old (q i) ∧
      relativePrime Q old (q i) ≤ 1/2) :
    q ∈ box r N (physicalLevel N Q old) := by
  apply mem_actualPrimeBoxTuples_iff.mpr
  intro i
  have hn := normalized_eq_relative hw q i
  have hcoords : (1/10:ℝ) ≤ normalizedLog N (physicalLevel N Q old) q i ∧
      normalizedLog N (physicalLevel N Q old) q i < 3/5 := by
    rw [hn]
    constructor <;> linarith [(hx i).1,(hx i).2]
  have hpow := (normalizedLog_window hw.1 (parentWindow_logs hw).2.2 q
    (fun i => (hp i).1.pos) i (1/10) (3/5)).mp hcoords
  refine ⟨(hp i).1, (hp i).1.coprime_iff_not_dvd.mp
    (Nat.coprime_mul_iff_right.mp (hp i).2).1, ?_, ?_⟩
  · convert hpow.1 using 1 <;> congr 1 <;> ring
  · convert hpow.2 using 1 <;> congr 1 <;> ring

theorem product_lt_of_relative_lt_one {N q : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (hq : 0 < q)
    (hu : relativePrime Q old q < 1) : ((parentProduct old*q:ℕ):ℝ) < Q := by
  have hR := (parentWindow_logs hw).2.1
  have hqR : (q:ℝ) < residualLevel Q old := by
    apply (Real.log_lt_log_iff (Nat.cast_pos.mpr hq) (zero_lt_one.trans hR)).mp
    exact (div_lt_one (Real.log_pos hR)).mp hu
  have hd : (0:ℝ) < parentProduct old := Nat.cast_pos.mpr hw.2.1
  have he : (parentProduct old:ℝ)*residualLevel Q old = Q := by
    unfold residualLevel
    field_simp [hd.ne']
  have hh := mul_lt_mul_of_pos_left hqR hd
  rw [he] at hh
  simpa only [Nat.cast_mul] using hh

/-- Product support is for the physical append order [large,small]. -/
theorem pair_product_lt_of_sum {N small large : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (hs : 0 < small) (hl : 0 < large)
    (hu : relativePrime Q old small + relativePrime Q old large < 1) :
    ((parentProduct old*large*small:ℕ):ℝ) < Q := by
  have hR := (parentWindow_logs hw).2.1
  have hsum : (Real.log (small:ℝ)+Real.log (large:ℝ)) /
      Real.log (residualLevel Q old) < 1 := by
    simpa only [relativePrime, add_div] using hu
  have hlogs := (div_lt_one (Real.log_pos hR)).mp hsum
  have hsR : (0:ℝ) < small := Nat.cast_pos.mpr hs
  have hlR : (0:ℝ) < large := Nat.cast_pos.mpr hl
  have hprod : (large:ℝ)*(small:ℝ) < residualLevel Q old := by
    apply (Real.log_lt_log_iff (mul_pos hlR hsR) (zero_lt_one.trans hR)).mp
    rw [Real.log_mul hlR.ne' hsR.ne']
    linarith only [hlogs]
  have hd : (0:ℝ) < parentProduct old := Nat.cast_pos.mpr hw.2.1
  have he : (parentProduct old:ℝ)*residualLevel Q old = Q := by
    unfold residualLevel
    field_simp [hd.ne']
  have hh := mul_lt_mul_of_pos_left hprod hd
  rw [he] at hh
  simpa only [Nat.cast_mul, mul_assoc] using hh

theorem prime_cap_of_relative_lt_one {N q : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (hq : 0 < q)
    (hu : relativePrime Q old q < 1) : q ≤ N := by
  have hprod : parentProduct old*q ≤ N := by
    exact_mod_cast (product_lt_of_relative_lt_one hw hq hu).le.trans hw.2.2.2.1
  have hsmall : q ≤ parentProduct old*q := by
    simpa only [one_mul] using Nat.mul_le_mul_right q (show 1 ≤ parentProduct old by omega)
  exact hsmall.trans hprod

theorem physical_lt_ceiling {N q : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (j : Fin 36)
    (hceil : physicalLevel N Q old/(originalW2At j).s ≤ chi)
    (hu : relativePrime Q old q < b (originalW2At j)) : physicalPrime N q < chi := by
  have hh := mul_lt_mul_of_pos_left hu (parentWindow_logs hw).2.2
  rw [relativePrime_physical hw] at hh
  exact hh.trans_le (by simpa only [b, mul_one_div] using hceil)

theorem mem_freshSingle_iff {N d : ℕ} {L : ℝ} {p : W2Parameters} {k : Fin 3}
    {q : Fin 1 → ℕ} : q ∈ freshSingle N d L p k ↔
      q ∈ box 1 N L ∧ singleInterior p k N L q ∧ Fresh d q := by
  simp only [freshSingle, singleCarrier, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hb,_⟩,hi,hf⟩
    exact ⟨hb,hi,hf⟩
  · rintro ⟨hb,hi,hf⟩
    have hx : a0 p < normalizedLog N L q 0 ∧ normalizedLog N L q 0 < singletonTop p k := by
      simpa only [singleInterior, singleton_domain, mem_Ioo] using hi
    exact ⟨⟨hb,⟨hx.1.le,hx.2⟩⟩,hi,hf⟩

theorem mem_freshPair_iff {N d : ℕ} {L : ℝ} {p : W2Parameters} {k : Fin 4}
    {q : Fin 2 → ℕ} : q ∈ freshPair N d L p k ↔
      q ∈ box 2 N L ∧ pairInterior p k N L q ∧ Fresh d q := by
  simp only [freshPair, pairCarrier, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hb,_⟩,hi,hf⟩
    exact ⟨hb,hi,hf⟩
  · rintro ⟨hb,hi,hf⟩
    exact ⟨⟨hb,(pairHalf_partition p k _).mpr (Or.inl hi)⟩,hi,hf⟩

end
end ImbalancedChen.Part5OriginalH430W2ProductionGeometry
