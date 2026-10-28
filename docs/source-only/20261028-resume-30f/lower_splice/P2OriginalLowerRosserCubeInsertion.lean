import ImbalancedChen.P2EnhancedNativeLowerConditionalPrefix
import ImbalancedChen.OrdinaryRosserContinuation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A concrete provider-prefix iff for the actual even-cube lower source.
No Rosser admissibility equivalence is assumed. The separated finite-set
filter theorem is reused to derive the new minimum's exact cubic test.
-/
namespace ImbalancedChen.P2OriginalLowerRosserCubeInsertion
noncomputable section
open scoped Classical BigOperators
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
open P2EnhancedNativeLowerConditionalPrefix

theorem lower_set_cons_iff (Q : ℝ) (q : ℕ) (pre : List ℕ)
    (hsort : (q::pre).Pairwise (· < ·)) :
    LowerAdmissibleSet Q (q::pre).toFinset ↔
      LowerAdmissibleSet Q pre.toFinset ∧
        (Even (pre.length+1) → (pre.prod : ℝ) * (q : ℝ)^3 < Q) := by
  have hnd : pre.Nodup := (List.pairwise_cons.mp hsort).2.nodup
  have hA : ∀ p ∈ pre.toFinset, (q : ℝ)+1 ≤ (p : ℝ) := by
    intro p hp
    have hqp : q < p := (List.pairwise_cons.mp hsort).1 p (List.mem_toFinset.mp hp)
    exact_mod_cast (show q+1 ≤ p by omega)
  have hB : ∀ p ∈ ({q} : Finset ℕ), (p : ℝ) < (q : ℝ)+1 := by
    intro p hp
    have hpq : p=q := Finset.mem_singleton.mp hp
    subst p
    linarith
  have hh := lowerAdmissible_union_iff (A := pre.toFinset) (B := {q})
    (w := (q : ℝ)+1) (L := Q) hA hB
  have hp : pre.toFinset.prod id = pre.prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p) hnd
  simpa [Finset.union_singleton, List.toFinset_cons, hp,
    List.toFinset_card_of_nodup hnd, pow_succ, mul_assoc] using hh

/-- Exact total-product and lower-prefix tests at one minimum insertion.
The inactive parity is proved from the retained original provider lemma;
the active parity is exactly the newly displayed cube. -/
theorem ordinary_lower_cons_iff (Q : ℝ) (q : ℕ) (pre : List ℕ)
    (hq : q.Prime) (hqQ : (q : ℝ) < Q)
    (hsort : (q::pre).Pairwise (· < ·)) :
    ordinaryRosserPrefixAdmissible true Q (q::pre) ↔
      ordinaryRosserPrefixAdmissible true Q pre ∧
        (Even (pre.length+1) → (pre.prod : ℝ) * (q : ℝ)^3 < Q) := by
  have hnd : pre.Nodup := (List.pairwise_cons.mp hsort).2.nodup
  have hnot : q ∉ pre.toFinset := by
    intro hqmem
    exact (lt_irrefl q) ((List.pairwise_cons.mp hsort).1 q
      (List.mem_toFinset.mp hqmem))
  have hmin : ∀ p ∈ pre.toFinset, q ≤ p :=
    fun p hp => ((List.pairwise_cons.mp hsort).1 p (List.mem_toFinset.mp hp)).le
  have hp : pre.toFinset.prod id = pre.prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p) hnd
  constructor
  · intro hn
    have ho := ordinaryRosserPrefixAdmissible_tail true Q q pre hq hsort hn
    exact ⟨ho, ((lower_set_cons_iff Q q pre hsort).mp hn.2).2⟩
  · rintro ⟨ho,hcube⟩
    have hset := (lower_set_cons_iff Q q pre hsort).mpr ⟨ho.2,hcube⟩
    refine ⟨?_,hset⟩
    by_cases heven : Even pre.length
    · have hevencard : Even pre.toFinset.card := by
        simpa only [List.toFinset_card_of_nodup hnd] using heven
      have hprod := prod_insert_min_lt_of_even hnot hq hqQ hmin ho.2 hevencard
      simpa only [Finset.prod_insert hnot, hp, List.prod_cons,
        Nat.cast_mul] using hprod
    · have hnewEven : Even (pre.length+1) := by
        simpa only [Nat.even_add_one] using heven
      have hc := hcube hnewEven
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_le
      have hqp : (q : ℝ) ≤ (q : ℝ)^3 := by
        have hh := mul_nonneg (sub_nonneg.mpr hq1) (sq_nonneg (q : ℝ))
        nlinarith
      have hprodle := mul_le_mul_of_nonneg_left hqp (Nat.cast_nonneg pre.prod :
        (0 : ℝ) ≤ pre.prod)
      simp only [List.prod_cons, Nat.cast_mul]
      nlinarith

theorem ordinary_lower_level_mono {Q R : ℝ} (hQR : Q ≤ R) (pre : List ℕ)
    (hpre : ordinaryRosserPrefixAdmissible true Q pre) :
    ordinaryRosserPrefixAdmissible true R pre := by
  refine ⟨hpre.1.trans_le hQR, ?_⟩
  intro p hp heven
  exact (hpre.2 p hp heven).trans_le hQR

end
end ImbalancedChen.P2OriginalLowerRosserCubeInsertion
