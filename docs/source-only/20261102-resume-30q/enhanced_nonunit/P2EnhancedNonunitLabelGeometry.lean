import ImbalancedChen.P2EnhancedNonunitPhysicalQuadrature
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitTupleGeometry
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitSieveMultiplicity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The source below is the ordinary rough erase-one sum on O's literal
half-open, target-deleted, strictly ordered lists. It is not O's larger
Sifted(d*N) nonunit carrier. The list embedding preserves every label.
No list is identified with another list having the same product.
-/

namespace ImbalancedChen.P2EnhancedNonunitLabelGeometry
noncomputable section
open Real Finset Set Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedSwitchedUnsiftedSource P2EnhancedSwitchedTrueNormalization
open P2EnhancedUnitSourceGeometry (labels_power)
open P2SeedOmegaLiteralFibre (a0 a1 a2 a3 b)
open P2EnhancedNonunitPhysicalQuadrature
open scoped Classical BigOperators

def ordinaryNonunitWord (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) : ℝ :=
  ∑ l ∈ labels N Q d cs,
    (((roughNumbers ((N : ℝ)/(d*l.prod : ℕ)) (l.getD (l.length-2) 0)).erase 1).card : ℝ)

theorem label_data {N d : ℕ} {Q : ℝ} {cs l : List ℕ}
    (hl : l ∈ labels N Q d cs) :
    l.length = cs.length ∧ l.Pairwise (· < ·) ∧
    (∀ p ∈ l, p ∈ primeWindow N ((Q/d)^a0) ((Q/d)^b)) ∧
    l.map (secondFunctionalMotherColour ((Q/d)^a1) ((Q/d)^a2) ((Q/d)^a3)) = cs := by
  rw [labels_power] at hl
  obtain ⟨ht, hc⟩ := mem_filter.mp hl
  obtain ⟨hlen, hord, hm⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp ht
  exact ⟨hlen, hord, hm, hc⟩

theorem label_prod_pos {N d : ℕ} {Q : ℝ} {cs l : List ℕ}
    (hl : l ∈ labels N Q d cs) : 0 < l.prod := by
  apply List.prod_pos
  intro p hp
  exact (mem_primeWindow.mp ((label_data hl).2.2.1 p hp)).1.pos

theorem label_slab {N d : ℕ} {Q : ℝ} {cs l : List ℕ}
    (hR : 1 < Q/d) (hl : l ∈ labels N Q d cs) :
    ∀ p ∈ l, p ∈ primeSlabPrimes (Q/d) := by
  intro p hp
  have hw := (label_data hl).2.2.1 p hp
  exact HighUnitSource.slab_of_window hR (by norm_num [a0])
    (by norm_num [b]) hw (mem_primeWindow.mp hw).2.2.1

/-- Complete original lists, at their original length. -/
def labelEmbedding {N d : ℕ} {Q : ℝ} (hR : 1 < Q/d) (cs : List ℕ) :
    (labels N Q d cs) ↪ (Fin cs.length → primeSlabPrimes (Q/d)) where
  toFun l i := ⟨l.val.getD i 0, label_slab hR l.property _ (by
    have hi : i.val < l.val.length := by rw [(label_data l.property).1]; exact i.isLt
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi)⟩
  inj' := by
    intro l l' he
    apply Subtype.ext
    apply HighNonunit.list_eq_of_getD (label_data l.property).1 (label_data l'.property).1
    funext i
    exact congrArg Subtype.val (congr_fun he i)

theorem label_ofFn {N d : ℕ} {Q : ℝ} (hR : 1 < Q/d) (cs : List ℕ)
    (l : labels N Q d cs) :
    List.ofFn (fun i => ((labelEmbedding hR cs l i).val)) = l.val := by
  have hlen := (label_data l.property).1
  have hh : List.ofFn (fun i : Fin cs.length => l.val.getD i 0) = l.val := by
    rw [← hlen]
    have he : (fun i : Fin l.val.length => l.val.getD i 0) =
        fun i : Fin l.val.length => l.val[i.val] := by
      funext i
      exact List.getD_eq_getElem _ _ i.isLt
    rw [he]
    exact List.ofFn_getElem
  exact hh

theorem label_weight {N d : ℕ} {Q : ℝ} (hR : 1 < Q/d) (cs : List ℕ)
    (l : labels N Q d cs) :
    primeSlabWeight (Q/d) (labelEmbedding hR cs l) = 1/(l.val.prod : ℝ) := by
  have hp : (∏ i, ((labelEmbedding hR cs l i).val : ℝ)) = (l.val.prod : ℝ) := by
    rw [← label_ofFn hR cs l, Nat.cast_list_prod, List.map_ofFn, List.prod_ofFn]
    rfl
  change (∏ i, 1/((labelEmbedding hR cs l i).val : ℝ)) = _
  rw [prod_div_distrib, prod_const_one, hp]

theorem label_log_sum {N d : ℕ} {Q : ℝ} (hR : 1 < Q/d) (cs : List ℕ)
    (l : labels N Q d cs) :
    (∑ i, gridCoordinates (Q/d) (labelEmbedding hR cs l) i) =
      log (l.val.prod : ℝ)/log (Q/d) := by
  change (∑ i, log ((labelEmbedding hR cs l i).val : ℝ)/log (Q/d)) = _
  rw [← sum_div]
  congr 1
  have hp : (∏ i, ((labelEmbedding hR cs l i).val : ℝ)) = (l.val.prod : ℝ) := by
    rw [← label_ofFn hR cs l, Nat.cast_list_prod, List.map_ofFn, List.prod_ofFn]
    rfl
  rw [← hp, log_prod]
  intro i _
  have hh := (mem_primesIcc (rpow_nonneg (zero_lt_one.trans hR).le _)).mp
    (labelEmbedding hR cs l i).property
  exact_mod_cast hh.1.ne_zero

def bandLo : ℕ → ℝ
  | 0 => a0 | 1 => a1 | 2 => a2 | _ => a3
def bandHi : ℕ → ℝ
  | 0 => a1 | 1 => a2 | 2 => a3 | _ => b

theorem colour_bounds {R : ℝ} {p : ℕ}
    (hlo : R^a0 ≤ (p : ℝ)) (hhi : (p : ℝ) < R^b) :
    R^(bandLo (secondFunctionalMotherColour (R^a1) (R^a2) (R^a3) p)) ≤ (p : ℝ) ∧
    (p : ℝ) ≤ R^(bandHi (secondFunctionalMotherColour (R^a1) (R^a2) (R^a3) p)) := by
  unfold secondFunctionalMotherColour
  split_ifs with h1 h2 h3
  · exact ⟨hlo, h1.le⟩
  · exact ⟨le_of_not_gt h1, h2.le⟩
  · exact ⟨le_of_not_gt h2, h3.le⟩
  · exact ⟨le_of_not_gt h3, hhi.le⟩

theorem label_coordinate_bands {N d : ℕ} {Q : ℝ} (hR : 1 < Q/d)
    (cs : List ℕ) (l : labels N Q d cs) (i : Fin cs.length) :
    bandLo (cs.getD i 0) ≤ gridCoordinates (Q/d) (labelEmbedding hR cs l) i ∧
    gridCoordinates (Q/d) (labelEmbedding hR cs l) i ≤ bandHi (cs.getD i 0) := by
  have hi : i.val < l.val.length := by rw [(label_data l.property).1]; exact i.isLt
  have hm := (label_data l.property).2.2.1 _ (List.getElem_mem hi)
  have hp := mem_primeWindow.mp hm
  have hc := congrArg (fun xs : List ℕ => xs.getD i 0) (label_data l.property).2.2.2
  have he : secondFunctionalMotherColour ((Q/d)^a1) ((Q/d)^a2) ((Q/d)^a3)
      (l.val.getD i 0) = cs.getD i 0 := by
    simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _
      (by simpa only [List.length_map] using hi), List.getElem_map] using hc
  have hh := colour_bounds (R := Q/d) hp.2.2.1 hp.2.2.2
  rw [← List.getD_eq_getElem _ _ hi, he] at hh
  have hp0 : 0 < l.val.getD i 0 := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hp.1.pos
  exact ⟨HighNonunit.log_coordinate_lower hR hh.1,
    HighNonunit.log_coordinate_upper hR hp0 hh.2⟩

abbrev Row (m : ℕ) := Fin m ⊕ (Fin (m+1) × Bool)

def rows (m : ℕ) : Row m → Fin (m+1) → ℝ
  | .inl k => fun i => gridFaceCoeff k.castSucc i - gridFaceCoeff k.succ i
  | .inr (k, false) => fun i => -gridFaceCoeff k i
  | .inr (k, true) => gridFaceCoeff k

def wordIntercept (m : ℕ) (cs : List ℕ) : Row m → ℝ
  | .inl _ => 0
  | .inr (k, false) => -bandLo (cs.getD k 0)
  | .inr (k, true) => bandHi (cs.getD k 0)

theorem rows_nonzero (m : ℕ) (q : Row m) : ∃ i, 1 ≤ |rows m q i| := by
  cases q with
  | inl k =>
    refine ⟨k.castSucc, ?_⟩
    have h : k.castSucc ≠ k.succ := by
      intro he
      have hv := congrArg Fin.val he
      exact Nat.ne_add_one k.val hv
    simp [rows, gridFaceCoeff, h]
  | inr p =>
    rcases p with ⟨k, b⟩
    cases b <;> exact ⟨k, by simp [rows, gridFaceCoeff]⟩

theorem rows_iff (m : ℕ) (cs : List ℕ) (t : Fin (m+1) → ℝ) :
    (∀ q, (∑ i, rows m q i * t i) ≤ wordIntercept m cs q) ↔
      (∀ k : Fin m, t k.castSucc ≤ t k.succ) ∧
      (∀ k, bandLo (cs.getD k 0) ≤ t k ∧ t k ≤ bandHi (cs.getD k 0)) := by
  simp only [Sum.forall, Prod.forall, Bool.forall_bool, rows, wordIntercept,
    sub_mul, sum_sub_distrib, neg_mul, sum_neg_distrib, gridFaceCoeff_sum,
    sub_nonpos, neg_le_neg_iff]
  tauto

/-- Only an upper-domain inclusion is asserted. All strict endpoints,
target deletion and strict ordering remain in the source labels. -/
theorem label_rows {N d m : ℕ} {Q : ℝ} (hR : 1 < Q/d)
    (cs : List ℕ) (hlen : cs.length = m+1) (l : labels N Q d cs) :
    let f : Fin (m+1) → primeSlabPrimes (Q/d) :=
      fun i => labelEmbedding hR cs l (Fin.cast hlen.symm i)
    ∀ q, (∑ i, rows m q i * gridCoordinates (Q/d) f i) ≤ wordIntercept m cs q := by
  dsimp only
  apply (rows_iff m cs _).mpr
  constructor
  · intro k
    have hk : k.val < l.val.length := by rw [(label_data l.property).1, hlen]; omega
    have hk' : k.val+1 < l.val.length := by rw [(label_data l.property).1, hlen]; omega
    have ho := (List.pairwise_iff_getElem.mp (label_data l.property).2.1)
      k.val (k.val+1) hk hk' (by omega)
    change log (l.val.getD k.val 0 : ℝ)/log (Q/d) ≤
      log (l.val.getD (k.val+1) 0 : ℝ)/log (Q/d)
    rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk']
    apply div_le_div_of_nonneg_right _ (log_pos hR).le
    apply log_le_log
    · exact_mod_cast (mem_primeWindow.mp ((label_data l.property).2.2.1 _
        (List.getElem_mem hk))).1.pos
    · exact_mod_cast ho.le
  · intro k
    simpa only [Fin.val_cast] using label_coordinate_bands hR cs l (Fin.cast hlen.symm k)

/-- Literal nonunit word as a scalar sum; all occurrences are later
aggregated with the original list, never via a Finset of colour words. -/
def ordinaryNonunitGamma (N : ℕ) (Q : ℝ) (d i : ℕ) : ℝ :=
  ((secondFunctionalMotherGammaWords i).map (ordinaryNonunitWord N Q d)).sum

theorem all_nonunit_occurrences (N : ℕ) (Q : ℝ) (d : ℕ) :
    (∑ j : Fin 13, ordinaryNonunitGamma N Q d (9+j.val)) =
      ordinaryNonunitWord N Q d [1,1,1] + 2*ordinaryNonunitWord N Q d [1,1,2] +
      2*ordinaryNonunitWord N Q d [1,2,2] + ordinaryNonunitWord N Q d [2,2,2] +
      ordinaryNonunitWord N Q d [1,1,3] + ordinaryNonunitWord N Q d [0,0,3] +
      ordinaryNonunitWord N Q d [0,1,2] + ordinaryNonunitWord N Q d [0,1,3] +
      ordinaryNonunitWord N Q d [0,2,2] + ordinaryNonunitWord N Q d [0,2,3] +
      ordinaryNonunitWord N Q d [0,3,3] + ordinaryNonunitWord N Q d [1,2,3] +
      ordinaryNonunitWord N Q d [2,2,2,2] + ordinaryNonunitWord N Q d [2,2,2,3] +
      ordinaryNonunitWord N Q d [2,2,3,3] + ordinaryNonunitWord N Q d [1,3,3,3] +
      ordinaryNonunitWord N Q d [2,3,3,3,3] + ordinaryNonunitWord N Q d [3,3,3,3,3,3] :=
  all_switched_multiplicities (ordinaryNonunitWord N Q d)

end
end ImbalancedChen.P2EnhancedNonunitLabelGeometry
