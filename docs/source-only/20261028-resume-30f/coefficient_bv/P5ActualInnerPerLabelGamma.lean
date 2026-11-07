import ImbalancedChen.P5ActualInnerMeshSeparatedGamma
import ImbalancedChen.P5ActualNormalizedPrimeLabelCoefficient

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal ORIGINAL per-label normalization on the SAME original ordinary
fine alphabet and the SAME computed endpoint occurrence assignment.
Every denominator below is prod_label (count label)!, never a total-slot
factorial. The actual inner reconstruction's injective fine word makes
each group word nodup. The raw Cartesian coefficient is then one-bounded
by the existing ORIGINAL label-factorial theorem with singleton blocks.

The input is a genuine independently defined presievedCoefficient source,
not a new candidate declared equal to it. Its original residual level,
common small-beta level, marked prefix and complete q remain unchanged.
The actual all16 fine-source dictionary and full marked/common-alphabet
capacity/SW licenses are separate ports, not assumptions of this file.
-/

namespace ImbalancedChen.P5Z.ActualInnerPerLabelGamma
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen
open All16FineMeshGateScalar ActualAll16UnrestrictedResidualConvolution
open OriginalOrdinaryCommonBetaModel PresievedRoughGateMeshReserve

def multiplicity {ι : Type*} [DecidableEq ι] (word : List ι) : ℕ :=
  ∏ i ∈ word.toFinset, (word.count i).factorial

theorem multiplicity_pos {ι : Type*} [DecidableEq ι] (word : List ι) :
    0 < multiplicity word := Finset.prod_pos (fun i hi => Nat.factorial_pos _)

theorem count_one_of_nodup {ι : Type*} [DecidableEq ι] :
    ∀ (word : List ι), word.Nodup → ∀ i ∈ word, word.count i = 1 := by
  intro word
  induction word with
  | nil => simp
  | cons a word ih =>
    intro hnd i hi
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hi with rfl | hi
    · simp [List.count_eq_zero.mpr ha]
    · have hne : a ≠ i := fun h => ha (h.symm ▸ hi)
      simpa [hne, Ne.symm hne] using ih ht i hi

theorem multiplicity_eq_one_of_nodup {ι : Type*} [DecidableEq ι]
    (word : List ι) (hnd : word.Nodup) : multiplicity word = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  rw [count_one_of_nodup word hnd i (List.mem_toFinset.mp hi)]
  norm_num

/-- The manuscript coefficient with its ORIGINAL product-of-label-
factorials denominator. Defined on every integer before support tests. -/
def gamma {ι : Type*} [DecidableEq ι] (B : ι → Finset ℕ)
    (word : List ι) (d : ℕ) : ℝ :=
  (actualPrimeTupleCoefficient (actualPrimeSlotBox B word) d : ℝ) /
    (multiplicity word : ℝ)

theorem singleton_blocks_word {ι : Type*} (word : List ι) :
    actualPrimeLabelBlocksWord (word.map (fun i => (i, 1))) = word := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    simpa only [List.map_cons, actualPrimeLabelBlocksWord,
      List.flatMap_cons, List.replicate_one, List.singleton_append] using congrArg (List.cons i) ih

/-- Actual injective fine words, not an assumed gamma bound, give the
raw full Cartesian one-bound including every off-support integer. -/
theorem gamma_abs_le_one_of_nodup {ι : Type*} [DecidableEq ι]
    (B : ι → Finset ℕ) (word : List ι) (hnd : word.Nodup)
    (hp : ∀ i, ∀ p ∈ B i, Nat.Prime p)
    (hdis : ∀ i j, i ≠ j → Disjoint (B i) (B j)) (d : ℕ) :
    |gamma B word d| ≤ 1 := by
  let blocks := word.map (fun i => (i, 1))
  have hprime : ∀ b ∈ blocks, ∀ p ∈ B b.1, Nat.Prime p := by
    intro b hb p hp'
    exact hp b.1 p hp'
  have hpair : blocks.Pairwise (fun b c => Disjoint (B b.1) (B c.1)) := by
    apply List.pairwise_map.mpr
    change word.Pairwise (· ≠ ·) at hnd
    exact hnd.imp (fun h => hdis _ _ h)
  have hraw := ActualNormalizedPrimeLabelCoefficient.raw_coefficient_le_label_factorial
    B blocks hprime hpair d
  have hM : actualPrimeLabelBlocksFactorial blocks = 1 := by
    simp [blocks, actualPrimeLabelBlocksFactorial, List.map_map, Function.comp_def]
  have hraw1 : actualPrimeTupleCoefficient (actualPrimeSlotBox B word) d ≤ 1 := by
    rw [hM] at hraw
    simpa only [blocks, singleton_blocks_word] using hraw
  rw [gamma, multiplicity_eq_one_of_nodup word hnd, Nat.cast_one, div_one,
    abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast hraw1

/-- A literal three-convolution identity with ORIGINAL M1 M2 M3.
There is no slot-count factorial hidden in the scalar. -/
theorem three_group_sum_per_label {ι : Type*} [DecidableEq ι]
    (B : ι → Finset ℕ) (word1 word2 word3 : List ι) (c : ℝ) (H : ℕ → ℝ) :
    (∑ ps ∈ actualPrimeSlotBox B word1, ∑ qs ∈ actualPrimeSlotBox B word2,
      ∑ rs ∈ actualPrimeSlotBox B word3, c * H (ps.prod * qs.prod * rs.prod)) =
    ∑ a ∈ (actualPrimeSlotBox B word1).image List.prod,
      ∑ b ∈ (actualPrimeSlotBox B word2).image List.prod,
        ∑ d ∈ (actualPrimeSlotBox B word3).image List.prod,
          (c * (multiplicity word1 : ℝ) * (multiplicity word2 : ℝ) *
            (multiplicity word3 : ℝ)) * gamma B word1 a * gamma B word2 b *
              gamma B word3 d * H (a * b * d) := by
  have hM1 : (multiplicity word1 : ℝ) ≠ 0 := by exact_mod_cast (multiplicity_pos word1).ne'
  have hM2 : (multiplicity word2 : ℝ) ≠ 0 := by exact_mod_cast (multiplicity_pos word2).ne'
  have hM3 : (multiplicity word3 : ℝ) ≠ 0 := by exact_mod_cast (multiplicity_pos word3).ne'
  simp_rw [actualPrimeTuple_sum_by_product, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro d hd
  dsimp only [gamma]
  field_simp [hM1, hM2, hM3] <;> ring

theorem computed_groups_nodup {r m : ℕ} (N : ℕ) (j : Grid r m)
    (hj : Function.Injective j) (D A : ℝ) (yz : Bool) :
    let out := computedGroups D A yz (meshUpper N m) (List.ofFn j)
    out.1.Nodup ∧ out.2.1.Nodup ∧ out.2.2.Nodup := by
  have hnd := (computedGroups_partition D A yz (meshUpper N m) (List.ofFn j)).nodup_iff.mpr
    (List.nodup_ofFn.mpr hj)
  obtain ⟨h1, h23, _⟩ := List.nodup_append.mp hnd
  obtain ⟨h2, h3, _⟩ := List.nodup_append.mp h23
  exact ⟨h1, h2, h3⟩

theorem mesh_alphabet_disjoint {N cap m : ℕ} (hN : 1 < N) (w Z : ℝ)
    (i j : Fin (m + 1)) (hij : i ≠ j) :
    Disjoint (meshPrimeAlphabet N cap w Z m i) (meshPrimeAlphabet N cap w Z m j) := by
  rw [mesh_alphabet_eq_original_intersection, mesh_alphabet_eq_original_intersection]
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hd := actualPrimeFineLabelFinset_disjoint (Nat.le_of_lt hN)
    (show (0 : ℝ) ≤ 1 / (m + 1 : ℝ) by positivity) hval
  exact Finset.disjoint_left.mpr (fun p hp hq => Finset.disjoint_left.mp hd
    (Finset.mem_inter.mp hp).2 (Finset.mem_inter.mp hq).2)

def meshGamma (N cap m : ℕ) (w Z : ℝ) (word : List (Fin (m + 1))) : ℕ → ℝ :=
  gamma (meshPrimeAlphabet N cap w Z m) word

theorem meshGamma_abs_le_one {N cap m : ℕ} (hN : 1 < N) (w Z : ℝ)
    (word : List (Fin (m + 1))) (hnd : word.Nodup) (d : ℕ) :
    |meshGamma N cap m w Z word d| ≤ 1 := by
  exact gamma_abs_le_one_of_nodup _ word hnd
    (fun _ _ hp => (mem_roughPrimeFinset.mp (ActualInnerMeshSeparatedGamma.mesh_prime_rough hp)).2.1)
    (mesh_alphabet_disjoint hN w Z) d

def attachedGamma (N cap m r : ℕ) (w Z B : ℝ) (word : List (Fin (m + 1))) : ℕ → ℝ :=
  smallRoughRho (actualSmallRosserSupport N cap w)
    (ActualInnerMeshSeparatedGamma.groupSupport N cap m w Z word)
    (meshGamma N cap m w Z word) (rawBetaWeight N cap r w B) (rawBetaWeight N cap r w B)

theorem attachedGamma_abs_le_one {N cap m r : ℕ} (hN : 1 < N) (w Z B : ℝ)
    (word : List (Fin (m + 1))) (hnd : word.Nodup) (q : ℕ) :
    |attachedGamma N cap m r w Z B word q| ≤ 1 := by
  by_cases hq : q ∈ ActualInnerMeshSeparatedGamma.attachedSupport N cap m w Z word
  · obtain ⟨⟨e, d⟩, hed, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨he, hd⟩ := Finset.mem_product.mp hed
    exact abs_smallRoughRho_mul_le_one
      (fun a ha => actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
      (fun d hd => ActualInnerMeshSeparatedGamma.groupSupport_rough w Z word hd)
      (meshGamma N cap m w Z word) _ _
      (fun d _ => meshGamma_abs_le_one hN w Z word hnd d)
      (fun e _ => raw_beta_abs_le_one N cap r w B e)
      (fun e _ => raw_beta_abs_le_one N cap r w B e) he hd
  · rw [attachedGamma, smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hq]
    norm_num

theorem attachedGamma_fullq_sum (N cap m r : ℕ) (w Z B : ℝ)
    (word : List (Fin (m + 1))) (H : ℕ → ℝ) :
    (∑ q ∈ ActualInnerMeshSeparatedGamma.attachedSupport N cap m w Z word,
      attachedGamma N cap m r w Z B word q * H q) =
    ∑ e ∈ actualSmallRosserSupport N cap w,
      ∑ d ∈ ActualInnerMeshSeparatedGamma.groupSupport N cap m w Z word,
        meshGamma N cap m w Z word d * rawBetaWeight N cap r w B e * H (e * d) := by
  rw [ActualInnerMeshSeparatedGamma.attachedSupport, attachedGamma, sum_smallRoughRho_mul
    (fun a ha => actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
    (fun d hd => ActualInnerMeshSeparatedGamma.groupSupport_rough w Z word hd)]
  rw [smallRoughPairs, Finset.sum_product]
  simp only [smallRoughPairCoefficient, signAttachedCoefficient, ite_self]

def atomScalar {r m : ℕ} (j : Grid r m) (out : List (Fin (m + 1)) ×
    List (Fin (m + 1)) × List (Fin (m + 1))) : ℝ :=
  (-1 : ℝ) ^ r *
    ((multiplicity out.1 : ℝ) * (multiplicity out.2.1 : ℝ) * (multiplicity out.2.2 : ℝ) /
      (multiplicity (List.ofFn j) : ℝ))

/-- On the ACTUAL injective fine word all ORIGINAL group and full-word
label factorials equal one. This does not use a total-slot denominator. -/
theorem computed_atomScalar_eq_sign {r m N : ℕ} (j : Grid r m)
    (hj : Function.Injective j) (D A : ℝ) (yz : Bool) :
    let out := computedGroups D A yz (meshUpper N m) (List.ofFn j)
    atomScalar j out = (-1 : ℝ) ^ r := by
  obtain ⟨h1, h2, h3⟩ := computed_groups_nodup N j hj D A yz
  simp only [atomScalar, multiplicity_eq_one_of_nodup _ h1,
    multiplicity_eq_one_of_nodup _ h2, multiplicity_eq_one_of_nodup _ h3,
    multiplicity_eq_one_of_nodup _ (List.nodup_ofFn.mpr hj), Nat.cast_one,
    one_mul, mul_one, div_one]

theorem computed_atomScalar_abs {r m N : ℕ} (j : Grid r m)
    (hj : Function.Injective j) (D A : ℝ) (yz : Bool) :
    let out := computedGroups D A yz (meshUpper N m) (List.ofFn j)
    |atomScalar j out| = 1 := by
  rw [computed_atomScalar_eq_sign j hj D A yz]
  simp

theorem actual_inner_fixed_e_per_label {r N cap m e : ℕ} (hN : 1 < N)
    (w Z ell B : ℝ) (hL : 1 < (N : ℝ) ^ ell)
    {j : Grid r m} (hj : j ∈ innerCells r 0 1 ell m)
    (he : e ∈ actualSmallRosserSupport N cap w)
    (D A : ℝ) (yz : Bool) (prefix : ℕ) (F : ℕ → ℝ) :
    let out := computedGroups D A yz (meshUpper N m) (List.ofFn j)
    (1 / (multiplicity (List.ofFn j) : ℝ)) *
      (∑ ps ∈ meshPrimeBox N cap w Z m j,
        presievedCoefficient N cap w Z ((N : ℝ) ^ ell) B (e * ps.prod) *
          F (prefix * (e * ps.prod))) =
    ∑ a ∈ ActualInnerMeshSeparatedGamma.groupSupport N cap m w Z out.1,
      ∑ b ∈ ActualInnerMeshSeparatedGamma.groupSupport N cap m w Z out.2.1,
        ∑ d ∈ ActualInnerMeshSeparatedGamma.groupSupport N cap m w Z out.2.2,
          atomScalar j out * rawBetaWeight N cap r w B e * meshGamma N cap m w Z out.1 a *
            meshGamma N cap m w Z out.2.1 b * meshGamma N cap m w Z out.2.2 d *
              F (prefix * (e * (a * b * d))) := by
  dsimp only
  let out := computedGroups D A yz (meshUpper N m) (List.ofFn j)
  have hsource : (∑ ps ∈ meshPrimeBox N cap w Z m j,
      presievedCoefficient N cap w Z ((N : ℝ) ^ ell) B (e * ps.prod) * F (prefix * (e * ps.prod))) =
      ∑ ps ∈ meshPrimeBox N cap w Z m j,
        (-1 : ℝ) ^ r * rawBetaWeight N cap r w B e * F (prefix * (e * ps.prod)) := by
    apply Finset.sum_congr rfl
    intro ps hps
    rw [ActualInnerMeshSeparatedGamma.inner_list_actual_presieved_value hN w Z ell B hL hj he ps hps]
  rw [hsource]
  have hperm := computedGroups_partition D A yz (meshUpper N m) (List.ofFn j)
  rw [actualPrimeSlotBox_product_sum_perm (meshPrimeAlphabet N cap w Z m) hperm.symm,
    actualPrimeSlotBox_product_sum_append]
  simp_rw [actualPrimeSlotBox_product_sum_append, Finset.mul_sum]
  have hnorm := three_group_sum_per_label (meshPrimeAlphabet N cap w Z m)
    out.1 out.2.1 out.2.2 ((1 / (multiplicity (List.ofFn j) : ℝ)) *
      ((-1 : ℝ) ^ r * rawBetaWeight N cap r w B e)) (fun n => F (prefix * (e * n)))
  calc
    _ = ∑ ps ∈ actualPrimeSlotBox (meshPrimeAlphabet N cap w Z m) out.1,
        ∑ qs ∈ actualPrimeSlotBox (meshPrimeAlphabet N cap w Z m) out.2.1,
          ∑ rs ∈ actualPrimeSlotBox (meshPrimeAlphabet N cap w Z m) out.2.2,
            ((1 / (multiplicity (List.ofFn j) : ℝ)) *
              ((-1 : ℝ) ^ r * rawBetaWeight N cap r w B e)) *
                F (prefix * (e * (ps.prod * qs.prod * rs.prod))) := by
      apply Finset.sum_congr rfl
      intro ps hps
      apply Finset.sum_congr rfl
      intro qs hqs
      apply Finset.sum_congr rfl
      intro rs hrs
      ring
    _ = _ := by
      rw [hnorm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      dsimp only [atomScalar, meshGamma]
      ring

/-- Exact same ordinary source as the E inner reconstruction, now with
the original M1*M2*M3/M_all and beta only in the third factor. -/
theorem actual_inner_beta_per_label {r N cap m : ℕ} (hN : 1 < N)
    (w Z ell B : ℝ) (hL : 1 < (N : ℝ) ^ ell)
    {j : Grid r m} (hj : j ∈ innerCells r 0 1 ell m)
    (D A : ℝ) (yz : Bool) (prefix : ℕ) (F : ℕ → ℝ) :
    let out := computedGroups D A yz (meshUpper N m) (List.ofFn j)
    (∑ e ∈ actualSmallRosserSupport N cap w,
      (1 / (multiplicity (List.ofFn j) : ℝ)) *
        (∑ ps ∈ meshPrimeBox N cap w Z m j,
          presievedCoefficient N cap w Z ((N : ℝ) ^ ell) B (e * ps.prod) *
            F (prefix * (e * ps.prod)))) =
    ∑ a ∈ ActualInnerMeshSeparatedGamma.groupSupport N cap m w Z out.1,
      ∑ b ∈ ActualInnerMeshSeparatedGamma.groupSupport N cap m w Z out.2.1,
        ∑ q3 ∈ ActualInnerMeshSeparatedGamma.attachedSupport N cap m w Z out.2.2,
          atomScalar j out * meshGamma N cap m w Z out.1 a * meshGamma N cap m w Z out.2.1 b *
            attachedGamma N cap m r w Z B out.2.2 q3 * F (prefix * (a * b * q3)) := by
  dsimp only
  let out := computedGroups D A yz (meshUpper N m) (List.ofFn j)
  have hfixed (e : ℕ) (he : e ∈ actualSmallRosserSupport N cap w) :=
    actual_inner_fixed_e_per_label hN w Z ell B hL hj he D A yz prefix F
  apply Eq.trans (Finset.sum_congr rfl hfixed)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  have hpush := attachedGamma_fullq_sum N cap m r w Z B out.2.2
    (fun q3 => atomScalar j out * meshGamma N cap m w Z out.1 a *
      meshGamma N cap m w Z out.2.1 b * F (prefix * (a * b * q3)))
  calc
    _ = ∑ e ∈ actualSmallRosserSupport N cap w,
        ∑ d ∈ ActualInnerMeshSeparatedGamma.groupSupport N cap m w Z out.2.2,
          meshGamma N cap m w Z out.2.2 d * rawBetaWeight N cap r w B e *
            (atomScalar j out * meshGamma N cap m w Z out.1 a * meshGamma N cap m w Z out.2.1 b *
              F (prefix * (a * b * (e * d)))) := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro d hd
      rw [show a * b * (e * d) = e * (a * b * d) by ring]
      ring
    _ = _ := by
      rw [← hpush]
      apply Finset.sum_congr rfl
      intro q3 hq3
      ring

end
end ImbalancedChen.P5Z.ActualInnerPerLabelGamma
