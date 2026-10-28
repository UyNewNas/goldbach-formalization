import ImbalancedChen.P5All16SquarefreeRawProjection
import ImbalancedChen.ActualPrimeDisjointLabelProducts
import ImbalancedChen.P5ActualNormalizedPrimeLabelCoefficient

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual all16 retained coefficient is reindexed by its computed weakly
ordered half-open owner word and run-length label blocks.  Each block key
has a WHOLE original Cartesian prime box, with original target exclusions,
cutoffs and half-open endpoints.  Its true retained fibre equals exactly
the squarefree products in that box passing the original raw upper gate.
The reverse inclusion and key identity are proved from unique prime
factorization and weak label order, not provided as chart-cover premises.

The full atom sum has the literal scalar beta_k(e)/M_res.  Its Mobius factor
is mu(rough product d), never mu(marked q * independent test product).  The
marked prefix and arbitrary signed count/mean test remain outside M_res.
Repeated rough prime words are retained in the full atom box and have zero
literal Mobius weight before absolute values.  No extra marked factorial
or later group factorial appears.

This exact block regrouping retains the original coupled upper gate inside
each atom's full-product test.  Gate-uniform fine subdivisions, three-group
analytic licences, absolute collision savings and the PP estimate remain
separate obligations.  The current two-label dictionary is not a proof for
an arbitrarily fine alphabet chosen by a later analytic caller.
-/

namespace ImbalancedChen.P5Z.All16SortedBlockAtomScalar
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryPresievedSigma
open OriginalPresievedRoughPrimeSlots OriginalPresievedRoughSlotCoefficient
open OriginalJointPresievedCompiler CanonicalTwoFineResidualWord
open TwoFineUnrestrictedOwnerAtoms All16CanonicalFineWordNoZGuard
open ActualAll16UnrestrictedResidualConvolution All16PhysicalOwnerDiscrepancy
open All16SquarefreeRawProjection
open U1011OriginalSixteenArithmeticProducts

/-- Computed sorted block keys of the genuine retained rough family. -/
def blockKeys (N cap : ℕ) (w Z L : ℝ) : Finset (List (ℕ × ℕ)) :=
  (fixedRoughSupport (ordinaryRetainOdd L) N cap w Z).image
    (canonicalFineBlocks N cap w Z)

def blockBox (N cap : ℕ) (w Z : ℝ) (blocks : List (ℕ × ℕ)) : Finset (List ℕ) :=
  actualPrimeSlotBox (twoFineBox N cap w Z) (actualPrimeLabelBlocksWord blocks)

def blockProducts (N cap : ℕ) (w Z : ℝ) (blocks : List (ℕ × ℕ)) : Finset ℕ :=
  (blockBox N cap w Z blocks).image List.prod

def blockActiveProducts (N cap : ℕ) (w Z L : ℝ)
    (blocks : List (ℕ × ℕ)) : Finset ℕ :=
  (blockProducts N cap w Z blocks).filter (fun d => Squarefree d ∧ rawUpperGate L d)

/-- The original common beta and the original residual label factorial
are fixed outside the entire Cartesian atom sum. -/
def blockAtomLinear (N cap : ℕ) (w Z L B : ℝ) (e : ℕ)
    (blocks : List (ℕ × ℕ)) (H : ℕ → ℝ) : ℝ :=
  (rawBetaWeight N cap (actualPrimeLabelBlocksWord blocks).length w B e /
    (actualPrimeLabelBlocksFactorial blocks : ℝ)) *
      ∑ ps ∈ blockBox N cap w Z blocks,
        (ArithmeticFunction.moebius ps.prod : ℝ) *
          (if rawUpperGate L ps.prod then H ps.prod else 0)

theorem twoFineBox_prime {N cap i p : ℕ} {w Z : ℝ}
    (hp : p ∈ twoFineBox N cap w Z i) : Nat.Prime p :=
  (mem_roughPrimeFinset.mp (twoFineBox_subset_rough hp)).2.1

theorem twoFineBox_disjoint {N cap i j : ℕ} {w Z : ℝ} (hij : i ≠ j) :
    Disjoint (twoFineBox N cap w Z i) (twoFineBox N cap w Z j) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact hij ((twoFineBox_owner_eq hp).symm.trans (twoFineBox_owner_eq hq))

/-- A real block key supplies its order and reconstruction internally. -/
theorem block_key_word_order {N cap : ℕ} {w Z L : ℝ}
    {blocks : List (ℕ × ℕ)} (hb : blocks ∈ blockKeys N cap w Z L) :
    (actualPrimeLabelBlocksWord blocks).Pairwise (· ≥ ·) ∧
      actualPrimeFineLabelBlocksOfWord (actualPrimeLabelBlocksWord blocks) = blocks ∧
      blocks.Pairwise (fun b c => b.1 ≠ c.1) := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hb
  refine ⟨?_, ?_, canonical_fine_blocks_distinct N cap w Z d⟩
  · rw [canonical_fine_blocks_word]
    exact canonical_fine_word_weak_order N cap w Z d
  · rw [canonical_fine_blocks_word]
    rfl

/-- Literal product of the within-label factorials, as computed from
the actual sorted block key; not the total-rank factorial. -/
theorem block_key_factorial_eq_ownerMres {N cap : ℕ} {w Z L : ℝ}
    {blocks : List (ℕ × ℕ)} (hb : blocks ∈ blockKeys N cap w Z L) :
    actualPrimeLabelBlocksFactorial blocks = ownerMres (actualPrimeLabelBlocksWord blocks) := by
  have hkey := block_key_word_order hb
  have h := actualPrimeFineLabelBlocksOfWord_factorial
    (actualPrimeLabelBlocksWord blocks) hkey.1
  rw [hkey.2.1] at h
  simpa only [ownerMres] using h

/-- The actual sorted block's original M_label-normalized convolution
is one-bounded on ALL integers, including repeated-prime products. -/
theorem block_gamma_abs_le_one {N cap : ℕ} {w Z L : ℝ}
    {blocks : List (ℕ × ℕ)} (hb : blocks ∈ blockKeys N cap w Z L) (d : ℕ) :
    |(actualPrimeTupleCoefficient (blockBox N cap w Z blocks) d : ℝ) /
      (actualPrimeLabelBlocksFactorial blocks : ℝ)| ≤ 1 := by
  have hdis := (block_key_word_order hb).2.2.imp
    (fun h => twoFineBox_disjoint (N := N) (cap := cap) (w := w) (Z := Z) h)
  exact ActualNormalizedPrimeLabelCoefficient.gamma_abs_le_one
    (twoFineBox N cap w Z) blocks (fun b hb p hp => twoFineBox_prime hp) hdis d

/-- A squarefree product from ANY original two-label word that passes
the literal gate is a true retained modulus. -/
theorem block_product_retained {N cap d : ℕ} {w Z L : ℝ}
    (hL : 1 < L) {blocks : List (ℕ × ℕ)}
    (hd : d ∈ blockProducts N cap w Z blocks)
    (hsf : Squarefree d) (hg : rawUpperGate L d) :
    d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z := by
  obtain ⟨ps, hps, hprod⟩ := Finset.mem_image.mp hd
  have hlen := actualPrimeSlotBox_length (twoFineBox N cap w Z)
    (actualPrimeLabelBlocksWord blocks) ps hps
  have hrough : ∀ p ∈ ps, p ∈ roughPrimeFinset N cap w Z :=
    actualPrimeSlotBox_forall (twoFineBox N cap w Z)
      (actualPrimeLabelBlocksWord blocks) (fun p => p ∈ roughPrimeFinset N cap w Z)
      (fun i hi p hp => twoFineBox_subset_rough hp) ps hps
  have hraw : d ∈ residualProducts N cap (actualPrimeLabelBlocksWord blocks).length w Z := by
    apply Finset.mem_image.mpr
    exact ⟨ps, (mem_actualPrimeSlotBox_replicate _ _ ps).mpr ⟨hlen, hrough⟩, hprod⟩
  exact (raw_squarefree_gated_product_retained hL hraw hsf hg).1

/-- The original sorted owner block of every active product is exactly
its block-box key.  Unique factorization supplies the owner-word Perm;
weak order makes the two words literally equal. -/
theorem active_product_block_key {N cap d : ℕ} {w Z L : ℝ}
    (hL : 1 < L) {blocks : List (ℕ × ℕ)}
    (hb : blocks ∈ blockKeys N cap w Z L)
    (hd : d ∈ blockActiveProducts N cap w Z L blocks) :
    d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z ∧
      canonicalFineBlocks N cap w Z d = blocks := by
  obtain ⟨hproduct, hsf, hg⟩ := Finset.mem_filter.mp hd
  have hret := block_product_retained hL hproduct hsf hg
  obtain ⟨ps, hps, hprod⟩ := Finset.mem_image.mp hproduct
  have hprime : ∀ p ∈ ps, Nat.Prime p :=
    actualPrimeSlotBox_prime (twoFineBox N cap w Z) _
      (fun i hi p hp => twoFineBox_prime hp) ps hps
  have hcprime : ∀ p ∈ canonicalSlots N cap w Z d, Nat.Prime p :=
    fun p hp => (canonicalSlots_prime_data hp).1
  have hperm : ps.Perm (canonicalSlots N cap w Z d) :=
    (Nat.primeFactorsList_unique (hprod.trans (canonicalSlots_prod hret).symm) hprime).trans
      (Nat.primeFactorsList_unique (rfl : (canonicalSlots N cap w Z d).prod =
        (canonicalSlots N cap w Z d).prod) hcprime).symm
  have howner : ownerWord N ps = actualPrimeLabelBlocksWord blocks :=
    owner_word_of_atom N cap w Z _ ps hps
  have hpermOwner : (actualPrimeLabelBlocksWord blocks).Perm
      (canonicalFineWord N cap w Z d) := by
    have hm := hperm.map (twoFineOwner N)
    change (ownerWord N ps).Perm (canonicalFineWord N cap w Z d) at hm
    rw [howner] at hm
    exact hm
  have hkey := block_key_word_order hb
  have hword : actualPrimeLabelBlocksWord blocks = canonicalFineWord N cap w Z d :=
    List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => Nat.le_antisymm hba hab)
      hkey.1 (canonical_fine_word_weak_order N cap w Z d) hpermOwner
  refine ⟨hret, ?_⟩
  unfold canonicalFineBlocks
  rw [← hword]
  exact hkey.2.1

/-- The computed sorted block fibre is exactly the active products of a
whole Cartesian atom.  Neither inclusion is a supplied coverage premise. -/
theorem retained_block_fibre_eq_active_products {N cap : ℕ} {w Z L : ℝ}
    (hN : 1 < N) (hZN : Z ≤ (N : ℝ)) (hL : 1 < L)
    {blocks : List (ℕ × ℕ)} (hb : blocks ∈ blockKeys N cap w Z L) :
    (fixedRoughSupport (ordinaryRetainOdd L) N cap w Z).filter
      (fun d => canonicalFineBlocks N cap w Z d = blocks) =
        blockActiveProducts N cap w Z L blocks := by
  ext d
  constructor
  · intro hd
    obtain ⟨hd, hblocks⟩ := Finset.mem_filter.mp hd
    have hcan := canonical_two_fine_residual_word hN hZN hd
    have hproduct : d ∈ blockProducts N cap w Z blocks := by
      apply Finset.mem_image.mpr
      refine ⟨canonicalSlots N cap w Z d, ?_, hcan.2.1⟩
      change canonicalSlots N cap w Z d ∈ actualPrimeSlotBox (twoFineBox N cap w Z)
        (actualPrimeLabelBlocksWord blocks)
      rw [← hblocks, canonical_fine_blocks_word]
      exact hcan.1
    have hg := (raw_squarefree_gated_iff_retained_rank hL).mpr ⟨hd, rfl⟩
    exact Finset.mem_filter.mpr ⟨hproduct, hg.2.1, hg.2.2⟩
  · intro hd
    exact Finset.mem_filter.mpr (active_product_block_key hL hb hd)

/-- On a real retained d, the sorted residual block fibre divided by its
literal M_res equals one.  This is proved from generic disjoint prime-label
normalization and the actual canonical Cartesian witness. -/
theorem canonical_sorted_fibre_normalized_one {N cap d : ℕ} {w Z L : ℝ}
    (hN : 1 < N) (hZN : Z ≤ (N : ℝ))
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z) :
    (actualPrimeTupleCoefficient
      (blockBox N cap w Z (canonicalFineBlocks N cap w Z d)) d : ℝ) /
        (canonicalFineMres N cap w Z d : ℝ) = 1 := by
  have hcan := canonical_two_fine_residual_word hN hZN hd
  have himage : d ∈ blockProducts N cap w Z (canonicalFineBlocks N cap w Z d) := by
    apply Finset.mem_image.mpr
    refine ⟨canonicalSlots N cap w Z d, ?_, hcan.2.1⟩
    simpa only [blockBox, canonical_fine_blocks_word] using hcan.1
  have hdis : (canonicalFineBlocks N cap w Z d).Pairwise
      (fun b c => Disjoint (twoFineBox N cap w Z b.1) (twoFineBox N cap w Z c.1)) :=
    (canonical_fine_blocks_distinct N cap w Z d).imp (fun h => twoFineBox_disjoint h)
  have h := actualPrimeLabelBlocks_moebius_fibre_disjoint (twoFineBox N cap w Z)
    (canonicalFineBlocks N cap w Z d) 1 d
    (fun b hb p hp => twoFineBox_prime hp) hdis
  simp only [one_mul, if_pos himage] at h
  have hmu : (ArithmeticFunction.moebius d : ℝ) ≠ 0 := by
    exact_mod_cast (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr
      (fixedRoughSupport_squarefree _ _ _ _ _ hd))
  apply mul_left_cancel₀ hmu
  simpa only [blockBox, canonicalFineMres, mul_div_assoc, mul_one] using h

/-- All raw owner orders, with their ORIGINAL M_res/k! interleaving
scalars, regroup exactly to the actual sorted block fibre.  This derives
the aggregate scalar cancellation rather than assuming a binomial factor. -/
theorem raw_owner_interleavings_eq_sorted_fibre {N cap d : ℕ} {w Z L : ℝ}
    (hN : 1 < N) (hZN : Z ≤ (N : ℝ))
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z) :
    (∑ J ∈ ownerWords N cap d.primeFactors.card w Z,
      ((ownerMres J : ℝ) / (d.primeFactors.card.factorial : ℝ)) *
        ownerAtomRawFibre N cap w Z J d) =
      (actualPrimeTupleCoefficient
        (blockBox N cap w Z (canonicalFineBlocks N cap w Z d)) d : ℝ) /
          (canonicalFineMres N cap w Z d : ℝ) := by
  calc
    _ = actualNormalizedPrimeTupleCoefficient (residualBox N cap d.primeFactors.card w Z)
        d.primeFactors.card d := (raw_normalized_fibre_by_Mres hN hZN).symm
    _ = 1 := actual_rough_original_factorial_normalized hd
    _ = _ := (canonical_sorted_fibre_normalized_one hN hZN hd).symm

/-- The actual physical row scalar on its computed sorted block.
Marked multiplicities stay external; beta and the rough Mobius sign
occur once, with a rank fixed by this block's literal word length. -/
theorem retained_row_eq_block_scalar {N cap e d : ℕ} {w Z L B : ℝ}
    (hL : 1 < L) (he : e ∈ actualSmallRosserSupport N cap w)
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z)
    {blocks : List (ℕ × ℕ)} (hblocks : canonicalFineBlocks N cap w Z d = blocks) :
    presievedCoefficient N cap w Z L B (e * d) =
      rawBetaWeight N cap (actualPrimeLabelBlocksWord blocks).length w B e *
        (ArithmeticFunction.moebius d : ℝ) := by
  have hlen : (actualPrimeLabelBlocksWord blocks).length = d.primeFactors.card := by
    rw [← hblocks, canonical_fine_blocks_word]
    simp only [canonicalFineWord, List.length_map, canonicalSlots_length hd]
  have hsign : roughWeight N cap w Z L d =
      (-1 : ℝ) ^ (actualPrimeLabelBlocksWord blocks).length := by
    rw [roughWeight_eq_slot_sign hL hd, canonicalSlots_length hd, hlen]
  have hbeta : commonSmallWeight N cap w Z L B d e =
      rawBetaWeight N cap (actualPrimeLabelBlocksWord blocks).length w B e := by
    simp only [commonSmallWeight, rawBetaWeight, hsign]
  rw [presieved_coefficient_value hL he hd, hbeta, roughWeight_eq_moebius hL hd]
  ring

/-- Original atom scalar identity on the entire Cartesian box.  Prime
power tuples vanish by literal mu(d), before absolute values. -/
theorem block_atom_eq_active_product_sum {N cap e : ℕ} {w Z L B : ℝ}
    {blocks : List (ℕ × ℕ)} (hb : blocks ∈ blockKeys N cap w Z L)
    (H : ℕ → ℝ) :
    blockAtomLinear N cap w Z L B e blocks H =
      ∑ d ∈ blockActiveProducts N cap w Z L blocks,
        rawBetaWeight N cap (actualPrimeLabelBlocksWord blocks).length w B e *
          (ArithmeticFunction.moebius d : ℝ) * H d := by
  have hdis := (block_key_word_order hb).2.2.imp
    (fun h => twoFineBox_disjoint (N := N) (cap := cap) (w := w) (Z := Z) h)
  have hnorm := actualPrimeLabelBlocks_moebius_sum_disjoint (twoFineBox N cap w Z)
    blocks 1 (fun d => if rawUpperGate L d then H d else 0)
    (fun b hb p hp => twoFineBox_prime hp) hdis
  simp only [one_mul] at hnorm
  unfold blockAtomLinear
  calc
    _ = rawBetaWeight N cap (actualPrimeLabelBlocksWord blocks).length w B e *
        ((∑ ps ∈ blockBox N cap w Z blocks,
          (ArithmeticFunction.moebius ps.prod : ℝ) *
            (if rawUpperGate L ps.prod then H ps.prod else 0)) /
          (actualPrimeLabelBlocksFactorial blocks : ℝ)) := by ring
    _ = rawBetaWeight N cap (actualPrimeLabelBlocksWord blocks).length w B e *
        ∑ d ∈ blockProducts N cap w Z blocks,
          (ArithmeticFunction.moebius d : ℝ) *
            (if rawUpperGate L d then H d else 0) := by rw [hnorm]
    _ = _ := by
      rw [Finset.mul_sum]
      simp only [blockActiveProducts, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hsf : Squarefree d
      · by_cases hg : rawUpperGate L d <;> simp [hsf, hg, mul_assoc]
      · have hzero : ArithmeticFunction.moebius d = 0 :=
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf
        simp [hsf, hzero]

/-- Each computed sorted block key has its exact complete atom scalar;
its true retained fibre is not left as an unproved analytic chart licence. -/
theorem block_atom_eq_retained_fibre {N cap e : ℕ} {w Z L B : ℝ}
    (hN : 1 < N) (hZN : Z ≤ (N : ℝ)) (hL : 1 < L)
    (he : e ∈ actualSmallRosserSupport N cap w)
    {blocks : List (ℕ × ℕ)} (hb : blocks ∈ blockKeys N cap w Z L)
    (H : ℕ → ℝ) :
    blockAtomLinear N cap w Z L B e blocks H =
      ∑ d ∈ (fixedRoughSupport (ordinaryRetainOdd L) N cap w Z).filter
        (fun d => canonicalFineBlocks N cap w Z d = blocks),
          presievedCoefficient N cap w Z L B (e * d) * H d := by
  rw [block_atom_eq_active_product_sum hb,
    ← retained_block_fibre_eq_active_products hN hZN hL hb]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hd, hblocks⟩ := Finset.mem_filter.mp hd
  rw [retained_row_eq_block_scalar hL he hd hblocks]

/-- Genuine finite regrouping by computed sorted block/label lists. -/
theorem retained_row_sum_by_blocks {N cap e : ℕ} {w Z L B : ℝ}
    (hN : 1 < N) (hZN : Z ≤ (N : ℝ)) (hL : 1 < L)
    (he : e ∈ actualSmallRosserSupport N cap w) (H : ℕ → ℝ) :
    (∑ d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z,
      presievedCoefficient N cap w Z L B (e * d) * H d) =
      ∑ blocks ∈ blockKeys N cap w Z L,
        blockAtomLinear N cap w Z L B e blocks H := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := fixedRoughSupport (ordinaryRetainOdd L) N cap w Z)
    (t := blockKeys N cap w Z L) (g := canonicalFineBlocks N cap w Z)
    (fun d hd => Finset.mem_image_of_mem _ hd)
    (fun d => presievedCoefficient N cap w Z L B (e * d) * H d)
  rw [← hf]
  apply Finset.sum_congr rfl
  intro blocks hb
  exact (block_atom_eq_retained_fibre hN hZN hL he hb H).symm

def all16BlockLinear (n N : ℕ) (eta : ℚ) (w B : ℝ)
    (E : ℕ × ℕ → Prop) (F : ℕ → ℝ) : ℝ :=
  ∑ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
    ∑ e ∈ rowSmall n N eta w t,
      ∑ blocks ∈ blockKeys N
        (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
        (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
        (U1011OriginalSixteenJointNearCapCompiler.D n N eta t),
        blockAtomLinear N
          (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
          (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
          (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) B e blocks
          (fun d => F (fullPrefix t * (e * d)))

/-- The physical all16 coefficient, including W and zero rows, is exactly
the sorted block atom functional for EVERY signed test on the complete q. -/
theorem joint_linear_eq_sorted_blocks {n N : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop) (F : ℕ → ℝ) :
    (∑ q ∈ jointSupport n N eta w E,
      jointPresievedSigma n N eta w B E q * F q) =
        all16BlockLinear n N eta w B E F := by
  rw [← joint_exact_pushforward n N eta w B E F]
  unfold all16BlockLinear
  apply Finset.sum_congr rfl
  intro t ht
  rw [physical_row_pullback]
  apply Finset.sum_congr rfl
  intro e he
  exact retained_row_sum_by_blocks hN
    (all16_physical_Z_le_N (by omega) heta ht)
    (U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht).2.1 he _

/-- Reading a coefficient by a finite indicator is independent of the
later arithmetic count or mean test. -/
def all16BlockSigma (n N : ℕ) (eta : ℚ) (w B : ℝ)
    (E : ℕ × ℕ → Prop) (q : ℕ) : ℝ :=
  all16BlockLinear n N eta w B E (fun x => if x = q then 1 else 0)

theorem all16_block_sigma_eq_joint {n N : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop) (q : ℕ) :
    all16BlockSigma n N eta w B E q = jointPresievedSigma n N eta w B E q := by
  unfold all16BlockSigma
  rw [← joint_linear_eq_sorted_blocks hN heta E]
  rw [joint_linear_eq_owner_linear hN heta E]
  exact physical_owner_sigma_eq_joint hN heta E q

/-- Count and exact coprime mean use the same sorted atoms and same q;
the independently labelled test word never enters M_res or marked t. -/
theorem joint_count_minus_mean_sorted_blocks {n N : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    (u P T : ℕ) (W : (Fin u → Fin (P + 1)) → ℝ) :
    (∑ q ∈ jointSupport n N eta w E,
      jointPresievedSigma n N eta w B E q *
        (labelledCountTest u P T W q - labelledExactCoprimeMeanTest u P W q)) =
      all16BlockLinear n N eta w B E
        (fun q => labelledCountTest u P T W q - labelledExactCoprimeMeanTest u P W q) :=
  joint_linear_eq_sorted_blocks hN heta E _

/-- The entire fixed-rank squarefree raw coefficient of the previous
batch now has this exact sorted block/label-list atom expansion. -/
theorem squarefree_all16_linear_eq_sorted_blocks {n N : ℕ} {eta : ℚ} {B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (rho : ℝ) (hrho : 0 < rho)
    (E : ℕ × ℕ → Prop)
    (hw : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      (N : ℝ) ^ rho ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (F : ℕ → ℝ) :
    squarefreeAll16Linear (actualRoughVectorRankBound rho) n N eta ((N : ℝ) ^ rho) B E F =
      all16BlockLinear n N eta ((N : ℝ) ^ rho) B E F := by
  rw [squarefree_all16_linear_eq_physical hN heta rho hrho E hw]
  exact joint_linear_eq_sorted_blocks hN heta E F

end
end ImbalancedChen.P5Z.All16SortedBlockAtomScalar
