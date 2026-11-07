import ImbalancedChen.P5OriginalPresievedRoughPrimeSlots
import ImbalancedChen.ActualPrimeMultiLabelNormalization

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal finite descending prime-slot fibres for the ACTUAL new presieved
ordinary coefficient. Rank is fixed before N/tuples, the original upper
gates remain inside the carrier, and each integer has exactly one ordered
representative. The original repeated-label factorial normalization is
also attached using the existing squarefree Cartesian-fibre theorem.
The small beta factor retains its independent COMMON physical level B.
-/
namespace ImbalancedChen.P5Z.OriginalPresievedRoughSlotCoefficient
noncomputable section
open Classical
open scoped BigOperators
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryPresievedSigma OriginalOrdinaryPresievedActiveRange
open OriginalOrdinaryResidualArithmeticFactor OriginalPresievedRoughRank OriginalPresievedRoughPrimeSlots
open U1011OriginalSixteenArithmeticProducts

def rankedOrderedSlots (R N cap : ℕ) (w Z L : ℝ) : Finset (List ℕ) :=
  (Finset.range (R + 1)).biUnion (fun r =>
    (actualPrimeSlotBox (fun _ : Unit => roughPrimeFinset N cap w Z) (List.replicate r ())).filter
      (fun ps => ps.Pairwise (· > ·) ∧ ordinaryRosserPrefixAdmissible false L ps.reverse))

def signedSlotCoefficient (R N cap : ℕ) (w Z L : ℝ) (d : ℕ) : ℝ :=
  ∑ ps ∈ rankedOrderedSlots R N cap w Z L,
    if ps.prod = d then (-1 : ℝ) ^ ps.length else 0

private theorem canonicalSlots_mem_primeBox {N cap d : ℕ} {w Z : ℝ} :
    canonicalSlots N cap w Z d ∈ actualPrimeSlotBox (fun _ : Unit => roughPrimeFinset N cap w Z)
      (List.replicate (canonicalSlots N cap w Z d).length ()) := by
  apply (mem_actualPrimeSlotBox_replicate _ _ _).mpr
  refine ⟨rfl, ?_⟩
  intro p hp
  have hu := (List.mem_filter.mp hp).1
  simpa only [← roughPrimeUniverse_toFinset N cap w Z, List.mem_toFinset] using hu

theorem canonicalSlots_mem_ranked {R N cap d : ℕ} {w Z L : ℝ} (hL : 1 < L)
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z)
    (hrank : d.primeFactors.card ≤ R) : canonicalSlots N cap w Z d ∈ rankedOrderedSlots R N cap w Z L := by
  apply Finset.mem_biUnion.mpr
  refine ⟨(canonicalSlots N cap w Z d).length, ?_, ?_⟩
  · apply Finset.mem_range.mpr
    rw [canonicalSlots_length hd]
    omega
  · exact Finset.mem_filter.mpr ⟨canonicalSlots_mem_primeBox,
      canonicalSlots_descending _ _ _ _ _, canonicalSlots_original_upper_gates hL hd⟩

/-- Literal descending product fibres have ONE representative. This does
not forget multiplicity in an unordered Cartesian prime-slot box. -/
theorem ranked_product_unique {R N cap d : ℕ} {w Z L : ℝ}
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z)
    {ps : List ℕ} (hps : ps ∈ rankedOrderedSlots R N cap w Z L) (hprod : ps.prod = d) :
    ps = canonicalSlots N cap w Z d := by
  obtain ⟨r, hr, hps⟩ := Finset.mem_biUnion.mp hps
  obtain ⟨hbox, hdesc, hgates⟩ := Finset.mem_filter.mp hps
  obtain ⟨hlen, hmem⟩ := (mem_actualPrimeSlotBox_replicate _ _ _).mp hbox
  have hprime : ∀ p ∈ ps, Nat.Prime p := fun p hp => (mem_roughPrimeFinset.mp (hmem p hp)).2.1
  have heq : ps.prod = (canonicalSlots N cap w Z d).prod := hprod.trans (canonicalSlots_prod hd).symm
  have hperm := (Nat.primeFactorsList_unique heq hprime).trans
    (Nat.primeFactorsList_unique (rfl : (canonicalSlots N cap w Z d).prod =
      (canonicalSlots N cap w Z d).prod) (fun p hp => (canonicalSlots_prime_data hp).1)).symm
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => Nat.le_antisymm hba hab)
    (hdesc.imp fun h => h.le) ((canonicalSlots_descending N cap w Z d).imp fun h => h.le) hperm

theorem roughWeight_eq_signedSlotCoefficient {R N cap d : ℕ} {w Z L : ℝ} (hL : 1 < L)
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z)
    (hrank : d.primeFactors.card ≤ R) : roughWeight N cap w Z L d = signedSlotCoefficient R N cap w Z L d := by
  unfold signedSlotCoefficient
  symm
  rw [Finset.sum_eq_single (canonicalSlots N cap w Z d)]
  · rw [if_pos (canonicalSlots_prod hd), roughWeight_eq_slot_sign hL hd]
  · intro ps hps hne
    rw [if_neg]
    exact fun hp => hne (ranked_product_unique hd hps hp)
  · intro hn
    exact (hn (canonicalSlots_mem_ranked hL hd hrank)).elim

/-- The full repeated-label Cartesian fibre has its ORIGINAL factorial,
not a new three-group factorial. Squarefreeness supplies the normalization;
no repeated-prime or boundary tuple is removed by hand. -/
theorem actual_rough_original_factorial_normalized {N cap d : ℕ} {w Z L : ℝ}
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z) :
    actualNormalizedPrimeTupleCoefficient
      (actualPrimeSlotBox (fun _ : Unit => roughPrimeFinset N cap w Z)
        (List.replicate d.primeFactors.card ())) d.primeFactors.card d = 1 := by
  have h := actualPrimeSlotBox_replicate_normalized_eq_one (roughPrimeFinset N cap w Z)
    (canonicalSlots N cap w Z d)
    (fun p hp => (mem_roughPrimeFinset.mp hp).2.1)
    (fun p hp => by
      have hu := (List.mem_filter.mp hp).1
      simpa only [← roughPrimeUniverse_toFinset N cap w Z, List.mem_toFinset] using hu)
    (canonicalSlots_nodup N cap w Z d)
  simpa only [canonicalSlots_length hd, canonicalSlots_prod hd] using h

/-- Exact NEW presieved row, with its actual residual upper-gated prime
slots and the unchanged common beta pair. No identity with old lambda(ed)
or its conditional small-level L/d is asserted. -/
theorem presieved_row_eq_signed_slots {R N cap e d : ℕ} {w Z L B : ℝ}
    (hL : 1 < L) (he : e ∈ actualSmallRosserSupport N cap w)
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z)
    (hrank : d.primeFactors.card ≤ R) :
    presievedCoefficient N cap w Z L B (e * d) =
      signedSlotCoefficient R N cap w Z L d * commonSmallWeight N cap w Z L B d e := by
  rw [presieved_coefficient_value hL he hd, roughWeight_eq_signedSlotCoefficient hL hd hrank]

/-- Binding to genuine nonzero NEW physical marks. The complete modulus
and actual e,d are extracted from that same coefficient, and its finite
rough-slot rank is fixed only by nu0,betaEta. -/
theorem actual_presievedSigma_slot_realization {n N q : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop) (nu0 betaEta B : ℝ)
    (hrho : 0 < roughExponent nu0 betaEta)
    (hw : ∀ t ∈ tuples n N E, (N : ℝ) ^ roughExponent nu0 betaEta ≤
      U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (hq : presievedSigma n N eta ((N : ℝ) ^ roughExponent nu0 betaEta) B E q ≠ 0) :
    ∃ t ∈ tuples n N E,
      ∃ e ∈ actualSmallRosserSupport N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
          ((N : ℝ) ^ roughExponent nu0 betaEta),
        ∃ d ∈ fixedRoughSupport (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
            (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
            ((N : ℝ) ^ roughExponent nu0 betaEta) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t),
          q = fullPrefix t * (e * d) ∧ d.primeFactors.card ≤ rankBound nu0 betaEta ∧
          presievedSigma n N eta ((N : ℝ) ^ roughExponent nu0 betaEta) B E q =
            signedSlotCoefficient (rankBound nu0 betaEta) N
              (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
              ((N : ℝ) ^ roughExponent nu0 betaEta) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
              (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) d *
            commonSmallWeight N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
              ((N : ℝ) ^ roughExponent nu0 betaEta) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
              (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) B d e := by
  obtain ⟨t, ht, r, hr, hqr, e, he, d, hd, her, heB, hfull, hphysical⟩ :=
    active_physical_factors hN heta E hw hq
  have hrank := actual_rough_rank_bound hN heta nu0 betaEta hrho ht (hw t ht) hd
  have hL := (U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta
    (Finset.mem_filter.mp ht).1).2.1
  have hm : (⟨t, r⟩ : Mark) ∈ marks n N eta ((N : ℝ) ^ roughExponent nu0 betaEta) E :=
    Finset.mem_sigma.mpr ⟨ht, hr⟩
  have hs := presievedSigma_eq_row hN heta hw hm
  have hmod : modulus (⟨t, r⟩ : Mark) = q := hqr.symm
  rw [hmod] at hs
  refine ⟨t, ht, e, he, d, hd, ?_, hrank, ?_⟩
  · rw [hqr, her]
  · rw [hs, rowCoefficient, her]
    exact presieved_row_eq_signed_slots hL he hd hrank

end
end ImbalancedChen.P5Z.OriginalPresievedRoughSlotCoefficient
