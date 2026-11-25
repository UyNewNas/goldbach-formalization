import ImbalancedChen.P3OriginalU5WarmMixedWallCover
import ImbalancedChen.P3OriginalU5MovingWallPayment

/-!
# One fine mesh pays the literal U5 warm rounding loss

SOURCE ONLY / UNCOMPILED / NO FORMAL ACCEPTANCE.

The existing actual mixed-fibre cover is joined to the existing canonical
wall payer.  The only coordinate identification is the complete canonical
word at its own rank.  A finite proper-wall alphabet is fixed at each rank,
and the ranks are bounded by the original U5 raw-support supplier.

One positive fine-width bound and one target threshold precede the target,
PairRange, bank, buffer, external pair and enumeration cap.  Every smaller
positive fine mesh satisfies the conclusion.  The policy and coefficients
in every wall charge are exactly those in the original roundingLoss.

No totient factorization, residual-mass estimate or moving-slab estimate is
reproved.  This result pays the rough rounding error; it does not evaluate
the raw density, identify raw and rounded rho, supply a common physical Q,
or assert a tensor, family-admission or PP conclusion.
-/

namespace ImbalancedChen.P3OriginalU5WarmRoundingPayment

noncomputable section
open scoped Classical BigOperators List
open P2PhysicalIncomingPrefixCells
open P2LowerCapPlanIntegerRetention (physicalWord coordinate)
open P2OriginalPairRootRoughProducer (pairRoot)
open P2OriginalPairSourceReceiver (PairRange pairPlan ceiling)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalSelectedPairNativeData (selectedPolicy rootSeed)
open P2LowerFiniteCellRounding
open P2RoundedCausalFibreLossAndLevel
open P2CanonicalWallFullResidualPayment
open P3OriginalU5WarmWordWalls
open P3OriginalU5WarmMixedWallCover
open P3OriginalU5RoundedModulusCap (rawRank)
open P3OriginalU5MovingWallPayment
open P5OriginalU5CausalFinite (attachmentNu smallCutoff cutoff pairSupport)

/-- At its full rank the canonical prefix is the very same physical word.
No membership, ordering or retained-representative hypothesis is needed. -/
theorem whole_word_eq_canonicalPrefix (N d : ℕ) :
    wordPoint d.primeFactorsList.length (physicalWord N d.primeFactorsList) =
      actualPrimeTupleLog N (canonicalPrefix d.primeFactorsList.length d) := by
  have htuple : List.ofFn (canonicalPrefix d.primeFactorsList.length d) =
      d.primeFactorsList.reverse := by
    unfold canonicalPrefix
    have htake : d.primeFactorsList.reverse.take d.primeFactorsList.length =
        d.primeFactorsList.reverse := List.take_of_length_le (by simp)
    rw [htake, List.reverse_reverse]
    exact primeHistoryTuple_ofFn rfl
  apply List.ofFn_injective
  rw [ofFn_wordPoint _ (by
    simp only [physicalWord, List.length_map, List.length_reverse])]
  change d.primeFactorsList.reverse.map (coordinate N) =
    List.ofFn ((coordinate N) ∘ canonicalPrefix d.primeFactorsList.length d)
  rw [← List.map_ofFn, htuple]

/-- Only actual nonzero rows enter the arithmetic wall payer. -/
abbrev ProperWall (mesh rank : ℕ) :=
  {w : WallIndex 5 mesh rank // wallForm w ≠ 0}

def properForms (mesh rank : ℕ) :
    Fin (Fintype.card (ProperWall mesh rank)) → (Fin rank → ℝ) →L[ℝ] ℝ :=
  fun i => wallForm ((Fintype.equivFin (ProperWall mesh rank)).symm i).val

def properCenters (mesh rank : ℕ) (P : CapPlan 5 mesh)
    (a b seed externalSum : ℝ) :
    Fin (Fintype.card (ProperWall mesh rank)) → ℝ :=
  fun i => wallCenter P a b seed externalSum
    ((Fintype.equivFin (ProperWall mesh rank)).symm i).val

theorem properForms_ne_zero (mesh rank : ℕ)
    (i : Fin (Fintype.card (ProperWall mesh rank))) :
    properForms mesh rank i ≠ 0 :=
  ((Fintype.equivFin (ProperWall mesh rank)).symm i).property

/-- The numerical centers retain the original plan, pair root and seed.
Only their finite index type and linear forms are fixed before N. -/
def selectedCenters (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (N : ℕ) (t : ℕ × ℕ) (rank : ℕ) :
    Fin (Fintype.card (ProperWall mesh rank)) → ℝ :=
  properCenters mesh rank
    (pairPlan R bank (2 * buffer) (rootSeed false buffer N t))
    (R.epsilon : ℝ) (ceiling : ℝ) (rootSeed false buffer N t)
    (pairRoot N t (rootSeed false buffer N t)).word.sum

/-- A fixed scalar bound for every oscillation factor at this rank. -/
def rowConstant (mesh rank : ℕ) : ℝ :=
  1 + ∑ w : ProperWall mesh rank, max (1 : ℝ) ‖wallForm w.val‖

theorem rowConstant_pos (mesh rank : ℕ) : 0 < rowConstant mesh rank := by
  have hs : 0 ≤ ∑ w : ProperWall mesh rank, max (1 : ℝ) ‖wallForm w.val‖ :=
    Finset.sum_nonneg (fun _ _ => zero_le_one.trans (le_max_left _ _))
  unfold rowConstant
  linarith

theorem wall_factor_le_rowConstant {mesh rank : ℕ} (w : ProperWall mesh rank) :
    max (1 : ℝ) ‖wallForm w.val‖ ≤ rowConstant mesh rank := by
  have hs := Finset.single_le_sum
    (f := fun u : ProperWall mesh rank => max (1 : ℝ) ‖wallForm u.val‖)
    (fun _ _ => zero_le_one.trans (le_max_left _ _)) (Finset.mem_univ w)
  exact hs.trans (le_add_of_nonneg_left zero_le_one)

/-- The actual charged modulus belongs to its own-rank canonical wall set.
Coverage, properness and the original rank are supplied internally. -/
theorem mixed_mem_own_rank_wall
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : 0 ≤ buffer) (hb' : buffer ≤ 1 / 1000)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (enum : ℕ) {tau delta : ℝ} (htau : 0 < tau) {d : ℕ}
    (hd : d ∈ «universe» N enum (smallCutoff N epsilon) (cutoff N))
    (hm : mixed (selectedPolicy R bank buffer false N t) N enum
      (smallCutoff N epsilon) (cutoff N) tau d)
    (hwidth : rowConstant mesh d.primeFactorsList.length * tau ≤ delta) :
    d ∈ canonicalWallModuli N enum (attachmentNu * epsilon ^ 2) (417 / 5000)
      (properForms mesh d.primeFactorsList.length)
      (selectedCenters R bank buffer N t d.primeFactorsList.length) delta := by
  obtain ⟨_hrank, w, hproper, hwall⟩ := selected_U5_mixed_wall_cover
    R bank buffer hb hb' epsilon hepsilon hN ht enum htau hd hm
  let q : ProperWall mesh d.primeFactorsList.length := ⟨w, hproper⟩
  let i := (Fintype.equivFin (ProperWall mesh d.primeFactorsList.length)) q
  apply Finset.mem_filter.mpr
  refine ⟨hd, le_rfl, i, ?_⟩
  have hbound := hwall.trans
    ((mul_le_mul_of_nonneg_right (wall_factor_le_rowConstant q) htau.le).trans hwidth)
  simpa only [properForms, selectedCenters, properCenters, i,
    Equiv.symm_apply_apply, q, whole_word_eq_canonicalPrefix] using hbound

/-- A transparent abbreviation for the existing payer's literal charge.
It is not a new mass or a replacement coefficient. -/
abbrev selectedWallCharge (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (epsilon : ℝ) (N : ℕ) (t : ℕ × ℕ)
    (enum : ℕ) (tau : ℝ) (rank : ℕ) (delta : ℝ) : ℝ :=
  wallRoundingCharge (selectedPolicy R bank buffer false N t) N enum
    (attachmentNu * epsilon ^ 2) (417 / 5000) tau
    (properForms mesh rank) (selectedCenters R bank buffer N t rank) delta

/-- Every nonzero error is covered at its own rank.  Other wall charges
may overcount it; all summands are nonnegative.  The actual coefficient
error vanishes outside mixed fibres by the existing exact theorem. -/
theorem roundingLoss_le_sum_selectedWallCharge
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : 0 ≤ buffer) (hb' : buffer ≤ 1 / 1000)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (enum : ℕ) {tau : ℝ} (htau : 0 < tau)
    (delta : Fin (rawRank epsilon + 1) → ℝ)
    (hwidth : ∀ r : Fin (rawRank epsilon + 1),
      rowConstant mesh r.val * tau ≤ delta r) :
    roundingLoss (selectedPolicy R bank buffer false N t) N enum
        (smallCutoff N epsilon) (cutoff N) tau ≤
      ∑ r : Fin (rawRank epsilon + 1),
        selectedWallCharge R bank buffer epsilon N t enum tau r.val (delta r) := by
  let keep := selectedPolicy R bank buffer false N t
  let U := «universe» N enum (smallCutoff N epsilon) (cutoff N)
  let W (r : Fin (rawRank epsilon + 1)) :=
    canonicalWallModuli N enum (attachmentNu * epsilon ^ 2) (417 / 5000)
      (properForms mesh r.val) (selectedCenters R bank buffer N t r.val) (delta r)
  let err (d : ℕ) : ℝ :=
    |coefficient keep N enum (smallCutoff N epsilon) (cutoff N) tau d -
      raw keep N enum (smallCutoff N epsilon) (cutoff N) d| / (Nat.totient d : ℝ)
  have herr (d : ℕ) : 0 ≤ err d :=
    div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  have hW (r : Fin (rawRank epsilon + 1)) : W r ⊆ U :=
    Finset.filter_subset _ _
  have hfilter (r : Fin (rawRank epsilon + 1)) :
      U.filter (fun d => d ∈ W r) = W r := by
    ext d
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hW r h, h⟩⟩
  have hterm (d : ℕ) (r : Fin (rawRank epsilon + 1)) :
      0 ≤ (if d ∈ W r then err d else 0) := by
    split_ifs
    · exact herr d
    · exact le_rfl
  have hpoint (d : ℕ) (hd : d ∈ U) :
      err d ≤ ∑ r : Fin (rawRank epsilon + 1), if d ∈ W r then err d else 0 := by
    by_cases hm : mixed keep N enum (smallCutoff N epsilon) (cutoff N) tau d
    · have hrank := selected_U5_mixed_rank R bank buffer hb hb'
        epsilon hepsilon hN ht enum tau hm
      let r : Fin (rawRank epsilon + 1) := ⟨d.primeFactorsList.length, by omega⟩
      have hdW : d ∈ W r := mixed_mem_own_rank_wall
        R bank buffer hb hb' epsilon hepsilon hN ht enum htau hd hm (hwidth r)
      calc
        err d = (if d ∈ W r then err d else 0) := (if_pos hdW).symm
        _ ≤ _ := Finset.single_le_sum (fun s _ => hterm d s) (Finset.mem_univ r)
    · have heq := coefficient_eq_raw_of_not_mixed keep N enum
        (smallCutoff N epsilon) (cutoff N) tau d hm
      have hz : err d = 0 := by simp only [err, heq, sub_self, abs_zero, zero_div]
      calc
        err d = 0 := hz
        _ ≤ _ := Finset.sum_nonneg (fun r _ => hterm d r)
  calc
    roundingLoss (selectedPolicy R bank buffer false N t) N enum
        (smallCutoff N epsilon) (cutoff N) tau = ∑ d ∈ U, err d := rfl
    _ ≤ ∑ d ∈ U, ∑ r : Fin (rawRank epsilon + 1),
        if d ∈ W r then err d else 0 := Finset.sum_le_sum hpoint
    _ = ∑ r : Fin (rawRank epsilon + 1), ∑ d ∈ W r, err d := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [← Finset.sum_filter, hfilter r]
    _ = ∑ r : Fin (rawRank epsilon + 1),
        selectedWallCharge R bank buffer epsilon N t enum tau r.val (delta r) := by
      apply Finset.sum_congr rfl
      intro r _
      rfl

/-- Fix the coarse mesh, positive rough exponent and reserve first.
Then one fine-width bound and one threshold work for all later targets,
actual banks, allowed buffers, pairs, caps and smaller positive meshes.
The rough cutoff remains omega = attachmentNu * epsilon^2 < 417/5000. -/
theorem exists_uniform_selected_U5_roundingLoss_lt
    (mesh : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hcut : attachmentNu * epsilon ^ 2 < (417 / 5000 : ℝ))
    (eta : ℝ) (heta : 0 < eta) :
    ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N →
        ∀ (R : PairRange) (bank : CandidateBank mesh) (buffer : ℚ),
          0 ≤ buffer → buffer ≤ 1 / 1000 →
          ∀ t ∈ pairSupport N, ∀ enum : ℕ, ∀ tau : ℝ,
            0 < tau → tau ≤ tau0 →
            roundingLoss (selectedPolicy R bank buffer false N t) N enum
              (smallCutoff N epsilon) (cutoff N) tau < eta := by
  have homega : 0 < attachmentNu * epsilon ^ 2 := by
    dsimp only [attachmentNu]
    positivity
  let M := rawRank epsilon
  let eps : ℝ := eta / ((M : ℝ) + 2)
  have heps : 0 < eps := div_pos heta (by positivity)
  have heach (r : Fin (M + 1)) :=
    exists_uniform_centers_full_residual_wall_payment
      (attachmentNu * epsilon ^ 2) (417 / 5000) homega hcut
      (properForms mesh r.val) (properForms_ne_zero mesh r.val) eps heps
  choose delta hdelta threshold _hthreshold hpay using heach
  let width (r : Fin (M + 1)) : ℝ := delta r / rowConstant mesh r.val
  have hwidthpos (r : Fin (M + 1)) : 0 < width r :=
    div_pos (hdelta r) (rowConstant_pos mesh r.val)
  let widths : Finset ℝ := insert 1 (Finset.univ.image width)
  have hne : widths.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let tau0 : ℝ := widths.min' hne
  have htau0 : 0 < tau0 := by
    have hm : tau0 ∈ widths := Finset.min'_mem _ _
    rcases Finset.mem_insert.mp hm with h | h
    · rw [h]
      exact zero_lt_one
    · obtain ⟨r, _hr, heq⟩ := Finset.mem_image.mp h
      exact heq ▸ hwidthpos r
  have hle (r : Fin (M + 1)) : tau0 ≤ width r :=
    Finset.min'_le widths (width r)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩))
  refine ⟨tau0, htau0, max 2 (Finset.univ.sup threshold), le_max_left _ _, ?_⟩
  intro N hN hEven R bank buffer hb hb' t ht enum tau htau htau0'
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hwidth (r : Fin (M + 1)) : rowConstant mesh r.val * tau ≤ delta r := by
    have hr := (le_div_iff₀ (rowConstant_pos mesh r.val)).mp (htau0'.trans (hle r))
    simpa only [mul_comm] using hr
  have hloss := roundingLoss_le_sum_selectedWallCharge
    R bank buffer hb hb' epsilon hepsilon hN2 ht enum htau delta hwidth
  have hsum : (∑ r : Fin (M + 1),
      selectedWallCharge R bank buffer epsilon N t enum tau r.val (delta r)) ≤
      ∑ _r : Fin (M + 1), eps := by
    apply Finset.sum_le_sum
    intro r _
    have hrN : threshold r ≤ N :=
      (Finset.le_sup (f := threshold) (Finset.mem_univ r)).trans
        ((le_max_right _ _).trans hN)
    exact (hpay r N hrN hEven enum (selectedPolicy R bank buffer false N t) tau
      (selectedCenters R bank buffer N t r.val)).le
  have hsum' : (∑ r : Fin (M + 1),
      selectedWallCharge R bank buffer epsilon N t enum tau r.val (delta r)) ≤
      ((M : ℝ) + 1) * eps := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using hsum
  have hreserve : ((M : ℝ) + 1) * eps < eta := by
    dsimp only [eps]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (show (0 : ℝ) < (M : ℝ) + 2 by positivity)).mpr
    nlinarith
  exact hloss.trans_lt (hsum'.trans_lt hreserve)

end
end ImbalancedChen.P3OriginalU5WarmRoundingPayment
