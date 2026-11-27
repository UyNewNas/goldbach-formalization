import ImbalancedChen.P3OriginalU5CoarseRootV
import ImbalancedChen.P3OriginalU5WarmCapCodeStability

/-!
A finite physical root policy for the original U5 pair carrier. Its
root exponent is the infimum of the actual enhanced envelope on the
owning external-pair cell, less twice the fixed buffer. Later lookups
keep the same buffer in the actual checked bank.

The policy has its own retained polynomial and rounded coefficient.
Applying the selected-policy density and distribution estimates to
this policy requires corresponding same-coefficient proofs.
-/

namespace ImbalancedChen.P3OriginalU5CommonPhysicalRoot

noncomputable section
open scoped Classical BigOperators List
open Set
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalLowerSelectedCapConstructor (Code)
open P2OriginalPairSourceReceiver
open P2OriginalPairRootRoughProducer (pairPolicy pairRoot)
open P2OriginalSelectedPairNativeData (rootSeed selectedPolicy)
open P3OriginalU5AllSourceSquares (actualTrace actualTrace_word actualTrace_append)
open P3OriginalU5CoarseRootV
open P3OriginalU5WarmCapCodeStability
open P5OriginalU5CausalFinite (pairSupport coordinates coordinates_mem_triangle)
open Part5OriginalUpsilon5CausalDictionary (a h triangle level mem_triangle level_bounds residual_bounds)

/-- The geometric owner and its envelope precede the target integer. -/
def physicalSeed (R : PairRange) {m : ℕ} (b : ℚ) (j : Label R m) : ℝ :=
  sInf ((fun x : Fin 2 → ℝ => level (x 0) (x 1)) '' ownedCell R m j.val) - 2 * (b : ℝ)

theorem physicalSeed_bounds (R : PairRange) {m : ℕ} (b : ℚ) (j : Label R m)
    {x : Fin 2 → ℝ} (hx : x ∈ ownedCell R m j.val) :
    physicalSeed R b j ≤ level (x 0) (x 1) - 2 * (b : ℝ) ∧
      level (x 0) (x 1) - 2 * (b : ℝ) ≤ physicalSeed R b j + 3 * meshStep R m := by
  let E := (fun y : Fin 2 → ℝ => level (y 0) (y 1)) '' ownedCell R m j.val
  have hself : level (x 0) (x 1) ∈ E := ⟨x, hx, rfl⟩
  have hlow : ∀ z ∈ E, level (x 0) (x 1) - 3 * meshStep R m ≤ z := by
    rintro _ ⟨y, hy, rfl⟩
    have hv := (abs_le.mp (root_level_variation R
      (ownedCell_subset_closedCell R m j.val hx)
      (ownedCell_subset_closedCell R m j.val hy))).2
    linarith only [hv]
  have hhi : sInf E ≤ level (x 0) (x 1) := csInf_le ⟨_, hlow⟩ hself
  have hlo : level (x 0) (x 1) - 3 * meshStep R m ≤ sInf E :=
    le_csInf ⟨_, hself⟩ hlow
  change sInf E - 2 * (b : ℝ) ≤ _ ∧ _ ≤ sInf E - 2 * (b : ℝ) + _
  constructor <;> linarith only [hhi, hlo]

/-- Fixed enhanced level margins, the ordinary root's residual window,
and the initial marked feedback condition on the complete owner cell. -/
theorem physicalSeed_reserves (R : PairRange) {m : ℕ} {b : ℚ}
    (hb : 0 < b) (hb' : b ≤ 1 / 1000) (hm : meshStep R m ≤ (b : ℝ) / 32)
    (j : Label R m) {x : Fin 2 → ℝ} (hx : x ∈ ownedCell R m j.val) :
    1 / 2 + 1 / 32 ≤ physicalSeed R b j ∧
      physicalSeed R b j ≤ 153 / 256 - 2 * (b : ℝ) ∧
      3 * a ≤ physicalSeed R b j - x 0 - x 1 ∧
      physicalSeed R b j - x 0 - x 1 ≤ 5 * a ∧
      2 * (physicalSeed R b j - x 0 - x 1) ≤ 1 - x 0 - x 1 := by
  obtain ⟨hl, hh⟩ := physicalSeed_bounds R b j hx
  obtain ⟨hu, hut, ht⟩ := mem_triangle.mp hx.1
  obtain ⟨hlo, hhi⟩ := level_bounds hu hut.le ht.le
  obtain ⟨hrlo, hrhi⟩ := residual_bounds hu hut.le ht.le
  change (34 / 125 : ℝ) ≤ level (x 0) (x 1) - x 0 - x 1 at hrlo
  change level (x 0) (x 1) - x 0 - x 1 ≤ (2083 / 5000 : ℝ) at hrhi
  have hc := P5CausalPrimeCorrectionPayment.original_U5_level_le_cap x
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hb1 : (b : ℝ) ≤ 1 / 1000 := by
    have hcast : (b : ℝ) ≤ ((1 / 1000 : ℚ) : ℝ) := Rat.cast_le.mpr hb'
    norm_num at hcast ⊢
    exact hcast
  dsimp only [a] at hu ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith only [hl, hh, hu, hut, hlo, hhi, hrlo, hrhi, hc, hm, hb0, hb1]

/-- The two external squares and the first rough head square use the
physical cell seed. -/
theorem physicalSeed_initial_squares (R : PairRange) {m : ℕ} {b : ℚ}
    (hb : 0 < b) (hb' : b ≤ 1 / 1000) (hm : meshStep R m ≤ (b : ℝ) / 32)
    (j : Label R m) {x : Fin 2 → ℝ} (hx : x ∈ ownedCell R m j.val) :
    2 * x 1 < physicalSeed R b j ∧ x 1 + 2 * x 0 < physicalSeed R b j ∧
      x 1 + x 0 + 2 * a < physicalSeed R b j := by
  have hseed := (physicalSeed_reserves R hb hb' hm j hx).1
  obtain ⟨_, hut, ht⟩ := mem_triangle.mp hx.1
  dsimp only [h] at ht
  dsimp only [a]
  refine ⟨?_, ?_, ?_⟩ <;> linarith only [hseed, hut, ht]

def rowAddress (R : PairRange) (m N : ℕ) (t : ℕ × ℕ) : Code m :=
  codeAt R m 2 [(coordinates N t) 1, (coordinates N t) 0]

theorem rowAddress_mem (R : PairRange) (m : ℕ) {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) : rowAddress R m N t ∈ family R m :=
  (labelAt R m (coordinates N t) (coordinates_mem_triangle hN ht)).property

def rowOwner (R : PairRange) (m : ℕ) {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) : Label R m :=
  ⟨rowAddress R m N t, rowAddress_mem R m hN ht⟩

theorem rowOwner_mem (R : PairRange) (m : ℕ) {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) :
    coordinates N t ∈ ownedCell R m (rowOwner R m hN ht).val :=
  ⟨coordinates_mem_triangle hN ht, rfl⟩

theorem rowOwner_seed_bounds (R : PairRange) (m : ℕ) (b : ℚ)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) :
    physicalSeed R b (rowOwner R m hN ht) ≤ rootSeed false b N t ∧
      rootSeed false b N t ≤ physicalSeed R b (rowOwner R m hN ht) + 3 * meshStep R m := by
  exact physicalSeed_bounds R b _ (rowOwner_mem R m hN ht)

/-- The physical grid is chosen before every arithmetic target. It can
approximate the original buffered seed to any given positive accuracy. -/
theorem exists_physical_root_mesh (R : PairRange) {b : ℚ}
    (hb : 0 < b) (hb' : b ≤ 1 / 1000) {η : ℝ} (hη : 0 < η) :
    ∃ m : ℕ, meshStep R m ≤ (b : ℝ) / 32 ∧
      ∀ {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N),
        let s := physicalSeed R b (rowOwner R m hN ht)
        s ≤ rootSeed false b N t ∧ rootSeed false b N t ≤ s + η ∧
          1 / 2 < s ∧ s < 153 / 256 ∧
          3 * a ≤ s - coordinate N t.1 - coordinate N t.2 ∧
          s - coordinate N t.1 - coordinate N t.2 ≤ 5 * a ∧
          2 * (s - coordinate N t.1 - coordinate N t.2) ≤
            1 - coordinate N t.1 - coordinate N t.2 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  obtain ⟨m, hm⟩ := exists_auxiliary_mesh R (lt_min hb0 hη)
  have hm1 : meshStep R m ≤ (b : ℝ) / 32 := by
    linarith only [hm, min_le_left (b : ℝ) η]
  have hm2 : 3 * meshStep R m ≤ η := by
    linarith only [hm, min_le_right (b : ℝ) η, hη]
  refine ⟨m, hm1, ?_⟩
  intro N hN t ht
  dsimp only
  obtain ⟨h₁, h₂⟩ := rowOwner_seed_bounds R m b hN ht
  obtain ⟨h₃, h₄, h₅, h₆, h₇⟩ :=
    physicalSeed_reserves R hb hb' hm1 _ (rowOwner_mem R m hN ht)
  exact ⟨h₁, h₂.trans (add_le_add_right hm2 _), by linarith only [h₃],
    by linarith only [h₄, hb0], h₅, h₆, h₇⟩

def rows (R : PairRange) (m N : ℕ) (code : Code m) : Finset (ℕ × ℕ) :=
  (pairSupport N).filter (fun t => rowAddress R m N t = code)

/-- Exact signed regrouping uses both original ordered prime labels. -/
theorem sum_rows (R : PairRange) (m : ℕ) {N : ℕ} (hN : 2 ≤ N) (f : ℕ × ℕ → ℝ) :
    (∑ j ∈ family R m, ∑ t ∈ rows R m N j, f t) = ∑ t ∈ pairSupport N, f t :=
  Finset.sum_fiberwise_of_maps_to (s := pairSupport N) (t := family R m)
    (g := rowAddress R m N) (fun _ ht => rowAddress_mem R m hN ht) f

/-- The checked bank and all three possible fresh ranks use the same
original buffer. Only the physical root supplied to the bank is new. -/
def policy (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (m N : ℕ) (t : ℕ × ℕ) : List ℕ → Bool :=
  if hx : coordinates N t ∈ triangle then
    let s := physicalSeed R b (labelAt R m (coordinates N t) hx)
    pairPolicy (pairPlan R bank (2 * b) s) (R.epsilon : ℝ) (ceiling : ℝ) s N t
  else selectedPolicy R bank b false N t

/-- Histories here follow the chronological order of the physical word. -/
def traceInCell (R : PairRange) {mesh m : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (j : Label R m) (N : ℕ) (t : ℕ × ℕ) (H : List ℕ) : Trace :=
  actualTrace R bank (2 * b) (physicalSeed R b j) N t H

theorem policy_eq_owner_trace (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (m : ℕ) {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (H : List ℕ) :
    policy R bank b m N t H =
      (traceInCell R bank b (rowOwner R m hN ht) N t H.reverse).accepted := by
  simp only [policy, dif_pos (coordinates_mem_triangle hN ht)]; rfl

/-- This alphabet is fixed before the target, both external primes,
and every subsequent history. -/
def physicalAlphabet (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (m : ℕ) : Finset ℝ :=
  Finset.univ.biUnion (fun j : Label R m =>
    capAlphabet (pairPlan R bank (2 * b) (physicalSeed R b j)) (physicalSeed R b j))

theorem trace_cap_mem (R : PairRange) {mesh m : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (j : Label R m) (N : ℕ) (t : ℕ × ℕ) (H : List ℕ) :
    (traceInCell R bank b j N t H).cap ∈ physicalAlphabet R bank b m := by
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ _, ?_⟩
  apply run_cap_mem_capAlphabet
  exact seed_mem_capAlphabet _ _

/-- Refining the external and subsequent bank codes leaves the physical
cap constant on each resulting cell. -/
theorem trace_cap_eq_on_codes (R : PairRange) {mesh m : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (j : Label R m) (N M : ℕ) (t u : ℕ × ℕ) (H K : List ℕ)
    (hp : coarseWord (R.epsilon : ℝ) (ceiling : ℝ) mesh
        [coordinate N t.2, coordinate N t.1] =
      coarseWord (R.epsilon : ℝ) (ceiling : ℝ) mesh [coordinate M u.2, coordinate M u.1])
    (hH : coarseWord (R.epsilon : ℝ) (ceiling : ℝ) mesh (H.map (coordinate N)) =
      coarseWord (R.epsilon : ℝ) (ceiling : ℝ) mesh (K.map (coordinate M))) :
    (traceInCell R bank b j N t H).cap = (traceInCell R bank b j M u K).cap := by
  exact run_cap_eq_of_coarseWord (pairPlan R bank (2 * b) (physicalSeed R b j))
    _ _ _ _ (pairRoot N t _) (pairRoot M u _) rfl hp hH

/-- On the ordinary descendants beyond full rank five, the total
physical level is exactly the level of the actual parent family. -/
theorem ordinary_child_cap (R : PairRange) {mesh m : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (j : Label R m) (N : ℕ) (t : ℕ × ℕ) (H K : List ℕ) (hH : 3 ≤ H.length) :
    (traceInCell R bank b j N t (H ++ K)).cap = (traceInCell R bank b j N t H).cap := by
  unfold traceInCell
  rw [actualTrace_append]
  apply P2OriginalPostFifthRoughSquares.run_cap_after_five
  simp only [actualTrace_word, List.length_append, List.length_map, List.length_cons,
    List.length_nil]
  omega

/-- The residual quotient uses every actual marked prime in the word. -/
def residualLevel (R : PairRange) {mesh m : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (j : Label R m) (N : ℕ) (t : ℕ × ℕ) (H : List ℕ) : ℝ :=
  (N : ℝ) ^ (traceInCell R bank b j N t H).cap / (((t.1 * t.2) * H.prod : ℕ) : ℝ)

theorem root_residualLevel (R : PairRange) {mesh m : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (j : Label R m) (N : ℕ) (t : ℕ × ℕ) :
    residualLevel R bank b j N t [] =
      (N : ℝ) ^ physicalSeed R b j / ((t.1 : ℝ) * t.2) := by
  change (N : ℝ) ^ physicalSeed R b j / (((t.1 * t.2) * [].prod : ℕ) : ℝ) = _
  simp

/-- On each actual external pair this level equals the power of the
physical residual exponent used in the root bounds. -/
theorem root_residualLevel_power (R : PairRange) {mesh m : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (j : Label R m) {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) :
    residualLevel R bank b j N t [] =
      (N : ℝ) ^ (physicalSeed R b j - coordinate N t.1 - coordinate N t.2) := by
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨hpair, _, _, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpair
  have h₁ := coordinate_power hNr (mem_chenAdditivePrimeCarrier.mp hp).2.1.pos
  have h₂ := coordinate_power hNr (mem_chenAdditivePrimeCarrier.mp hq).2.1.pos
  rw [root_residualLevel, show physicalSeed R b j - coordinate N t.1 - coordinate N t.2 =
    physicalSeed R b j - (coordinate N t.1 + coordinate N t.2) by ring,
    Real.rpow_sub (zero_lt_one.trans hNr), Real.rpow_add (zero_lt_one.trans hNr), h₁, h₂]

theorem ordinary_child_residualLevel (R : PairRange) {mesh m : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (j : Label R m) (N : ℕ) (t : ℕ × ℕ) (H K : List ℕ) (hH : 3 ≤ H.length) :
    residualLevel R bank b j N t (H ++ K) = residualLevel R bank b j N t H / (K.prod : ℝ) := by
  unfold residualLevel
  rw [ordinary_child_cap R bank b j N t H K hH]
  simp only [List.prod_append, Nat.cast_mul, div_div, mul_assoc]

end
end ImbalancedChen.P3OriginalU5CommonPhysicalRoot
