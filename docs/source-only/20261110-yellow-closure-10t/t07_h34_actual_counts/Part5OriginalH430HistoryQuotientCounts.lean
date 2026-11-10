import ImbalancedChen.Part5OriginalH430OriginalRootQBound
import ImbalancedChen.Part5OriginalH430BuchstabCutoffCancellation
import ImbalancedChen.P5OriginalU5FrozenSource

/-! Arithmetic count at the cutoff of each actual history occurrence.
The old integer word consists of genuine prime factors of its product.
In a pair the added word is [large,small] and the small exponent becomes
the new ceiling. These facts give both primitive roughness gates at the
same fixed power, beginning at the original U3/U4 root. -/

namespace ImbalancedChen.Part5OriginalH430HistoryQuotientCounts

noncomputable section
open scoped Classical BigOperators
open P5OriginalActionMassBound
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers
open P2EnhancedLowerPrimeChildGeometry P2FrozenReceiverCountActions
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P5OriginalU5FrozenSource (receiver frozenCount_eq_original_count)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430CutoffCoherence
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedMember Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430ActualMarkedRootConsumer Part5OriginalH430OriginalRootQBound

private def BelowWord (v : PhysicalNode) : Prop :=
  ∀ x ∈ word v, v.ceiling ≤ x

private theorem below_append_one {v : PhysicalNode} {x s : ℝ}
    (hv : BelowWord v) (hx : x ≤ v.ceiling) : BelowWord (appendOne v x s) := by
  intro u hu
  rw [word_appendOne] at hu
  rcases List.mem_append.mp hu with h | h
  · exact hx.trans (hv u h)
  · have he := List.mem_singleton.mp h
    change x ≤ u
    exact he.ge

private theorem below_append_pair {v : PhysicalNode} {x y s : ℝ}
    (hv : BelowWord v) (hxy : x < y) (hy : y ≤ v.ceiling) :
    BelowWord (appendPair v x y s) := by
  intro u hu
  rw [word_appendPair] at hu
  change x ≤ u
  rcases List.mem_append.mp hu with h | h
  · exact hxy.le.trans (hy.trans (hv u h))
  · rcases List.mem_cons.mp h with h | h
    · simpa only [h] using hxy.le
    · exact (List.mem_singleton.mp h).ge

private theorem below_perform {v : PhysicalNode} {shape : StepShape} {z : Point}
    (hv : BelowWord v) (hz : LocalDomain v shape z) :
    BelowWord (perform v shape z) := by
  cases shape with
  | retain => exact hv
  | transport i => exact hv
  | buchstabUpper => exact below_append_one hv hz.2.1.2.1
  | buchstabLower => exact below_append_one hv hz.2.2.1.2.1
  | w1Fixed i j => exact hv
  | w1Singleton i j => exact below_append_one hv hz.2.1.2.1
  | w2Fixed j a => exact hv
  | w2Singleton j b => exact below_append_one hv hz.2.1.2.1
  | w2Pair j b => exact below_append_pair hv hz.2.1.2.1 hz.2.1.2.2.1

private theorem below_replay {N g : ℕ} {Q : ℝ} {r : Request} {es : List (Edge N)}
    (hc : Coherent N Q r) (hw : BelowWord r.node.physical) (hs : ChosenPath N Q g r es) :
    BelowWord (replay r es).node.physical := by
  induction es generalizing g r with
  | nil => exact hw
  | cons e es ih =>
      cases g with
      | zero => exact False.elim hs
      | succ g =>
          exact ih (child_coherent hc hs.1)
            (below_perform hw (child_admission hc hs.1).2.1) hs.2

/-- The actual chosen history, with no assumption about earlier selected
actions or the old word. This includes retention and both fixed-pair reads. -/
theorem history_ceiling_le_letter {N n p : ℕ} {k : Root} {t : ℝ}
    {o : Occurrence N} (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384)
    (hp : p ∈ originalBand N k) (ho : o ∈ rootHistory N n k t p) :
    ∀ q ∈ o.current.old, o.current.node.physical.ceiling ≤ physicalPrime N q := by
  have hroot := root_coherent (by omega : 1 < N) ht ht' hn
    (original_band_prime hp) (original_band_geometry hN hp)
  have hw : BelowWord (rootRequest N n k t p).node.physical := by
    simp [BelowWord, rootRequest, frozenRoot, sourceRoot, word]
  have hist : BelowWord o.current.node.physical := by
    rw [(history_facts ho).2.2]
    exact below_replay hroot hw (history_facts ho).1
  intro q hq
  apply hist
  rw [rootHistory_integer_word ho]
  exact List.mem_map.mpr ⟨q, hq, rfl⟩

private theorem prime_mem_of_dvd_word {q : ℕ} (hq : q.Prime) (xs : List ℕ)
    (hxs : ∀ r ∈ xs, r.Prime) (hd : q ∣ xs.prod) : q ∈ xs := by
  induction xs with
  | nil =>
      have he : q = 1 := Nat.dvd_one.mp (by simpa using hd)
      exact (hq.ne_one he).elim
  | cons r rs ih =>
      rcases hq.dvd_mul.mp (show q ∣ r * rs.prod from hd) with h | h
      · exact List.mem_cons.mpr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hq (hxs r (List.mem_cons_self r rs))).mp h))
      · exact List.mem_cons.mpr (Or.inr
          (ih (fun u hu => hxs u (List.mem_cons.mpr (Or.inr hu))) h))

private theorem recover_letter {N q : ℕ} (hN : 2 ≤ N) (hq : 0 < q) :
    (N : ℝ) ^ physicalPrime N q = (q : ℝ) := by
  have hN' : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  calc
    (N : ℝ) ^ physicalPrime N q = Real.exp (Real.log (q : ℝ)) := by
      rw [physicalPrime, Real.rpow_def_of_pos (zero_lt_one.trans hN')]
      congr 1
      field_simp [(Real.log_pos hN').ne'] <;> ring
    _ = (q : ℝ) := Real.exp_log hq'

/-- Converts a positive physical residual from the genuine common-Q
factorization at the occurrence. The query can also be a comparison
argument such as 227/50, with the same parent product. -/
theorem history_cutoff_power {N n p : ℕ} {k : Root} {t : ℝ}
    {o : Occurrence N} (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384)
    (hp : p ∈ originalBand N k) (ho : o ∈ rootHistory N n k t p) (w : ℝ) :
    cutoff (rootQ N n k t p) (parentProduct o.current.old) w =
      (N : ℝ) ^ (residual o.current.node.physical / w) := by
  have hs := rootHistory_support (by omega : 1 < N) ht ht' hn
    (original_band_prime hp) (original_band_geometry hN hp) ho
  have hd : 0 < (parentProduct o.current.old : ℝ) := by exact_mod_cast hs.1.2.1
  have hQ : rootQ N n k t p =
      (parentProduct o.current.old : ℝ) * (N : ℝ) ^ residual o.current.node.physical := by
    rw [hs.2.1]
    exact hs.2.2.2.2.2
  have hratio : rootQ N n k t p / (parentProduct o.current.old : ℝ) =
      (N : ℝ) ^ residual o.current.node.physical := by
    rw [hQ]
    field_simp [hd.ne'] <;> ring
  rw [cutoff, hratio, ← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1
  ring

/-- Physical roughness of every chosen old product at its very own query.
The same fixed 440-step floor also bounds each prime factor and the actual
second-seed comparison cutoff, with no assumptions on active positions. -/
theorem history_integer_roughness {N n p : ℕ} {k : Root} {t : ℝ} {o : Occurrence N}
    (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384)
    (hp : p ∈ originalBand N k) (ho : o ∈ rootHistory N n k t p) :
    let d := parentProduct o.current.old
    let Q := rootQ N n k t p
    let z := cutoff Q d o.current.node.physical.argument
    ChenPrimeRough z d ∧ (N : ℝ) ^ frozenLeafCutoffFloor ≤ z ∧
      (∀ q ∈ d.primeFactors, (N : ℝ) ^ frozenLeafCutoffFloor ≤ (q : ℝ)) ∧
      (N : ℝ) ^ frozenLeafCutoffFloor ≤ cutoff Q d (227/50) := by
  dsimp only
  have hc := rootHistory_coherent (by omega : 1 < N) ht ht' hn
    (original_band_prime hp) (original_band_geometry hN hp) ho
  have hs := rootHistory_support (by omega : 1 < N) ht ht' hn
    (original_band_prime hp) (original_band_geometry hN hp) ho
  have harg : o.current.node.physical.argument ∈ Set.Icc (1 : ℝ) 6 := hs.2.2.2.1
  have hargpos : 0 < o.current.node.physical.argument := zero_lt_one.trans_le harg.1
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hfloor : frozenResidualFloor ≤ residual o.current.node.physical := by
    rw [hs.2.1]
    exact hs.2.2.1
  have hexp (w : ℝ) (hw : 0 < w) (hw6 : w ≤ 6) :
      (N : ℝ) ^ frozenLeafCutoffFloor ≤
        cutoff (rootQ N n k t p) (parentProduct o.current.old) w := by
    rw [history_cutoff_power hN ht ht' hn hp ho w]
    apply Real.rpow_le_rpow_of_exponent_le hbase
    change frozenResidualFloor / 6 ≤ residual o.current.node.physical / w
    exact (div_le_div_of_nonneg_right hfloor (by norm_num : (0 : ℝ) ≤ 6)).trans
      (div_le_div_of_nonneg_left hc.residual_pos.le hw hw6)
  have hrough : ChenPrimeRough
      (cutoff (rootQ N n k t p) (parentProduct o.current.old)
        o.current.node.physical.argument) (parentProduct o.current.old) := by
    intro q hq hdiv
    have hmem := prime_mem_of_dvd_word hq o.current.old (fun r hr => (hc.letters r hr).1) hdiv
    have hceil := history_ceiling_le_letter hN ht ht' hn hp ho q hmem
    have hcut : residual o.current.node.physical / o.current.node.physical.argument ≤
        o.current.node.physical.ceiling :=
      target_cutoff_le_ceiling hc.ceiling_pos hc.cutoff_fits hargpos le_rfl
    rw [history_cutoff_power hN ht ht' hn hp ho]
    exact (Real.rpow_le_rpow_of_exponent_le hbase (hcut.trans hceil)).trans_eq
      (recover_letter hN hq.pos)
  have hz := hexp _ hargpos harg.2
  refine ⟨hrough, hz, ?_, hexp _ (by norm_num) (by norm_num)⟩
  intro q hq
  exact hz.trans (hrough q (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq))

/-- On every finite history request the old prime mask can be removed.
The receiver remains the original centre-coprime additive prime. This
identifies a count before making any asymptotic or selected-floor claim. -/
theorem history_frozen_count_eq_true_quotient {N n p : ℕ} {k : Root} {t : ℝ}
    {o : Occurrence N} (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384)
    (hp : p ∈ originalBand N k) (ho : o ∈ rootHistory N n k t p) :
    let d := parentProduct o.current.old
    let z := cutoff (rootQ N n k t p) d o.current.node.physical.argument
    (frozenCount N d (receiver N) z : ℝ) =
      ((chenSiftedQuotientPrimeSource N d z).card : ℝ) :=
  frozenCount_eq_original_count _ _ _ (history_integer_roughness hN ht ht' hn hp ho).1

/-- The earlier original U3+U4 marked entrance no longer needs any
prime-factor roughness or 227/50 cutoff gate from its caller. Its positive
q-to-5-Phi discrepancy at arbitrary inspected depth remains in the budget. -/
theorem original_U34_actual_marked_entrance {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (n : ℕ) (t : ℝ) (depth : Root → ℕ → Fin 430),
      0 ≤ t → t ≤ 1/12 → 1 / ((n : ℝ) + 1) ≤ 11/384 →
      currentChenUpsilon3 N + currentChenUpsilon4 N ≤
        (∑ p ∈ originalBand N .U3, actualMarkedRootBudget N n .U3 t p (depth .U3 p) ε) +
        (∑ p ∈ originalBand N .U4, actualMarkedRootBudget N n .U4 t p (depth .U4 p) ε) := by
  obtain ⟨T, hT4, hT⟩ := original_U34_le_actual_budgets_without_Q_gate frozenLeafCutoffFloor_pos hε
  refine ⟨T, hT4, ?_⟩
  intro N hNT he n t depth ht ht' hn
  apply hT N hNT he n t depth ht ht' hn
  intro k p hp
  constructor
  · intro l _
    exact (history_integer_roughness (by omega : 2 ≤ N) ht ht' hn hp
      (levelOccurrence_source l).1).2.2.1
  · intro l _
    exact (history_integer_roughness (by omega : 2 ≤ N) ht ht' hn hp
      (levelOccurrence_source l).1).2.2.2

end
end ImbalancedChen.Part5OriginalH430HistoryQuotientCounts

