import ImbalancedChen.P3OriginalU5ChangedFrontierSupport
import ImbalancedChen.P3OriginalU5ThreeFrontierIdentity
import ImbalancedChen.P2ActualPairPlanRunSupport
import ImbalancedChen.ActualRosserResidualDensity

/-! Exact power coordinates and old and new level bounds for every admitted
U5 frontier at rough depth one, two or three. The even incoming cube gives
the stronger square reserve at depth two. -/

namespace ImbalancedChen.P3OriginalU5FrontierParameters

noncomputable section
open scoped Classical List
open P2LowerCapPlanIntegerRetention (coordinate coordinate_power)
open P2OriginalPairSourceReceiver (PairRange pairPlan ceiling pairPlan_fresh_cap_bound)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalSelectedPairNativeData (selectedPolicy rootSeed original_root_seed_bounded)
open P2OriginalPairRootRoughProducer (pairRoot)
open P2OriginalPairBufferedRootProvenance (fifth_buffered_root_squares)
open P2ActualPairPlanRawSupport (run_cap_le)
open P3OriginalU5WarmRosserAdmission (incoming rowLevel)
open P3OriginalU5ThreeFrontierIdentity (original_U5_selected_frontier_admissible)
open P3OriginalU5ChangedFrontierSupport (original_U5_incoming_cap_mono)
open P5OriginalU5CausalFinite (cutoff pairSupport coordinates coordinates_mem_triangle)
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser (LowerAdmissibleSet)

/-- The external pair has already been removed in Q. The complete rough
history appears in this denominator, also when Q is read at the parent. -/
def residualExponent (N : ℕ) (Q : ℝ) (H : List ℕ) : ℝ :=
  Real.log (Q / (H.prod : ℝ)) / Real.log (N : ℝ)

structure FrontierParameters (N enum k : ℕ) (Q : List ℕ → ℝ) (H : List ℕ) : Prop where
  length_eq : H.length = k
  parity_eq : evenListLength H = decide (Even k)
  head_power : (N : ℝ) ^ coordinate N (H.headD 0) = (H.headD 0 : ℝ)
  head_le_cap : (H.headD 0 : ℝ) ≤ (enum : ℝ)
  old_power : (N : ℝ) ^ residualExponent N (Q H.tail) H = Q H.tail / (H.prod : ℝ)
  new_power : (N : ℝ) ^ residualExponent N (Q H) H = Q H / (H.prod : ℝ)
  coord_pos : 0 < coordinate N (H.headD 0)
  coord_le_old : coordinate N (H.headD 0) ≤ residualExponent N (Q H.tail) H
  old_le_new : residualExponent N (Q H.tail) H ≤ residualExponent N (Q H) H
  new_le_one : residualExponent N (Q H) H ≤ 1
  two_coord_le_old : k = 2 → 2 * coordinate N (H.headD 0) ≤ residualExponent N (Q H.tail) H

private theorem parity_length (H : List ℕ) : evenListLength H = decide (Even H.length) := by
  induction H with
  | nil => rfl
  | cons p ps ih => simp only [evenListLength, ih, List.length_cons, Nat.even_add_one, decide_not]

private theorem pair_cube {Q : ℝ} {q p : ℕ} (hqp : q < p)
    (hadm : ordinaryRosserPrefixAdmissible true Q [q,p]) : (p : ℝ) * q ^ 3 < Q := by
  let S : Finset ℕ := {q,p}
  have hS : LowerAdmissibleSet Q S := by simpa [S] using hadm.2
  have hfilter : S.filter (fun r => q ≤ r) = S := by
    apply Finset.filter_eq_self.mpr
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact le_rfl
    · rw [Finset.mem_singleton.mp hr]
      exact hqp.le
  have hev : Even ((S.filter (fun r => q ≤ r)).card) := by
    rw [hfilter]
    norm_num [S, hqp.ne]
  have hcube := hS q (by simp [S]) hev
  rw [hfilter] at hcube
  simpa [S, hqp.ne, Nat.cast_mul, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hcube

private theorem short_frontier_lower (Q : List ℕ → ℝ) (H : List ℕ)
    (h₁ : 1 ≤ H.length) (h₃ : H.length ≤ 3) (hs : H.Pairwise (· < ·))
    (hp : ∀ q ∈ H, q.Prime) (hroot : ∀ q ∈ H, (q : ℝ)^2 ≤ Q [])
    (hadm : ordinaryRosserPrefixAdmissible true (Q H.tail) H) :
    (H.headD 0 : ℝ) ≤ Q H.tail / (H.prod : ℝ) ∧
      (H.length = 2 → (H.headD 0 : ℝ)^2 ≤ Q H.tail / (H.prod : ℝ)) := by
  cases H with
  | nil => simp at h₁
  | cons q tail =>
    have hq := hp q List.mem_cons_self
    have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr hq.pos
    cases tail with
    | nil =>
      have h := hroot q (by simp)
      simp only [List.headD_cons, List.tail_cons, List.prod_cons, List.prod_nil,
        mul_one, List.length_cons, List.length_nil]
      exact ⟨(le_div_iff₀ hqpos).mpr (by simpa only [pow_two] using h), by intro hlen; omega⟩
    | cons p tail =>
      have hqp := (List.pairwise_cons.mp hs).1 p List.mem_cons_self
      cases tail with
      | nil =>
        have hp' := hp p (by simp)
        have hd : (0 : ℝ) < ([q,p].prod : ℕ) :=
          Nat.cast_pos.mpr (by simpa using Nat.mul_pos hq.pos hp'.pos)
        have hcube := (pair_cube hqp hadm).le
        have hsq : (q : ℝ)^2 ≤ Q [p] / ([q,p].prod : ℕ) := by
          apply (le_div_iff₀ hd).mpr
          calc
            (q : ℝ)^2 * ([q,p].prod : ℕ) = (p : ℝ) * q^3 := by
              simp only [List.prod_cons, List.prod_nil, mul_one, Nat.cast_mul]
              ring
            _ ≤ _ := hcube
        have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_lt.le
        have hle : (q : ℝ) ≤ (q : ℝ)^2 := by nlinarith only [hq1, sq_nonneg ((q : ℝ) - 1)]
        exact ⟨hle.trans hsq, fun _ => hsq⟩
      | cons p₁ tail =>
        cases tail with
        | nil =>
          have hpp₁ := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 p₁ List.mem_cons_self
          have htail := ordinaryRosserPrefixAdmissible_tail true (Q [p,p₁]) q [p,p₁] hq hs hadm
          have hcube := (pair_cube hpp₁ htail).le
          have hpr := hp p (by simp)
          have hpr₁ := hp p₁ (by simp)
          have hd : (0 : ℝ) < ([q,p,p₁].prod : ℕ) :=
            Nat.cast_pos.mpr (by simpa using Nat.mul_pos hq.pos (Nat.mul_pos hpr.pos hpr₁.pos))
          have hqp' : (q : ℝ) ≤ p := by exact_mod_cast hqp.le
          have hsq := mul_self_le_mul_self hqpos.le hqp'
          have hprod := mul_le_mul_of_nonneg_right hsq
            (mul_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p) (Nat.cast_nonneg p₁))
          refine ⟨(le_div_iff₀ hd).mpr ?_, ?_⟩
          · change (q : ℝ) * ([q,p,p₁].prod : ℕ) ≤ Q [p,p₁]
            simp only [List.prod_cons, List.prod_nil, mul_one, Nat.cast_mul]
            nlinarith only [hprod, hcube]
          · simp
        | cons r rs => simp only [List.length_cons] at h₃; omega

/-- The parameters come from the literal selected frontier, its old and new
caps, and the actual primes. This includes each terminal frontier state. -/
theorem original_U5_frontier_parameters (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (hb₀ : 0 ≤ b) (hb : b ≤ 1/1000) {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) (enum k : ℕ) (hk₁ : 1 ≤ k) (hk₃ : k ≤ 3)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier k (evenFirstExitPolicy (selectedPolicy R bank b false N t))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N enum 0 (cutoff N))) :
    FrontierParameters N enum k (rowLevel R bank b N t) s.selectedPrefix := by
  let H := s.selectedPrefix
  let Q := rowLevel R bank b N t
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNr₀ := zero_lt_one.trans hNr
  obtain ⟨hlen, hsort, hprod, _, _, _, _⟩ := actualPrimeFrontier_geometry k hk₁
    (evenFirstExitPolicy (selectedPolicy R bank b false N t)) N enum (cutoff N) s hs
  have hlen' : H.length = k := hlen
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist k _ _ _ s hs
  have hmem (p : ℕ) (hp : p ∈ H) : p ∈ roughPrimeUniverse N enum 0 (cutoff N) :=
    hsub.subset (List.mem_reverse.mpr hp)
  have hp (p : ℕ) (h : p ∈ H) : p.Prime := mem_roughPrimeUniverse_prime (hmem p h)
  have hHne : H ≠ [] := by intro e; rw [e] at hlen'; simp at hlen'; omega
  have hhead : H.headD 0 ∈ H := by cases he : H with
    | nil => exact (hHne he).elim
    | cons a as => exact List.mem_cons_self
  obtain ⟨hpair, _, _, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨ht₁, ht₂⟩ := Finset.mem_product.mp hpair
  have hp₁ := (mem_chenAdditivePrimeCarrier.mp ht₁).2.1
  have hp₂ := (mem_chenAdditivePrimeCarrier.mp ht₂).2.1
  have hB : 0 < (t.1 : ℝ) * t.2 := mul_pos (Nat.cast_pos.mpr hp₁.pos) (Nat.cast_pos.mpr hp₂.pos)
  have hQ (K : List ℕ) : 0 < Q K := div_pos (Real.rpow_pos_of_pos hNr₀ _) hB
  have he (K : List ℕ) : (N : ℝ) ^ residualExponent N (Q K) H = Q K / (H.prod : ℝ) :=
    residual_rpow_log_div _ _ hNr (div_pos (hQ K) hprod)
  have hroot := (fifth_buffered_root_squares (coordinates_mem_triangle hN ht) b hb).2.2
  change coordinate N t.2 + coordinate N t.1 + 2 * (417/5000 : ℝ) < rootSeed false b N t at hroot
  have hsingle (q : ℕ) (hq : q ∈ H) : (q : ℝ)^2 ≤ Q [] := by
    have hqpow := coordinate_power hNr (hp q hq).pos
    have hqa : coordinate N q ≤ (417/5000 : ℝ) := by
      apply (Real.rpow_le_rpow_left_iff hNr).mp
      rw [hqpow]
      exact (mem_roughPrimeUniverse_upper (hmem q hq)).le
    change (q : ℝ)^2 ≤ (N : ℝ) ^ rootSeed false b N t / ((t.1 : ℝ) * t.2)
    apply (le_div_iff₀ hB).mpr
    calc
      (q : ℝ)^2 * ((t.1 : ℝ) * t.2) =
          (N : ℝ) ^ ((coordinate N q + coordinate N q) + (coordinate N t.1 + coordinate N t.2)) := by
        rw [Real.rpow_add hNr₀, Real.rpow_add hNr₀, Real.rpow_add hNr₀,
          hqpow, coordinate_power hNr hp₁.pos, coordinate_power hNr hp₂.pos, pow_two]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith only [hroot, hqa])
  have hadm := (original_U5_selected_frontier_admissible R bank b hb hN ht enum k _ s hs).1
  have hf := short_frontier_lower Q H (by rw [hlen']; exact hk₁)
    (by rw [hlen']; exact hk₃) hsort hp hsingle hadm
  have hhpow := coordinate_power hNr (hp _ hhead).pos
  have hcap : (incoming R bank b N t H).cap ≤ (153/256 : ℝ) :=
    run_cap_le (pairPlan R bank (2*b) (rootSeed false b N t)) _
      (pairPlan_fresh_cap_bound R bank (2*b) (rootSeed false b N t))
      (R.epsilon : ℝ) (ceiling : ℝ) (pairRoot N t (rootSeed false b N t))
      (H.reverse.map (coordinate N)) (original_root_seed_bounded false b hb₀ N t)
  have hcapM : (incoming R bank b N t H.tail).cap ≤ (incoming R bank b N t H).cap := by
    cases H with
    | nil => exact le_rfl
    | cons q K => exact original_U5_incoming_cap_mono R bank b N t K q
  have hQmono : Q H.tail ≤ Q H := div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hNr.le hcapM) hB.le
  have hB1 : (1 : ℝ) ≤ (t.1 : ℝ) * t.2 := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hp₁.one_lt.le) (by exact_mod_cast hp₂.one_lt.le)
  have hDnat : 0 < H.prod := by exact_mod_cast hprod
  have hD1 : (1 : ℝ) ≤ H.prod := by exact_mod_cast (show 1 ≤ H.prod by omega)
  have hupper : Q H / (H.prod : ℝ) ≤ (N : ℝ) := by
    calc
      _ ≤ Q H := div_le_self (hQ H).le hD1
      _ ≤ (N : ℝ) ^ (incoming R bank b N t H).cap := div_le_self (Real.rpow_nonneg hNr₀.le _) hB1
      _ ≤ _ := by simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hNr.le (hcap.trans (by norm_num : (153/256 : ℝ) ≤ 1))
  refine ⟨hlen', (parity_length H).trans (by rw [hlen']), hhpow, ?_, he H.tail, he H,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast (mem_roughPrimeUniverse.mp (hmem _ hhead)).1.le
  · exact div_pos (Real.log_pos (by exact_mod_cast (hp _ hhead).one_lt)) (Real.log_pos hNr)
  · apply (Real.rpow_le_rpow_left_iff hNr).mp
    rw [hhpow, he H.tail]
    exact hf.1
  · apply (Real.rpow_le_rpow_left_iff hNr).mp
    rw [he H.tail, he H]
    exact div_le_div_of_nonneg_right hQmono hprod.le
  · apply (Real.rpow_le_rpow_left_iff hNr).mp
    rw [he H, Real.rpow_one]
    exact hupper
  · intro hk
    apply (Real.rpow_le_rpow_left_iff hNr).mp
    rw [two_mul, Real.rpow_add hNr₀, hhpow, he H.tail, ← pow_two]
    exact hf.2 (hlen'.trans hk)

end

end ImbalancedChen.P3OriginalU5FrontierParameters
