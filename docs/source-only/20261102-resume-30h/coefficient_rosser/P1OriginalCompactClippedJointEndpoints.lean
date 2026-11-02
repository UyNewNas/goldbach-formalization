import ImbalancedChen.P1OriginalClippedSixthAttainedWinner
import ImbalancedChen.P1OriginalCompactSixthEndpointCaller

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Pay the missing critical-window cost of the selected NATURAL upper
endpoints and the larger auxiliary cover, at a genuine original compact
caller. The original non-tent source cell is proved to be an ACTUAL winner
of all eleven rows before its compact margins are used. All labels,
widths and the canonical endpoint map are fixed before N.

Physical Q6 and B are retained. The additional critical interval concerns
the auxiliary C and Bupper, which previous G support did not assert.
All ordinary tails of policy6 are covered; later policy8 caps are not
identified with Q6. The tent source cells and changing-mesh reserves
remain separate obligations.
-/

namespace ImbalancedChen.P1OriginalCompactClippedJointEndpoints

noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface P2CompactThirdHistorySelection
open P2OriginalSixthSourceCompactCores P2OriginalSixthCompactArithmeticFibre
open P2OriginalSixthCommonScheduleAndFullQ
open P5OriginalCommonRefinedConstructor
open P1CommonSixthCompactActualCaller P1OriginalClippedSixthAttainedWinner
open P1ActualCommonSixthWinnerSelectedTail P1ActualSixthWinnerUniformEndpoints
open OriginalFourthCanonicalIntegerEndpoints20261026b
open OriginalSelectedEndpointQuotientInflation20261026b
open Certificates.P2OriginalSixthElevenLogSemantics

private theorem fold_min_le_face (fs : List (Physical → ℝ)) (t : Physical) :
    ∀ f ∈ fs, fs.foldr (fun g z => min (g t) z) 1 ≤ f t := by
  induction fs with
  | nil => simp
  | cons g gs ih =>
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (ih f hf)

/-- These are the actual two strict source faces, not an extra
winner-margin hypothesis supplied by the arithmetic caller. -/
theorem core_selected_margins (c : Cell) (n : ℕ) (t : Physical)
    (ht : t ∈ coreSequence c n) :
    1 / (n + 1 : ℝ) ≤ (1 + selectedSum c.selectedMask t) / 2 - newCap c t ∧
      1 / (n + 1 : ℝ) ≤
        57 / 64 - 3 * selectedSum c.selectedMask t / 2 - newCap c t := by
  have hm : 1 / (n + 1 : ℝ) ≤ strictMargin c t := ht.2
  have hf (i : Fin 19) : strictMargin c t ≤ baseFace c i t :=
    fold_min_le_face (sourceFaces c) t (baseFace c i)
      (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  constructor
  · exact hm.trans (hf 14)
  · exact hm.trans (hf 15)

private theorem selected_length_le_three (c : Cell) : (selectedSlots6 c).length ≤ 3 := by
  cases c <;> simp [selectedSlots6, Cell.selectedMask]

private theorem selected_remainder_length (c : Cell) (p : Fin 6 → ℕ) :
    ((selectedSlots6 c).map p).length + (remainderPrimes6 c p).length = 6 := by
  cases c <;> simp [selectedSlots6, remainderPrimes6, remainderSlots6, Cell.selectedMask]

private theorem selected_upper_product_bound
    (c : Cell) (p : Fin 6 → ℕ) (U : ℕ → ℕ) (x tau : ℝ)
    (hx : 1 < x) (htau : 0 ≤ tau)
    (hsize : ∀ i, (U (p i) : ℝ) ≤ x ^ tau * (p i : ℝ)) :
    (selectedProduct6 c (fun i => U (p i)) : ℝ) ≤
      x ^ (3 * tau) * (selectedProduct6 c p : ℝ) := by
  let S := (selectedSlots6 c).map p
  have hs := List.prod_map_le_prod_map₀ (fun q : ℕ => (U q : ℝ))
    (fun q : ℕ => x ^ tau * (q : ℝ)) (fun q _ => Nat.cast_nonneg _)
    (by
      intro q hq
      obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hq
      exact hsize i : ∀ q ∈ S, (U q : ℝ) ≤ x ^ tau * (q : ℝ))
  have hs' : (selectedProduct6 c (fun i => U (p i)) : ℝ) ≤
      (x ^ tau) ^ S.length * (selectedProduct6 c p : ℝ) := by
    simpa only [S, selectedProduct6, List.prod_map_mul, List.map_const', List.prod_replicate,
      List.map_map, Function.comp_def, ← actualNatList_cast_prod] using hs
  apply hs'.trans
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← Real.rpow_mul_natCast (zero_lt_one.trans hx).le]
  apply Real.rpow_le_rpow_of_exponent_le hx.le
  have hlen : (S.length : ℝ) ≤ 3 := by
    exact_mod_cast (show S.length ≤ 3 by simpa [S] using selected_length_le_three c)
  nlinarith [mul_le_mul_of_nonneg_left hlen htau]

/-- G's native support is retained verbatim. The new fields are precisely
the selected-upper-product window at the AUXILIARY cover. -/
def JointEndpointSupport (d : OriginalData) (b delta : ℝ) (m k N : ℕ)
    (s : FirstExitDepthState ℕ) (l : WinnerLabel m) : Prop :=
  WinnerEndpointSupport d b delta m k N s l ∧
    let p := primeHistoryTuple 6 (rosserAncestor 6 s.selectedPrefix)
    let B := selectedProduct6 l.1 p
    let Bu := selectedProduct6 l.1 (fun i => integerUpper k N (p i))
    let lam := lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix)
    let T := remainderPrimes6 l.1 p ++ s.selectedPrefix.reverse.drop 6
    let C := winnerCover b delta m l
    actualDwellSupport ((N : ℝ) ^ lam) s.selectedPrefix.reverse ∧
      actualDwellSupport ((N : ℝ) ^ lam / (B : ℝ)) T ∧
      B * T.prod = s.selectedPrefix.prod ∧ (1 / 2 : ℝ) < C ∧
      ((N : ℝ) ^ (2 * C - 1) < (Bu : ℝ) ∧
        (Bu : ℝ) < (N : ℝ) ^ ((2 / 3 : ℝ) * (57 / 64 - C)))

/-- Fixed original compact source, with EVERY actual policy6 ordinary
tail. The ancestor identity names the actual source tuple; no guard,
winner, upper-product support or critical-window conclusion is assumed.
The original source cell c is the attained winner, so its own compact
selected faces may legitimately pay the endpoint costs. -/
theorem exists_uniform_original_compact_clipped_joint_endpoints
    {n : ℕ} (D : CompactThirdChoice (commonCore n))
    (omega rho : ℝ) (homega : omega ≤ D.roughFloor) (hrho : 0 < rho) (hro : rho ≤ omega)
    (rows4 : Finset ProducerRow) (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 D.mesh))
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow D.mesh)) :
    let d := dataOfChoice D omega rows4 licensedOriginal J5 rows5
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 / 1000 ∧ ∃ delta : ℝ, 0 < delta ∧ delta ≤ b / 36 ∧
      ∃ m k : ℕ, ∀ᶠ N : ℕ in atTop, ∀ cap : ℕ,
        (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
        ∀ (c : Cell), c.family ≠ .tent33 → ∀ p : Fin 6 → ℕ, p ∈ compactTuples c n N →
          ∀ (weight : ℕ → ℝ) (rank : ℕ), 6 ≤ rank → ∀ s : FirstExitDepthState ℕ,
            s ∈ firstExitDepthFrontier rank (policy6 d (N : ℝ)) weight [] true 1
              (roughPrimeUniverse N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ (19 / 96 : ℝ))) →
            rosserAncestor 6 s.selectedPrefix = tupleHistory6 p →
              ∃ j, (c, j) ∈ winnerLabels m ∧ JointEndpointSupport d b delta m k N s (c, j) := by
  dsimp only
  let d := dataOfChoice D omega rows4 licensedOriginal J5 rows5
  let kap : ℝ := 1 / (n + 1 : ℝ)
  let b : ℝ := min (1 / 1000) (kap / 100)
  let R := actualRoughVectorRankBound rho
  let tau : ℝ := b / (4 * ((R : ℝ) + 1))
  let delta : ℝ := b / 72
  have hkap : 0 < kap := by dsimp [kap]; positivity
  have hb : 0 < b := lt_min (by norm_num) (by positivity)
  have hbk : b ≤ kap / 100 := min_le_right _ _
  have hbsmall : b ≤ 1 / 1000 := min_le_left _ _
  have hR : 0 < (R : ℝ) + 1 := by positivity
  have htau : 0 < tau := by dsimp [tau]; positivity
  have hwidth : tau * ((R : ℝ) + 1) = b / 4 := by
    dsimp [tau]
    field_simp [hR.ne']
    <;> ring
  have htausmall : tau ≤ b / 4 := by
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    nlinarith [mul_nonneg htau.le hR0]
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hdsmall : delta ≤ b / 36 := by dsimp [delta]; linarith
  obtain ⟨m, hm⟩ := ((tendsto_logPrimeMeshStep 0 (19 / 96 : ℝ)).eventually
    (gt_mem_nhds hd)).exists
  obtain ⟨k, _hk, hendpoint⟩ := exists_uniform_canonical_endpoints tau htau
  refine ⟨b, hb, hbsmall, delta, hd, hdsmall, m, k, ?_⟩
  filter_upwards [hendpoint, eventually_ge_atTop (2 : ℕ)] with N hU hN
  intro cap hcap c hc p hp weight rank hrank s hs hancestor
  have hNnat : 1 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hNnat
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNr
  let a := rosserAncestor 6 s.selectedPrefix
  let q := primeHistoryTuple 6 a
  let t := primeHistoryLogCoordinates (N : ℝ) 6 a
  let lam := lambda6 d (N : ℝ) a
  let S := (selectedSlots6 c).map q
  let T := remainderPrimes6 c q ++ s.selectedPrefix.reverse.drop 6
  let U := integerUpper k N
  have hsource := Finset.mem_filter.mp hp
  have hraw := Finset.mem_filter.mp hsource.1
  have hphys : PhysicalCell c t := by
    dsimp only [t, a]
    rw [hancestor, tupleHistory6_log]
    exact hraw.2
  have hcore : t ∈ coreSequence c n := by
    dsimp only [t, a]
    rw [hancestor, tupleHistory6_log]
    exact hsource.2
  have hcaller := original_compact_clipped_cell_is_actual_winner D N cap hNnat omega homega
    hcap rows4 licensedOriginal J5 rows5 c hc p hp
  have helig : eligibleSixth d (N : ℝ) c a := by
    simpa only [a, hancestor] using hcaller.1
  have hwin : lam = newCap c t :=
    eligible_clipped_attains_actual_lambda6 d (N : ℝ) a c hc helig
  obtain ⟨hB, hfull, hquot, hfact, hlo, hhi⟩ :=
    attained_sixth_selected_tail_support d N cap rank hNnat hrank
      ((N : ℝ) ^ omega) ((N : ℝ) ^ (19 / 96 : ℝ)) weight s hs c helig hwin
  have hlen := firstExitDepthFrontier_selected_length rank _ weight []
    (roughPrimeUniverse N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ (19 / 96 : ℝ))) true 1
    (by simp) s hs
  have ha : a.length = 6 := by simp only [a, rosserAncestor_length, hlen]; omega
  have hfront : List.ofFn q = s.selectedPrefix.reverse.take 6 := by
    rw [primeHistoryTuple_ofFn ha]
    simp only [a, rosserAncestor, List.reverse_drop]
    congr 1
    omega
  have hsplit : List.ofFn q ++ s.selectedPrefix.reverse.drop 6 = s.selectedPrefix.reverse := by
    rw [hfront]
    exact List.take_append_drop 6 s.selectedPrefix.reverse
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist rank (policy6 d (N : ℝ))
    weight (roughPrimeUniverse N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ (19 / 96 : ℝ))) s hs
  have hqMem (i : Fin 6) : q i ∈ s.selectedPrefix.reverse := by
    apply (List.take_sublist 6 s.selectedPrefix.reverse).subset
    rw [← hfront]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have htbox : t ∈ logPrimeBox (fun _ : Fin 6 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) := by
    apply mem_logPrimeBox.mpr
    intro i
    have hi := hsub.subset (hqMem i)
    exact primeCoordinate_mem hNnat (mem_roughPrimeUniverse_prime hi).pos
      (mem_roughPrimeUniverse_upper hi)
  obtain ⟨j, hj⟩ := exists_logPrimeMeshCell 0 (19 / 96 : ℝ) m htbox
  have hclose : ∀ i, |t i - logPrimeMeshLo 0 (19 / 96 : ℝ) m j i| ≤ delta := by
    intro i
    have hi := mem_logPrimeMeshCell.mp hj i
    rw [logPrimeMeshHi_eq_lo_add_step] at hi
    exact abs_le.mpr ⟨by linarith [hm], by linarith [hm]⟩
  let C := winnerCover b delta m (c, j)
  have hC : lam + b / 2 ≤ C ∧ C ≤ lam + b := by
    rw [hwin]
    exact winnerCover_bracket c t b delta m j hd.le hdsmall hclose
  have hsmall : C < (3 / 5 : ℝ) := by
    have hcap := P5Z.ActualCommonRefinedRange.eleven_newCap_lt_envelope hphys
    rw [← hwin] at hcap
    linarith [hC.2]
  have hep (v : ℕ) (hv : v ∈ s.selectedPrefix.reverse) :
      v ≤ U v ∧ (U v : ℝ) ≤ (N : ℝ) ^ tau * (v : ℝ) := by
    have hv' := hsub.subset hv
    exact hU v (mem_roughPrimeUniverse_prime hv').pos (mem_roughPrimeUniverse_upper hv')
  have hne : s.selectedPrefix.reverse ≠ [] := by
    intro heq
    have hh := congrArg List.length heq
    simp only [List.length_reverse, List.length_nil, hlen] at hh
    omega
  have hRank : s.selectedPrefix.reverse.length ≤ R := by
    apply actualRoughPrimeVector_length_le hNr hrho
      (by linarith [hC.1] : lam ≤ (5 / 8 : ℝ)) s.selectedPrefix.reverse hne
      (fun v hv => (mem_roughPrimeUniverse_prime (hsub.subset hv)).pos)
    · intro v hv
      exact (Real.rpow_le_rpow_of_exponent_le hNr.le hro).trans
        (mem_roughPrimeUniverse_lower (hsub.subset hv))
    · exact hfull
  have hbudget : lam + tau * ((R : ℝ) + 1) ≤ C := by linarith [hC.1]
  have hfullU : actualDwellSupport ((N : ℝ) ^ C) (s.selectedPrefix.reverse.map U) := by
    apply actualDwellSupport_upper_inflation hNr htau.le id U s.selectedPrefix.reverse hRank
      (fun v hv => (hep v hv).2)
    · simpa using hfull
    · exact hbudget
  have hSTmem : ∀ v ∈ S ++ T, v ∈ s.selectedPrefix.reverse := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hv
      exact hqMem i
    · rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hv
        exact hqMem i
      · exact List.mem_of_mem_drop hv
  have hlengthST : S.length + T.length = s.selectedPrefix.reverse.length := by
    have h6 := selected_remainder_length c q
    simp only [S, T, List.length_append, List.length_drop, List.length_reverse]
    omega
  have hquotU := selected_endpoint_quotient_support hNr htau.le S T U
    (fun v hv => (mem_roughPrimeUniverse_prime
      (hsub.subset (hSTmem v (List.mem_append_left _ hv)))).pos)
    (fun v hv => (hep v (hSTmem v (List.mem_append_left _ hv))).1)
    (fun v hv => (hep v (hSTmem v hv)).2)
    (by rw [hlengthST]; exact hRank) hquot hbudget
  have hSU : (S.map U).prod = selectedProduct6 c (fun i => U (q i)) := by
    simp only [S, selectedProduct6, List.map_map, Function.comp_def]
  change selectedProduct6 c q ≤ (S.map U).prod ∧ 0 < (S.map U).prod ∧ _ at hquotU
  rw [hSU] at hquotU
  have hparent := P5OriginalElevenBelowMuAncestor.actual_parent_eq_original_on_eleven
    d (N : ℝ) a ha c hphys
  have hprod := endpoint_selected_times_remainder6 c q (s.selectedPrefix.reverse.drop 6) U
  rw [hsplit] at hprod
  refine ⟨j, Finset.mem_product.mpr
    ⟨List.mem_toFinset.mpr (allCells_complete c), Finset.mem_univ j⟩, ?_, ?_⟩
  · exact ⟨helig, hwin, hj, hparent, helig.2.2.2, hC.1, hC.2, hsmall,
      (fun v hv => (hep v hv).1), hfullU, hquotU.1, hquotU.2.1, hquotU.2.2, hprod, hlo, hhi⟩
  · refine ⟨hfull, hquot, hfact, ?_, ?_⟩
    · have hx := hphys.coordinates_pos 0
      have hcompare := hphys.comparison
      have hgap := hphys.positiveGap
      rw [← hwin] at hgap
      dsimp only [R0] at hcompare
      linarith [hC.1]
    · change (N : ℝ) ^ (2 * C - 1) < (selectedProduct6 c (fun i => U (q i)) : ℝ) ∧
        (selectedProduct6 c (fun i => U (q i)) : ℝ) <
          (N : ℝ) ^ ((2 / 3 : ℝ) * (57 / 64 - C))
      obtain ⟨hmarginA, hmarginD⟩ := core_selected_margins c n t hcore
      rw [← hwin] at hmarginA hmarginD
      change kap ≤ _ at hmarginA hmarginD
      have hbpow : (selectedProduct6 c q : ℝ) = (N : ℝ) ^ selectedSum c.selectedMask t := by
        rw [selected_product_eq_finset]
        have he : selectedSum c.selectedMask t = ∑ i ∈ selectedSet6 c, t i := by
          simp only [selectedSum, selectedSet6, Finset.sum_filter]
        rw [he, Nat.cast_prod, Real.rpow_sum_of_pos hNpos]
        apply Finset.prod_congr rfl
        intro i _hi
        exact (rpow_primeHistoryLogCoordinates (N : ℝ) hNr ha
          (by
            intro v hv
            have hv' : v ∈ s.selectedPrefix := (List.drop_sublist _ _).subset hv
            exact (mem_roughPrimeUniverse_prime
              (hsub.subset (List.mem_reverse.mpr hv'))).pos) i).symm
      have hBu := selected_upper_product_bound c q U (N : ℝ) tau hNr htau.le
        (fun i => (hep (q i) (hqMem i)).2)
      rw [hbpow, ← Real.rpow_add hNpos] at hBu
      constructor
      · have hlog : 2 * C - 1 < selectedSum c.selectedMask t := by
          linarith [hC.2]
        have hBule : (N : ℝ) ^ selectedSum c.selectedMask t ≤
            (selectedProduct6 c (fun i => U (q i)) : ℝ) := by
          rw [← hbpow]
          exact_mod_cast hquotU.1
        exact ((Real.rpow_lt_rpow_left_iff hNr).mpr hlog).trans_le hBule
      · apply hBu.trans_lt
        apply (Real.rpow_lt_rpow_left_iff hNr).mpr
        linarith [hC.2]

/-- Fully constructed original rank-six caller, attached to the original
signed beta pair at the unchanged full q=a*roughProduct p. The preceding
theorem also licenses every policy6 tail with this same sixth ancestor. -/
theorem exists_original_compact_clipped_joint_caller
    {n : ℕ} (D : CompactThirdChoice (commonCore n))
    (omega rho : ℝ) (homega : omega ≤ D.roughFloor) (hrho : 0 < rho) (hro : rho ≤ omega)
    (rows4 : Finset ProducerRow) (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 D.mesh))
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow D.mesh)) :
    let d := dataOfChoice D omega rows4 licensedOriginal J5 rows5
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 / 1000 ∧ ∃ delta : ℝ, 0 < delta ∧ delta ≤ b / 36 ∧
      ∃ m k : ℕ, ∀ᶠ N : ℕ in atTop, ∀ cap : ℕ,
        (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
        ∀ c : Cell, c.family ≠ .tent33 → ∀ p : Fin 6 → ℕ, p ∈ compactTuples c n N →
          ∀ weight : ℕ → ℝ, ∃ s ∈ firstExitDepthFrontier 6 (policy6 d (N : ℝ)) weight [] true 1
            (roughPrimeUniverse N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ (19 / 96 : ℝ))),
            s.selectedPrefix = tupleHistory6 p ∧
              (∃ j, (c, j) ∈ winnerLabels m ∧ JointEndpointSupport d b delta m k N s (c, j)) ∧
              ∀ (L : ℝ) (a : ℕ), a ∈ actualSmallRosserSupport N cap ((N : ℝ) ^ omega) →
                P5OriginalCommonRefinedConstructor.rho d N cap ((N : ℝ) ^ omega)
                    ((N : ℝ) ^ (19 / 96 : ℝ)) L (a * roughProduct p) =
                  smallRoughPairCoefficient
                    (fixedRoughCoefficient ((policy8 d (N : ℝ)) false) N cap
                      ((N : ℝ) ^ omega) ((N : ℝ) ^ (19 / 96 : ℝ)))
                    (actualSmallRosserMinus N cap ((N : ℝ) ^ omega) L)
                    (actualSmallRosserPlus N cap ((N : ℝ) ^ omega) L)
                    (a, roughProduct p) := by
  dsimp only
  obtain ⟨b, hb, hbs, delta, hd, hds, m, k, hall⟩ :=
    exists_uniform_original_compact_clipped_joint_endpoints D omega rho homega hrho hro
      rows4 licensedOriginal J5 rows5
  refine ⟨b, hb, hbs, delta, hd, hds, m, k, ?_⟩
  filter_upwards [hall, eventually_ge_atTop (2 : ℕ)] with N hlic hN
  intro cap hcap c hc p hp weight
  obtain ⟨s, hs, hselected⟩ :=
    P1OriginalCompactSixthEndpointCaller.compact_tuple_has_actual_common_sixth_frontier
      D N cap (by omega) omega homega hcap rows4 licensedOriginal J5 rows5 c p hp weight
  refine ⟨s, hs, hselected, ?_, ?_⟩
  · apply hlic cap hcap c hc p hp weight 6 (by decide) s hs
    rw [hselected]
    exact rosserAncestor_self_of_length 6 _ (by simp [tupleHistory6])
  · intro L a ha
    exact compact_fullq_coefficient_eq_pair D N cap (by omega) omega homega hcap
      rows4 licensedOriginal J5 rows5 c p hp L a ha

end
end ImbalancedChen.P1OriginalCompactClippedJointEndpoints
