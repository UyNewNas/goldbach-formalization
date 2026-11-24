import ImbalancedChen.P5OriginalCommonThirdScreenedSource
import ImbalancedChen.P1ActualCoarseLevelCeiling

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

The actual second/third pointwise v actions have one finite rectangular
approximation table before N. The table uses the existing rational mesh
and qVLo, including cells crossing mu, and keeps all half-open owners.
Taking max with the original stored third cap retains its exact inherited
decision. The second scalar table reads only the second ancestor; the
third table reads only the third ancestor. Neither deletes a child-wall
projection from an earlier parent.

This is a low-rank approximation candidate. It does not redefine O's
OriginalData, policy8 or compiledRho, identify full87, or pay either total
reserve. The old fourth/fifth signed gains are not asserted for this new
candidate without a transport proof.
-/

namespace ImbalancedChen.P4AOriginalBufferedFallbackCaps
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set VariableEnvelope HistoricalThirdCoarse
open P5OriginalCommonRefinedConstructor P5OriginalCommonThirdScreenedSource
open P5OriginalAboveMuThirdLowerPhysicalCoefficient

abbrev Mesh (r m : ℕ) := Fin r → Fin (m + 1)

def step (m : ℕ) : ℝ := logPrimeMeshStep 0 (19 / 96) m

def table2 (m : ℕ) (j : Mesh 2 m) : ℚ :=
  qVLo (qLogPrimeMeshLo 0 (19 / 96) m j 1)
    (qLogPrimeMeshHi 0 (19 / 96) m j 1)

def table3 (m : ℕ) (j : Mesh 3 m) : ℚ :=
  qVLo (qLogPrimeMeshLo 0 (19 / 96) m j 1 +
    qLogPrimeMeshLo 0 (19 / 96) m j 2)
    (qLogPrimeMeshHi 0 (19 / 96) m j 1 +
    qLogPrimeMeshHi 0 (19 / 96) m j 2)

def lookup {r : ℕ} (m : ℕ) (buffer : ℝ) (table : Mesh r m → ℚ)
    (t : Fin r → ℝ) : ℝ :=
  (historicalPrefixLookup 0 (19 / 96) m Finset.univ table 0 t : ℝ) - buffer

def alphabet {r : ℕ} (m : ℕ) (buffer : ℝ) (table : Mesh r m → ℚ) : Finset ℝ :=
  insert (-buffer) (Finset.univ.image (fun j => (table j : ℝ) - buffer))

theorem lookup_on_cell {r : ℕ} (m : ℕ) (buffer : ℝ) (table : Mesh r m → ℚ)
    (t : Fin r → ℝ) (j : Mesh r m)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    lookup m buffer table t = (table j : ℝ) - buffer := by
  unfold lookup
  have ht' : t ∈ logPrimeMeshCell ((0 : ℚ) : ℝ) ((19 / 96 : ℚ) : ℝ) m j := by
    simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using ht
  rw [historicalPrefixLookup_on_cell 0 (19 / 96) (by norm_num) m
    Finset.univ table 0 t j (Finset.mem_univ _) ht']

theorem lookup_mem_alphabet {r : ℕ} (m : ℕ) (buffer : ℝ)
    (table : Mesh r m → ℚ) (t : Fin r → ℝ) :
    lookup m buffer table t ∈ alphabet m buffer table := by
  by_cases ht : ∃ j : Mesh r m, t ∈ logPrimeMeshCell 0 (19 / 96) m j
  · obtain ⟨j, hj⟩ := ht
    rw [lookup_on_cell m buffer table t j hj]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  · have hout : ∀ j ∈ (Finset.univ : Finset (Mesh r m)),
        t ∉ logPrimeMeshCell ((0 : ℚ) : ℝ) ((19 / 96 : ℚ) : ℝ) m j := by
      intro j _ hj
      apply ht
      exact ⟨j, by simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using hj⟩
    unfold lookup
    rw [historicalPrefixLookup_outside 0 (19 / 96) m Finset.univ table 0 t hout]
    simpa only [Rat.cast_zero, zero_sub] using Finset.mem_insert_self (-buffer) _

private theorem coordinate_bounds {r m : ℕ} {j : Mesh r m} {t : Fin r → ℝ}
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) (i : Fin r) :
    (qLogPrimeMeshLo 0 (19 / 96) m j i : ℝ) ≤ t i ∧
      t i ≤ (qLogPrimeMeshHi 0 (19 / 96) m j i : ℝ) ∧
      (qLogPrimeMeshHi 0 (19 / 96) m j i : ℝ) -
        qLogPrimeMeshLo 0 (19 / 96) m j i = step m := by
  rw [congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m j) i,
    congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) m j) i]
  norm_num only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat]
  have hh := mem_logPrimeMeshCell.mp ht i
  refine ⟨hh.1, hh.2.le, ?_⟩
  rw [logPrimeMeshHi_eq_lo_add_step]
  exact add_sub_cancel_left _ _

theorem table2_interval {m : ℕ} {j : Mesh 2 m} {t : Fin 2 → ℝ}
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    v (t 1) - (3 / 2 : ℝ) * step m ≤ (table2 m j : ℝ) ∧
      (table2 m j : ℝ) ≤ v (t 1) := by
  obtain ⟨hl, hu, hw⟩ := coordinate_bounds ht 1
  have he := rationalInterval_v_error hl hu
  rw [hw] at he
  exact ⟨by dsimp only [table2]; linarith, qVLo_le_v hl hu⟩

theorem table3_interval {m : ℕ} {j : Mesh 3 m} {t : Fin 3 → ℝ}
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    v (t 1 + t 2) - 3 * step m ≤ (table3 m j : ℝ) ∧
      (table3 m j : ℝ) ≤ v (t 1 + t 2) := by
  obtain ⟨hl1, hu1, hw1⟩ := coordinate_bounds ht 1
  obtain ⟨hl2, hu2, hw2⟩ := coordinate_bounds ht 2
  have hl : ((qLogPrimeMeshLo 0 (19 / 96) m j 1 +
      qLogPrimeMeshLo 0 (19 / 96) m j 2 : ℚ) : ℝ) ≤ t 1 + t 2 := by
    push_cast
    exact add_le_add hl1 hl2
  have hu : t 1 + t 2 ≤ ((qLogPrimeMeshHi 0 (19 / 96) m j 1 +
      qLogPrimeMeshHi 0 (19 / 96) m j 2 : ℚ) : ℝ) := by
    push_cast
    exact add_le_add hu1 hu2
  have he := rationalInterval_v_error hl hu
  push_cast at he
  refine ⟨?_, qVLo_le_v hl hu⟩
  change v (t 1 + t 2) - 3 * step m ≤ _
  dsimp only [table3]
  linarith

theorem secondRegion_in_box {t : Fin 2 → ℝ} (ht : SecondRegion (t 0) (t 1)) :
    t ∈ logPrimeBox (fun _ => 0) (fun _ => (19 / 96 : ℝ)) := by
  have hc := above_mu_old_cap_gt_cube ht.1 ht.2.1
  have hx : 0 < t 0 := by dsimp [mu] at ht; linarith [ht.1]
  have hy : 0 < t 1 := by
    have hxmu := ht.1
    dsimp only [mu] at hxmu
    linarith [ht.2.2.1]
  apply mem_logPrimeBox.mpr
  intro i
  fin_cases i
  · exact ⟨hx.le, ht.2.1⟩
  · exact ⟨hy.le, ht.2.2.2.trans ht.2.1⟩

theorem thirdRegion_in_box {t : Fin 3 → ℝ}
    (ht : ThirdRegion (t 0) (t 1) (t 2)) :
    t ∈ logPrimeBox (fun _ => 0) (fun _ => (19 / 96 : ℝ)) := by
  obtain ⟨hx, hxr, hz, hzy, hlo, hsum, hrest⟩ := ht
  have hx0 : 0 < t 0 := by dsimp [mu] at hx; linarith
  apply mem_logPrimeBox.mpr
  intro i
  fin_cases i
  · exact ⟨hx0.le, hxr⟩
  · exact ⟨(hz.trans hzy).le, by dsimp [rho] at hxr; linarith⟩
  · exact ⟨hz.le, by dsimp [rho] at hxr; linarith⟩

def secondCap (m : ℕ) (buffer N : ℝ) (pre : List ℕ) : ℝ :=
  lookup m buffer (table2 m) (primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre))

def thirdCap (m : ℕ) (buffer N : ℝ) (pre : List ℕ) : ℝ :=
  lookup m buffer (table3 m) (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre))

theorem secondCap_interval (m : ℕ) (buffer N : ℝ) (pre : List ℕ)
    (hg : secondGuard N pre) :
    secondExponent N pre - ((3 / 2 : ℝ) * step m + buffer) ≤
      secondCap m buffer N pre ∧
      secondCap m buffer N pre ≤ secondExponent N pre - buffer := by
  obtain ⟨j, hj⟩ := exists_logPrimeMeshCell 0 (19 / 96) m (secondRegion_in_box hg)
  have h := table2_interval hj
  rw [secondCap, lookup_on_cell m buffer (table2 m) _ j hj]
  dsimp only [secondExponent]
  constructor <;> linarith

theorem thirdCap_interval (m : ℕ) (buffer N : ℝ) (pre : List ℕ)
    (hg : thirdGuard N pre) :
    thirdExponent N pre - (3 * step m + buffer) ≤ thirdCap m buffer N pre ∧
      thirdCap m buffer N pre ≤ thirdExponent N pre - buffer := by
  obtain ⟨j, hj⟩ := exists_logPrimeMeshCell 0 (19 / 96) m (thirdRegion_in_box hg)
  have h := table3_interval hj
  rw [thirdCap, lookup_on_cell m buffer (table3 m) _ j hj]
  dsimp only [thirdExponent]
  constructor <;> linarith

theorem secondCap_ancestor (m : ℕ) (buffer N : ℝ) (later pre : List ℕ)
    (hlen : 2 ≤ pre.length) :
    secondCap m buffer N (later ++ pre) = secondCap m buffer N pre := by
  simp only [secondCap, rosserAncestor_append 2 later pre hlen]

theorem thirdCap_ancestor (m : ℕ) (buffer N : ℝ) (later pre : List ℕ)
    (hlen : 3 ≤ pre.length) :
    thirdCap m buffer N (later ++ pre) = thirdCap m buffer N pre := by
  simp only [thirdCap, rosserAncestor_append 3 later pre hlen]

abbrev oldAlphabet (d : OriginalData) : Finset ℝ :=
  P1ActualCoarseLevelCeiling.exponentValues (d.e : ℝ) d.chi d.m

theorem originalSeed_mem_oldAlphabet (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    originalSeed d N pre ∈ oldAlphabet d := by
  change (if P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre) then exponent (d.e : ℝ) d.chi d.m
        (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre))
      else initial (d.e : ℝ)) ∈ oldAlphabet d
  split_ifs
  · exact P1ActualCoarseLevelCeiling.exponent_mem_values _ _ _ _
  · exact Finset.mem_insert_self _ _

def effective2 (d : OriginalData) (m : ℕ) (buffer N : ℝ) (pre : List ℕ) : ℝ :=
  max (originalSeed d N pre) (secondCap m buffer N pre)

def effective3 (d : OriginalData) (m : ℕ) (buffer N : ℝ) (pre : List ℕ) : ℝ :=
  max (originalSeed d N pre) (thirdCap m buffer N pre)

theorem effective2_ancestor (d : OriginalData) (m : ℕ) (buffer N : ℝ)
    (later pre : List ℕ) (hlen : 3 ≤ pre.length) :
    effective2 d m buffer N (later ++ pre) = effective2 d m buffer N pre := by
  simp only [effective2, originalSeed, P1OriginalVariableFourthContinuation.seedExponent,
    rosserAncestor_append 3 later pre hlen,
    secondCap_ancestor m buffer N later pre (by omega)]

theorem effective3_ancestor (d : OriginalData) (m : ℕ) (buffer N : ℝ)
    (later pre : List ℕ) (hlen : 3 ≤ pre.length) :
    effective3 d m buffer N (later ++ pre) = effective3 d m buffer N pre := by
  simp only [effective3, originalSeed, P1OriginalVariableFourthContinuation.seedExponent,
    rosserAncestor_append 3 later pre hlen, thirdCap_ancestor m buffer N later pre hlen]

def effectiveAlphabet (d : OriginalData) (m : ℕ) (buffer : ℝ) : Finset ℝ :=
  (oldAlphabet d).biUnion (fun a =>
    ((alphabet m buffer (table2 m)) ∪ (alphabet m buffer (table3 m))).image (max a))

theorem effective_caps_finite (d : OriginalData) (m : ℕ) (buffer N : ℝ)
    (pre : List ℕ) :
    effective2 d m buffer N pre ∈ effectiveAlphabet d m buffer ∧
      effective3 d m buffer N pre ∈ effectiveAlphabet d m buffer := by
  constructor
  · exact Finset.mem_biUnion.mpr ⟨originalSeed d N pre, originalSeed_mem_oldAlphabet d N pre,
      Finset.mem_image.mpr ⟨secondCap m buffer N pre,
        Finset.mem_union_left _ (lookup_mem_alphabet m buffer (table2 m) _), rfl⟩⟩
  · exact Finset.mem_biUnion.mpr ⟨originalSeed d N pre, originalSeed_mem_oldAlphabet d N pre,
      Finset.mem_image.mpr ⟨thirdCap m buffer N pre,
        Finset.mem_union_right _ (lookup_mem_alphabet m buffer (table3 m) _), rfl⟩⟩

private theorem originalSeed_second_buffer (d : OriginalData) (he : 0 ≤ (d.e : ℝ))
    (N : ℝ) (pre : List ℕ) (hlen : 3 ≤ pre.length)
    (hs : selectedThird d N pre) (hg : secondGuard N pre) :
    originalSeed d N pre ≤ secondExponent N pre - 2 * (d.e : ℝ) := by
  have hx := P5OriginalCommonFourthSourceNavigation.ancestor_first_coordinate N 2 (by omega) pre (by omega)
  have hm : mu < P5OriginalCommonFourthSourceNavigation.firstCoordinate N pre := by
    simpa only [← hx] using hg.1
  have hold := (originalSeed_supported_interval d he N pre hlen hs hm).2
  have hnew := new_cap_gt_old hg.1 hg.2.2.1 hg.2.2.2
  rw [hx] at hnew
  dsimp only [secondExponent]
  linarith

private theorem originalSeed_third_buffer (d : OriginalData) (he : 0 ≤ (d.e : ℝ))
    (N : ℝ) (pre : List ℕ) (hlen : 3 ≤ pre.length)
    (hs : selectedThird d N pre) (hg : thirdGuard N pre) :
    originalSeed d N pre ≤ thirdExponent N pre - 2 * (d.e : ℝ) := by
  have hx := P5OriginalCommonFourthSourceNavigation.ancestor_first_coordinate N 3 (by omega) pre hlen
  have hm : mu < P5OriginalCommonFourthSourceNavigation.firstCoordinate N pre := by
    simpa only [← hx] using hg.1
  have hold := (originalSeed_supported_interval d he N pre hlen hs hm).2
  have hnew := (third_initial_physical_gates hg).2.2.2.2.2
  rw [hx] at hnew
  dsimp only [thirdExponent]
  linarith

theorem effective2_interval (d : OriginalData) (he : 0 ≤ (d.e : ℝ))
    (m : ℕ) (buffer N : ℝ) (hb : buffer ≤ 2 * (d.e : ℝ))
    (pre : List ℕ) (hlen : 3 ≤ pre.length)
    (hs : selectedThird d N pre) (hg : secondGuard N pre) :
    originalSeed d N pre ≤ effective2 d m buffer N pre ∧
      secondExponent N pre - ((3 / 2 : ℝ) * step m + buffer) ≤ effective2 d m buffer N pre ∧
      effective2 d m buffer N pre ≤ secondExponent N pre - buffer := by
  have ht := secondCap_interval m buffer N pre hg
  have ho := originalSeed_second_buffer d he N pre hlen hs hg
  exact ⟨le_max_left _ _, ht.1.trans (le_max_right _ _), max_le (by linarith) ht.2⟩

theorem effective3_interval (d : OriginalData) (he : 0 ≤ (d.e : ℝ))
    (m : ℕ) (buffer N : ℝ) (hb : buffer ≤ 2 * (d.e : ℝ))
    (pre : List ℕ) (hlen : 3 ≤ pre.length)
    (hs : selectedThird d N pre) (hg : thirdGuard N pre) :
    originalSeed d N pre ≤ effective3 d m buffer N pre ∧
      thirdExponent N pre - (3 * step m + buffer) ≤ effective3 d m buffer N pre ∧
      effective3 d m buffer N pre ≤ thirdExponent N pre - buffer := by
  have ht := thirdCap_interval m buffer N pre hg
  have ho := originalSeed_third_buffer d he N pre hlen hs hg
  exact ⟨le_max_left _ _, ht.1.trans (le_max_right _ _), max_le (by linarith) ht.2⟩

/-- One finite table, one positive buffer, before every N and prime history.
The existing historical e is fixed first and never replaced or retuned. -/
theorem exists_one_preN_buffered_fallback (d : OriginalData) (he : 0 < (d.e : ℝ))
    (eta : ℝ) (heta : 0 < eta) :
    ∃ m : ℕ, ∃ buffer : ℚ, 0 < (buffer : ℝ) ∧ (buffer : ℝ) < eta ∧
      (buffer : ℝ) ≤ 2 * (d.e : ℝ) ∧
      ∀ N : ℝ, ∀ pre : List ℕ, 3 ≤ pre.length → selectedThird d N pre →
        (secondGuard N pre → originalSeed d N pre ≤ effective2 d m buffer N pre ∧
          effective2 d m buffer N pre ≤ secondExponent N pre - buffer ∧
          secondExponent N pre - effective2 d m buffer N pre < eta) ∧
        (thirdGuard N pre → originalSeed d N pre ≤ effective3 d m buffer N pre ∧
          effective3 d m buffer N pre ≤ thirdExponent N pre - buffer ∧
          thirdExponent N pre - effective3 d m buffer N pre < eta) := by
  obtain ⟨buffer, hb, hbmin⟩ := exists_rat_btwn
    (show (0 : ℝ) < min (d.e : ℝ) (eta / 4) from lt_min he (by positivity))
  have hbe : (buffer : ℝ) ≤ 2 * (d.e : ℝ) :=
    (hbmin.le.trans (min_le_left _ _)).trans (by linarith)
  have hbq : (buffer : ℝ) ≤ eta / 4 := hbmin.le.trans (min_le_right _ _)
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp
    ((tendsto_logPrimeMeshStep 0 (19 / 96)).eventually
      (gt_mem_nhds (show (0 : ℝ) < eta / 12 by positivity)))
  have hs : step m < eta / 12 := hm m le_rfl
  refine ⟨m, buffer, hb, by linarith, hbe, ?_⟩
  intro N pre hlen hselected
  constructor
  · intro hg
    obtain ⟨ho, hlo, hhi⟩ := effective2_interval d he.le m buffer N hbe pre hlen hselected hg
    exact ⟨ho, hhi, by linarith⟩
  · intro hg
    obtain ⟨ho, hlo, hhi⟩ := effective3_interval d he.le m buffer N hbe pre hlen hselected hg
    exact ⟨ho, hhi, by linarith⟩

/-- These are physical Rosser decisions. Earlier stages and unsupported
histories are retained literally, including open inherited regions. -/
def bufferedSecondPolicy (d : OriginalData) (m : ℕ) (buffer N : ℝ)
    (positive : Bool) (pre : List ℕ) : Bool :=
  if pre.length ≤ 2 then old3 d N positive pre
  else if selectedThird d N pre ∧ secondGuard N pre then
    ordinaryParityRosserPolicy false (N ^ effective2 d m buffer N pre) positive pre
  else old3 d N positive pre

def bufferedThirdPolicy (d : OriginalData) (m : ℕ) (buffer N : ℝ)
    (positive : Bool) (pre : List ℕ) : Bool :=
  if pre.length ≤ 3 then bufferedSecondPolicy d m buffer N positive pre
  else if selectedThird d N pre ∧ thirdGuard N pre then
    ordinaryParityRosserPolicy false (N ^ effective3 d m buffer N pre) positive pre
  else bufferedSecondPolicy d m buffer N positive pre

theorem buffered_third_preserves_rank_three (d : OriginalData) (m : ℕ)
    (buffer N : ℝ) (positive : Bool) (pre : List ℕ) (hlen : pre.length ≤ 3) :
    bufferedThirdPolicy d m buffer N positive pre =
      bufferedSecondPolicy d m buffer N positive pre := by
  simp only [bufferedThirdPolicy, if_pos hlen]

theorem buffered_preserves_first_two (d : OriginalData) (m : ℕ)
    (buffer N : ℝ) (positive : Bool) (pre : List ℕ) (hlen : pre.length ≤ 2) :
    bufferedThirdPolicy d m buffer N positive pre = old3 d N positive pre := by
  simp only [bufferedThirdPolicy, if_pos (show pre.length ≤ 3 by omega),
    bufferedSecondPolicy, if_pos hlen]

theorem buffered_inherit_exact (d : OriginalData) (m : ℕ)
    (buffer N : ℝ) (positive : Bool) (pre : List ℕ)
    (hs : ¬selectedThird d N pre) :
    bufferedThirdPolicy d m buffer N positive pre = old3 d N positive pre := by
  simp [bufferedThirdPolicy, bufferedSecondPolicy, hs]

private theorem old_retained_at_larger_exponent (d : OriginalData) (N : ℝ)
    (hN : 1 ≤ N) (positive : Bool) (pre : List ℕ) (hlen : 3 ≤ pre.length)
    (a : ℝ) (ha : originalSeed d N pre ≤ a)
    (ho : old3 d N positive pre = true) :
    ordinaryParityRosserPolicy false (N ^ a) positive pre = true := by
  rw [P5OriginalCommonRefinedPreservation.old3_after_two d N positive pre (by omega)] at ho
  cases positive with
  | true => simp [ordinaryParityRosserPolicy, oddFirstExitPolicy]
  | false =>
      have hh : ordinaryRosserPrefixAdmissible false (N ^ originalSeed d N pre) pre := by
        simpa only [ordinaryParityRosserPolicy, Bool.false_eq_true, if_false,
          oddFirstExitPolicy, Bool.false_or, decide_eq_true_eq] using ho
      have hn := ordinaryRosserPrefixAdmissible_mono false pre
        (Real.rpow_le_rpow_of_exponent_le hN ha) hh
      simp only [ordinaryParityRosserPolicy, Bool.false_eq_true, if_false,
        oddFirstExitPolicy, Bool.false_or, decide_eq_true_eq]
      exact hn

theorem bufferedSecond_preserves_old_decision (d : OriginalData) (m : ℕ)
    (buffer N : ℝ) (hN : 1 ≤ N) (positive : Bool) (pre : List ℕ)
    (ho : old3 d N positive pre = true) :
    bufferedSecondPolicy d m buffer N positive pre = true := by
  unfold bufferedSecondPolicy
  split_ifs with hlen hactive
  · exact ho
  · exact old_retained_at_larger_exponent d N hN positive pre (by omega) _
      (le_max_left _ _) ho
  · exact ho

theorem buffered_preserves_old_decision (d : OriginalData) (m : ℕ)
    (buffer N : ℝ) (hN : 1 ≤ N) (positive : Bool) (pre : List ℕ)
    (ho : old3 d N positive pre = true) :
    bufferedThirdPolicy d m buffer N positive pre = true := by
  unfold bufferedThirdPolicy
  split_ifs with hlen hactive
  · exact bufferedSecond_preserves_old_decision d m buffer N hN positive pre ho
  · exact old_retained_at_larger_exponent d N hN positive pre (by omega) _
      (le_max_left _ _) ho
  · exact bufferedSecond_preserves_old_decision d m buffer N hN positive pre ho

theorem buffered_even (d : OriginalData) (m : ℕ) (buffer N : ℝ) (pre : List ℕ) :
    bufferedThirdPolicy d m buffer N true pre = true := by
  simp [bufferedThirdPolicy, bufferedSecondPolicy, old3,
    HistoricalThirdCoarse.policy_even, ordinaryParityRosserPolicy, oddFirstExitPolicy]

end
end ImbalancedChen.P4AOriginalBufferedFallbackCaps
