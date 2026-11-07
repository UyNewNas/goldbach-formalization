import ImbalancedChen.RosserBoxFamilyMargins
import ImbalancedChen.RosserTopStrictFiniteApproximation
import ImbalancedChen.ActualRosserBoxUnionUniformity

/-!
# Local thresholds from actual strict-margin boundary boxes

At the central parameters we freeze finitely many genuine inner prime boxes.
A fixed slightly smaller outer exponent controls every box mass in a whole
neighborhood. The strict finite gates persist there. The target threshold is
selected before the nearby exponents, even target, and enumeration cap.
The comparison is with the canonical continuous factor at the center; this
is the local input for a separate compact-cover argument.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Filter Topology
open MathlibNt.SieveTheory

/-- A single actual upper-density lower threshold holds throughout a
neighborhood of every legal central pair. Pairs are ordered `(u,s)`. -/
theorem exists_actualSmallRosserPlusDensity_local_lower_threshold
    (u0 : ℝ) (hu0 : 0 < u0) (s0 : ℝ) (hs0 : 1 < s0) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ᶠ p : ℝ × ℝ in 𝓝 (u0, s0),
      ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ p.1 ≤ (cap : ℝ) →
        suzukiContinuousUpperFactor s0 - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ p.1) ((N : ℝ) ^ (p.2 * p.1)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ p.1) := by
  obtain ⟨K, n, hcut, happ⟩ :=
    exists_rosserOddTopStrictFiniteApproximation s0 hs0 (eta / 4) (by positivity)
  let J := fun k => rosserOddTopStrictMeshCells k s0 n
  let a := fun (k : ℕ) (j : Fin (2 * k + 1) → Fin (n + 1)) =>
    fun i => u0 * rosserOddMeshLo k s0 n j i
  let b := fun (k : ℕ) (j : Fin (2 * k + 1) → Fin (n + 1)) =>
    fun i => u0 * rosserOddMeshHi k s0 n j i
  let G := ∑ k ∈ K, rosserOddTopStrictMeshLowerSum k s0 n
  have hspos : 0 < s0 := by linarith
  have hmem (k : ℕ) (j : Fin (2 * k + 1) → Fin (n + 1)) (hj : j ∈ J k) :
      j ∈ rosserOddMeshCells k s0 n := (mem_rosserOddTopStrictMeshCells.mp hj).1
  have ha (k : ℕ) (hk : k ∈ K)
      (j : Fin (2 * k + 1) → Fin (n + 1)) (_hj : j ∈ J k)
      (i : Fin (2 * k + 1)) : 0 < a k j i := by
    have hpos : (0 : ℝ) < s0 / 3 ^ (k + 1) := by positivity
    exact mul_pos hu0 (hpos.trans_le (rosserOddMeshLoHi_bounds (hcut k hk) n j i).1)
  have hab (k : ℕ) (hk : k ∈ K)
      (j : Fin (2 * k + 1) → Fin (n + 1)) (_hj : j ∈ J k)
      (i : Fin (2 * k + 1)) : a k j i < b k j i :=
    mul_lt_mul_of_pos_left (rosserOddMeshLoHi_bounds (hcut k hk) n j i).2.1 hu0
  have hsep (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 1) → Fin (n + 1)) (hj : j ∈ J k)
      (i : Fin (2 * k)) : b k j i.succ ≤ a k j i.castSucc :=
    mul_le_mul_of_nonneg_left ((mem_rosserOddMeshCells.mp (hmem k j hj)).1 i) hu0.le
  have htop (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 1) → Fin (n + 1)) (hj : j ∈ J k) : b k j 0 < u0 := by
    simpa only [b, mul_one] using
      mul_lt_mul_of_pos_left (mem_rosserOddTopStrictMeshCells.mp hj).2 hu0
  have hprod (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 1) → Fin (n + 1)) (hj : j ∈ J k) :
      (∑ i : Fin (2 * k), b k j i.castSucc) < s0 * u0 := by
    have h := mul_lt_mul_of_pos_left (mem_rosserOddMeshCells.mp (hmem k j hj)).2.2.1 hu0
    simpa [b, Finset.mul_sum, mul_comm] using h
  have hprefix (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 1) → Fin (n + 1)) (hj : j ∈ J k)
      (i : Fin (2 * k)) (hi : Even i.val) :
      (∑ t : Fin (2 * k) with t.val < i.val, b k j t.castSucc) +
        3 * b k j i.castSucc < s0 * u0 := by
    have h := mul_lt_mul_of_pos_left
      ((mem_rosserOddMeshCells.mp (hmem k j hj)).2.2.2.1 i hi) hu0
    dsimp [b]
    rw [← Finset.mul_sum]
    dsimp [rosserOddLogPrefix] at h
    nlinarith
  have hshell (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 1) → Fin (n + 1)) (hj : j ∈ J k) :
      s0 * u0 < (∑ i : Fin (2 * k), a k j i.castSucc) +
        3 * a k j (Fin.last (2 * k)) := by
    have h := mul_lt_mul_of_pos_left
      (mem_rosserOddMeshCells.mp (hmem k j hj)).2.2.2.2 hu0
    dsimp [a]
    rw [← Finset.mul_sum]
    nlinarith
  have hdisj (k : ℕ) (hk : k ∈ K)
      (j : Fin (2 * k + 1) → Fin (n + 1)) (_hj : j ∈ J k)
      (r : Fin (2 * k + 1) → Fin (n + 1)) (_hr : r ∈ J k) (hjr : j ≠ r) :
      ∃ i, b k j i ≤ a k r i ∨ b k r i ≤ a k j i := by
    obtain ⟨i, hi | hi⟩ := rosserOddMesh_separated (hcut k hk).le hjr
    · exact ⟨i, Or.inl (mul_le_mul_of_nonneg_left hi hu0.le)⟩
    · exact ⟨i, Or.inr (mul_le_mul_of_nonneg_left hi hu0.le)⟩
  obtain ⟨u_min, humin, _hfloor, hmin0, hminTop, hgain⟩ :=
    exists_finite_outer_reference_with_gain (K.sigma J)
      (fun z => b z.1 z.2 0) 0 u0 G (eta / 4) hu0 hu0
      (fun z hz => htop z.1 (Finset.mem_sigma.mp hz).1 z.2 (Finset.mem_sigma.mp hz).2)
      (by positivity)
  have hbu (k : ℕ) (hk : k ∈ K) (j : Fin (2 * k + 1) → Fin (n + 1))
      (hj : j ∈ J k) : b k j 0 ≤ u_min :=
    (hminTop ⟨k, j⟩ (Finset.mem_sigma.mpr ⟨hk, hj⟩)).le
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_oddBoxUnion_uniform_lower_threshold
      K J a b u_min humin ha hab hsep hbu hdisj (eta / 4) (by positivity)
  have heq (k : ℕ) (j : Fin (2 * k + 1) → Fin (n + 1)) :
      (u_min / b k j (Fin.last (2 * k))) * (∏ i, Real.log (b k j i / a k j i)) =
        (u_min / u0) * ((1 / rosserOddMeshHi k s0 n j (Fin.last (2 * k))) *
          (∏ i, Real.log (rosserOddMeshHi k s0 n j i / rosserOddMeshLo k s0 n j i))) := by
    have hratio (i : Fin (2 * k + 1)) : b k j i / a k j i =
        rosserOddMeshHi k s0 n j i / rosserOddMeshLo k s0 n j i := by
      dsimp [a, b]
      exact mul_div_mul_left _ _ hu0.ne'
    simp_rw [hratio]
    dsimp [b]
    rw [div_mul_eq_div_div]
    ring
  have hsum :
      (∑ k ∈ K, ∑ j ∈ J k, (u_min / b k j (Fin.last (2 * k))) *
        (∏ i, Real.log (b k j i / a k j i))) = (u_min / u0) * G := by
    simp_rw [heq]
    simp only [← Finset.mul_sum, J, G, rosserOddTopStrictMeshLowerSum]
  have hp : Tendsto (fun p : ℝ × ℝ => p.2 * p.1) (𝓝 (u0, s0)) (𝓝 (s0 * u0)) :=
    (continuous_snd.mul continuous_fst).continuousAt
  have hpEv : ∀ᶠ p : ℝ × ℝ in 𝓝 (u0, s0),
      ∀ k ∈ K, ∀ j ∈ J k, (∑ i : Fin (2 * k), b k j i.castSucc) ≤ p.2 * p.1 := by
    apply (eventually_all_finset K).mpr
    intro k hk
    apply (eventually_all_finset (J k)).mpr
    intro j hj
    exact (hp.eventually (lt_mem_nhds (hprod k hk j hj))).mono (fun _ h => h.le)
  have hcEv : ∀ᶠ p : ℝ × ℝ in 𝓝 (u0, s0),
      ∀ k ∈ K, ∀ j ∈ J k, ∀ i : Fin (2 * k), Even i.val →
        (∑ t : Fin (2 * k) with t.val < i.val, b k j t.castSucc) +
          3 * b k j i.castSucc ≤ p.2 * p.1 := by
    apply (eventually_all_finset K).mpr
    intro k hk
    apply (eventually_all_finset (J k)).mpr
    intro j hj
    apply eventually_all.mpr
    intro i
    by_cases hi : Even i.val
    · exact (hp.eventually (lt_mem_nhds (hprefix k hk j hj i hi))).mono (fun _ h _ => h.le)
    · exact Eventually.of_forall (fun _ h => (hi h).elim)
  have hsEv : ∀ᶠ p : ℝ × ℝ in 𝓝 (u0, s0),
      ∀ k ∈ K, ∀ j ∈ J k, p.2 * p.1 ≤
        (∑ i : Fin (2 * k), a k j i.castSucc) + 3 * a k j (Fin.last (2 * k)) := by
    apply (eventually_all_finset K).mpr
    intro k hk
    apply (eventually_all_finset (J k)).mpr
    intro j hj
    exact (hp.eventually (gt_mem_nhds (hshell k hk j hj))).mono (fun _ h => h.le)
  have huEv : ∀ᶠ p : ℝ × ℝ in 𝓝 (u0, s0), u_min < p.1 :=
    continuous_fst.continuousAt.eventually (lt_mem_nhds hmin0)
  have hs1Ev : ∀ᶠ p : ℝ × ℝ in 𝓝 (u0, s0), 1 < p.2 :=
    continuous_snd.continuousAt.eventually (lt_mem_nhds hs0)
  refine ⟨N0, hN0, ?_⟩
  filter_upwards [huEv, hs1Ev, hpEv, hcEv, hsEv] with p hpu hps hp' hc' hs'
  intro N hN hEven cap hcap
  have hubeta : p.1 ≤ p.2 * p.1 := by nlinarith
  have h := hbound N hN hEven p.1 (p.2 * p.1) hpu.le hubeta hp' hc' hs' cap hcap
  rw [hsum] at h
  have hg := (abs_lt.mp hgain).1
  change suzukiContinuousUpperFactor s0 - eta / 4 < 1 + G at happ
  linarith

/-- A single actual lower-density upper threshold holds throughout a
neighborhood of every legal central pair. Pairs are ordered `(u,s)`. -/
theorem exists_actualSmallRosserMinusDensity_local_upper_threshold
    (u0 : ℝ) (hu0 : 0 < u0) (s0 : ℝ) (hs0 : 2 ≤ s0) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ᶠ p : ℝ × ℝ in 𝓝 (u0, s0),
      ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ p.1 ≤ (cap : ℝ) →
        actualSmallRosserMinusDensity N cap ((N : ℝ) ^ p.1) ((N : ℝ) ^ (p.2 * p.1)) /
          actualSmallEulerProduct N cap ((N : ℝ) ^ p.1) ≤ suzukiContinuousLowerFactor s0 + eta := by
  obtain ⟨K, n, hcut, happ⟩ :=
    exists_rosserEvenTopStrictFiniteApproximation s0 hs0 (eta / 4) (by positivity)
  let J := fun k => rosserEvenTopStrictMeshCells k s0 n
  let a := fun (k : ℕ) (j : Fin (2 * k + 2) → Fin (n + 1)) =>
    fun i => u0 * rosserEvenMeshLo k s0 n j i
  let b := fun (k : ℕ) (j : Fin (2 * k + 2) → Fin (n + 1)) =>
    fun i => u0 * rosserEvenMeshHi k s0 n j i
  let G := ∑ k ∈ K, rosserEvenTopStrictMeshLowerSum k s0 n
  have hmem (k : ℕ) (j : Fin (2 * k + 2) → Fin (n + 1)) (hj : j ∈ J k) :
      j ∈ rosserEvenMeshCells k s0 n := (mem_rosserEvenTopStrictMeshCells.mp hj).1
  have ha (k : ℕ) (hk : k ∈ K)
      (j : Fin (2 * k + 2) → Fin (n + 1)) (_hj : j ∈ J k)
      (i : Fin (2 * k + 2)) : 0 < a k j i := by
    have hpos : (0 : ℝ) < (s0 - 1) / 3 ^ (k + 1) :=
      div_pos (by linarith) (by positivity)
    exact mul_pos hu0 (hpos.trans_le (rosserEvenMeshLoHi_bounds (hcut k hk) n j i).1)
  have hab (k : ℕ) (hk : k ∈ K)
      (j : Fin (2 * k + 2) → Fin (n + 1)) (_hj : j ∈ J k)
      (i : Fin (2 * k + 2)) : a k j i < b k j i :=
    mul_lt_mul_of_pos_left (rosserEvenMeshLoHi_bounds (hcut k hk) n j i).2.1 hu0
  have hsep (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 2) → Fin (n + 1)) (hj : j ∈ J k)
      (i : Fin (2 * k + 1)) : b k j i.succ ≤ a k j i.castSucc :=
    mul_le_mul_of_nonneg_left ((mem_rosserEvenMeshCells.mp (hmem k j hj)).1 i) hu0.le
  have htop (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 2) → Fin (n + 1)) (hj : j ∈ J k) : b k j 0 < u0 := by
    simpa only [b, mul_one] using
      mul_lt_mul_of_pos_left (mem_rosserEvenTopStrictMeshCells.mp hj).2 hu0
  have hprod (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 2) → Fin (n + 1)) (hj : j ∈ J k) :
      (∑ i : Fin (2 * k + 1), b k j i.castSucc) < s0 * u0 := by
    have h := mul_lt_mul_of_pos_left (mem_rosserEvenMeshCells.mp (hmem k j hj)).2.2.1 hu0
    simpa [b, Finset.mul_sum, mul_comm] using h
  have hprefix (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 2) → Fin (n + 1)) (hj : j ∈ J k)
      (i : Fin (2 * k + 1)) (hi : Odd i.val) :
      (∑ t : Fin (2 * k + 1) with t.val < i.val, b k j t.castSucc) +
        3 * b k j i.castSucc < s0 * u0 := by
    have h := mul_lt_mul_of_pos_left
      ((mem_rosserEvenMeshCells.mp (hmem k j hj)).2.2.2.1 i hi) hu0
    dsimp [b]
    rw [← Finset.mul_sum]
    dsimp [rosserEvenLogPrefix] at h
    nlinarith
  have hshell (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 2) → Fin (n + 1)) (hj : j ∈ J k) :
      s0 * u0 < (∑ i : Fin (2 * k + 1), a k j i.castSucc) +
        3 * a k j (Fin.last (2 * k + 1)) := by
    have h := mul_lt_mul_of_pos_left
      (mem_rosserEvenMeshCells.mp (hmem k j hj)).2.2.2.2 hu0
    dsimp [a]
    rw [← Finset.mul_sum]
    nlinarith
  have hdisj (k : ℕ) (hk : k ∈ K)
      (j : Fin (2 * k + 2) → Fin (n + 1)) (_hj : j ∈ J k)
      (r : Fin (2 * k + 2) → Fin (n + 1)) (_hr : r ∈ J k) (hjr : j ≠ r) :
      ∃ i, b k j i ≤ a k r i ∨ b k r i ≤ a k j i := by
    obtain ⟨i, hi | hi⟩ := rosserEvenMesh_separated (hcut k hk).le hjr
    · exact ⟨i, Or.inl (mul_le_mul_of_nonneg_left hi hu0.le)⟩
    · exact ⟨i, Or.inr (mul_le_mul_of_nonneg_left hi hu0.le)⟩
  obtain ⟨u_min, humin, _hfloor, hmin0, hminTop, hgain⟩ :=
    exists_finite_outer_reference_with_gain (K.sigma J)
      (fun z => b z.1 z.2 0) 0 u0 G (eta / 4) hu0 hu0
      (fun z hz => htop z.1 (Finset.mem_sigma.mp hz).1 z.2 (Finset.mem_sigma.mp hz).2)
      (by positivity)
  have hbu (k : ℕ) (hk : k ∈ K) (j : Fin (2 * k + 2) → Fin (n + 1))
      (hj : j ∈ J k) : b k j 0 ≤ u_min :=
    (hminTop ⟨k, j⟩ (Finset.mem_sigma.mpr ⟨hk, hj⟩)).le
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserMinusDensity_evenBoxUnion_uniform_upper_threshold
      K J a b u_min humin ha hab hsep hbu hdisj (eta / 4) (by positivity)
  have heq (k : ℕ) (j : Fin (2 * k + 2) → Fin (n + 1)) :
      (u_min / b k j (Fin.last (2 * k + 1))) * (∏ i, Real.log (b k j i / a k j i)) =
        (u_min / u0) * ((1 / rosserEvenMeshHi k s0 n j (Fin.last (2 * k + 1))) *
          (∏ i, Real.log (rosserEvenMeshHi k s0 n j i / rosserEvenMeshLo k s0 n j i))) := by
    have hratio (i : Fin (2 * k + 2)) : b k j i / a k j i =
        rosserEvenMeshHi k s0 n j i / rosserEvenMeshLo k s0 n j i := by
      dsimp [a, b]
      exact mul_div_mul_left _ _ hu0.ne'
    simp_rw [hratio]
    dsimp [b]
    rw [div_mul_eq_div_div]
    ring
  have hsum :
      (∑ k ∈ K, ∑ j ∈ J k, (u_min / b k j (Fin.last (2 * k + 1))) *
        (∏ i, Real.log (b k j i / a k j i))) = (u_min / u0) * G := by
    simp_rw [heq]
    simp only [← Finset.mul_sum, J, G, rosserEvenTopStrictMeshLowerSum]
  have hp : Tendsto (fun p : ℝ × ℝ => p.2 * p.1) (𝓝 (u0, s0)) (𝓝 (s0 * u0)) :=
    (continuous_snd.mul continuous_fst).continuousAt
  have hpEv : ∀ᶠ p : ℝ × ℝ in 𝓝 (u0, s0),
      ∀ k ∈ K, ∀ j ∈ J k, (∑ i : Fin (2 * k + 1), b k j i.castSucc) ≤ p.2 * p.1 := by
    apply (eventually_all_finset K).mpr
    intro k hk
    apply (eventually_all_finset (J k)).mpr
    intro j hj
    exact (hp.eventually (lt_mem_nhds (hprod k hk j hj))).mono (fun _ h => h.le)
  have hcEv : ∀ᶠ p : ℝ × ℝ in 𝓝 (u0, s0),
      ∀ k ∈ K, ∀ j ∈ J k, ∀ i : Fin (2 * k + 1), Odd i.val →
        (∑ t : Fin (2 * k + 1) with t.val < i.val, b k j t.castSucc) +
          3 * b k j i.castSucc ≤ p.2 * p.1 := by
    apply (eventually_all_finset K).mpr
    intro k hk
    apply (eventually_all_finset (J k)).mpr
    intro j hj
    apply eventually_all.mpr
    intro i
    by_cases hi : Odd i.val
    · exact (hp.eventually (lt_mem_nhds (hprefix k hk j hj i hi))).mono (fun _ h _ => h.le)
    · exact Eventually.of_forall (fun _ h => (hi h).elim)
  have hsEv : ∀ᶠ p : ℝ × ℝ in 𝓝 (u0, s0),
      ∀ k ∈ K, ∀ j ∈ J k, p.2 * p.1 ≤
        (∑ i : Fin (2 * k + 1), a k j i.castSucc) + 3 * a k j (Fin.last (2 * k + 1)) := by
    apply (eventually_all_finset K).mpr
    intro k hk
    apply (eventually_all_finset (J k)).mpr
    intro j hj
    exact (hp.eventually (gt_mem_nhds (hshell k hk j hj))).mono (fun _ h => h.le)
  have huEv : ∀ᶠ p : ℝ × ℝ in 𝓝 (u0, s0), u_min < p.1 :=
    continuous_fst.continuousAt.eventually (lt_mem_nhds hmin0)
  have hs1Ev : ∀ᶠ p : ℝ × ℝ in 𝓝 (u0, s0), 1 < p.2 :=
    continuous_snd.continuousAt.eventually (lt_mem_nhds (show 1 < s0 by linarith))
  refine ⟨N0, hN0, ?_⟩
  filter_upwards [huEv, hs1Ev, hpEv, hcEv, hsEv] with p hpu hps hp' hc' hs'
  intro N hN hEven cap hcap
  have hubeta : p.1 ≤ p.2 * p.1 := by nlinarith
  have h := hbound N hN hEven p.1 (p.2 * p.1) hpu.le hubeta hp' hc' hs' cap hcap
  rw [hsum] at h
  have hg := (abs_lt.mp hgain).1
  change 1 - G < suzukiContinuousLowerFactor s0 + eta / 4 at happ
  linarith

end

end ImbalancedChen
