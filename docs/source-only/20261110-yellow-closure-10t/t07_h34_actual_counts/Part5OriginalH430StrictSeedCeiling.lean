import ImbalancedChen.Part5OriginalH430HistoryQuotientCounts
import ImbalancedChen.FinitePrimeGeometryCore

/-! Exact rational cutoffs versus genuine old primes in the frozen 430 family.
The complete frozen level is rational even at a real source exponent and
real reserve. Clearing its denominator rules out exact equality of a
target-coprime prime factor with a rational power of the target. This
gives the manuscript's strict 11/5 seed comparison on actual positive
seed requests, including the closed endpoint. -/

namespace ImbalancedChen.Part5OriginalH430StrictSeedCeiling

noncomputable section
open scoped Classical BigOperators
open P2PhysicalIncomingPrefixCells
open P2Selected430CausalOccurrenceExporter (iterate seed queryCell)
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430CutoffCoherence
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedMember Part5OriginalH430TaggedArithmeticReceivers

private theorem raw_lower_rational (n : ℕ) (x : ℝ) :
    ∃ u v : ℕ, 0 < v ∧ rawLower n x = (u : ℝ)/v := by
  cases h : exponentCode 0 1 n x with
  | none =>
      exact ⟨1, 1, by decide, by simp [rawLower, h, lowerEndpoint]⟩
  | some i =>
      refine ⟨i.val, n+1, Nat.succ_pos _, ?_⟩
      simp only [rawLower, h, lowerEndpoint, logPrimeMeshPoint, logPrimeMeshStep,
        zero_add, sub_zero, Nat.cast_add, Nat.cast_one] <;> ring

/-- A finite maximum selects one of the original rational grid levels.
There is no rationality requirement on the real root or its reserve. -/
theorem frozen_level_rational (n : ℕ) (x : ℝ) :
    ∃ u v : ℕ, 0 < v ∧ frozenLevel n x = (u : ℝ)/v := by
  induction n with
  | zero => exact raw_lower_rational 0 x
  | succ n ih =>
      change ∃ u v : ℕ, 0 < v ∧ max (frozenLevel n x) (rawLower (n+1) x) = _
      rcases le_total (frozenLevel n x) (rawLower (n+1) x) with h | h
      · rw [max_eq_right h]
        exact raw_lower_rational (n+1) x
      · rw [max_eq_left h]
        exact ih

theorem frozen_root_power (N n p : ℕ) (k : Root) (tau : ℝ) :
    ∃ u v : ℕ, 0 < v ∧ rootQ N n k tau p ^ v = (N : ℝ)^u := by
  obtain ⟨u, v, hv, hx⟩ := frozen_level_rational n
    (sourceRoot k tau (physicalPrime N p)).physical.total
  refine ⟨u,v,hv,?_⟩
  have hv' : (v : ℝ) ≠ 0 := (Nat.cast_pos.mpr hv).ne'
  change ((N : ℝ)^(frozenLevel n _))^v = _
  rw [hx]
  calc
    ((N : ℝ)^((u : ℝ)/v))^v = (N : ℝ)^(((u : ℝ)/v)*(v : ℝ)) := by
      rw [Real.rpow_mul (Nat.cast_nonneg N), Real.rpow_natCast]
    _ = _ := by rw [div_mul_cancel₀ _ hv', Real.rpow_natCast]

private theorem divides_own_pos_power (q : ℕ) {v : ℕ} (hv : 0 < v) : q ∣ q^v := by
  cases v with
  | zero => omega
  | succ v =>
      rw [pow_succ]
      exact ⟨q^v, Nat.mul_comm _ _⟩

/-- A true integer full or selected square product with a prime factor
q∤N cannot equal *any* natural power of this very frozen level Q.
Either side of a weak inequality may still occur. -/
theorem root_power_ne_coprime_multiple {N p q D : ℕ} (n e : ℕ) (k : Root) (tau : ℝ)
    (hq : q.Prime) (hcop : q.Coprime N) (hD : q ∣ D) :
    rootQ N n k tau p ^ e ≠ (D : ℝ) := by
  intro he
  obtain ⟨u, v, hv, hroot⟩ := frozen_root_power N n p k tau
  have hreal : ((N : ℝ)^u)^e = (D : ℝ)^v := by
    rw [← hroot, ← pow_mul, Nat.mul_comm v e, pow_mul, he]
  have hnat : (N^u)^e = D^v := by exact_mod_cast hreal
  have hqd := hD.trans (divides_own_pos_power D hv)
  rw [← hnat] at hqd
  exact (hq.coprime_iff_not_dvd.mp hcop) (hq.dvd_of_dvd_pow (hq.dvd_of_dvd_pow hqd))

private theorem ceiling_perform (v : PhysicalNode) (s : StepShape) (z : Point)
    (hv : v.ceiling ∈ word v) : (perform v s z).ceiling ∈ word (perform v s z) := by
  have hone (x w : ℝ) : (appendOne v x w).ceiling ∈ word (appendOne v x w) := by
    rw [word_appendOne]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  have hpair (x y w : ℝ) : (appendPair v x y w).ceiling ∈ word (appendPair v x y w) := by
    rw [word_appendPair]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))))
  cases s <;> first | exact hv | exact hone _ _ | exact hpair _ _ _

private theorem ceiling_replay {N : ℕ} (r : Request) (es : List (Edge N))
    (hr : r.node.physical.ceiling ∈ word r.node.physical) :
    (replay r es).node.physical.ceiling ∈ word (replay r es).node.physical := by
  induction es generalizing r with
  | nil => exact hr
  | cons e es ih => exact ih (nextRequest r e)
      (ceiling_perform r.node.physical (edgeShape e) (edgeCoordinates e) hr)

theorem history_ceiling_is_old_prime {N n p : ℕ} {k : Root} {tau : ℝ}
    {o : Occurrence N} (hN : 2 ≤ N) (ht : 0 ≤ tau) (hu : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) (hp : p ∈ originalBand N k)
    (ho : o ∈ rootHistory N n k tau p) :
    ∃ q ∈ o.current.old, q.Prime ∧ q.Coprime N ∧
      physicalPrime N q = o.current.node.physical.ceiling := by
  have hc := rootHistory_coherent (by omega : 1 < N) ht hu hn
    (original_band_prime hp) (original_band_geometry hN hp) ho
  have hroot : (rootRequest N n k tau p).node.physical.ceiling ∈
      word (rootRequest N n k tau p).node.physical := by
    simp [rootRequest, frozenRoot, sourceRoot, word]
  have hmem : o.current.node.physical.ceiling ∈ word o.current.node.physical := by
    rw [(history_facts ho).2.2]
    exact ceiling_replay _ _ hroot
  rw [rootHistory_integer_word ho] at hmem
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hmem
  exact ⟨q, hq, (hc.letters q hq).1, (hc.letters q hq).2, he⟩

/-- At this same frozen Q, a weak prefix-square test on a genuine old
prime is equivalent to its strict test. The integer B is the accumulated
prefix, including the full selected product on a complement lane. This
preserves failed tests as well as successful ones. -/
theorem history_integer_square_iff_strict {N n p q : ℕ} {k : Root} {tau : ℝ}
    {o : Occurrence N} (hN : 2 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) (hp : p ∈ originalBand N k)
    (ho : o ∈ rootHistory N n k tau p) (hq : q ∈ o.current.old) (B : ℕ) :
    (B : ℝ)*(q : ℝ)^2 ≤ rootQ N n k tau p ↔
      (B : ℝ)*(q : ℝ)^2 < rootQ N n k tau p := by
  have hc := rootHistory_coherent (by omega : 1 < N) ht ht' hn
    (original_band_prime hp) (original_band_geometry hN hp) ho
  have hh := root_power_ne_coprime_multiple (p := p) n 1 k tau
    (hc.letters q hq).1 (hc.letters q hq).2
    (dvd_mul_of_dvd_right (divides_own_pos_power q (show 0 < 2 by decide)) B)
  simp only [pow_one, Nat.cast_mul, Nat.cast_pow] at hh
  exact ⟨fun hle => lt_of_le_of_ne hle hh.symm, le_of_lt⟩

/-- Any positive rational requested cutoff has a genuine strict or
opposite side at this arithmetic occurrence. The actual root Q,
complete parent product d, and old ceiling q are all retained. -/
theorem history_rational_cutoff_ne_ceiling {N n p : ℕ} {k : Root} {tau : ℝ}
    {o : Occurrence N} (hN : 2 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) (hp : p ∈ originalBand N k)
    (ho : o ∈ rootHistory N n k tau p) {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    residual o.current.node.physical / ((u : ℝ)/v) ≠ o.current.node.physical.ceiling := by
  intro heq
  obtain ⟨q, _, hpr, hcop, hceil⟩ := history_ceiling_is_old_prime hN ht ht' hn hp ho
  let d := parentProduct o.current.old
  let L := residual o.current.node.physical
  have hden : (u : ℝ)/v ≠ 0 := (div_pos (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hv)).ne'
  have hreal : L*(v : ℝ) = physicalPrime N q*(u : ℝ) := by
    have hh : L = physicalPrime N q*((u : ℝ)/v) := by
      rw [hceil]
      exact (div_eq_iff hden).mp heq
    rw [hh]
    field_simp [(Nat.cast_pos.mpr hv).ne'] <;> ring
  have hrecover : (N : ℝ) ^ physicalPrime N q = (q : ℝ) := by
    have hh := actualPrimeTupleLog_rpow (by omega : 1 < N) ![q]
      (fun i => by fin_cases i; exact hpr.pos) 0
    exact hh
  have hpowers : ((N : ℝ)^L)^v = (q : ℝ)^u := by
    calc
      ((N : ℝ)^L)^v = (N : ℝ)^(L*(v : ℝ)) := by
        rw [Real.rpow_mul (Nat.cast_nonneg N), Real.rpow_natCast]
      _ = (N : ℝ)^(physicalPrime N q*(u : ℝ)) := by rw [hreal]
      _ = (q : ℝ)^u := by
        rw [Real.rpow_mul (Nat.cast_nonneg N), Real.rpow_natCast, hrecover]
  have hs := rootHistory_support (by omega : 1 < N) ht ht' hn
    (original_band_prime hp) (original_band_geometry hN hp) ho
  have hQ : rootQ N n k tau p = (d : ℝ)*(N : ℝ)^L := by
    dsimp only [d,L]
    rw [hs.2.1]
    exact hs.2.2.2.2.2
  have hbad : rootQ N n k tau p ^ v = ((d^v*q^u : ℕ) : ℝ) := by
    rw [hQ, mul_pow, hpowers, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  exact root_power_ne_coprime_multiple n v k tau hpr hcop
    (dvd_mul_of_dvd_right (divides_own_pos_power q hu) (d^v)) hbad

theorem history_strict_rational_cutoff {N n p : ℕ} {k : Root} {tau : ℝ}
    {o : Occurrence N} (hN : 2 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) (hp : p ∈ originalBand N k)
    (ho : o ∈ rootHistory N n k tau p) {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hs : o.current.node.physical.argument ≤ (u : ℝ)/v) :
    residual o.current.node.physical / ((u : ℝ)/v) < o.current.node.physical.ceiling := by
  have hc := rootHistory_coherent (by omega : 1 < N) ht ht' hn
    (original_band_prime hp) (original_band_geometry hN hp) ho
  exact lt_of_le_of_ne
    (target_cutoff_le_ceiling hc.ceiling_pos hc.cutoff_fits
      (div_pos (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hv)) hs)
    (history_rational_cutoff_ne_ceiling hN ht ht' hn hp ho hu hv)

/-- At every genuine positive generation-zero inherited or scalar request,
the literal adopted 2327/100000 seed is supported on i<60, so the source
argument is at most 11/5. Its original enhanced ceiling test is strict
even at the closed right endpoint. This proves admission geometry, not
the initial 1/50 counting estimate or its four feedback rounds. -/
theorem actual_positive_seed_strict_ceiling {N n p : ℕ} {k : Root} {tau : ℝ}
    {o : Occurrence N} (hN : 2 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) (hp : p ∈ originalBand N k)
    (ho : o ∈ rootHistory N n k tau p)
    (hpositive : 0 < requestValue (iterate 0) o.current) :
    residual o.current.node.physical / (11/5 : ℝ) < o.current.node.physical.ceiling := by
  have hc := rootHistory_coherent (by omega : 1 < N) ht ht' hn
    (original_band_prime hp) (original_band_geometry hN hp) ho
  cases hi : resolve 0 o.current with
  | none => exact False.elim ((lt_irrefl 0) (hpositive.trans_le (resolve_none_value hi).le))
  | some i =>
      have hread := resolve_value hi
      rw [hread] at hpositive
      have hind : i.val < 60 := by
        by_contra h
        simp [iterate, seed, h, Part5OriginalUpsilon5CausalDictionary.floorValue] at hpositive
      have hcell := resolve_contains hc.read_valid hi
      have hright : o.current.node.physical.argument ≤ 1+((i.val : ℝ)+1)/50 := hcell.2
      have hnum : (i.val : ℝ) ≤ 59 := by exact_mod_cast (show i.val ≤ 59 by omega)
      exact history_strict_rational_cutoff hN ht ht' hn hp ho
        (u := 11) (v := 5) (by decide) (by decide) (by norm_num; linarith)

end
end ImbalancedChen.Part5OriginalH430StrictSeedCeiling
