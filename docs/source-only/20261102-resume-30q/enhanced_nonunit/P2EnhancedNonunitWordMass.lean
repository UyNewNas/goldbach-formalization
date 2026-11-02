import ImbalancedChen.P2EnhancedNonunitLabelGeometry
import ImbalancedChen.P2EnhancedReceiverRoughPurification

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual ordinary rough nonunit source upper mass on the complete original
word. The scalar error is paid by the native reciprocal prime mass, and
the finite main is compared with the closed affine word at the SAME
true alpha. Both uniform thresholds precede Q,d and all source labels.
-/

namespace ImbalancedChen.P2EnhancedNonunitWordMass
noncomputable section
open Real Finset Set Filter MeasureTheory Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedSwitchedUnsiftedSource P2EnhancedSwitchedTrueNormalization
open P2EnhancedNonunitPhysicalQuadrature P2EnhancedNonunitLabelGeometry
open scoped Classical BigOperators Topology

def selectedWord (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) (j : Fin cs.length) : ℝ :=
  ∑ l ∈ labels N Q d cs,
    (((roughNumbers ((N : ℝ)/(d*l.prod : ℕ)) (l.getD j 0)).erase 1).card : ℝ)

def wordIntegral (c : ℕ) (cs : List ℕ) (j : Fin (c::cs).length) (alpha : ℝ) : ℝ :=
  closedIntegral j (rows cs.length) alpha (wordIntercept cs.length (c::cs))

def rawScale (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ := (N : ℝ)/((d : ℝ)*log (Q/d))

/-- Rejoin the new erase-one source to P's inclusive ordinary source.
The unit on the RHS is exactly O's original unsifted unit carrier. -/
theorem ordinary_word_unit_nonunit {N d : ℕ} (hd : 0 < d) (Q : ℝ) (cs : List ℕ) :
    P2EnhancedReceiverRoughPurification.ordinaryWordMass N Q d cs =
      unitWordMass N Q d cs + ordinaryNonunitWord N Q d cs := by
  unfold P2EnhancedReceiverRoughPurification.ordinaryWordMass unitWordMass ordinaryNonunitWord
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro l hl
  have hD : 0 < d*l.prod := Nat.mul_pos hd (label_prod_pos hl)
  have hcap : (1 : ℝ) ≤ (N : ℝ)/(d*l.prod : ℕ) ↔ d*l.prod ≤ N := by
    rw [le_div_iff₀ (Nat.cast_pos.mpr hD), one_mul]
    exact_mod_cast Iff.rfl
  rw [InclusiveRoughUniform.card_eq_unit_add_erase_real, unit_card hD, hcap]
  split_ifs <;> norm_num

/-- Explicit full-dimensional original word kernel. Equality at the
nonunit legal face is retained, as are all closed order/window faces. -/
theorem wordIntegral_literal (c : ℕ) (cs : List ℕ)
    (j : Fin (c::cs).length) (alpha : ℝ) :
    wordIntegral c cs j alpha =
      ∫ t in continuousCube (c::cs).length,
        if ((∀ k : Fin cs.length, t k.castSucc ≤ t k.succ) ∧
            ∀ k, bandLo ((c::cs).getD k 0) ≤ t k ∧ t k ≤ bandHi ((c::cs).getD k 0)) ∧
            (∑ i, t i) + t j ≤ alpha
        then buchstab ((alpha - ∑ i, t i)/t j)/(t j * ∏ i, t i) else 0 := by
  unfold wordIntegral closedIntegral
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [rows_iff, HighNonunitLegal.G, HighNonunitLegal.legal,
    Set.indicator_apply, Set.mem_setOf_eq, continuousDensity,
    prod_div_distrib, prod_const_one]
  split_ifs <;> simp_all [div_eq_mul_inv, mul_inv_rev] <;> ring

theorem label_kernel {N d : ℕ} {Q : ℝ} (hN : 0 < N) (hd : 0 < d)
    (hR : 1 < Q/d) (cs : List ℕ) (j : Fin cs.length) (l : labels N Q d cs) :
    let f := labelEmbedding hR cs l
    let t := gridCoordinates (Q/d) f
    let p := l.val.getD j 0
    let x := (N : ℝ)/(d*l.val.prod : ℕ)
    (t ∈ HighNonunitLegal.legal j (trueAlpha N Q d) ↔ (p : ℝ) ≤ x) ∧
    ((p : ℝ) ≤ x →
      buchstab (log x/log p)*x/log p =
        rawScale N Q d * primeSlabWeight (Q/d) f *
          HighNonunitLegal.G j (trueAlpha N Q d) t) ∧
    x/log p = rawScale N Q d * primeSlabWeight (Q/d) f * (1/t j) := by
  dsimp only
  let f := labelEmbedding hR cs l
  let t := gridCoordinates (Q/d) f
  let p := l.val.getD j 0
  let x := (N : ℝ)/(d*l.val.prod : ℕ)
  have hpdata := (mem_primesIcc (rpow_nonneg (zero_lt_one.trans hR).le _)).mp
    (f j).property
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpdata.1.one_lt
  have hp0 := zero_lt_one.trans hp1
  have hprod := label_prod_pos l.property
  have hD : 0 < d*l.val.prod := Nat.mul_pos hd hprod
  have hx0 : 0 < x := div_pos (Nat.cast_pos.mpr hN) (Nat.cast_pos.mpr hD)
  have htj : t j = log (p : ℝ)/log (Q/d) := rfl
  have htj0 : 0 < t j := by rw [htj]; exact div_pos (log_pos hp1) (log_pos hR)
  have harg : (trueAlpha N Q d - ∑ i, t i)/t j = log x/log p := by
    rw [htj, label_log_sum hR cs l]
    exact (P2EnhancedReceiverRoughPurification.physical_buchstab_argument
      hN hd hprod hR hp1).symm
  have hlegal : t ∈ HighNonunitLegal.legal j (trueAlpha N Q d) ↔ (p : ℝ) ≤ x := by
    change (∑ i, t i) + t j ≤ trueAlpha N Q d ↔ _
    have h1 : (∑ i, t i) + t j ≤ trueAlpha N Q d ↔
        1 ≤ (trueAlpha N Q d - ∑ i, t i)/t j := by
      rw [le_div_iff₀ htj0]
      constructor <;> intro h <;> linarith
    rw [h1, harg, le_div_iff₀ (log_pos hp1), one_mul]
    exact log_le_log_iff hp0 hx0
  have herror : x/log p = rawScale N Q d * primeSlabWeight (Q/d) f * (1/t j) := by
    rw [htj, label_weight hR cs l]
    dsimp [x, rawScale]
    push_cast
    field_simp [(log_pos hR).ne', (log_pos hp1).ne',
      (Nat.cast_pos.mpr hd : (0 : ℝ) < d).ne',
      (Nat.cast_pos.mpr hprod : (0 : ℝ) < l.val.prod).ne'] <;> ring
  refine ⟨hlegal, ?_, herror⟩
  intro hpx
  rw [HighNonunitLegal.G_of_legal (hlegal.mpr hpx), harg]
  rw [show buchstab (log x/log p)*x/log p = buchstab (log x/log p)*(x/log p) by ring]
  rw [herror]
  ring

theorem label_cutoff_floor {N d : ℕ} {Q eta : ℝ} (hN : 0 < N)
    (hR : 1 < Q/d) (hscale : (N : ℝ)^eta ≤ Q/d)
    (cs : List ℕ) (j : Fin cs.length) (l : labels N Q d cs) :
    (N : ℝ)^(eta/10) ≤ (l.val.getD j 0 : ℝ) := by
  have hp := (mem_primesIcc (rpow_nonneg (zero_lt_one.trans hR).le _)).mp
    (labelEmbedding hR cs l j).property
  calc
    _ = ((N : ℝ)^eta)^(1/10 : ℝ) := by rw [← rpow_mul (Nat.cast_nonneg N)]; congr 1; ring
    _ ≤ (Q/d)^(1/10 : ℝ) := rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg N) _) hscale (by norm_num)
    _ ≤ _ := hp.2.1

/-- One scalar Buchstab threshold, with exact zero beyond the legal
face. The original lists and their target deletions are untouched. -/
theorem scalar_word_upper {eta tau : ℝ} (heta : 0 < eta) (htau : 0 < tau) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ d : ℕ,
      0 < d → (N : ℝ)^eta ≤ Q/d → ∀ cs : List ℕ, ∀ j : Fin cs.length,
      ∀ hR : 1 < Q/d,
      selectedWord N Q d cs j ≤ rawScale N Q d *
        ∑ l : labels N Q d cs, primeSlabWeight (Q/d) (labelEmbedding hR cs l) *
          (HighNonunitLegal.G j (trueAlpha N Q d)
            (gridCoordinates (Q/d) (labelEmbedding hR cs l)) + 10*tau) := by
  obtain ⟨T, hT, hscalar⟩ := NonunitRoughUniform.uniform_upper
    (div_pos heta (by norm_num : (0 : ℝ) < 10)) htau
  refine ⟨T, hT, ?_⟩
  intro N hN Q d hd hscale cs j hR
  have hN4 := hT.trans hN
  have hN0 : 0 < N := by omega
  rw [selectedWord, ← sum_coe_sort (labels N Q d cs), mul_sum]
  apply sum_le_sum
  intro l _
  let f := labelEmbedding hR cs l
  let t := gridCoordinates (Q/d) f
  let p := l.val.getD j 0
  let x := (N : ℝ)/(d*l.val.prod : ℕ)
  have hD : 0 < d*l.val.prod := Nat.mul_pos hd (label_prod_pos l.property)
  have hxN : x ≤ N := div_le_self (Nat.cast_nonneg N) (by exact_mod_cast hD)
  have hy := label_cutoff_floor hN0 hR hscale cs j l
  obtain ⟨hzero, hupper⟩ := hscalar N hN x p hxN hy
  obtain ⟨hlegal, hmain, herr⟩ := label_kernel hN0 hd hR cs j l
  have hscale0 : 0 ≤ rawScale N Q d := div_nonneg (Nat.cast_nonneg N)
    (mul_nonneg (Nat.cast_nonneg d) (log_pos hR).le)
  have hweight : 0 ≤ rawScale N Q d * primeSlabWeight (Q/d) f :=
    mul_nonneg hscale0 (gridWeight_nonneg (Q/d) f)
  have hg := (HighNonunitLegal.G_bounds j (trueAlpha N Q d) (gridCoordinates_mem hR f)).1
  have hcoord := (gridCoordinates_mem hR f j (mem_univ _)).1
  have htpos : 0 < t j := by linarith
  have hinv : 1/t j ≤ 10 := (div_le_iff₀ htpos).mpr (by linarith)
  change (((roughNumbers x p).erase 1).card : ℝ) ≤ _
  by_cases hpx : (p : ℝ) ≤ x
  · have hs := hupper hpx
    have he : (buchstab (log x/log p)+tau)*x/log p =
        rawScale N Q d * primeSlabWeight (Q/d) f *
          (HighNonunitLegal.G j (trueAlpha N Q d) t + tau*(1/t j)) := by
      rw [add_mul, add_div, hmain hpx, show tau*x/log p = tau*(x/log p) by ring, herr]
      ring
    rw [he] at hs
    exact hs.trans (by
      have hh := mul_le_mul_of_nonneg_left hinv htau.le
      have hm := mul_le_mul_of_nonneg_left (add_le_add_left hh
        (HighNonunitLegal.G j (trueAlpha N Q d) t)) hweight
      simpa only [mul_assoc, mul_comm tau 10] using hm)
  · rw [hzero (lt_of_not_ge hpx), Nat.cast_zero]
    exact mul_nonneg (show 0 ≤ rawScale N Q d by
      unfold rawScale; exact div_nonneg (Nat.cast_nonneg N)
        (mul_nonneg (Nat.cast_nonneg d) (log_pos hR).le))
      (mul_nonneg (by unfold primeSlabWeight; positivity) (by linarith))

/-- Closed-mask domination is an injection of complete labels. The
closed sum retains possible diagonal and endpoint atoms on its RHS. -/
theorem labelled_sum_le_closed {N d : ℕ} {Q : ℝ} (hR : 1 < Q/d)
    (c : ℕ) (cs : List ℕ) (j : Fin (c::cs).length) (alpha tau : ℝ) (htau : 0 ≤ tau) :
    (∑ l : labels N Q d (c::cs), primeSlabWeight (Q/d) (labelEmbedding hR (c::cs) l) *
      (HighNonunitLegal.G j alpha
        (gridCoordinates (Q/d) (labelEmbedding hR (c::cs) l)) + 10*tau)) ≤
      closedPrime j (rows cs.length) (Q/d) alpha (wordIntercept cs.length (c::cs)) +
        10*tau * ∑ f : Fin (c::cs).length → primeSlabPrimes (Q/d), primeSlabWeight (Q/d) f := by
  let E := labelEmbedding hR (c::cs)
  let H := fun f : Fin (c::cs).length → primeSlabPrimes (Q/d) =>
    primeSlabWeight (Q/d) f *
      ((if ∀ q, (∑ i, rows cs.length q i * gridCoordinates (Q/d) f i) ≤
          wordIntercept cs.length (c::cs) q
        then HighNonunitLegal.G j alpha (gridCoordinates (Q/d) f) else 0) + 10*tau)
  have hnonneg (f : Fin (c::cs).length → primeSlabPrimes (Q/d)) : 0 ≤ H f := by
    have hg := (HighNonunitLegal.G_bounds j alpha (gridCoordinates_mem hR f)).1
    dsimp [H]
    split_ifs <;> (try unfold primeSlabWeight) <;> positivity
  have hinj := sum_le_sum_of_subset_of_nonneg (subset_univ (univ.image E))
    (fun f _ _ => hnonneg f)
  have hrows (l : labels N Q d (c::cs)) :
      ∀ q, (∑ i, rows cs.length q i * gridCoordinates (Q/d) (E l) i) ≤
        wordIntercept cs.length (c::cs) q := by
    simpa only [Fin.cast_refl] using label_rows hR (c::cs) rfl l
  have hE (l : labels N Q d (c::cs)) :
      H (E l) = primeSlabWeight (Q/d) (E l) *
        (HighNonunitLegal.G j alpha (gridCoordinates (Q/d) (E l)) + 10*tau) := by
    dsimp only [H]
    rw [if_pos (hrows l)]
  rw [sum_image (fun a _ b _ h => E.injective h)] at hinj
  simp only [hE] at hinj
  convert hinj using 1
  rw [closedPrime, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro f _
  dsimp [H]
  ring

/-- Genuine source-to-integral supplier. It applies to every complete
original colour word and any selected prime coordinate. No count,
integral-mass, PP or closed-prime-error estimate is a hypothesis. -/
theorem actual_selected_word_upper (c : ℕ) (cs : List ℕ)
    (j : Fin (c::cs).length) {eta epsilon : ℝ} (heta : 0 < eta) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ d : ℕ,
      0 < d → (N : ℝ)^eta ≤ Q/d → 2 ≤ trueAlpha N Q d →
      selectedWord N Q d (c::cs) j ≤
        rawScale N Q d * (wordIntegral c cs j (trueAlpha N Q d) + epsilon) := by
  let tau := epsilon/(20*(5 : ℝ)^(c::cs).length)
  have htau : 0 < tau := by dsimp [tau]; positivity
  obtain ⟨Ts, hTs, hs⟩ := scalar_word_upper heta htau
  obtain ⟨Tq, _, hq⟩ := physical_closed_rows_uniform cs.length j (rows cs.length)
    (rows_nonzero cs.length) heta (half_pos he)
  obtain ⟨Tm, _, hm⟩ := physical_prime_mass heta
  refine ⟨max Ts (max Tq Tm), hTs.trans (le_max_left _ _), ?_⟩
  intro N hN Q d hd hscale ha
  have hNs : Ts ≤ N := (le_max_left _ _).trans hN
  have hNq : Tq ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNm : Tm ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hN4 := hTs.trans hNs
  have hR : 1 < Q/d :=
    (one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) heta).trans_le hscale
  have hscalar := hs N hNs Q d hd hscale (c::cs) j hR
  have hclosed := labelled_sum_le_closed hR c cs j (trueAlpha N Q d) tau htau.le
  have hmass := hm N hNm Q d hscale (c::cs).length univ
  have hquad := hq N hNq Q d hd hscale ha (wordIntercept cs.length (c::cs))
  have herr := (le_abs_self _).trans hquad.le
  have hpay : 10*tau*(5 : ℝ)^(c::cs).length = epsilon/2 := by
    dsimp [tau]
    field_simp
    ring
  have hfinite :
      (∑ l : labels N Q d (c::cs), primeSlabWeight (Q/d) (labelEmbedding hR (c::cs) l) *
        (HighNonunitLegal.G j (trueAlpha N Q d)
          (gridCoordinates (Q/d) (labelEmbedding hR (c::cs) l)) + 10*tau)) ≤
      wordIntegral c cs j (trueAlpha N Q d) + epsilon := by
    have hb := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 10*tau)
    rw [hpay] at hb
    unfold wordIntegral
    linarith [hclosed]
  exact hscalar.trans (mul_le_mul_of_nonneg_left hfinite (by
    unfold rawScale
    exact div_nonneg (Nat.cast_nonneg N)
      (mul_nonneg (Nat.cast_nonneg d) (log_pos hR).le)))

end
end ImbalancedChen.P2EnhancedNonunitWordMass
