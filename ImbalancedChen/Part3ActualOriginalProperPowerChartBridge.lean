import ImbalancedChen.P5ActualLabelledPrimeSmoothCharts
import ImbalancedChen.Part3OriginalProperPowerChartCount

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / ready=false.
-- The second import is the held Phase6 candidate, not an actual source API.
-- This is the original labelled smooth chart, with its literal eta, psi, W.
-- A proper-power coordinate replaces one prime occurrence; no permutation
-- quotient, new density, signed modulus envelope, or b=T estimate is used.

namespace ImbalancedChen.Part3.OriginalProperPowerActualChart

noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.P5Z.ExactOriginalSmoothDyadicPartition
open ImbalancedChen.P5Z.ActualLabelledPrimeSmoothCharts
open OriginalProperPowerChartCount

def wordVector (k : ℕ) (ps : List ℕ) : Fin k → ℕ :=
  fun i => ps.getD i.val 0

theorem ofFn_wordVector {k : ℕ} {ps : List ℕ} (hlen : ps.length = k) :
    List.ofFn (wordVector k ps) = ps := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i _ hi
    simp only [List.getElem_ofFn, wordVector]
    exact List.getD_eq_getElem _ _ hi

theorem wordVector_injOn_length (k : ℕ) {ps qs : List ℕ}
    (hp : ps.length = k) (hq : qs.length = k)
    (heq : wordVector k ps = wordVector k qs) : ps = qs := by
  calc
    ps = List.ofFn (wordVector k ps) := (ofFn_wordVector hp).symm
    _ = List.ofFn (wordVector k qs) := by rw [heq]
    _ = qs := ofFn_wordVector hq

-- Exact natural upper endpoint of the original smooth chart's j-th scale.
-- Its dependence on the full label word js is preserved coordinatewise.
def chartUpper (k : ℕ) (js : List ℕ) (i : Fin k) : ℕ :=
  2 ^ (js.getD i.val 0 + 1)

def integerWords (cap k : ℕ) : Finset (List ℕ) :=
  words (Finset.Icc 1 cap) k

-- This is a subset of all *integer* chart words, since a proper power is
-- absent from primeTuples. The literal chartTerm controls the support.
def badChartWords (chi eta : ℝ → ℝ) (W : List ℕ → ℂ)
    (T kappa0 : ℝ) (cap k : ℕ) (js : List ℕ) (bad : Fin k) :
    Finset (List ℕ) :=
  (integerWords cap k).filter (fun ps =>
    chartTerm chi eta W T kappa0 js ps ≠ 0 ∧
      ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ ps.getD bad.val 0 = p ^ e)

theorem badChartWords_spec
    {chi eta : ℝ → ℝ} {W : List ℕ → ℂ} {T kappa0 : ℝ}
    {cap k : ℕ} {js : List ℕ} {bad : Fin k} {ps : List ℕ}
    (hps : ps ∈ badChartWords chi eta W T kappa0 cap k js bad) :
    ps.length = k ∧ (∀ n ∈ ps, 1 ≤ n ∧ n ≤ cap) ∧
      chartTerm chi eta W T kappa0 js ps ≠ 0 ∧
      (∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ ps.getD bad.val 0 = p ^ e) := by
  obtain ⟨hword,hactive,hpower⟩ := Finset.mem_filter.mp hps
  obtain ⟨hlen,hmem⟩ := words_spec (Finset.Icc 1 cap) k ps hword
  exact ⟨hlen,fun n hn => Finset.mem_Icc.mp (hmem n hn),hactive,hpower⟩

-- The replacement word is injected, in its original occurrence order, into
-- the Phase6 proper-power Cartesian box. The chart profile controls each
-- coordinate, including the composite coordinate; no prime-tuple theorem
-- is misapplied to it.
theorem active_bad_word_in_chart_box
    (chi eta : ℝ → ℝ) (W : List ℕ → ℂ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (cap k : ℕ) (T kappa0 : ℝ) {js : List ℕ} (bad : Fin k)
    (hjs : js ∈ chartBank cap k) {ps : List ℕ}
    (hps : ps ∈ badChartWords chi eta W T kappa0 cap k js bad) :
    wordVector k ps ∈ oneBadSlotBox (chartUpper k js) bad := by
  obtain ⟨hplen,hpositive,hactive,p,e,hp,he,hpower⟩ := badChartWords_spec hps
  have hjlen := (words_spec (Finset.range (cutoffIndex cap+1)) k js hjs).1
  have hprofile : tupleProfile chi js ps ≠ 0 := (mul_ne_zero_iff.mp hactive).1
  have hcoord := profile_nonzero_support chi hone hzero js ps hprofile
  apply Finset.mem_piFinset.mpr
  intro i
  have hpi : i.val < ps.length := by simpa [hplen] using i.isLt
  have hji : i.val < js.length := by simpa [hjlen] using i.isLt
  have hpair := List.Forall₂.get hcoord hji hpi
  have hupperReal : (ps.getD i.val 0 : ℝ) ≤
      (chartUpper k js i : ℝ) := by
    have hgetp : ps.getD i.val 0 = ps[i.val] :=
      List.getD_eq_getElem _ _ hpi
    have hgetj : js.getD i.val 0 = js[i.val] :=
      List.getD_eq_getElem _ _ hji
    rw [hgetp]
    change (ps[i.val] : ℝ) ≤ (2 ^ (js.getD i.val 0 + 1) : ℕ)
    rw [hgetj]
    have hscale : (2 * R js[i.val] : ℝ) =
        ((2 ^ (js[i.val] + 1) : ℕ) : ℝ) := by
      simp [R, pow_succ, mul_comm]
    rw [← hscale]
    exact hpair.2.2
  have hupperNat : ps.getD i.val 0 ≤ chartUpper k js i :=
    by exact_mod_cast hupperReal
  have hlowNat : 1 ≤ ps.getD i.val 0 := by
    rw [List.getD_eq_getElem _ _ hpi]
    exact (hpositive ps[i.val] (List.getElem_mem hpi)).1
  by_cases hib : i = bad
  · subst i
    simp only [if_pos rfl, wordVector]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hlowNat,hupperNat⟩,?_⟩
    exact ⟨p,e,hp,he,hpower⟩
  · simp only [if_neg hib, wordVector]
    exact Finset.mem_Icc.mpr ⟨hlowNat,hupperNat⟩

theorem badChartWords_image_subset_box
    (chi eta : ℝ → ℝ) (W : List ℕ → ℂ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (cap k : ℕ) (T kappa0 : ℝ) {js : List ℕ} (bad : Fin k)
    (hjs : js ∈ chartBank cap k) :
    (badChartWords chi eta W T kappa0 cap k js bad).image (wordVector k) ⊆
      oneBadSlotBox (chartUpper k js) bad := by
  intro v hv
  obtain ⟨ps,hps,rfl⟩ := Finset.mem_image.mp hv
  exact active_bad_word_in_chart_box chi eta W hone hzero cap k T kappa0 bad hjs hps

-- The unchanged literal W and any signed residue/mean kernel rho survive
-- the occurrence reindex. The RHS is only an absolute box envelope. Its
-- pointwise W bound and signed q/divisor sum remain separate obligations.
theorem signed_kernel_bad_chart_absolute_box
    (chi eta : ℝ → ℝ) (W : List ℕ → ℂ)
    (rho : ℕ → ℂ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (cap k : ℕ) (T kappa0 : ℝ) {js : List ℕ} (bad : Fin k)
    (hjs : js ∈ chartBank cap k) :
    (∑ ps ∈ badChartWords chi eta W T kappa0 cap k js bad,
      ‖chartTerm chi eta W T kappa0 js ps * rho ps.prod‖) ≤
    ∑ v ∈ oneBadSlotBox (chartUpper k js) bad,
      ‖chartTerm chi eta W T kappa0 js (List.ofFn v) *
        rho (List.ofFn v).prod‖ := by
  let S := badChartWords chi eta W T kappa0 cap k js bad
  have hinj : Set.InjOn (wordVector k) S := by
    intro ps hps qs hqs heq
    exact wordVector_injOn_length k (badChartWords_spec hps).1
      (badChartWords_spec hqs).1 heq
  calc
    (∑ ps ∈ S, ‖chartTerm chi eta W T kappa0 js ps * rho ps.prod‖) =
        ∑ v ∈ S.image (wordVector k),
          ‖chartTerm chi eta W T kappa0 js (List.ofFn v) *
            rho (List.ofFn v).prod‖ := by
              rw [Finset.sum_image hinj]
              apply Finset.sum_congr rfl
              intro ps hps
              rw [ofFn_wordVector (badChartWords_spec hps).1]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (badChartWords_image_subset_box chi eta W hone hzero cap k T kappa0 bad hjs)
      (fun _ _ _ => norm_nonneg _)

-- Smooth geometric support on the replacement integer word is an explicit
-- extension license. The original Phase5 support theorem only quantifies
-- over primeTuples, which cannot include this proper-power coordinate.
theorem active_bad_word_physical_support
    (chi eta : ℝ → ℝ) (W : List ℕ → ℂ)
    (heta : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (cap k : ℕ) {T kappa0 c astar C : ℝ} (hT : 0 < T)
    (hW : ∀ ps ∈ integerWords cap k, W ps ≠ 0 →
      (∀ n ∈ ps, c*T^astar ≤ (n : ℝ)) ∧
        (ps.prod : ℝ) ≤ C*T)
    {js : List ℕ} (bad : Fin k) {ps : List ℕ}
    (hps : ps ∈ badChartWords chi eta W T kappa0 cap k js bad) :
    eta ((ps.prod : ℝ)/T^(1-kappa0)) ≠ 0 ∧ W ps ≠ 0 ∧
      T^(1-kappa0) < (ps.prod : ℝ) ∧
      (∀ n ∈ ps, c*T^astar ≤ (n : ℝ)) ∧
        (ps.prod : ℝ) ≤ C*T := by
  obtain ⟨hword,hactive,_⟩ := Finset.mem_filter.mp hps
  have hh := mul_ne_zero_iff.mp hactive
  have ht := mul_ne_zero_iff.mp hh.2
  have hWne : W ps ≠ 0 := ht.2
  have hetaNe : eta ((ps.prod : ℝ)/T^(1-kappa0)) ≠ 0 := by
    intro he
    exact ht.1 (by simp only [he, Complex.ofReal_zero])
  have htrim : T^(1-kappa0) < (ps.prod : ℝ) := by
    apply lt_of_not_ge
    intro h
    exact hetaNe (heta _ ((div_le_one (Real.rpow_pos_of_pos hT _)).mpr h))
  obtain ⟨hfloor,hcomplete⟩ := hW ps hword hWne
  exact ⟨hetaNe,hWne,htrim,hfloor,hcomplete⟩

-- For an active word, the padded dyadic Cartesian box has complete product
-- at most 5^k times the *actual full replacement word* product. This is the
-- needed bridge from physical product trim to the Phase6 box hypothesis;
-- a single pointwise ps.prod≤C*T does not by itself bound the box.
theorem padded_chart_product_le_five_pow_word
    (chi eta : ℝ → ℝ) (W : List ℕ → ℂ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (cap k : ℕ) (T kappa0 : ℝ) {js : List ℕ} (bad : Fin k)
    (hjs : js ∈ chartBank cap k) {ps : List ℕ}
    (hps : ps ∈ badChartWords chi eta W T kappa0 cap k js bad) :
    (∏ i : Fin k, ((chartUpper k js i + 1 : ℕ) : ℝ)) ≤
      5^k * (ps.prod : ℝ) := by
  obtain ⟨hplen,hpositive,hactive,_⟩ := badChartWords_spec hps
  have hjlen := (words_spec (Finset.range (cutoffIndex cap+1)) k js hjs).1
  have hprofile : tupleProfile chi js ps ≠ 0 := (mul_ne_zero_iff.mp hactive).1
  have hcoord := profile_nonzero_support chi hone hzero js ps hprofile
  have hlocal : ∀ i : Fin k,
      ((chartUpper k js i + 1 : ℕ) : ℝ) ≤
        5 * (wordVector k ps i : ℝ) := by
    intro i
    have hpi : i.val < ps.length := by simpa [hplen] using i.isLt
    have hji : i.val < js.length := by simpa [hjlen] using i.isLt
    have hpair := List.Forall₂.get hcoord hji hpi
    have hpos : (1 : ℝ) ≤ (ps[i.val] : ℝ) := by
      exact_mod_cast (hpositive ps[i.val] (List.getElem_mem hpi)).1
    have hscale : ((chartUpper k js i : ℕ) : ℝ) = 2*R js[i.val] := by
      simp [chartUpper, List.getD_eq_getElem _ _ hji, R, pow_succ, mul_comm]
    have hword : wordVector k ps i = ps[i.val] := by
      exact List.getD_eq_getElem _ _ hpi
    rw [Nat.cast_add, Nat.cast_one, hscale, hword]
    nlinarith [hpair.2.1]
  have hproduct :
      (∏ i : Fin k, ((chartUpper k js i + 1 : ℕ) : ℝ)) ≤
        ∏ i : Fin k, 5 * (wordVector k ps i : ℝ) := by
    apply Finset.prod_le_prod
    · intro i hi
      positivity
    · intro i hi
      exact hlocal i
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin,
    ← List.prod_ofFn, ofFn_wordVector hplen, Nat.cast_prod] using hproduct

theorem padded_chart_product_physical_bound
    (chi eta : ℝ → ℝ) (W : List ℕ → ℂ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (heta : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (cap k : ℕ) {T kappa0 c astar C : ℝ} (hT : 0 < T)
    (hW : ∀ ps ∈ integerWords cap k, W ps ≠ 0 →
      (∀ n ∈ ps, c*T^astar ≤ (n : ℝ)) ∧
        (ps.prod : ℝ) ≤ C*T)
    {js : List ℕ} (bad : Fin k) (hjs : js ∈ chartBank cap k)
    {ps : List ℕ}
    (hps : ps ∈ badChartWords chi eta W T kappa0 cap k js bad)
    (hC : 0 ≤ C) :
    (∏ i : Fin k, ((chartUpper k js i + 1 : ℕ) : ℝ)) ≤
      (5:ℝ)^k * C*T := by
  have hbox := padded_chart_product_le_five_pow_word chi eta W hone hzero
    cap k T kappa0 bad hjs hps
  have hphysical := (active_bad_word_physical_support chi eta W heta cap k
    hT hW bad hps).2.2.2.2
  have hp : 0 ≤ (5:ℝ)^k := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hphysical hp]

end
end ImbalancedChen.Part3.OriginalProperPowerActualChart
