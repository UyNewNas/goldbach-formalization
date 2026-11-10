import ImbalancedChen.P5ExactOriginalSmoothDyadicPartition

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- W can be any one fixed ORIGINAL labelled geometric mark. The same W,
-- tuple, eta and chart appear on both sides of count and exact mean.
-- No claim identifies an arbitrary W with the native ALL16 rho: that
-- identification belongs to the selected-W/tensor source owner.
namespace ImbalancedChen.P5Z.ActualLabelledPrimeSmoothCharts
noncomputable section
open Classical
open scoped BigOperators
open LiteralHeathBrownOccurrenceWords ActualRoughHeathBrownWords
open HBRightClosedDyadicRoles ActualHBDyadicOccurrenceFamily
open ActualHBDyadicProductWindow ActualHBMediumBranchPartition
open ActualMultiGroupHBChartScale ExactOriginalSmoothDyadicPartition

def primeAlphabet (cap : ℕ) : Finset ℕ := (Finset.range (cap+1)).filter Nat.Prime
def primeTuples (cap k : ℕ) : Finset (List ℕ) := words (primeAlphabet cap) k

theorem primeTuples_spec (cap k : ℕ) {ps : List ℕ} (hps : ps ∈ primeTuples cap k) :
    ps.length = k ∧ ∀ p ∈ ps, p.Prime ∧ 1 ≤ p ∧ p ≤ cap := by
  obtain ⟨hlen,hmem⟩ := words_spec (primeAlphabet cap) k ps hps
  refine ⟨hlen,?_⟩
  intro p hp
  obtain ⟨hrange,hprime⟩ := Finset.mem_filter.mp (hmem p hp)
  have hcap := Finset.mem_range.mp hrange
  exact ⟨hprime,by have := hprime.two_le; omega,by omega⟩

theorem primeTuples_mem (cap k : ℕ) (ps : List ℕ) (hlen : ps.length = k)
    (hprime : ∀ p ∈ ps, p.Prime ∧ p ≤ cap) : ps ∈ primeTuples cap k := by
  apply words_mem (primeAlphabet cap) k ps hlen
  intro p hp
  obtain ⟨hpr,hcap⟩ := hprime p hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hcap),hpr⟩

def trimmedWeight (eta : ℝ → ℝ) (W : List ℕ → ℂ) (T kappa0 : ℝ) (ps : List ℕ) : ℂ :=
  (eta ((ps.prod : ℝ)/T^(1-kappa0)) : ℂ)*W ps

def chartTerm (chi eta : ℝ → ℝ) (W : List ℕ → ℂ) (T kappa0 : ℝ)
    (js ps : List ℕ) : ℂ := tupleProfile chi js ps * trimmedWeight eta W T kappa0 ps

theorem prime_tuple_expansion (chi eta : ℝ → ℝ) (W F : List ℕ → ℂ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (cap k : ℕ) (T kappa0 : ℝ) {ps : List ℕ} (hps : ps ∈ primeTuples cap k) :
    trimmedWeight eta W T kappa0 ps*F ps =
      ∑ js ∈ chartBank cap k, chartTerm chi eta W T kappa0 js ps*F ps := by
  obtain ⟨hlen,hprime⟩ := primeTuples_spec cap k hps
  have hpart := chart_partition chi hone hzero cap ps (fun p hp => (hprime p hp).2)
  rw [hlen] at hpart
  calc
    trimmedWeight eta W T kappa0 ps*F ps =
        (∑ js ∈ chartBank cap k, tupleProfile chi js ps)*
          (trimmedWeight eta W T kappa0 ps*F ps) := by rw [hpart,one_mul]
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro js hjs
      unfold chartTerm
      ring

-- F may be the literal residue-count minus exact coprime-mean kernel
-- evaluated at ps.prod. The same formula works for both functionals,
-- every primitive residue and every fixed original marked coefficient.
theorem original_prime_sum_charts (chi eta : ℝ → ℝ) (W F : List ℕ → ℂ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (cap k : ℕ) (T kappa0 : ℝ) :
    (∑ ps ∈ primeTuples cap k, trimmedWeight eta W T kappa0 ps*F ps) =
      ∑ js ∈ chartBank cap k, ∑ ps ∈ primeTuples cap k,
        chartTerm chi eta W T kappa0 js ps*F ps := by
  calc
    _ = ∑ ps ∈ primeTuples cap k, ∑ js ∈ chartBank cap k,
        chartTerm chi eta W T kappa0 js ps*F ps := by
      apply Finset.sum_congr rfl
      intro ps hps
      exact prime_tuple_expansion chi eta W F hone hzero cap k T kappa0 hps
    _ = _ := Finset.sum_comm

theorem profile_nonzero_support (chi : ℝ → ℝ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0) :
    ∀ js ps : List ℕ, tupleProfile chi js ps ≠ 0 →
      List.Forall₂ (fun j p => psi chi ((p : ℝ)/R j) ≠ 0 ∧
        R j/2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*R j) js ps := by
  intro js
  induction js with
  | nil =>
    intro ps hn
    cases ps with
    | nil => exact List.Forall₂.nil
    | cons p ps => simp [tupleProfile] at hn
  | cons j js ih =>
    intro ps hn
    cases ps with
    | nil => simp [tupleProfile] at hn
    | cons p ps =>
      have hh := mul_ne_zero_iff.mp hn
      have hlo : (1/2 : ℝ) ≤ (p : ℝ)/R j := by
        apply le_of_not_gt
        intro h
        exact hh.1 (psi_left chi hone _ h)
      have hhi : (p : ℝ)/R j ≤ 2 := by
        apply le_of_not_gt
        intro h
        exact hh.1 (psi_right chi hzero _ h)
      have hlow := (le_div_iff₀ (R_pos j)).mp hlo
      have hhigh := (div_le_iff₀ (R_pos j)).mp hhi
      exact List.Forall₂.cons ⟨hh.1,by linarith,hhigh⟩ (ih ps hh.2)

-- Nonzero eta is proved on the SAME original mark and complete tuple.
-- This supplies the selected-W compiler's true smooth-trim input.
theorem active_original_chart_support
    (chi eta : ℝ → ℝ) (W : List ℕ → ℂ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (heta : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (cap k : ℕ) {T kappa0 c astar C : ℝ} (hT : 0 < T)
    (hW : ∀ ps ∈ primeTuples cap k, W ps ≠ 0 →
      (∀ p ∈ ps, c*T^astar ≤ (p : ℝ)) ∧ (ps.prod : ℝ) ≤ C*T)
    {js ps : List ℕ} (hjs : js ∈ chartBank cap k) (hps : ps ∈ primeTuples cap k)
    (hactive : chartTerm chi eta W T kappa0 js ps ≠ 0) :
    js.length = k ∧ ps.length = k ∧
      List.Forall₂ (fun j p => psi chi ((p : ℝ)/R j) ≠ 0 ∧
        R j/2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*R j) js ps ∧
      eta ((ps.prod : ℝ)/T^(1-kappa0)) ≠ 0 ∧ W ps ≠ 0 ∧
      T^(1-kappa0) < (ps.prod : ℝ) ∧
      (∀ p ∈ ps, c*T^astar ≤ (p : ℝ)) ∧ (ps.prod : ℝ) ≤ C*T := by
  have hh := mul_ne_zero_iff.mp hactive
  have ht := mul_ne_zero_iff.mp hh.2
  have hWne : W ps ≠ 0 := ht.2
  have hetaNe : eta ((ps.prod : ℝ)/T^(1-kappa0)) ≠ 0 := by
    intro he
    exact ht.1 (by simp only [he,Complex.ofReal_zero])
  have htrim : T^(1-kappa0) < (ps.prod : ℝ) := by
    apply lt_of_not_ge
    intro h
    exact hetaNe (heta _ ((div_le_one (Real.rpow_pos_of_pos hT _)).mpr h))
  have hsupport := hW ps hps hWne
  have hchart := words_spec (Finset.range (cutoffIndex cap+1)) k js hjs
  have hprime := primeTuples_spec cap k hps
  exact ⟨hchart.1,hprime.1,profile_nonzero_support chi hone hzero js ps hh.1,
    hetaNe,hWne,htrim,hsupport.1,hsupport.2⟩

-- Expose the exact local grouped-scale floor needed by the marked W
-- bridge. The complementary dyadic atom is the owner of the ACTUAL
-- complementary integer product, including its unit endpoint atom.
theorem grouped_scale_half_raw (gs : List Group) (left right : List Block) (b : Block)
    (hsplit : blocks gs = left++b::right) :
    ∃ pl p pr, integers gs = pl++p::pr ∧
      List.Forall₂ Owns left pl ∧ Owns b p ∧ List.Forall₂ Owns right pr ∧
      let x : ℝ := (lower b : ℝ)*(lower (owner (pl++pr).prod) : ℝ)
      rawProduct (blocks gs)/2 ≤ x := by
  have hall := all_owns gs
  rw [hsplit] at hall
  obtain ⟨pl,p,pr,hints,hl,hp,hr⟩ := owns_split left right b (integers gs) hall
  have hc := owns_product_window (List.rel_append hl hr)
  have hpos : 0 < ((left++right).map lower).prod := by
    apply List.prod_pos
    intro u hu
    obtain ⟨bb,hbb,rfl⟩ := List.mem_map.mp hu
    exact lower_pos bb
  have hcomp : 0 < (pl++pr).prod := hpos.trans_le hc.1
  have ho := (owns_bounds (owner_owns hcomp)).2
  have hlow : rawProduct (left++right) ≤ ((pl++pr).prod : ℝ) := by exact_mod_cast hc.1
  have hhigh : ((pl++pr).prod : ℝ) ≤ 2*(lower (owner (pl++pr).prod) : ℝ) := by
    exact_mod_cast ho
  have hid : rawProduct (blocks gs) = (lower b : ℝ)*rawProduct (left++right) := by
    rw [hsplit,raw_append,rawProduct_cons,raw_append]
    ring
  have hmul := mul_le_mul_of_nonneg_left (hlow.trans hhigh) (Nat.cast_nonneg (lower b))
  refine ⟨pl,p,pr,hints,hl,hp,hr,?_⟩
  rw [hid]
  linarith

end
end ImbalancedChen.P5Z.ActualLabelledPrimeSmoothCharts
