import ImbalancedChen.P5OriginalChartRoughCutoff

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- Literal original psi(t)=chi(t)-chi(2t), with exact finite coverage.
-- The common chart bank is fixed from cap BEFORE tuples and BEFORE HB.
namespace ImbalancedChen.P5Z.ExactOriginalSmoothDyadicPartition
noncomputable section
open Classical
open scoped BigOperators
open OriginalChartRoughCutoff

def R (j : ℕ) : ℝ := (2 : ℝ)^j
def bump (chi : ℝ → ℝ) (t : ℝ) : ℝ := chi t-chi (2*t)
def psi (chi : ℝ → ℝ) (t : ℝ) : ℂ := (bump chi t : ℝ)
def cutoffIndex (cap : ℕ) : ℕ := Nat.log2 cap+1

theorem R_pos (j : ℕ) : 0 < R j := by unfold R; positivity

theorem psi_left (chi : ℝ → ℝ) (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (t : ℝ) (ht : t < 1/2) : psi chi t = 0 := by
  have h1 : t ≤ 1 := by linarith
  have h2 : 2*t ≤ 1 := by linarith
  simp only [psi,bump,hone t h1,hone (2*t) h2,sub_self,Complex.ofReal_zero]

theorem psi_right (chi : ℝ → ℝ) (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (t : ℝ) (ht : 2 < t) : psi chi t = 0 := by
  have h2 : 2 ≤ 2*t := by linarith
  simp only [psi,bump,hzero t ht.le,hzero (2*t) h2,sub_self,Complex.ofReal_zero]

theorem bump_bounds (chi : ℝ → ℝ) (hmono : Antitone chi)
    (hchi : ∀ t : ℝ, 0 ≤ chi t ∧ chi t ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ bump chi t ∧ bump chi t ≤ 1 := by
  have hm := hmono (by linarith : t ≤ 2*t)
  obtain ⟨h0,h1⟩ := hchi t
  obtain ⟨h20,h21⟩ := hchi (2*t)
  unfold bump
  constructor <;> linarith

theorem telescope (chi : ℝ → ℝ) (n : ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range (J+1), bump chi (n/R j)) = chi (n/R J)-chi (2*n) := by
  induction J with
  | zero => simp [R,bump]
  | succ J ih =>
    have hmove : 2*(n/R (J+1)) = n/R J := by
      unfold R
      rw [pow_succ]
      field_simp [pow_ne_zero J (by norm_num : (2 : ℝ) ≠ 0)] <;> ring
    rw [Finset.sum_range_succ,ih]
    simp only [bump]
    rw [hmove]
    ring

theorem scalar_partition (chi : ℝ → ℝ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    {p J : ℕ} (hp : 1 ≤ p) (hcap : p ≤ 2^J) :
    (∑ j ∈ Finset.range (J+1), psi chi ((p : ℝ)/R j)) = 1 := by
  have hl : (p : ℝ)/R J ≤ 1 := by
    apply (div_le_one (R_pos J)).mpr
    exact_mod_cast hcap
  have hh : 2 ≤ 2*(p : ℝ) := by exact_mod_cast (show 2 ≤ 2*p by omega)
  have hreal : (∑ j ∈ Finset.range (J+1), bump chi ((p : ℝ)/R j)) = 1 := by
    rw [telescope,hone _ hl,hzero _ hh]
    norm_num
  have hc := congrArg (fun a : ℝ => (a : ℂ)) hreal
  simpa only [psi,Complex.ofReal_sum,Complex.ofReal_one] using hc

-- A single finite word bank serves chart labels and labelled prime
-- tuples. Order and repeated coordinates remain literal occurrences.
def words (A : Finset ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | k+1 => (A.product (words A k)).image (fun q => q.1::q.2)

theorem words_sum_cons (A : Finset ℕ) (k : ℕ) (F : List ℕ → ℂ) :
    (∑ js ∈ words A (k+1), F js) = ∑ j ∈ A, ∑ js ∈ words A k, F (j::js) := by
  rw [words,Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro u hu v hv h
    exact Prod.ext (List.cons.inj h).1 (List.cons.inj h).2

theorem words_spec (A : Finset ℕ) : ∀ k : ℕ, ∀ js ∈ words A k,
    js.length = k ∧ ∀ j ∈ js, j ∈ A := by
  intro k
  induction k with
  | zero =>
    intro js hjs
    have h : js = [] := by simpa [words] using hjs
    subst js
    simp
  | succ k ih =>
    intro js hjs
    obtain ⟨⟨j,tail⟩,hjt,rfl⟩ := Finset.mem_image.mp hjs
    obtain ⟨hj,ht⟩ := Finset.mem_product.mp hjt
    obtain ⟨hlen,hmem⟩ := ih tail ht
    refine ⟨by simp [hlen],?_⟩
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hj
    · exact hmem n hn

theorem words_mem (A : Finset ℕ) : ∀ k : ℕ, ∀ js : List ℕ,
    js.length = k → (∀ j ∈ js, j ∈ A) → js ∈ words A k := by
  intro k
  induction k with
  | zero =>
    intro js hlen hmem
    have hnil : js = [] := List.length_eq_zero.mp hlen
    simp only [hnil,words,Finset.mem_singleton]
  | succ k ih =>
    intro js hlen hmem
    cases js with
    | nil => simp at hlen
    | cons j js =>
      have hj : j ∈ A := hmem j (by simp)
      have htlen : js.length = k := by simpa only [List.length_cons,Nat.succ.injEq] using hlen
      have ht := ih js htlen (fun q hq => hmem q (List.mem_cons_of_mem j hq))
      exact Finset.mem_image.mpr ⟨(j,js),Finset.mem_product.mpr ⟨hj,ht⟩,rfl⟩

def chartBank (cap k : ℕ) : Finset (List ℕ) :=
  words (Finset.range (cutoffIndex cap+1)) k

def tupleProfile (chi : ℝ → ℝ) : List ℕ → List ℕ → ℂ
  | [],[] => 1
  | j::js,p::ps => psi chi ((p : ℝ)/R j)*tupleProfile chi js ps
  | _,_ => 0

theorem chart_partition (chi : ℝ → ℝ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (cap : ℕ) : ∀ ps : List ℕ, (∀ p ∈ ps, 1 ≤ p ∧ p ≤ cap) →
      (∑ js ∈ chartBank cap ps.length, tupleProfile chi js ps) = 1 := by
  intro ps
  induction ps with
  | nil => intro hp; simp [chartBank,words,tupleProfile]
  | cons p ps ih =>
    intro hp
    have hhead := hp p (by simp)
    have htail := ih (fun q hq => hp q (List.mem_cons_of_mem p hq))
    have hpow : cap ≤ 2^(cutoffIndex cap) := Nat.le_of_lt Nat.lt_log2_self
    have hscalar := scalar_partition chi hone hzero hhead.1 (hhead.2.trans hpow)
    change (∑ js ∈ words (Finset.range (cutoffIndex cap+1)) (ps.length+1),
      tupleProfile chi js (p::ps)) = 1
    rw [words_sum_cons]
    simp only [tupleProfile]
    simp_rw [← Finset.mul_sum,show
      (∑ js ∈ words (Finset.range (cutoffIndex cap+1)) ps.length,
        tupleProfile chi js ps) = 1 from htail,mul_one]
    exact hscalar

def scales (js : List ℕ) : List ℝ := js.map R
def beforeHBCutoff (K : ℕ) (js : List ℕ) : ℝ := chartCutoff K (scales js)

-- Equal original R lists give equal cutoffs regardless of all HB data.
theorem cutoff_preserved (K : ℕ) (js : List ℕ)
    (gs : List ActualMultiGroupHBChartScale.Group)
    (hscales : gs.map ActualMultiGroupHBChartScale.Group.R = scales js) :
    chartCutoff K (gs.map ActualMultiGroupHBChartScale.Group.R) = beforeHBCutoff K js := by
  rw [hscales]
  rfl

end
end ImbalancedChen.P5Z.ExactOriginalSmoothDyadicPartition
