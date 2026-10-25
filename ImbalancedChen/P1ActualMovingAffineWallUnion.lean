import ImbalancedChen.P1ActualMovingAffineWallMass

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

Finite unions of exact affine prime walls with arbitrary moving heights.
An atom lying on several walls is counted once in the union and at least
once in the sum of individual wall masses. One threshold is uniform over
all real height vectors. Consequently any uniformly bounded test supported
on the moving wall union has weighted arithmetic sum tending to zero,
without continuity. The final transfer theorem applies to bounded tests
that agree away from those exact prime atoms, retaining target deletion
and the full original prime-box endpoint convention.
-/

namespace ImbalancedChen.P1ActualMovingAffineWallUnion

noncomputable section
open scoped Classical BigOperators Topology
open Filter P1ActualMovingAffineWallMass

def OnWallUnion {d r : ℕ} (N : ℕ)
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (p : Fin d → ℕ) : Prop :=
  ∃ i, L i (actualPrimeTupleLog N p) = c i

def unionTuples {d r : ℕ} (N : ℕ) (a b : Fin d → ℝ)
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) : Finset (Fin d → ℕ) :=
  (actualPrimeBoxTuples N a b).filter (OnWallUnion N L c)

def unionMass {d r : ℕ} (N : ℕ) (a b : Fin d → ℝ)
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) : ℝ :=
  ∑ p ∈ unionTuples N a b L c, tupleWeight p

def weightedTestSum {d : ℕ} (N : ℕ) (a b : Fin d → ℝ) (F : (Fin d → ℕ) → ℝ) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N a b, tupleWeight p*F p

theorem unionMass_nonneg {d r : ℕ} (N : ℕ) (a b : Fin d → ℝ)
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) :
    0 ≤ unionMass N a b L c := by
  apply Finset.sum_nonneg
  intro p hp
  exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

/-- Overlapping wall atoms are retained once by the union. Positivity
makes their possible multiple counting on the right harmless. -/
theorem unionMass_le_sum {d r : ℕ} (N : ℕ) (a b : Fin d → ℝ)
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) :
    unionMass N a b L c ≤ ∑ i, linearWallMass N a b (L i) (c i) := by
  have hpoint (p : Fin d → ℕ) (hp : p ∈ actualPrimeBoxTuples N a b) :
      (if OnWallUnion N L c p then tupleWeight p else 0) ≤
        ∑ i : Fin r, if L i (actualPrimeTupleLog N p) = c i then tupleWeight p else 0 := by
    have hw : 0 ≤ tupleWeight p := actualPrimeBoxWeight_nonneg hp
    have hterm (i : Fin r) :
        0 ≤ (if L i (actualPrimeTupleLog N p) = c i then tupleWeight p else 0) := by
      split_ifs
      · exact hw
      · exact le_rfl
    by_cases hwall : OnWallUnion N L c p
    · obtain ⟨i,hi⟩ := hwall
      rw [if_pos (show OnWallUnion N L c p from ⟨i,hi⟩)]
      have hh := Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)
      simpa only [if_pos hi] using hh
    · rw [if_neg hwall]
      exact Finset.sum_nonneg (fun i _ => hterm i)
  calc
    unionMass N a b L c =
        ∑ p ∈ actualPrimeBoxTuples N a b,
          if OnWallUnion N L c p then tupleWeight p else 0 := by
      rw [unionMass,unionTuples,Finset.sum_filter]
    _ ≤ ∑ p ∈ actualPrimeBoxTuples N a b,
        ∑ i : Fin r, if L i (actualPrimeTupleLog N p) = c i then tupleWeight p else 0 :=
      Finset.sum_le_sum hpoint
    _ = ∑ i : Fin r, ∑ p ∈ actualPrimeBoxTuples N a b,
        if L i (actualPrimeTupleLog N p) = c i then tupleWeight p else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by simp only [linearWallMass,Finset.sum_filter]

theorem linearWall_uniform_threshold {k : ℕ}
    (a b : Fin (k+1) → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (L : (Fin (k+1) → ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) (eps : ℝ) (heps : 0 < eps) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ N : ℕ, M ≤ N → ∀ c : ℝ, linearWallMass N a b L c < eps := by
  obtain ⟨j,hj⟩ := exists_nonzero_coordinate (linearCoefficients_ne_zero hL)
  simpa only [linearWallMass_eq] using
    exists_wallMass_uniform_threshold a b (linearCoefficients L) ha hab j hj eps heps

/-- Uniformity includes the empty wall family, whose exact union is empty. -/
theorem exists_unionMass_uniform_threshold {k r : ℕ}
    (a b : Fin (k+1) → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (L : Fin r → (Fin (k+1) → ℝ) →L[ℝ] ℝ) (hL : ∀ i, L i ≠ 0)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ N : ℕ, M ≤ N → ∀ c : Fin r → ℝ, unionMass N a b L c < eps := by
  have hr : (0 : ℝ) < r+1 := by positivity
  have hsmall : 0 < eps/(r+1 : ℝ) := div_pos heps hr
  choose m hm2 hm using
    fun i : Fin r => linearWall_uniform_threshold a b ha hab (L i) (hL i)
      (eps/(r+1 : ℝ)) hsmall
  refine ⟨max 2 (Finset.univ.sup m),le_max_left _ _,?_⟩
  intro N hN c
  have hrow (i : Fin r) : linearWallMass N a b (L i) (c i) ≤ eps/(r+1 : ℝ) := by
    apply (hm i N _ (c i)).le
    exact (Finset.le_sup (f := m) (Finset.mem_univ i)).trans ((le_max_right _ _).trans hN)
  have hsum : (∑ i, linearWallMass N a b (L i) (c i)) ≤ (r : ℝ)*(eps/(r+1 : ℝ)) := by
    calc
      _ ≤ ∑ _i : Fin r, eps/(r+1 : ℝ) := Finset.sum_le_sum (fun i _ => hrow i)
      _ = _ := by simp
  have hstrict : (r : ℝ)*(eps/(r+1 : ℝ)) < eps := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hr).2
    nlinarith
  exact (unionMass_le_sum N a b L c).trans_lt (hsum.trans_lt hstrict)

theorem tendsto_unionMass_moving {k r : ℕ}
    (a b : Fin (k+1) → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (L : Fin r → (Fin (k+1) → ℝ) →L[ℝ] ℝ) (hL : ∀ i, L i ≠ 0)
    (c : ℕ → Fin r → ℝ) :
    Tendsto (fun N : ℕ => unionMass N a b L (c N)) atTop (𝓝 0) := by
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin r))
    (fun i _ => tendsto_linearWallMass_moving a b ha hab (L i) (hL i) (fun N => c N i))
  have hsum0 : Tendsto (fun N : ℕ => ∑ i, linearWallMass N a b (L i) (c N i))
      atTop (𝓝 0) := by simpa only [Finset.sum_const_zero] using hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum0
  · exact Filter.Eventually.of_forall (fun N => unionMass_nonneg N a b L (c N))
  · exact Filter.Eventually.of_forall (fun N => unionMass_le_sum N a b L (c N))

/-- No continuity is required: support on the exact arithmetic wall atoms
and a pointwise bound on the original carrier suffice. -/
theorem abs_weightedTestSum_le {d r : ℕ} (N : ℕ) (a b : Fin d → ℝ)
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (F : (Fin d → ℕ) → ℝ) (B : ℝ)
    (hbound : ∀ p ∈ actualPrimeBoxTuples N a b, |F p| ≤ B)
    (hsupport : ∀ p ∈ actualPrimeBoxTuples N a b, ¬OnWallUnion N L c p → F p = 0) :
    |weightedTestSum N a b F| ≤ B*unionMass N a b L c := by
  have heq : weightedTestSum N a b F =
      ∑ p ∈ unionTuples N a b L c, tupleWeight p*F p := by
    rw [weightedTestSum,unionTuples,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hwall : OnWallUnion N L c p
    · simp only [if_pos hwall]
    · rw [if_neg hwall,hsupport p hp hwall,mul_zero]
  rw [heq]
  calc
    |∑ p ∈ unionTuples N a b L c, tupleWeight p*F p| ≤
        ∑ p ∈ unionTuples N a b L c, |tupleWeight p*F p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ unionTuples N a b L c, B*tupleWeight p := by
      apply Finset.sum_le_sum
      intro p hp
      have hpbox := (Finset.mem_filter.mp hp).1
      have hw : 0 ≤ tupleWeight p := actualPrimeBoxWeight_nonneg hpbox
      rw [abs_mul,abs_of_nonneg hw]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbound p hpbox) hw
    _ = B*unionMass N a b L c := by rw [unionMass,Finset.mul_sum]

/-- One threshold is uniform in both the height vector and every bounded
test supported on its exact union. The bound B may be zero. -/
theorem exists_supportedTest_uniform_threshold {k r : ℕ}
    (a b : Fin (k+1) → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (L : Fin r → (Fin (k+1) → ℝ) →L[ℝ] ℝ) (hL : ∀ i, L i ≠ 0)
    (B : ℝ) (hB : 0 ≤ B) (eps : ℝ) (heps : 0 < eps) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ N : ℕ, M ≤ N → ∀ (c : Fin r → ℝ) (F : (Fin (k+1) → ℕ) → ℝ),
      (∀ p ∈ actualPrimeBoxTuples N a b, |F p| ≤ B) →
      (∀ p ∈ actualPrimeBoxTuples N a b, ¬OnWallUnion N L c p → F p = 0) →
      |weightedTestSum N a b F| < eps := by
  have hp : 0 < B+1 := by linarith
  obtain ⟨M,hM2,hM⟩ := exists_unionMass_uniform_threshold a b ha hab L hL
    (eps/(B+1)) (div_pos heps hp)
  refine ⟨M,hM2,?_⟩
  intro N hN c F hb hs
  have hmass := hM N hN c
  have hnonneg := unionMass_nonneg N a b L c
  have hmul := mul_lt_mul_of_pos_left hmass hp
  have hcancel : (B+1)*(eps/(B+1)) = eps := by field_simp [hp.ne']
  rw [hcancel] at hmul
  exact (abs_weightedTestSum_le N a b L c F B hb hs).trans_lt
    ((mul_le_mul_of_nonneg_right (show B ≤ B+1 by linarith) hnonneg).trans_lt hmul)

theorem tendsto_supportedTest_moving {k r : ℕ}
    (a b : Fin (k+1) → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (L : Fin r → (Fin (k+1) → ℝ) →L[ℝ] ℝ) (hL : ∀ i, L i ≠ 0)
    (c : ℕ → Fin r → ℝ) (F : ℕ → (Fin (k+1) → ℕ) → ℝ) (B : ℝ)
    (hbound : ∀ N p, p ∈ actualPrimeBoxTuples N a b → |F N p| ≤ B)
    (hsupport : ∀ N p, p ∈ actualPrimeBoxTuples N a b →
      ¬OnWallUnion N L (c N) p → F N p = 0) :
    Tendsto (fun N : ℕ => weightedTestSum N a b (F N)) atTop (𝓝 0) := by
  have hu : Tendsto (fun N : ℕ => B*unionMass N a b L (c N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_unionMass_moving a b ha hab L hL c).const_mul B
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa only [neg_zero] using hu.neg) hu
  · exact Filter.Eventually.of_forall (fun N =>
      (abs_le.mp (abs_weightedTestSum_le N a b L (c N) (F N) B
        (hbound N) (hsupport N))).1)
  · exact Filter.Eventually.of_forall (fun N =>
      (abs_le.mp (abs_weightedTestSum_le N a b L (c N) (F N) B
        (hbound N) (hsupport N))).2)

/-- Exact closed/strict ownership changes may alter the arithmetic atoms.
Bounded policies agreeing off the finite moving walls have the same limit. -/
theorem tendsto_policyDifference_moving {k r : ℕ}
    (a b : Fin (k+1) → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (L : Fin r → (Fin (k+1) → ℝ) →L[ℝ] ℝ) (hL : ∀ i, L i ≠ 0)
    (c : ℕ → Fin r → ℝ) (F G : ℕ → (Fin (k+1) → ℕ) → ℝ) (B : ℝ)
    (hF : ∀ N p, p ∈ actualPrimeBoxTuples N a b → |F N p| ≤ B)
    (hG : ∀ N p, p ∈ actualPrimeBoxTuples N a b → |G N p| ≤ B)
    (hagree : ∀ N p, p ∈ actualPrimeBoxTuples N a b →
      ¬OnWallUnion N L (c N) p → F N p = G N p) :
    Tendsto (fun N : ℕ => weightedTestSum N a b (F N) - weightedTestSum N a b (G N))
      atTop (𝓝 0) := by
  have hb (N : ℕ) (p : Fin (k+1) → ℕ) (hp : p ∈ actualPrimeBoxTuples N a b) :
      |F N p-G N p| ≤ 2*B := by
    calc
      |F N p-G N p| ≤ |F N p|+|G N p| := by
        simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (F N p) 0 (G N p)
      _ ≤ 2*B := by linarith [hF N p hp,hG N p hp]
  have hs (N : ℕ) (p : Fin (k+1) → ℕ) (hp : p ∈ actualPrimeBoxTuples N a b)
      (hw : ¬OnWallUnion N L (c N) p) : F N p-G N p = 0 := by rw [hagree N p hp hw,sub_self]
  have ht := tendsto_supportedTest_moving a b ha hab L hL c
    (fun N p => F N p-G N p) (2*B) hb hs
  convert ht using 1
  funext N
  simp only [weightedTestSum,mul_sub,Finset.sum_sub_distrib]

end
end ImbalancedChen.P1ActualMovingAffineWallUnion
