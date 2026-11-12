import ImbalancedChen.P4BOriginalHighRankPostModulusRow

/-! On a first-medium word use its fixed whole-complement fibres. On a
no-medium word retain the unsplit original mother at the same bandwidth. -/
namespace ImbalancedChen.P4BOriginalHighRankPostModulusFibres
noncomputable section
open Classical Filter
open scoped BigOperators
open ImbalancedChen.PrimeProducts
open P5Z.HBRightClosedDyadicRoles (Block bank)
open P5Z.ActualRoughHeathBrownWords (Role)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle)
open P5Z.ActualHBMediumBranchPartition (firstMedium)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le)
open P4BUpperPairOrderedRowGeometry (integerProfile)
open P4BOriginalHighRankComplementBlocks (fibre cap partition complement_count)
open P4BOriginalUpperFourierTailPaid (dyadicConstant dyadicConstant_pos)
open P4BOriginalHighRankPostModulusRow (original retained original_dead exists_row_payment)
open P4BOriginalHighRankScheduledCount (resolution outerWidth)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BOuterRampRoughness (baseline)

def first {t : ℕ} (cj ck : ℕ) (zeta : ℝ) (bs : Fin t→Block) : Option (Fin t) :=
  (firstMedium (originalMediumLow zeta [cj,ck]) (originalMediumHigh zeta [cj,ck])
    (List.ofFn bs)).bind (fun j => if h : j<t then some ⟨j,h⟩ else none)

theorem first_eq {t : ℕ} {cj ck : ℕ} {zeta : ℝ} {bs : Fin t→Block} {i : Fin t}
    (h : firstMedium (originalMediumLow zeta [cj,ck]) (originalMediumHigh zeta [cj,ck])
      (List.ofFn bs)=some i.val) : first cj ck zeta bs=some i := by
  simp [first,h,i.isLt]

variable {u v : ℕ}

def split (b kap s : ℝ) (N : ℕ) (kap0 : ℝ) (cj ck : ℕ) (zeta : ℝ)
    (bs : Fin (u+v)→Block) (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role)
    (S : Finset ℕ) (c : ℕ→ℝ) (A : ℕ) :=
  match first cj ck zeta bs with
  | none => retained (u:=u) (v:=v) b kap s N kap0 cj ck bs (rectangle bs) Z ys rs S c A
  | some i => ∑ C∈bank (cap N),retained (u:=u) (v:=v) b kap s N kap0 cj ck bs (fibre bs i C) Z ys rs S c A

theorem original_partition {N : ℕ} {b kap s kap0 : ℝ} (hb : 0<b) (hk : 0<kap) (hs : 0<s)
    (hg : 2*s≤baseline b kap-19/96) (cj ck : ℕ) (bs : Fin (u+v)→Block) (i : Fin (u+v))
    (hm : u+v≤12) (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role) (S : Finset ℕ) (c : ℕ→ℝ) :
    (∑ C∈bank (cap N),original (u:=u) (v:=v) b kap s N kap0 cj ck (fibre bs i C) Z ys rs S c)=
      original (u:=u) (v:=v) b kap s N kap0 cj ck (rectangle bs) Z ys rs S c := by
  by_cases hn : ∃ y∈rectangle bs,integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y≠0
  · unfold original MellinInsertion20261028.exactDiscrepancy MellinInsertion20261028.functional
    exact partition hb hk hs hg cj ck bs i hm hn _
  · rw [original_dead _ _ _ _ _ _ _ _ _ _ _ _ _ hn]
    apply Finset.sum_eq_zero
    intro C hC
    apply original_dead
    rintro ⟨y,hy,hny⟩
    exact hn ⟨y,(Finset.mem_filter.mp hy).1,hny⟩

/-- Summing the post-modulus fees over the actual complementary labels
spends one of the fifteen reserved logarithmic powers. -/
theorem exists_split_payment :
    ∃ C : ℝ,0≤C ∧ ∀ {N u v : ℕ} {b kap : ℝ},0<N → 0<b → b≤1 → 0<kap →
    2*outerWidth N≤baseline b kap-19/96 → (resolution N+1:ℝ)≤logScale (countingScale N) → u+v≤12 →
    ∀ (kap0 zeta : ℝ) (A cj ck : ℕ) (bs : Fin (u+v)→Block)
      (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role)
      (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ) (S : Finset ℕ),
    S⊆Q omega N → let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
    (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
    ‖original (u:=u) (v:=v) b kap (outerWidth N) N kap0 cj ck (rectangle bs) Z ys rs S c-
      split (u:=u) (v:=v) b kap (outerWidth N) N kap0 cj ck zeta bs Z ys rs S c A‖≤
      C*(N:ℝ)/logScale (countingScale N)^(A+14+3) := by
  obtain ⟨C,hC,H⟩ := exists_row_payment
  refine ⟨dyadicConstant*C,mul_nonneg dyadicConstant_pos.le hC,?_⟩
  intro N u v b kap hN hb hb1 hk hg hres hm kap0 zeta A cj ck bs Z ys rs m r n e q a omega k ell S hS
  dsimp only
  intro hr
  let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
  let s := outerWidth N
  let L := logScale (countingScale N)
  let fee := C*(N:ℝ)/L^(A+15+3)
  have hL : 1≤L := logScale_one_le (countingScale_one_le hN)
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have hf : 0≤fee := div_nonneg (mul_nonneg hC (Nat.cast_nonneg N)) (pow_nonneg hL0.le _)
  let G := fun I => original (u:=u) (v:=v) b kap s N kap0 cj ck I Z ys rs S c
  let B := fun I => retained (u:=u) (v:=v) b kap s N kap0 cj ck bs I Z ys rs S c A
  have hbnd (I) (hI : I⊆rectangle bs) : ‖G I-B I‖≤fee :=
    H hN hb hb1 hk hg hres hm kap0 A cj ck bs I hI Z ys rs m r n e q a omega k ell S hS hr
  have hcount := complement_count hN
  have hc1 : 1≤(bank (cap N)).card := Finset.card_pos.mpr
    ⟨.unit,Finset.mem_insert_self _ _⟩
  have step : ‖G (rectangle bs)-split (u:=u) (v:=v) b kap s N kap0 cj ck zeta bs Z ys rs S c A‖≤
      ((bank (cap N)).card:ℝ)*fee := by
    cases h : first cj ck zeta bs with
    | none =>
      rw [split,h]
      exact (hbnd _ (fun _ hy => hy)).trans
        (le_mul_of_one_le_left hf (by exact_mod_cast hc1))
    | some i =>
      have hpart := original_partition (u:=u) (v:=v) hb hk
        (by apply one_div_pos.mpr; positivity : 0<s) hg cj ck bs i hm Z ys rs S c
      rw [split,h,show G (rectangle bs)=∑ D∈bank (cap N),G (fibre bs i D) from hpart.symm]
      change ‖(∑ D∈bank (cap N),G (fibre bs i D))-(∑ D∈bank (cap N),B (fibre bs i D))‖≤_
      rw [←Finset.sum_sub_distrib]
      exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun D _ =>
        hbnd _ (fun _ h => (Finset.mem_filter.mp h).1))).trans_eq (by simp [nsmul_eq_mul]))
  exact step.trans ((mul_le_mul_of_nonneg_right hcount hf).trans_eq (by
    dsimp only [fee]
    rw [show A+15+3=A+14+3+1 by omega,pow_succ]
    field_simp [hL0.ne']
    ring))

end
end ImbalancedChen.P4BOriginalHighRankPostModulusFibres
