import ImbalancedChen.Part3MediumCanonicalFixedBlock
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Paper medium module 102--122: deterministic half-open dyadic ownership
for the actual retained installed row labels. Every coefficient, beta
label, deleted indicator and independent copy of W is preserved.
The d coordinate in a key is log2(d), NOT an individual exact d;
no D separate arbitrary-logarithmic error terms are introduced.
-/
namespace ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3.MediumCanonicalFixedBlock20261028
open ImbalancedChen.Part3.MediumActualPostSquareDeletion20261028
open ImbalancedChen.Part3.OriginalMediumDoubleLambdaColorWindows20261028

structure Key where
  s t u v d w : ℕ
  deriving DecidableEq

/-- Every positive integer occupies [2^k,2^(k+1)), including 1 at k=0. -/
def dyadicWindow (k : ℕ) : Finset ℕ := Ico (2 ^ k) (2 ^ (k + 1))

theorem mem_dyadicWindow_iff {n k : ℕ} (hn : n ≠ 0) :
    n ∈ dyadicWindow k ↔ Nat.log2 n = k := by
  rw [dyadicWindow, mem_Ico]
  exact (Nat.log2_eq_iff hn).symm

theorem dyadicWindow_upper_excluded (k : ℕ) :
    2 ^ (k + 1) ∉ dyadicWindow k := by simp [dyadicWindow]

theorem dyadicWindow_lower_owned (k : ℕ) :
    2 ^ k ∈ dyadicWindow k := by
  apply mem_Ico.mpr
  refine ⟨le_rfl, ?_⟩
  have hpos : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) _
  rw [pow_succ]
  omega

def actualD (z : ℝ) (q : ℕ × ℕ) : ℕ :=
  (canonicalFactor z q.1 q.2).s * (canonicalFactor z q.1 q.2).t

def actualW (z : ℝ) (q : ℕ × ℕ) : ℕ :=
  (canonicalFactor z q.1 q.2).u * (canonicalFactor z q.1 q.2).v

def owner (z : ℝ) (q : ℕ × ℕ) : Key :=
  { s := Nat.log2 (smoothPart z q.1), t := Nat.log2 (smoothPart z q.2),
    u := Nat.log2 (roughPart z q.1), v := Nat.log2 (roughPart z q.2),
    d := Nat.log2 (actualD z q), w := Nat.log2 (actualW z q) }

/-- Precisely the smooth-factor trim in paper 102--114. The count/mean
estimate for its complement is a separate quantitative obligation. -/
def Retained (z y : ℝ) (q : ℕ × ℕ) : Prop :=
  q.1 ≠ 0 ∧ q.2 ≠ 0 ∧ (smoothPart z q.1 : ℝ) ≤ y ∧
    (smoothPart z q.2 : ℝ) ≤ y

def retainedModuli (atom : MediumAtom) (z y : ℝ) : Finset (ℕ × ℕ) :=
  (factorCarrier atom.Q2 ×ˢ factorCarrier atom.Q3).filter (Retained z y)

def ownedModuli (atom : MediumAtom) (z y : ℝ) (k : Key) : Finset (ℕ × ℕ) :=
  (retainedModuli atom z y).filter (fun q => owner z q = k)

/-- This bank depends only on the original atom, z and the fixed trim y.
It does not depend on m, beta label n, coefficients, signs or arithmetic
congruences. Being a finite image, it contains exactly the occupied keys. -/
def keyBank (atom : MediumAtom) (z y : ℝ) : Finset Key :=
  (retainedModuli atom z y).image (owner z)

theorem owner_mem_keyBank {atom : MediumAtom} {z y : ℝ} {q : ℕ × ℕ}
    (hq : q ∈ retainedModuli atom z y) : owner z q ∈ keyBank atom z y :=
  mem_image.mpr ⟨q, hq, rfl⟩

theorem ownedModuli_mem_iff (atom : MediumAtom) (z y : ℝ) (k : Key)
    (q : ℕ × ℕ) :
    q ∈ ownedModuli atom z y k ↔ q ∈ retainedModuli atom z y ∧ owner z q = k :=
  mem_filter

theorem unique_owner {atom : MediumAtom} {z y : ℝ} {q : ℕ × ℕ}
    (hq : q ∈ retainedModuli atom z y) :
    ∃! k, k ∈ keyBank atom z y ∧ q ∈ ownedModuli atom z y k := by
  refine ⟨owner z q, ⟨owner_mem_keyBank hq, mem_filter.mpr ⟨hq, rfl⟩⟩, ?_⟩
  intro k hk
  exact (mem_filter.mp hk.2).2.symm

theorem ownedModuli_disjoint (atom : MediumAtom) (z y : ℝ)
    {k k' : Key} (hkk : k ≠ k') :
    Disjoint (ownedModuli atom z y k) (ownedModuli atom z y k') := by
  apply disjoint_left.mpr
  intro q hq hq'
  exact hkk ((mem_filter.mp hq).2.symm.trans (mem_filter.mp hq').2)

/-- Exact signed finite partition, with no norm inserted into a row. -/
theorem sum_ownedModuli (atom : MediumAtom) (z y : ℝ)
    (f : (ℕ × ℕ) → ℂ) :
    (∑ k ∈ keyBank atom z y, ∑ q ∈ ownedModuli atom z y k, f q) =
      ∑ q ∈ retainedModuli atom z y, f q := by
  simp only [ownedModuli, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro q hq
  have hk := owner_mem_keyBank hq
  rw [sum_eq_single (owner z q)]
  · simp
  · intro k hkm hne
    simp [Ne.symm hne]
  · exact fun h => False.elim (h hk)

/-- Positive factors and their products remain positive, including q=1. -/
theorem split_nonzero (z : ℝ) (q : ℕ × ℕ) :
    smoothPart z q.1 ≠ 0 ∧ smoothPart z q.2 ≠ 0 ∧
    roughPart z q.1 ≠ 0 ∧ roughPart z q.2 ≠ 0 ∧
    actualD z q ≠ 0 ∧ actualW z q ≠ 0 := by
  have hs := (smoothPart_supported z q.1).1
  have ht := (smoothPart_supported z q.2).1
  have hu := (roughPart_supported z q.1).1
  have hv := (roughPart_supported z q.2).1
  exact ⟨hs, ht, hu, hv, mul_ne_zero hs ht, mul_ne_zero hu hv⟩

/-- Ownership is the literal sixfold half-open condition. A boundary
2^(k+1) belongs to the next key; it never contributes twice. -/
theorem owner_eq_iff_windows (z : ℝ) (q : ℕ × ℕ) (k : Key) :
    owner z q = k ↔
      smoothPart z q.1 ∈ dyadicWindow k.s ∧
      smoothPart z q.2 ∈ dyadicWindow k.t ∧
      roughPart z q.1 ∈ dyadicWindow k.u ∧
      roughPart z q.2 ∈ dyadicWindow k.v ∧
      actualD z q ∈ dyadicWindow k.d ∧ actualW z q ∈ dyadicWindow k.w := by
  obtain ⟨hs, ht, hu, hv, hd, hw⟩ := split_nonzero z q
  rw [mem_dyadicWindow_iff hs, mem_dyadicWindow_iff ht,
    mem_dyadicWindow_iff hu, mem_dyadicWindow_iff hv,
    mem_dyadicWindow_iff hd, mem_dyadicWindow_iff hw]
  constructor
  · intro h
    exact ⟨congrArg Key.s h, congrArg Key.t h, congrArg Key.u h,
      congrArg Key.v h, congrArg Key.d h, congrArg Key.w h⟩
  · rintro ⟨hs, ht, hu, hv, hd, hw⟩
    cases k
    simp_all [owner]

/-- Original q1 and beta labels are untouched by dyadic ownership. -/
def rowModuli (l : RowLabel) : ℕ × ℕ := (l.1.2.1, l.1.2.2)

def retainedRows (atom : MediumAtom) (z y : ℝ) : Finset RowLabel :=
  atom.complexRowLabels.filter (fun l => Retained z y (rowModuli l))

def ownedRows (atom : MediumAtom) (z y : ℝ) (k : Key) : Finset RowLabel :=
  (retainedRows atom z y).filter (fun l => owner z (rowModuli l) = k)

theorem rowModuli_mem_retainedModuli {atom : MediumAtom} {z y : ℝ}
    {l : RowLabel} (hl : l ∈ retainedRows atom z y) :
    rowModuli l ∈ retainedModuli atom z y := by
  obtain ⟨hl, ht⟩ := mem_filter.mp hl
  have hfac := (mem_product.mp hl).1
  have h23 := (mem_product.mp hfac).2
  exact mem_filter.mpr ⟨h23, ht⟩

theorem ownedRows_disjoint (atom : MediumAtom) (z y : ℝ)
    {k k' : Key} (hkk : k ≠ k') :
    Disjoint (ownedRows atom z y k) (ownedRows atom z y k') := by
  apply disjoint_left.mpr
  intro l hl hl'
  exact hkk ((mem_filter.mp hl).2.symm.trans (mem_filter.mp hl').2)

theorem sum_ownedRows (atom : MediumAtom) (z y : ℝ) (f : RowLabel → ℂ) :
    (∑ k ∈ keyBank atom z y, ∑ l ∈ ownedRows atom z y k, f l) =
      ∑ l ∈ retainedRows atom z y, f l := by
  simp only [ownedRows, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro l hl
  have hk := owner_mem_keyBank (rowModuli_mem_retainedModuli hl)
  rw [sum_eq_single (owner z (rowModuli l))]
  · simp
  · intro k hkm hne
    simp [Ne.symm hne]
  · exact fun h => False.elim (h hk)

def retainedDeletedRow (atom : MediumAtom) (z y : ℝ) (m : ℕ) : ℂ :=
  ∑ l ∈ retainedRows atom z y,
    atom.complexFactorGamma l.1 * atom.beta l.2 * deletedCongruence atom m l

def ownedDeletedRow (atom : MediumAtom) (z y : ℝ) (k : Key) (m : ℕ) : ℂ :=
  ∑ l ∈ ownedRows atom z y k,
    atom.complexFactorGamma l.1 * atom.beta l.2 * deletedCongruence atom m l

theorem retainedDeletedRow_eq_owned (atom : MediumAtom) (z y : ℝ) (m : ℕ) :
    retainedDeletedRow atom z y m =
      ∑ k ∈ keyBank atom z y, ownedDeletedRow atom z y k m :=
  (sum_ownedRows atom z y _).symm

def retainedDeletedW (atom : MediumAtom) (z y : ℝ)
    (S : Finset ℕ) (weight : ℕ → ℝ) : ℂ :=
  ∑ m ∈ S, (weight m : ℂ) * retainedDeletedRow atom z y m *
    star (retainedDeletedRow atom z y m)

/-- The whole retained installed W has both independent dyadic keys.
The same m remains shared. No diagonal-only surrogate replaces W. -/
theorem retainedDeletedW_eq_two_owned_keys (atom : MediumAtom) (z y : ℝ)
    (S : Finset ℕ) (weight : ℕ → ℝ) :
    retainedDeletedW atom z y S weight =
      ∑ m ∈ S, ∑ k ∈ keyBank atom z y, ∑ k' ∈ keyBank atom z y,
        (weight m : ℂ) * ownedDeletedRow atom z y k m *
          star (ownedDeletedRow atom z y k' m) := by
  unfold retainedDeletedW
  apply sum_congr rfl
  intro m hm
  simp_rw [retainedDeletedRow_eq_owned, star_sum]
  rw [mul_assoc, sum_mul_sum]
  simp only [mul_sum, mul_assoc]

/-- Exact original installed row-label multiplicities can be retained
while the physical modulus-pair variable is reindexed separately. -/
theorem sum_retainedRows_eq_physical_pairs (atom : MediumAtom) (z y : ℝ)
    (f : RowLabel → ℂ) :
    (∑ l ∈ retainedRows atom z y, f l) =
      ∑ q1 ∈ factorCarrier atom.Q1, ∑ q ∈ retainedModuli atom z y,
        ∑ n ∈ atom.betaCarrier, f ((q1, q.1, q.2), n) := by
  simp only [retainedRows, retainedModuli, MediumAtom.complexRowLabels,
    MediumAtom.complexFactorLabels, sum_filter, sum_product, rowModuli]
  apply sum_congr rfl
  intro q1 hq1
  apply sum_congr rfl
  intro q2 hq2
  apply sum_congr rfl
  intro q3 hq3
  by_cases h : Retained z y (q2, q3) <;> simp [h]

/-- A uniform atom bound, fixed before any retained tuple is chosen. -/
def physicalCap (atom : MediumAtom) : ℕ :=
  Nat.floor (2 * atom.Q2) * Nat.floor (2 * atom.Q3)

def toSix (k : Key) (i : Fin 6) : ℕ :=
  match i.val with
  | 0 => k.s
  | 1 => k.t
  | 2 => k.u
  | 3 => k.v
  | 4 => k.d
  | _ => k.w

def decodeKey {L : ℕ} (v : Fin 6 → Fin L) : Key :=
  ⟨(v 0).val, (v 1).val, (v 2).val, (v 3).val, (v 4).val, (v 5).val⟩

def uniformKeyBank (atom : MediumAtom) : Finset Key :=
  (univ : Finset (Fin 6 → Fin (Nat.log2 (physicalCap atom) + 1))).image decodeKey

private theorem log2_le_of_le {n M : ℕ} (hn : n ≠ 0) (hnM : n ≤ M) :
    Nat.log2 n ≤ Nat.log2 M := by
  have hM : M ≠ 0 := by omega
  exact (Nat.le_log2 hM).mpr ((Nat.log2_self_le hn).trans hnM)

/-- Coordinate sizes are derived from the actual positive modulus pair;
they are not a later licence or a postulated dyadic cover. -/
theorem actual_coordinate_bounds {atom : MediumAtom} {z y : ℝ}
    {q : ℕ × ℕ} (hq : q ∈ retainedModuli atom z y) :
    ∀ i : Fin 6, toSix (owner z q) i < Nat.log2 (physicalCap atom) + 1 := by
  obtain ⟨hpair, h2, h3, hsy, hty⟩ := mem_filter.mp hq
  obtain ⟨hQ2, hQ3⟩ := mem_product.mp hpair
  have hq2 := (mem_Icc.mp hQ2).2
  have hq3 := (mem_Icc.mp hQ3).2
  have hcap : q.1 * q.2 ≤ physicalCap atom := Nat.mul_le_mul hq2 hq3
  obtain ⟨hs, ht, hu, hv, hd, hw⟩ := split_nonzero z q
  have hsu := smooth_mul_rough z h2
  have htv := smooth_mul_rough z h3
  have hs1 : 1 ≤ smoothPart z q.1 := by omega
  have ht1 : 1 ≤ smoothPart z q.2 := by omega
  have hu1 : 1 ≤ roughPart z q.1 := by omega
  have hv1 : 1 ≤ roughPart z q.2 := by omega
  have hs2 : smoothPart z q.1 ≤ q.1 := by nlinarith
  have hu2 : roughPart z q.1 ≤ q.1 := by nlinarith
  have ht3 : smoothPart z q.2 ≤ q.2 := by nlinarith
  have hv3 : roughPart z q.2 ≤ q.2 := by nlinarith
  have hq2cap : q.1 ≤ physicalCap atom := by
    have hq3pos : 1 ≤ q.2 := by omega
    nlinarith
  have hq3cap : q.2 ≤ physicalCap atom := by
    have hq2pos : 1 ≤ q.1 := by omega
    nlinarith
  have hdCap : actualD z q ≤ physicalCap atom :=
    (Nat.mul_le_mul hs2 ht3).trans hcap
  have hwCap : actualW z q ≤ physicalCap atom :=
    (Nat.mul_le_mul hu2 hv3).trans hcap
  have hslog := Nat.lt_succ_of_le (log2_le_of_le hs (hs2.trans hq2cap))
  have htlog := Nat.lt_succ_of_le (log2_le_of_le ht (ht3.trans hq3cap))
  have hulog := Nat.lt_succ_of_le (log2_le_of_le hu (hu2.trans hq2cap))
  have hvlog := Nat.lt_succ_of_le (log2_le_of_le hv (hv3.trans hq3cap))
  have hdlog := Nat.lt_succ_of_le (log2_le_of_le hd hdCap)
  have hwlog := Nat.lt_succ_of_le (log2_le_of_le hw hwCap)
  intro i
  fin_cases i
  · exact hslog
  · exact htlog
  · exact hulog
  · exact hvlog
  · exact hdlog
  · exact hwlog

theorem keyBank_subset_uniformKeyBank (atom : MediumAtom) (z y : ℝ) :
    keyBank atom z y ⊆ uniformKeyBank atom := by
  intro k hk
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hk
  let v : Fin 6 → Fin (Nat.log2 (physicalCap atom) + 1) :=
    fun i => ⟨toSix (owner z q) i, actual_coordinate_bounds hq i⟩
  exact mem_image.mpr ⟨v, mem_univ _, rfl⟩

/-- Exact finite logarithmic bank count, before any asymptotic estimate.
All individual d values remain inside a key and do not enlarge this bank. -/
theorem keyBank_card_le (atom : MediumAtom) (z y : ℝ) :
    (keyBank atom z y).card ≤ (Nat.log2 (physicalCap atom) + 1) ^ 6 := by
  calc
    _ ≤ (uniformKeyBank atom).card := card_le_card (keyBank_subset_uniformKeyBank atom z y)
    _ ≤ (univ : Finset (Fin 6 → Fin (Nat.log2 (physicalCap atom) + 1))).card :=
      card_image_le
    _ = _ := by simp

end
end ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
