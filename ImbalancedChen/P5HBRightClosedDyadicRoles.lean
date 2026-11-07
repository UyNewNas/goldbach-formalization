import ImbalancedChen.P5ActualRoughHeathBrownWords

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
HB ROLE intervals have their OWN endpoint convention: the unit is a
separate atom, and nonunits occupy (2^k,2^(k+1)]. This agrees with the
actual rough-slot (u,v] interval convention and does not change the earlier
gamma [Q,2Q) partition. The finite bank is fixed from n BEFORE its tuples.
-/
namespace ImbalancedChen.P5Z.HBRightClosedDyadicRoles
noncomputable section
open Classical
open scoped BigOperators
open LiteralHeathBrownOccurrenceWords ActualRoughHeathBrownWords

inductive Block where
  | unit
  | dyadic (k : ℕ)
  deriving DecidableEq

def Owns : Block → ℕ → Prop
  | .unit,p => p=1
  | .dyadic k,p => 2^k<p ∧ p≤2^(k+1)

def owner (p : ℕ) : Block :=
  if p=1 then .unit else .dyadic (Nat.log2 (p-1))

def bank (n : ℕ) : Finset Block :=
  insert .unit ((Finset.range (Nat.log2 (n-1)+1)).image Block.dyadic)

theorem owner_owns {p : ℕ} (hp : 0<p) : Owns (owner p) p := by
  by_cases h1 : p=1
  · simp [owner,h1,Owns]
  have hm : p-1≠0 := by omega
  have hlo := Nat.log2_self_le hm
  have hhi : p-1<2^(Nat.log2 (p-1)+1) := Nat.lt_log2_self
  simp only [owner,if_neg h1,Owns]
  omega

theorem owns_unique {b : Block} {p : ℕ} (hp : 0<p) (hb : Owns b p) : b=owner p := by
  cases b with
  | unit =>
    change p=1 at hb
    simp [owner,hb]
  | dyadic k =>
    change 2^k<p ∧ p≤2^(k+1) at hb
    have hpow : 1≤2^k := Nat.one_le_pow k 2 (by omega)
    have h1 : p≠1 := by omega
    have hm : p-1≠0 := by omega
    have hlog : Nat.log2 (p-1)=k := (Nat.log2_eq_iff hm).mpr ⟨by omega,by omega⟩
    simp [owner,h1,hlog]

theorem owner_mem_bank {p n : ℕ} (hp : 0<p) (hpn : p≤n) : owner p∈bank n := by
  by_cases h1 : p=1
  · simp [bank,owner,h1]
  have hm : p-1≠0 := by omega
  have hn : n-1≠0 := by omega
  have hpow : 2^(Nat.log2 (p-1))≤n-1 := (Nat.log2_self_le hm).trans (by omega)
  have hk : Nat.log2 (p-1)≤Nat.log2 (n-1) := (Nat.le_log2 hn).mpr hpow
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  exact ⟨Nat.log2 (p-1),Finset.mem_range.mpr (by omega),by simp [owner,h1]⟩

theorem bank_card (n : ℕ) : (bank n).card=Nat.log2 (n-1)+2 := by
  have hnot : Block.unit∉(Finset.range (Nat.log2 (n-1)+1)).image Block.dyadic := by simp
  have hinj : Function.Injective Block.dyadic := by
    intro k l h
    cases h
    rfl
  rw [bank,Finset.card_insert_of_notMem hnot,Finset.card_image_of_injective _ hinj,Finset.card_range]
  omega

/-- The coordinate bound is DERIVED from the actual positive product
tuple; no per-factor bound is supplied by a later HB licence. -/
theorem actual_factor_bound {r n : ℕ} {ps : List ℕ} (hps : ps∈factorTuples r n)
    {p : ℕ} (hp : p∈ps) : 0<p ∧ p≤n := by
  have hs := factorTuples_spec r n ps hps
  have hn : 0<ps.prod := List.prod_pos hs.2.2
  have hpn : p≤ps.prod := Nat.le_of_dvd hn (List.dvd_prod hp)
  exact ⟨hs.2.2 p hp,by simpa only [hs.2.1] using hpn⟩

def blockValue (z y : ℝ) (r : Role) (b : Block) (p : ℕ) : ℂ :=
  if Owns b p then actual z y r p else 0

/-- One actual rough role, including its original REAL Mobius cutoff
and signed value, decomposes EXACTLY over this finite interval bank. -/
theorem role_reconstruct {p n : ℕ} (hp : 0<p) (hpn : p≤n)
    (z y : ℝ) (r : Role) :
    (∑ b∈bank n,blockValue z y r b p)=actual z y r p := by
  have hmem := owner_mem_bank hp hpn
  rw [Finset.sum_eq_single (owner p)]
  · simp only [blockValue,if_pos (owner_owns hp)]
  · intro b hb hne
    have ho : ¬Owns b p := fun h => hne (owns_unique hp h)
    simp only [blockValue,if_neg ho]
  · exact fun h => False.elim (h hmem)

theorem mobius_interval_cutoff {z y : ℝ} {b : Block} {p : ℕ}
    (h : blockValue z y .mobius b p≠0) : Owns b p ∧ (p : ℝ)≤y := by
  have hb : Owns b p := by
    by_contra hn
    exact h (by simp [blockValue,hn])
  refine ⟨hb,?_⟩
  by_contra hcut
  exact h (by simp [blockValue,hb,actual,roughMuTrunc,hcut])

end
end ImbalancedChen.P5Z.HBRightClosedDyadicRoles
