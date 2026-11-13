import ImbalancedChen.P1OriginalSingletonOneLongRectangle

/-! Exact finite short fibres. The selected occurrence is a POSITION;
equal short values or equal block labels are never identified. All these
carriers and their cap depend on the source tuple, not on the modulus. -/
namespace ImbalancedChen.P1OriginalSingletonOneLongFibres
noncomputable section
open Classical
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles P5Z.ActualHBDyadicProductWindow
open P5Z.OrderedFactorTupleRectangleReindex P5Z.ActualHBPostModulusLogCutoff

abbrev ShortIndex {r : ℕ} (a : Fin r) := {i : Fin r // i≠a}

def restrict {r : ℕ} (a : Fin r) (n : Fin r→ℕ) : ShortIndex a→ℕ := fun i=>n i.val

def insert {r : ℕ} (a : Fin r) (v : ShortIndex a→ℕ) (n : ℕ) : Fin r→ℕ :=
  fun i=>if h : i=a then n else v ⟨i,h⟩

def shortProduct {r : ℕ} {a : Fin r} (v : ShortIndex a→ℕ) : ℕ := ∏ i,v i

def shortBox {r : ℕ} (bs : Fin r→Block) (a : Fin r) : Finset (ShortIndex a→ℕ) :=
  Fintype.piFinset (fun i=>blockIntegers (bs i.val))

def shortSize {r : ℕ} (bs : Fin r→Block) (a : Fin r) : ℕ :=
  ∏ i : ShortIndex a,lower (bs i.val)

@[simp] theorem insert_at {r : ℕ} (a : Fin r) (v : ShortIndex a→ℕ) (n : ℕ) :
    insert a v n a=n := by simp [insert]

@[simp] theorem insert_away {r : ℕ} (a : Fin r) (v : ShortIndex a→ℕ)
    (n : ℕ) (i : ShortIndex a) : insert a v n i.val=v i := by simp [insert,i.property]

@[simp] theorem restrict_insert {r : ℕ} (a : Fin r) (v : ShortIndex a→ℕ) (n : ℕ) :
    restrict a (insert a v n)=v := by funext i; simp [restrict]

@[simp] theorem insert_restrict {r : ℕ} (a : Fin r) (n : Fin r→ℕ) :
    insert a (restrict a n) (n a)=n := by
  funext i
  by_cases hi : i=a <;> simp [insert,restrict,hi]

theorem product_split {r : ℕ} (a : Fin r) (n : Fin r→ℕ) :
    completeProduct n=shortProduct (restrict a n)*n a := by
  have hshort : shortProduct (restrict a n)=∏ i∈Finset.univ.erase a,n i := by
    unfold shortProduct restrict
    apply Finset.prod_bij (fun i _=>i.val)
    · intro i hi
      exact Finset.mem_erase.mpr ⟨i.property,Finset.mem_univ _⟩
    · intro i hi j hj hij
      exact Subtype.ext hij
    · intro i hi
      exact ⟨⟨i,(Finset.mem_erase.mp hi).1⟩,Finset.mem_univ _,rfl⟩
    · intro i hi
      rfl
  rw [hshort]
  exact (Finset.prod_erase_mul Finset.univ n (Finset.mem_univ a)).symm

@[simp] theorem product_insert {r : ℕ} (a : Fin r) (v : ShortIndex a→ℕ) (n : ℕ) :
    completeProduct (insert a v n)=shortProduct v*n := by
  rw [product_split a,restrict_insert,insert_at]

theorem mem_shortBox {r : ℕ} (bs : Fin r→Block) (a : Fin r) (v : ShortIndex a→ℕ) :
    v∈shortBox bs a ↔ ∀ i,Owns (bs i.val) (v i) := by
  simp only [shortBox,Fintype.mem_piFinset,mem_blockIntegers]

theorem short_product_pos {r : ℕ} (bs : Fin r→Block) (a : Fin r)
    {v : ShortIndex a→ℕ} (hv : v∈shortBox bs a) : 0<shortProduct v := by
  exact Finset.prod_pos (fun i hi=>owns_pos ((mem_shortBox bs a v).mp hv i))

theorem insert_mem_rectangle {r : ℕ} (bs : Fin r→Block) (a : Fin r)
    (v : ShortIndex a→ℕ) (n : ℕ) :
    insert a v n∈rectangle bs ↔ v∈shortBox bs a ∧ n∈blockIntegers (bs a) := by
  rw [mem_rectangle,mem_shortBox,mem_blockIntegers]
  constructor
  · intro h
    exact ⟨fun i=>by simpa using h i.val,by simpa using h a⟩
  · rintro ⟨hv,hn⟩ i
    by_cases hi : i=a
    · subst i
      simpa using hn
    · simpa only [insert,dif_neg hi] using hv ⟨i,hi⟩

/-- Literal full Cartesian sum, not a pushforward by the short product.
Every ordered short vector remains a separate summand. -/
theorem sum_rectangle_short_fibres {r : ℕ} (bs : Fin r→Block) (a : Fin r)
    (F : (Fin r→ℕ)→ℂ) :
    (∑ n∈rectangle bs,F n)=
      ∑ v∈shortBox bs a,∑ t∈blockIntegers (bs a),F (insert a v t) := by
  rw [←Finset.sum_product]
  apply Finset.sum_bij (fun n _=>(restrict a n,n a))
  · intro n hn
    have h := (mem_rectangle bs n).mp hn
    exact Finset.mem_product.mpr ⟨(mem_shortBox bs a _).mpr (fun i=>h i.val),
      (mem_blockIntegers _ _).mpr (h a)⟩
  · intro n hn m hm hnm
    have h1 := congrArg Prod.fst hnm
    have h2 := congrArg Prod.snd hnm
    calc
      n=insert a (restrict a n) (n a) := (insert_restrict a n).symm
      _=insert a (restrict a m) (m a) := by rw [h1,h2]
      _=m := insert_restrict a m
  · intro p hp
    obtain ⟨hv,ht⟩ := Finset.mem_product.mp hp
    refine ⟨insert a p.1 p.2,(insert_mem_rectangle bs a _ _).mpr ⟨hv,ht⟩,?_⟩
    simp
  · intro n hn
    simp

/-- The original complete-product cap is retained exactly in each fibre. -/
theorem sum_rectangle_capped_short_fibres {r : ℕ} (bs : Fin r→Block) (a : Fin r)
    (cap : ℕ) (F : (Fin r→ℕ)→ℂ) :
    (∑ n∈(rectangle bs).filter (fun n=>completeProduct n≤cap),F n)=
      ∑ v∈shortBox bs a,
        ∑ t∈(blockIntegers (bs a)).filter (fun t=>shortProduct v*t≤cap),F (insert a v t) := by
  rw [Finset.sum_filter,sum_rectangle_short_fibres bs a]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_filter]
  simp only [product_insert]

def fibreTop (cap m U : ℕ) : ℕ := min (2*U) (cap/m)
def fibreWidth (cap m U : ℕ) : ℕ := fibreTop cap m U-U
def fibreInterval (cap m U : ℕ) : Finset ℕ :=
  Finset.Ico (U+1) (U+1+fibreWidth cap m U)

theorem fibre_width_le (cap m U : ℕ) : fibreWidth cap m U≤U := by
  have h : fibreTop cap m U≤2*U := min_le_left _ _
  unfold fibreWidth
  omega

/-- If the upper cap is below U, the interval is empty. Otherwise its
right endpoint is min(2U,floor(cap/m)); the closed endpoint is retained. -/
theorem mem_fibreInterval {cap m U n : ℕ} (hm : 0<m) :
    n∈fibreInterval cap m U ↔ U<n ∧ n≤2*U ∧ m*n≤cap := by
  have hmul : n≤cap/m ↔ m*n≤cap := by
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm : n≤cap/m ↔ n*m≤cap)
  simp only [fibreInterval,Finset.mem_Ico,fibreWidth,fibreTop]
  constructor
  · rintro ⟨hlo,hhi⟩
    have htop : n≤min (2*U) (cap/m) := by omega
    exact ⟨by omega,htop.trans (min_le_left _ _),hmul.mp (htop.trans (min_le_right _ _))⟩
  · rintro ⟨hlo,hU,hcap⟩
    have htop : n≤min (2*U) (cap/m) := le_min hU (hmul.mpr hcap)
    exact ⟨by omega,by omega⟩

theorem dyadic_fibre_exact (cap m k : ℕ) (hm : 0<m) :
    (blockIntegers (.dyadic k)).filter (fun n=>m*n≤cap)=fibreInterval cap m (2^k) := by
  ext n
  rw [mem_fibreInterval hm]
  simp only [Finset.mem_filter,blockIntegers,Finset.mem_Ioc,pow_succ]
  omega

theorem block_card (b : Block) : (blockIntegers b).card=lower b := by
  cases b with
  | unit => simp [blockIntegers,lower]
  | dyadic k =>
    simp only [blockIntegers,Nat.card_Ioc,lower,pow_succ]
    omega

/-- This is the exact number of ordered short vectors, even with repeated
block labels. It is not the number of distinct short products. -/
theorem short_card {r : ℕ} (bs : Fin r→Block) (a : Fin r) :
    (shortBox bs a).card=shortSize bs a := by
  rw [shortBox,Fintype.card_piFinset]
  simp only [block_card,shortSize]

theorem short_size_pos {r : ℕ} (bs : Fin r→Block) (a : Fin r) : 0<shortSize bs a :=
  Finset.prod_pos (fun i hi=>lower_pos _)

theorem raw_product_split {r : ℕ} (bs : Fin r→Block) (a : Fin r) :
    (∏ i,lower (bs i))=shortSize bs a*lower (bs a) :=
  product_split a (fun i=>lower (bs i))

theorem width_sum_le_raw {r : ℕ} (bs : Fin r→Block) (a : Fin r) (cap : ℕ) :
    (∑ v∈shortBox bs a,fibreWidth cap (shortProduct v) (lower (bs a)))≤
      shortSize bs a*lower (bs a) := by
  calc
    _≤∑ _v∈shortBox bs a,lower (bs a) :=
      Finset.sum_le_sum (fun v hv=>fibre_width_le _ _ _)
    _=shortSize bs a*lower (bs a) := by simp [short_card]

/-- Activity supplies the full original 2N-width budget. No sum-of-widths
or short-coefficient mass is accepted as a new hypothesis. -/
theorem width_sum_le_cap {r : ℕ} (bs : Fin r→Block) (a : Fin r) (cap : ℕ)
    (hactive : ∃ n∈rectangle bs,completeProduct n≤cap) :
    (∑ v∈shortBox bs a,fibreWidth cap (shortProduct v) (lower (bs a)))≤cap := by
  obtain ⟨n,hn,hcap⟩ := hactive
  have hraw : (∏ i,lower (bs i))≤completeProduct n := by
    apply Finset.prod_le_prod
    · intro i hi
      exact Nat.zero_le _
    · intro i hi
      exact (owns_bounds ((mem_rectangle _ _).mp hn i)).1
  exact (width_sum_le_raw bs a cap).trans (by rw [←raw_product_split]; exact hraw.trans hcap)

/-- The genuine singleton profile, rather than a supplied complete-scale
or sum-of-widths budget, supplies the source witness used above. -/
theorem actual_width_sum_le_twoN (kap : ℝ) (hk : kap<1) (B N cj : ℕ) (kap0 : ℝ)
    {r : ℕ} (bs : Fin r→Block) (a : Fin r)
    (hactive : ∃ n∈rectangle bs,
      P5Z.ActualLowerNormalizedAtlasOccurrence.integerProfile kap B N cj kap0 n≠0) :
    (∑ v∈shortBox bs a,fibreWidth (2*N) (shortProduct v) (lower (bs a)))≤2*N := by
  apply width_sum_le_cap
  obtain ⟨n,hn,hprofile⟩ := hactive
  exact ⟨n,hn,P5Z.ActualLowerNormalizedAtlasOccurrence.scalarProfile_support
    kap hk B N cj kap0 hprofile⟩

end
end ImbalancedChen.P1OriginalSingletonOneLongFibres
