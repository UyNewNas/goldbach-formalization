import ImbalancedChen.Part3MediumInstalledSplitConverse
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original medium proof, distribution-medium-completion-20261010.txt 102--120.
Unlike an arbitrary FactorData, the FactorData below has no opaque allowed
field: it is exactly the original Q2/Q3 supports and rough-product window.
The small/rough split is constructed with every prime-factor multiplicity.
This proves the reverse support map for a complete selected fixed block,
and an exact weighted reindexing, without a supplied PhysicalSplitWitness.
-/
namespace ImbalancedChen.Part3.MediumCanonicalFixedBlock20261028

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3.OriginalMediumDoubleLambdaColorWindows20261028
open ImbalancedChen.Part3.MediumInstalledFactorChoiceMap20261028
open ImbalancedChen.Part3.MediumInstalledSplitConverse20261028

/-- Repeated prime powers stay wholly on the strict small side. -/
def smoothPart (z : ℝ) (q : ℕ) : ℕ :=
  (q.primeFactorsList.filter fun p => (p : ℝ) < z).prod

/-- A prime exactly at z is retained on the rough side. -/
def roughPart (z : ℝ) (q : ℕ) : ℕ :=
  (q.primeFactorsList.filter fun p => ¬ (p : ℝ) < z).prod

private theorem split_list_product (z : ℝ) (l : List ℕ) :
    (l.filter fun p => (p : ℝ) < z).prod *
      (l.filter fun p => ¬ (p : ℝ) < z).prod = l.prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
      by_cases hp : (p : ℝ) < z <;>
        simp [hp, ← ih, mul_assoc, mul_comm, mul_left_comm]

theorem smooth_mul_rough (z : ℝ) {q : ℕ} (hq : q ≠ 0) :
    smoothPart z q * roughPart z q = q := by
  rw [smoothPart, roughPart, split_list_product, Nat.prod_primeFactorsList hq]

private theorem list_prod_ne_zero (l : List ℕ)
    (h : ∀ p ∈ l, p ≠ 0) : l.prod ≠ 0 := by
  revert h
  induction l with
  | nil => intro _; simp
  | cons p l ih =>
      intro h
      exact mul_ne_zero (h p (by simp))
        (ih fun r hr => h r (by simp [hr]))

private theorem prime_dvd_prime_list_product
    (p : ℕ) (hp : p.Prime) (l : List ℕ)
    (hprime : ∀ r ∈ l, r.Prime) (hdiv : p ∣ l.prod) : p ∈ l := by
  revert hprime hdiv
  induction l with
  | nil =>
      intro _ hdiv
      exact False.elim (hp.not_dvd_one hdiv)
  | cons r l ih =>
      intro hprime hdiv
      have hmul : p ∣ r * l.prod := by simpa using hdiv
      rcases hp.dvd_mul.mp hmul with hpr | hpl
      · have heq : p = r :=
          ((Nat.dvd_prime (hprime r (by simp))).mp hpr).resolve_left hp.ne_one
        simp [heq]
      · exact List.mem_cons_of_mem r
          (ih (fun s hs => hprime s (by simp [hs])) hpl)

private theorem prime_factor_mem_of_list_product
    (l : List ℕ) (hprime : ∀ r ∈ l, r.Prime)
    {p : ℕ} (hp : p ∈ l.prod.primeFactors) : p ∈ l := by
  exact prime_dvd_prime_list_product p (Nat.prime_of_mem_primeFactors hp)
    l hprime (Nat.dvd_of_mem_primeFactors hp)

theorem smoothPart_supported (z : ℝ) (q : ℕ) :
    SmallPrimeSupportedAt z (smoothPart z q) := by
  have hprime : ∀ p ∈ q.primeFactorsList.filter (fun p => (p : ℝ) < z),
      p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1
  constructor
  · exact list_prod_ne_zero _ (fun p hp => (hprime p hp).ne_zero)
  · intro p hp
    have hmem := prime_factor_mem_of_list_product _ hprime hp
    have hlt := (List.mem_filter.mp hmem).2
    simpa only [decide_eq_true_eq] using hlt

theorem roughPart_supported (z : ℝ) (q : ℕ) :
    RoughPrimeSupportedAt z (roughPart z q) := by
  have hprime : ∀ p ∈ q.primeFactorsList.filter (fun p => ¬ (p : ℝ) < z),
      p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1
  constructor
  · exact list_prod_ne_zero _ (fun p hp => (hprime p hp).ne_zero)
  · intro p hp
    have hmem := prime_factor_mem_of_list_product _ hprime hp
    have hnot : ¬ (p : ℝ) < z := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp hmem).2
    exact le_of_not_gt hnot

private theorem factor_ext {p p' : Factor}
    (hs : p.s = p'.s) (ht : p.t = p'.t)
    (hu : p.u = p'.u) (hv : p.v = p'.v) : p = p' := by
  cases p
  cases p'
  simp_all

def physicalModuli (p : Factor) : ℕ × ℕ :=
  (p.u * p.s, p.v * p.t)

def canonicalFactor (z : ℝ) (q2 q3 : ℕ) : Factor :=
  ⟨smoothPart z q2, smoothPart z q3, roughPart z q2, roughPart z q3⟩

theorem physical_canonical (z : ℝ) {q2 q3 : ℕ}
    (h2 : q2 ≠ 0) (h3 : q3 ≠ 0) :
    physicalModuli (canonicalFactor z q2 q3) = (q2, q3) := by
  apply Prod.ext
  · exact (Nat.mul_comm _ _).trans (smooth_mul_rough z h2)
  · exact (Nat.mul_comm _ _).trans (smooth_mul_rough z h3)

/-- Four individual fixed integer windows and the fixed rough-product
window. Dyadic comparability constraints are unnecessary for this exact
identity and remain hypotheses of the later analytic estimate. -/
structure Block where
  sLo sHi tLo tHi uLo uHi vLo vHi wLo wHi d : ℕ

def Block.factorData (B : Block) (atom : MediumAtom) (z : ℝ) : FactorData where
  smoothS := (Icc B.sLo B.sHi).filter (SmallPrimeSupportedAt z)
  smoothT := (Icc B.tLo B.tHi).filter (SmallPrimeSupportedAt z)
  roughU := (Icc B.uLo B.uHi).filter (RoughPrimeSupportedAt z)
  roughV := (Icc B.vLo B.vHi).filter (RoughPrimeSupportedAt z)
  allowed p := p.u * p.s ∈ factorCarrier atom.Q2 ∧
    p.v * p.t ∈ factorCarrier atom.Q3 ∧ p.u * p.v ∈ Icc B.wLo B.wHi
  lambdaCoeff := atom.gamma2
  nuCoeff := atom.gamma3

/-- The selected physical modulus pairs. This predicate is expressed
only through the original modulus intervals and the canonical prime
factorization, not through FactorData.choices or an existential witness. -/
def Block.selectedModuli (B : Block) (atom : MediumAtom) (z : ℝ)
    (w : ℕ) : Finset (ℕ × ℕ) :=
  (factorCarrier atom.Q2 ×ˢ factorCarrier atom.Q3).filter fun q =>
    q.1 ≠ 0 ∧ q.2 ≠ 0 ∧
    (canonicalFactor z q.1 q.2).s ∈ Icc B.sLo B.sHi ∧
    (canonicalFactor z q.1 q.2).t ∈ Icc B.tLo B.tHi ∧
    (canonicalFactor z q.1 q.2).u ∈ Icc B.uLo B.uHi ∧
    (canonicalFactor z q.1 q.2).v ∈ Icc B.vLo B.vHi ∧
    (canonicalFactor z q.1 q.2).s * (canonicalFactor z q.1 q.2).t = B.d ∧
    (canonicalFactor z q.1 q.2).u * (canonicalFactor z q.1 q.2).v = w ∧
    w ∈ Icc B.wLo B.wHi

private theorem mem_choices_iff (F : FactorData) (d w : ℕ) (p : Factor) :
    p ∈ F.choices d w ↔
      p.s ∈ F.smoothS ∧ p.t ∈ F.smoothT ∧
      p.u ∈ F.roughU ∧ p.v ∈ F.roughV ∧
      p.s * p.t = d ∧ p.u * p.v = w ∧ F.allowed p := by
  constructor
  · intro hp
    obtain ⟨hs, ht, hu, hv⟩ := choice_all_four_supports F hp
    obtain ⟨hd, hw, ha⟩ := choice_products hp
    exact ⟨hs, ht, hu, hv, hd, hw, ha⟩
  · rintro ⟨hs, ht, hu, hv, hd, hw, ha⟩
    apply mem_filter.mpr
    refine ⟨?_, hd, hw, ha⟩
    apply mem_biUnion.mpr
    refine ⟨p.s, hs, ?_⟩
    apply mem_biUnion.mpr
    refine ⟨p.t, ht, ?_⟩
    apply mem_biUnion.mpr
    refine ⟨p.u, hu, ?_⟩
    apply mem_image.mpr
    exact ⟨p.v, hv, by cases p; rfl⟩

/-- The canonical split recovers every choice, with no squarefreeness
assumption and with no information lost when q2 or q3 has a prime power. -/
theorem canonical_choice (B : Block) (atom : MediumAtom) (z : ℝ)
    {w : ℕ} {p : Factor} (hp : p ∈ (B.factorData atom z).choices B.d w) :
    canonicalFactor z (physicalModuli p).1 (physicalModuli p).2 = p := by
  obtain ⟨hs, ht, hu, hv⟩ := choice_all_four_supports _ hp
  have hsS := (mem_filter.mp hs).2
  have htS := (mem_filter.mp ht).2
  have huR := (mem_filter.mp hu).2
  have hvR := (mem_filter.mp hv).2
  have h2 : p.u * p.s ≠ 0 := mul_ne_zero huR.1 hsS.1
  have h3 : p.v * p.t ≠ 0 := mul_ne_zero hvR.1 htS.1
  have hsu : (smoothPart z (p.u * p.s), roughPart z (p.u * p.s)) =
      (p.s, p.u) := smallRough_factorization_unique
    (smoothPart_supported z _) (roughPart_supported z _) hsS huR
    ((smooth_mul_rough z h2).trans (Nat.mul_comm _ _))
  have htv : (smoothPart z (p.v * p.t), roughPart z (p.v * p.t)) =
      (p.t, p.v) := smallRough_factorization_unique
    (smoothPart_supported z _) (roughPart_supported z _) htS hvR
    ((smooth_mul_rough z h3).trans (Nat.mul_comm _ _))
  exact factor_ext (congrArg Prod.fst hsu) (congrArg Prod.fst htv)
    (congrArg Prod.snd hsu) (congrArg Prod.snd htv)

/-- Construct the missing reverse support witness from an actual
canonical physical pair in the fixed block. No allowed-equivalence or
PhysicalSplitWitness is assumed. -/
theorem canonical_mem_choices (B : Block) (atom : MediumAtom) (z : ℝ)
    {w : ℕ} {q : ℕ × ℕ} (hq : q ∈ B.selectedModuli atom z w) :
    canonicalFactor z q.1 q.2 ∈ (B.factorData atom z).choices B.d w := by
  obtain ⟨hpair, h2, h3, hs, ht, hu, hv, hd, hw, hwr⟩ := mem_filter.mp hq
  obtain ⟨hQ2, hQ3⟩ := mem_product.mp hpair
  have hmod := physical_canonical z h2 h3
  have hmod2 := congrArg Prod.fst hmod
  have hmod3 := congrArg Prod.snd hmod
  apply (mem_choices_iff _ _ _ _).mpr
  refine ⟨mem_filter.mpr ⟨hs, smoothPart_supported z _⟩,
    mem_filter.mpr ⟨ht, smoothPart_supported z _⟩,
    mem_filter.mpr ⟨hu, roughPart_supported z _⟩,
    mem_filter.mpr ⟨hv, roughPart_supported z _⟩, hd, hw, ?_⟩
  change _ ∈ factorCarrier atom.Q2 ∧ _ ∈ factorCarrier atom.Q3 ∧
    _ ∈ Icc B.wLo B.wHi
  exact ⟨hmod2.symm ▸ hQ2, hmod3.symm ▸ hQ3, hw.symm ▸ hwr⟩

/-- The PhaseE receiver now gets a constructed witness for every
selected physical pair, rather than a witness as an input premise. -/
def canonicalPhysicalSplitWitness (B : Block) (atom : MediumAtom) (z : ℝ)
    {w : ℕ} {q : ℕ × ℕ} (hq : q ∈ B.selectedModuli atom z w) :
    PhysicalSplitWitness (B.factorData atom z) q.1 q.2 B.d := by
  let p := canonicalFactor z q.1 q.2
  have hp : p ∈ (B.factorData atom z).choices B.d w :=
    canonical_mem_choices B atom z hq
  obtain ⟨hs, ht, hu, hv⟩ := choice_all_four_supports _ hp
  obtain ⟨hd, hw, ha⟩ := choice_products hp
  obtain ⟨_, h2, h3, _⟩ := mem_filter.mp hq
  have hmod := physical_canonical z h2 h3
  exact { s := p.s, t := p.t, u := p.u, v := p.v,
    hs := hs, ht := ht, hu := hu, hv := hv,
    hq2 := congrArg Prod.fst hmod, hq3 := congrArg Prod.snd hmod,
    hd := hd, hallowed := ha }

theorem choice_mem_selected (B : Block) (atom : MediumAtom) (z : ℝ)
    {w : ℕ} {p : Factor} (hp : p ∈ (B.factorData atom z).choices B.d w) :
    physicalModuli p ∈ B.selectedModuli atom z w := by
  obtain ⟨hs, ht, hu, hv, hd, hw, ha⟩ := (mem_choices_iff _ _ _ _).mp hp
  obtain ⟨hQ2, hQ3, hwr⟩ := ha
  obtain ⟨hsI, hsS⟩ := mem_filter.mp hs
  obtain ⟨htI, htS⟩ := mem_filter.mp ht
  obtain ⟨huI, huR⟩ := mem_filter.mp hu
  obtain ⟨hvI, hvR⟩ := mem_filter.mp hv
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨hQ2, hQ3⟩, ?_⟩
  rw [canonical_choice B atom z hp]
  exact ⟨mul_ne_zero huR.1 hsS.1, mul_ne_zero hvR.1 htS.1,
    hsI, htI, huI, hvI, hd, hw, hw ▸ hwr⟩

/-- Entire fixed-block support equality, rather than a one-direction
map for a pre-supplied split certificate. -/
theorem selectedModuli_eq_image_choices (B : Block) (atom : MediumAtom)
    (z : ℝ) (w : ℕ) :
    B.selectedModuli atom z w =
      ((B.factorData atom z).choices B.d w).image physicalModuli := by
  ext q
  constructor
  · intro hq
    obtain ⟨_, h2, h3, _⟩ := mem_filter.mp hq
    exact mem_image.mpr ⟨canonicalFactor z q.1 q.2,
      canonical_mem_choices B atom z hq, physical_canonical z h2 h3⟩
  · intro hq
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
    exact choice_mem_selected B atom z hp

theorem physicalModuli_injOn_choices (B : Block) (atom : MediumAtom)
    (z : ℝ) (w : ℕ) :
    Set.InjOn physicalModuli ((B.factorData atom z).choices B.d w) := by
  intro p hp p' hp' heq
  calc
    p = canonicalFactor z (physicalModuli p).1 (physicalModuli p).2 :=
      (canonical_choice B atom z hp).symm
    _ = canonicalFactor z (physicalModuli p').1 (physicalModuli p').2 := by rw [heq]
    _ = p' := canonical_choice B atom z hp'

/-- Arbitrary signed/complex weights reindex on the exact same physical
pairs. This also applies with deleted congruence indicators attached. -/
theorem sum_selectedModuli_eq_choices (B : Block) (atom : MediumAtom)
    (z : ℝ) (w : ℕ) (f : (ℕ × ℕ) → ℂ) :
    (∑ q ∈ B.selectedModuli atom z w, f q) =
      ∑ p ∈ (B.factorData atom z).choices B.d w, f (physicalModuli p) := by
  rw [selectedModuli_eq_image_choices]
  exact sum_image (physicalModuli_injOn_choices B atom z w)

/-- Both copies of the original square are reindexed independently.
The arbitrary kernel can contain the common q and m, the n1 != n2 gate,
all deleted congruence indicators, and retained complex weights. -/
theorem sum_selected_pair_eq_choices (B : Block) (atom : MediumAtom)
    (z : ℝ) (r s : ℕ) (f : (ℕ × ℕ) → (ℕ × ℕ) → ℂ) :
    (∑ q ∈ B.selectedModuli atom z r,
      ∑ q' ∈ B.selectedModuli atom z s, f q q') =
    ∑ p ∈ (B.factorData atom z).choices B.d r,
      ∑ p' ∈ (B.factorData atom z).choices B.d s,
        f (physicalModuli p) (physicalModuli p') := by
  rw [sum_selectedModuli_eq_choices]
  apply sum_congr rfl
  intro p hp
  exact sum_selectedModuli_eq_choices B atom z s (f (physicalModuli p))

/-- Literal paper Lambda_d(w) equals the original gamma2(q2)gamma3(q3)
weighted physical slice, retaining every admissible pair exactly once. -/
theorem lambdaAt_eq_original_physical_slice (B : Block) (atom : MediumAtom)
    (z : ℝ) (w : ℕ) :
    (B.factorData atom z).lambdaAt B.d w =
      ∑ q ∈ B.selectedModuli atom z w, atom.gamma2 q.1 * atom.gamma3 q.2 := by
  rw [sum_selectedModuli_eq_choices]
  rfl

end
end ImbalancedChen.Part3.MediumCanonicalFixedBlock20261028
