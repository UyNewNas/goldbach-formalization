import ImbalancedChen.FiniteSieveModel
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite discrepancy transfer across a curved boundary

All masses in this file are actual finite sums on a common carrier. The
normalizing mass is restricted to integers coprime to the modulus, exactly
as in the manuscript. For `0 ≤ h ≤ u`, the boundary comparison is proved
with constant one, improving the manuscript's constant two:

`|Δ h| ≤ |Δ u| + coprimeMass u / φ(d) ≤ |Δ u| + totalMass u / φ(d)`.

The proof holds for every residue and modulus; in particular it applies
to every primitive class with positive modulus. Exact additivity, source
partitions, and summation over finitely many moduli are also proved.

For a curved-source sandwich, the common carrier must contain the full
upper-envelope support, including points outside the curved source.
The zero-extension and half-product indicator lemmas below preserve those
outside-source boundary contributions. No rectangle distribution theorem,
boundary lattice-point estimate, or reciprocal-totient estimate is assumed
or claimed. The final sieve-remainder identity retains the existing
roughness gate and restriction to divisors of the actual sieve product.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The total weight on the common finite carrier. -/
def finiteSourceMass (S : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ m ∈ S, w m

/-- The literal weighted sum in the residue class `a` modulo `d`. -/
def finiteCongruenceMass (S : Finset ℕ) (w : ℕ → ℝ) (a d : ℕ) : ℝ :=
  ∑ m ∈ S with Nat.ModEq d m a, w m

/-- The literal weighted sum restricted to integers coprime to `d`. -/
def finiteCoprimeMass (S : Finset ℕ) (w : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ m ∈ S with Nat.Coprime m d, w m

/-- The actual coprime-normalized discrepancy. Its definition also makes
sense for nonprimitive classes and for Lean's totalized division at zero. -/
def finitePrimitiveDiscrepancy
    (S : Finset ℕ) (w : ℕ → ℝ) (a d : ℕ) : ℝ :=
  finiteCongruenceMass S w a d - finiteCoprimeMass S w d / (Nat.totient d : ℝ)

/-- A single finite-sum expression exposes the linearity in the source. -/
theorem finitePrimitiveDiscrepancy_eq_sum
    (S : Finset ℕ) (w : ℕ → ℝ) (a d : ℕ) :
    finitePrimitiveDiscrepancy S w a d =
      ∑ m ∈ S, ((if Nat.ModEq d m a then w m else 0) -
        (if Nat.Coprime m d then w m else 0) / (Nat.totient d : ℝ)) := by
  classical
  simp only [finitePrimitiveDiscrepancy, finiteCongruenceMass,
    finiteCoprimeMass, Finset.sum_filter, div_eq_mul_inv,
    Finset.sum_sub_distrib, Finset.sum_mul]

/-- Weights need only agree on the common carrier. -/
theorem finitePrimitiveDiscrepancy_congr
    (S : Finset ℕ) (w v : ℕ → ℝ) (a d : ℕ)
    (hwv : ∀ m ∈ S, w m = v m) :
    finitePrimitiveDiscrepancy S w a d = finitePrimitiveDiscrepancy S v a d := by
  rw [finitePrimitiveDiscrepancy_eq_sum, finitePrimitiveDiscrepancy_eq_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hwv m hm]

@[simp] theorem finitePrimitiveDiscrepancy_zero (S : Finset ℕ) (a d : ℕ) :
    finitePrimitiveDiscrepancy S (fun _ => 0) a d = 0 := by
  simp [finitePrimitiveDiscrepancy, finiteCongruenceMass, finiteCoprimeMass]

/-- Exact additivity for weighted sources on the same carrier. -/
theorem finitePrimitiveDiscrepancy_add
    (S : Finset ℕ) (w v : ℕ → ℝ) (a d : ℕ) :
    finitePrimitiveDiscrepancy S (fun m => w m + v m) a d =
      finitePrimitiveDiscrepancy S w a d + finitePrimitiveDiscrepancy S v a d := by
  simp only [finitePrimitiveDiscrepancy, finiteCongruenceMass,
    finiteCoprimeMass, Finset.sum_add_distrib, add_div]
  ring

/-- Exact subtraction, used for the difference of the two envelopes. -/
theorem finitePrimitiveDiscrepancy_sub
    (S : Finset ℕ) (w v : ℕ → ℝ) (a d : ℕ) :
    finitePrimitiveDiscrepancy S (fun m => w m - v m) a d =
      finitePrimitiveDiscrepancy S w a d - finitePrimitiveDiscrepancy S v a d := by
  simp only [finitePrimitiveDiscrepancy, finiteCongruenceMass,
    finiteCoprimeMass, Finset.sum_sub_distrib, sub_div]
  ring

/-- A finite family of rectangle weights contributes exactly the sum of
its discrepancies, including any multiplicities in those weights. -/
theorem finitePrimitiveDiscrepancy_sum {ι : Type*}
    (I : Finset ι) (S : Finset ℕ) (w : ι → ℕ → ℝ) (a d : ℕ) :
    finitePrimitiveDiscrepancy S (fun m => ∑ i ∈ I, w i m) a d =
      ∑ i ∈ I, finitePrimitiveDiscrepancy S (w i) a d := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
      simp only [Finset.sum_insert hi]
      rw [finitePrimitiveDiscrepancy_add, ih]

/-- Triangle inequality after exact finite source decomposition. -/
theorem abs_finitePrimitiveDiscrepancy_sum_le {ι : Type*}
    (I : Finset ι) (S : Finset ℕ) (w : ι → ℕ → ℝ) (a d : ℕ) :
    |finitePrimitiveDiscrepancy S (fun m => ∑ i ∈ I, w i m) a d| ≤
      ∑ i ∈ I, |finitePrimitiveDiscrepancy S (w i) a d| := by
  rw [finitePrimitiveDiscrepancy_sum]
  exact Finset.abs_sum_le_sum_abs _ _

/-- A genuine disjoint source partition gives exact discrepancy additivity. -/
theorem finitePrimitiveDiscrepancy_union
    (S R : Finset ℕ) (w : ℕ → ℝ) (a d : ℕ) (hSR : Disjoint S R) :
    finitePrimitiveDiscrepancy (S ∪ R) w a d =
      finitePrimitiveDiscrepancy S w a d + finitePrimitiveDiscrepancy R w a d := by
  simp only [finitePrimitiveDiscrepancy_eq_sum]
  exact Finset.sum_union hSR

/-- Exact inside/outside source partition, with no sign assumptions. -/
theorem finitePrimitiveDiscrepancy_filter_partition
    (S : Finset ℕ) (P : ℕ → Prop) [DecidablePred P]
    (w : ℕ → ℝ) (a d : ℕ) :
    finitePrimitiveDiscrepancy S w a d =
      finitePrimitiveDiscrepancy (S.filter P) w a d +
      finitePrimitiveDiscrepancy (S.filter (fun m => ¬P m)) w a d := by
  classical
  simp only [finitePrimitiveDiscrepancy_eq_sum]
  exact (Finset.sum_filter_add_sum_filter_not S P _).symm

/-- Zero extension to a larger carrier leaves the discrepancy unchanged. -/
theorem finitePrimitiveDiscrepancy_eq_of_subset
    (A S : Finset ℕ) (w : ℕ → ℝ) (a d : ℕ) (hAS : A ⊆ S)
    (hz : ∀ m ∈ S, m ∉ A → w m = 0) :
    finitePrimitiveDiscrepancy S w a d = finitePrimitiveDiscrepancy A w a d := by
  classical
  simp only [finitePrimitiveDiscrepancy_eq_sum]
  symm
  apply Finset.sum_subset hAS
  intro m hmS hmA
  simp [hz m hmS hmA]

/-- The indicator of a source can be evaluated on any finite carrier
containing it. This permits upper envelopes with larger support. -/
theorem finitePrimitiveDiscrepancy_indicator_of_subset
    (A S : Finset ℕ) (a d : ℕ) (hAS : A ⊆ S) :
    finitePrimitiveDiscrepancy S (fun m => if m ∈ A then 1 else 0) a d =
      finitePrimitiveDiscrepancy A (fun _ => 1) a d := by
  classical
  rw [finitePrimitiveDiscrepancy_eq_of_subset A S _ a d hAS
    (fun m _ hmA => if_neg hmA)]
  exact finitePrimitiveDiscrepancy_congr A _ _ a d fun m hm => if_pos hm

theorem finiteCongruenceMass_nonneg
    (S : Finset ℕ) (w : ℕ → ℝ) (a d : ℕ) (hw : ∀ m ∈ S, 0 ≤ w m) :
    0 ≤ finiteCongruenceMass S w a d := by
  exact Finset.sum_nonneg fun m hm => hw m (Finset.mem_filter.mp hm).1

theorem finiteCoprimeMass_nonneg
    (S : Finset ℕ) (w : ℕ → ℝ) (d : ℕ) (hw : ∀ m ∈ S, 0 ≤ w m) :
    0 ≤ finiteCoprimeMass S w d := by
  exact Finset.sum_nonneg fun m hm => hw m (Finset.mem_filter.mp hm).1

theorem finiteCongruenceMass_mono
    (S : Finset ℕ) (w v : ℕ → ℝ) (a d : ℕ)
    (hwv : ∀ m ∈ S, w m ≤ v m) :
    finiteCongruenceMass S w a d ≤ finiteCongruenceMass S v a d := by
  exact Finset.sum_le_sum fun m hm => hwv m (Finset.mem_filter.mp hm).1

theorem finiteCoprimeMass_mono
    (S : Finset ℕ) (w v : ℕ → ℝ) (d : ℕ)
    (hwv : ∀ m ∈ S, w m ≤ v m) :
    finiteCoprimeMass S w d ≤ finiteCoprimeMass S v d := by
  exact Finset.sum_le_sum fun m hm => hwv m (Finset.mem_filter.mp hm).1

/-- Nonnegative coprime mass is bounded by the full carrier mass. -/
theorem finiteCoprimeMass_le_sourceMass
    (S : Finset ℕ) (w : ℕ → ℝ) (d : ℕ) (hw : ∀ m ∈ S, 0 ≤ w m) :
    finiteCoprimeMass S w d ≤ finiteSourceMass S w := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun m hm _ => hw m hm

/-- Finite boundary domination with constant one and the sharper coprime
mass. Positive modulus and primitive residue assumptions are unnecessary. -/
theorem abs_finitePrimitiveDiscrepancy_le_of_nonneg_le
    (S : Finset ℕ) (h u : ℕ → ℝ) (a d : ℕ)
    (hh : ∀ m ∈ S, 0 ≤ h m) (hhu : ∀ m ∈ S, h m ≤ u m) :
    |finitePrimitiveDiscrepancy S h a d| ≤
      |finitePrimitiveDiscrepancy S u a d| +
        finiteCoprimeMass S u d / (Nat.totient d : ℝ) := by
  have hA := finiteCongruenceMass_nonneg S h a d hh
  have hAm := finiteCongruenceMass_mono S h u a d hhu
  have hphi : (0 : ℝ) ≤ (Nat.totient d : ℝ) := Nat.cast_nonneg _
  have hB : 0 ≤ finiteCoprimeMass S h d / (Nat.totient d : ℝ) :=
    div_nonneg (finiteCoprimeMass_nonneg S h d hh) hphi
  have hBm : finiteCoprimeMass S h d / (Nat.totient d : ℝ) ≤
      finiteCoprimeMass S u d / (Nat.totient d : ℝ) :=
    div_le_div_of_nonneg_right (finiteCoprimeMass_mono S h u d hhu) hphi
  have habs := abs_nonneg (finitePrimitiveDiscrepancy S u a d)
  have hupper := le_abs_self (finitePrimitiveDiscrepancy S u a d)
  unfold finitePrimitiveDiscrepancy at habs hupper ⊢
  apply abs_le.mpr
  constructor <;> linarith

/-- The manuscript's boundary comparison, strengthened to constant one
in front of the literal total boundary mass. -/
theorem abs_finitePrimitiveDiscrepancy_le_sourceMass
    (S : Finset ℕ) (h u : ℕ → ℝ) (a d : ℕ)
    (hh : ∀ m ∈ S, 0 ≤ h m) (hhu : ∀ m ∈ S, h m ≤ u m) :
    |finitePrimitiveDiscrepancy S h a d| ≤
      |finitePrimitiveDiscrepancy S u a d| +
        finiteSourceMass S u / (Nat.totient d : ℝ) := by
  have hu : ∀ m ∈ S, 0 ≤ u m := fun m hm => (hh m hm).trans (hhu m hm)
  exact (abs_finitePrimitiveDiscrepancy_le_of_nonneg_le S h u a d hh hhu).trans
    (add_le_add le_rfl
      (div_le_div_of_nonneg_right (finiteCoprimeMass_le_sourceMass S u d hu)
        (Nat.cast_nonneg _)))

/-- Summing the finite boundary comparison costs a reciprocal-totient
sum, rather than the number of moduli times the boundary mass. The
chosen class may depend arbitrarily on the modulus. -/
theorem sum_abs_finitePrimitiveDiscrepancy_le_sourceMass
    (D S : Finset ℕ) (h u : ℕ → ℝ) (a : ℕ → ℕ)
    (hh : ∀ m ∈ S, 0 ≤ h m) (hhu : ∀ m ∈ S, h m ≤ u m) :
    (∑ d ∈ D, |finitePrimitiveDiscrepancy S h (a d) d|) ≤
      (∑ d ∈ D, |finitePrimitiveDiscrepancy S u (a d) d|) +
        finiteSourceMass S u * (∑ d ∈ D, 1 / (Nat.totient d : ℝ)) := by
  calc
    (∑ d ∈ D, |finitePrimitiveDiscrepancy S h (a d) d|) ≤
        ∑ d ∈ D, (|finitePrimitiveDiscrepancy S u (a d) d| +
          finiteSourceMass S u / (Nat.totient d : ℝ)) :=
      Finset.sum_le_sum fun d _ =>
        abs_finitePrimitiveDiscrepancy_le_sourceMass S h u (a d) d hh hhu
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      ring

/-- A sandwich transfers the lower-envelope discrepancy to the target.
The carrier must include the full upper-envelope support; the target is
zero-extended there if its original source is smaller. -/
theorem abs_finitePrimitiveDiscrepancy_le_of_sandwich
    (S : Finset ℕ) (f lower upper : ℕ → ℝ) (a d : ℕ)
    (hlower : ∀ m ∈ S, lower m ≤ f m)
    (hupper : ∀ m ∈ S, f m ≤ upper m) :
    |finitePrimitiveDiscrepancy S f a d| ≤
      |finitePrimitiveDiscrepancy S lower a d| +
      |finitePrimitiveDiscrepancy S (fun m => upper m - lower m) a d| +
        finiteSourceMass S (fun m => upper m - lower m) / (Nat.totient d : ℝ) := by
  have hh : ∀ m ∈ S, 0 ≤ f m - lower m :=
    fun m hm => sub_nonneg.mpr (hlower m hm)
  have hhu : ∀ m ∈ S, f m - lower m ≤ upper m - lower m :=
    fun m hm => sub_le_sub_right (hupper m hm) (lower m)
  have hboundary := abs_finitePrimitiveDiscrepancy_le_sourceMass S
    (fun m => f m - lower m) (fun m => upper m - lower m) a d hh hhu
  rw [finitePrimitiveDiscrepancy_sub] at hboundary
  have htriangle : |finitePrimitiveDiscrepancy S f a d| ≤
      |finitePrimitiveDiscrepancy S lower a d| +
      |finitePrimitiveDiscrepancy S f a d - finitePrimitiveDiscrepancy S lower a d| := by
    calc
      |finitePrimitiveDiscrepancy S f a d| =
          |finitePrimitiveDiscrepancy S lower a d +
            (finitePrimitiveDiscrepancy S f a d -
              finitePrimitiveDiscrepancy S lower a d)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  linarith

/-- The general discrepancy agrees exactly with the existing literal
half-product congruence and coprime masses. No new source is substituted. -/
theorem finitePrimitiveDiscrepancy_halfProductSource
    (num den N : ℕ) (T : ℝ) (d : ℕ) :
    finitePrimitiveDiscrepancy (halfProductSource num den N T) (fun _ => 1) N d =
      halfProductCongruenceMass num den N T d -
        halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ) := by
  simp [finitePrimitiveDiscrepancy, finiteCongruenceMass, finiteCoprimeMass,
    halfProductCongruenceMass, halfProductCoprimeMass]

/-- Place the actual half-product indicator on a carrier large enough for
all inside and intersecting rectangles, without deleting exterior mass. -/
theorem finitePrimitiveDiscrepancy_halfProductIndicator
    (num den N : ℕ) (T : ℝ) (S : Finset ℕ) (d : ℕ)
    (hS : halfProductSource num den N T ⊆ S) :
    finitePrimitiveDiscrepancy S
        (fun m => if m ∈ halfProductSource num den N T then 1 else 0) N d =
      halfProductCongruenceMass num den N T d -
        halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ) := by
  rw [finitePrimitiveDiscrepancy_indicator_of_subset _ S N d hS]
  exact finitePrimitiveDiscrepancy_halfProductSource num den N T d

/-- Concrete curved-source transfer, expressed in the pre-existing
half-product masses. The envelopes are compared on the full carrier. -/
theorem abs_halfProductPrimitiveDiscrepancy_le_of_sandwich
    (num den N : ℕ) (T : ℝ) (S : Finset ℕ) (lower upper : ℕ → ℝ) (d : ℕ)
    (hS : halfProductSource num den N T ⊆ S)
    (hlower : ∀ m ∈ S,
      lower m ≤ if m ∈ halfProductSource num den N T then 1 else 0)
    (hupper : ∀ m ∈ S,
      (if m ∈ halfProductSource num den N T then 1 else 0) ≤ upper m) :
    |halfProductCongruenceMass num den N T d -
        halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)| ≤
      |finitePrimitiveDiscrepancy S lower N d| +
      |finitePrimitiveDiscrepancy S (fun m => upper m - lower m) N d| +
        finiteSourceMass S (fun m => upper m - lower m) / (Nat.totient d : ℝ) := by
  rw [← finitePrimitiveDiscrepancy_halfProductIndicator num den N T S d hS]
  exact abs_finitePrimitiveDiscrepancy_le_of_sandwich S _ lower upper N d hlower hupper

/-- The actual sieve remainder is this finite discrepancy only under the
already-proved geometric gate and the actual allowed-modulus condition. -/
theorem halfProductBoundingSieve_rem_eq_finitePrimitiveDiscrepancy
    {num den N z d : ℕ} {T : ℝ} (hN : Even N)
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (((num : ℝ) / (den : ℝ)) /
      (1 + (num : ℝ) / (den : ℝ)))) (hd : d ∣ sieveProduct N z) :
    (halfProductBoundingSieve num den N T z hN).rem d =
      finitePrimitiveDiscrepancy (halfProductSource num den N T) (fun _ => 1) N d := by
  rw [finitePrimitiveDiscrepancy_halfProductSource]
  exact halfProductBoundingSieve_rem_eq_primitive_discrepancy hN hnum hden hT hcap hd

end

end ImbalancedChen
