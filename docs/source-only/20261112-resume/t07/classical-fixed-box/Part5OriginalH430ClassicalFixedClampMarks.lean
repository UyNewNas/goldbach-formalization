import ImbalancedChen.Part5OriginalH430ClassicalSeedIntegralCap

/-! The fixed geometric family before and after removal of the original
target-prime deletions. Both sides count the prefixed prime p, the full
colour-labelled list and the same rough integer m at Q=N^ν. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalFixedClampMarks
noncomputable section
open Finset Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedSwitchedUnsiftedSource (labels)
open P2EnhancedNonunitLabelGeometry (label_data label_prod_pos)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2SeedOmegaLiteralFibre (a0 b)
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open Part5UpperTables.OriginalU34
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430FrozenRootRefinement (frozenLevel frozenLevel_bounds)
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430RootIntervalTheta
open Part5OriginalH430ClassicalCausalSeedScale (smallProduct)
open Part5OriginalH430ClassicalSmallSwitchedIntegers
open Part5OriginalH430ClassicalSeedIntegralCap
open scoped Classical BigOperators

abbrev Mark := Σ _p : ℕ, Σ _qs : List ℕ, ℕ

def outer (mask N : ℕ) : Finset ℕ :=
  primeWindow mask ((N:ℝ)^clampStart) ((N:ℝ)^(1/3:ℝ))

def marks (mask N : ℕ) (ν κ : ℝ) (cs : List ℕ) : Finset Mark :=
  (outer mask N).sigma (fun p => (labels mask ((N:ℝ)^ν) p cs).sigma
    (fun qs => largeIntegers N (p*qs.prod) (qs.getD (qs.length-2) 0) (smallProduct N κ)))

def letters (u : Mark) := u.1::u.2.1
def product (u : Mark) := u.1*u.2.1.prod*u.2.2

def count (tested : Bool) (mask N : ℕ) (ν κ : ℝ) : ℝ :=
  wordsSum (fun cs => ∑ u∈marks mask N ν κ cs,testWeight tested N (u.1*u.2.1.prod) u.2.2)

theorem flags {N mask : ℕ} {ν κ : ℝ} {cs : List ℕ} {u : Mark} :
    u∈marks mask N ν κ cs ↔ u.1∈outer mask N ∧
      u.2.1∈labels mask ((N:ℝ)^ν) u.1 cs ∧
      u.2.2∈largeIntegers N (u.1*u.2.1.prod) (u.2.1.getD (u.2.1.length-2) 0) (smallProduct N κ) := by
  simp only [marks,mem_sigma]

theorem outer_eq_primeBand {N : ℕ} (hN : 1<N) :
    outer N N=primeBand N clampStart (1/3) := by
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have hhi : (N:ℝ)^(1/3:ℝ)<N := by
    simpa only [rpow_one] using rpow_lt_rpow_of_exponent_lt hNr (by norm_num : (1/3:ℝ)<1)
  ext p
  change p∈primeWindow N _ _ ↔ p∈chenSinglePrimeSelector N _ _
  rw [mem_primeWindow,chenSinglePrimeSelector,mem_filter,mem_chenAdditivePrimeCarrier]
  exact ⟨fun ⟨hp,hc,hlo,hup⟩ => ⟨⟨by exact_mod_cast hup.trans hhi,hp,hc⟩,hlo,hup⟩,
    fun ⟨⟨_,hp,hc⟩,hlo,hup⟩ => ⟨hp,hc,hlo,hup⟩⟩

theorem outer_eq_clamp {N : ℕ} (hN : 1<N) : outer N N=clampPrimes N := by
  rw [outer_eq_primeBand hN]
  have ha : (N:ℝ)^a≤(N:ℝ)^clampStart := rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hN.le) (by norm_num [a,clampStart])
  ext p
  change p∈chenSinglePrimeSelector N _ _ ↔ p∈(chenSinglePrimeSelector N _ _).filter _
  simp only [chenSinglePrimeSelector,mem_filter]
  exact ⟨fun ⟨h,hlo,hhi⟩ => ⟨⟨h,ha.trans hlo,hhi⟩,hlo⟩,
    fun ⟨⟨h,_,hhi⟩,hlo⟩ => ⟨h,hlo,hhi⟩⟩

private theorem label_mask (N : ℕ) (Q : ℝ) (p : ℕ) (cs qs : List ℕ) :
    qs∈labels N Q p cs ↔ qs∈labels 1 Q p cs ∧ ∀ q∈qs,q.Coprime N := by
  simp only [labels,mem_filter,secondFunctionalMother_tuple_mem,mem_primeWindow,Nat.coprime_one_right,true_and]
  constructor
  · rintro ⟨⟨hl,ho,hs⟩,hc⟩
    exact ⟨⟨⟨hl,ho,fun q h => ⟨(hs q h).1,(hs q h).2.2⟩⟩,hc⟩,
      fun q h => (hs q h).2.1⟩
  · rintro ⟨⟨⟨hl,ho,hs⟩,hc⟩,hcop⟩
    exact ⟨⟨hl,ho,fun q h => ⟨(hs q h).1,hcop q h,(hs q h).2⟩⟩,hc⟩

theorem exact_target_mask {N : ℕ} {ν κ : ℝ} {cs : List ℕ} {u : Mark} :
    u∈marks N N ν κ cs ↔ u∈marks 1 N ν κ cs ∧ ∀ q∈letters u,q.Coprime N := by
  simp only [flags,outer,mem_primeWindow,Nat.coprime_one_right,true_and,label_mask N,
    letters,List.forall_mem_cons]
  tauto

theorem original_count {N n : ℕ} {τ : ℝ} (hN : 1<N) (ht : 0≤τ) (ht' : τ≤1/12)
    (tested : Bool) (κ : ℝ) :
    count tested N N (clampLevel n τ) κ=
      ∑ p∈clampPrimes N,allLarge tested N (rootQ N n .U3 τ p) p (smallProduct N κ) := by
  unfold count marks
  simp only [sum_sigma]
  rw [words_sum,outer_eq_clamp hN]
  apply sum_congr rfl
  intro p hp
  rw [(clamp_physical_level hN ht ht' hp).1]
  rfl

theorem original_le_geometry (N : ℕ) (ν κ : ℝ) (tested : Bool) :
    count tested N N ν κ≤count tested 1 N ν κ := by
  apply words_mono
  intro j cs hc
  apply sum_le_sum_of_subset_of_nonneg (fun u h => (exact_target_mask.mp h).1)
  intro u _ _
  cases tested <;> simp [testWeight] <;> positivity

theorem frozen_bounds {n : ℕ} {τ : ℝ} (ht : 0≤τ) (ht' : τ≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) :
    1/3+7/128≤clampLevel n τ ∧ clampLevel n τ≤1/2 := by
  have hf := frozenLevel_bounds (show 1/2-τ∈Set.Icc (0:ℝ) 1 from ⟨by linarith,by linarith⟩) n
  change _≤frozenLevel n (1/2-τ) ∧ frozenLevel n (1/2-τ)≤_
  constructor <;> linarith only [hf.1,hf.2,ht,ht',hn]

theorem platform {N p : ℕ} {ν : ℝ} (hN : 1<N) (hν : 1/3+7/128≤ν)
    (hp : p∈outer 1 N) :
    let R := (N:ℝ)^ν/(p:ℝ)
    (N:ℝ)^(7/128:ℝ)≤R ∧ 1<R ∧ (N:ℝ)^(1/200:ℝ)≤R^a0 ∧
      (N:ℝ)^(1/200:ℝ)≤(p:ℝ) := by
  let R := (N:ℝ)^ν/(p:ℝ)
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have h0 := zero_lt_one.trans hNr
  have h := mem_primeWindow.mp hp
  have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr h.1.pos
  have hR : (N:ℝ)^(7/128:ℝ)≤R := by
    apply (le_div_iff₀ hp0).mpr
    calc
      _ ≤ (N:ℝ)^(7/128:ℝ)*(N:ℝ)^(1/3:ℝ) :=
        mul_le_mul_of_nonneg_left h.2.2.2.le (rpow_nonneg h0.le _)
      _ ≤ _ := by rw [←rpow_add h0]; exact rpow_le_rpow_of_exponent_le hNr.le (by linarith)
  refine ⟨hR,(one_lt_rpow hNr (by norm_num : (0:ℝ)<7/128)).trans_le hR,?_,?_⟩
  · calc
      _ ≤ (N:ℝ)^((7/128)*a0) := rpow_le_rpow_of_exponent_le hNr.le (by norm_num [a0])
      _ ≤ _ := by rw [rpow_mul h0.le]; exact rpow_le_rpow (rpow_nonneg h0.le _) hR (by norm_num [a0])
  · exact (rpow_le_rpow_of_exponent_le hNr.le (by norm_num [clampStart] : (1/200:ℝ)≤clampStart)).trans h.2.2.1

end
end ImbalancedChen.Part5OriginalH430ClassicalFixedClampMarks
