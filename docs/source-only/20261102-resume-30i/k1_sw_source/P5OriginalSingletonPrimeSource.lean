import ImbalancedChen.P5All16ComputedMarkedTensorBudget
import ImbalancedChen.Part3MellinPrimeIntervalSW
import ImbalancedChen.ChenInitialCorrectionBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The singleton class of the ORIGINAL per-label gamma, including p ∤ N.
The common alphabet is Ico in logarithmic coordinates. Its intersection
with a right-closed dyadic interval is converted using ceil(endpoint)-1;
no endpoint prime is thrown away. The coefficient is still the gamma
which occurs in H's computed marked tensor, with denominator count! = 1.
This file does not assign SW to longer words, beta, or arbitrary masks.
-/

namespace ImbalancedChen.P5Z.OriginalSingletonPrimeSource
noncomputable section
open Classical Finset Set
open scoped BigOperators
open ImbalancedChen ImbalancedChen.Part3
open All16MarkedCommonFineSource All16FineMeshGateScalar
open ActualInnerPerLabelGamma
open PrimeMellinProfileVariation20261026b MellinPrimeIntervalSW20261026b
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def lower (N m : ℕ) (i : Fin (m+1)) : ℝ :=
  (N : ℝ)^logPrimeMeshPoint 0 1 m i.val

def upper (N m : ℕ) (i : Fin (m+1)) : ℝ :=
  (N : ℝ)^logPrimeMeshPoint 0 1 m (i.val+1)

theorem common_label_bounds {N m : ℕ} (hN : 1 < N) (i : Fin (m+1)) :
    1 ≤ lower N m i ∧ upper N m i ≤ N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hlo : 0 ≤ logPrimeMeshPoint 0 1 m i.val := by
    simpa using logPrimeMeshPoint_mono (by norm_num : (0 : ℝ) ≤ 1) m
      (Nat.zero_le i.val)
  have hhi : logPrimeMeshPoint 0 1 m (i.val+1) ≤ 1 := by
    simpa using logPrimeMeshPoint_mono (by norm_num : (0 : ℝ) ≤ 1) m
      (Nat.succ_le_of_lt i.isLt)
  exact ⟨Real.one_le_rpow hn hlo,
    (Real.rpow_le_rpow_of_exponent_le hn hhi).trans_eq (Real.rpow_one _)⟩

theorem mem_commonAlphabet_iff {N m p : ℕ} (hN : 1 < N) (i : Fin (m+1)) :
    p ∈ commonAlphabet N m i ↔
      p.Prime ∧ ¬p ∣ N ∧ lower N m i ≤ p ∧ (p : ℝ) < upper N m i := by
  obtain ⟨hlo,hhi⟩ := common_label_bounds hN i
  change p ∈ (roughPrimeFinset N N 1 N).filter
    (fun p => lower N m i ≤ (p : ℝ) ∧ (p : ℝ) < upper N m i) ↔ _
  rw [Finset.mem_filter, mem_roughPrimeFinset]
  constructor
  · rintro ⟨⟨hpN,hp,hd,hp1,hpN'⟩,hl,hh⟩
    exact ⟨hp,hd,hl,hh⟩
  · rintro ⟨hp,hd,hl,hh⟩
    have hpN : (p : ℝ) < N := hh.trans_le hhi
    exact ⟨⟨by exact_mod_cast hpN,hp,hd,hlo.trans hl,hpN⟩,hl,hh⟩

theorem gamma_singleton {ι : Type*} [DecidableEq ι]
    (B : ι → Finset ℕ) (i : ι) (n : ℕ) :
    gamma B [i] n = if n ∈ B i then 1 else 0 := by
  have hf : (actualPrimeSlotBox B [i]).filter (fun ps => ps.prod = n) =
      if n ∈ B i then {[n]} else ∅ := by
    ext ps
    by_cases hn : n ∈ B i
    · simp only [hn,if_true,Finset.mem_singleton,Finset.mem_filter]
      constructor
      · rintro ⟨hps,hprod⟩
        obtain ⟨⟨p,qs⟩,hpqs,rfl⟩ := Finset.mem_image.mp hps
        obtain ⟨hp,hqs⟩ := Finset.mem_product.mp hpqs
        have hqs' : qs = [] := Finset.mem_singleton.mp hqs
        subst qs
        simpa using congrArg (fun x : ℕ => [x]) hprod
      · rintro rfl
        exact ⟨Finset.mem_image.mpr ⟨(n,[]),
          Finset.mem_product.mpr ⟨hn,Finset.mem_singleton_self _⟩,rfl⟩,by simp⟩
    · simp only [hn,if_false,Finset.not_mem_empty,Finset.mem_filter,iff_false]
      rintro ⟨hps,hprod⟩
      obtain ⟨⟨p,qs⟩,hpqs,rfl⟩ := Finset.mem_image.mp hps
      obtain ⟨hp,hqs⟩ := Finset.mem_product.mp hpqs
      have hqs' : qs = [] := Finset.mem_singleton.mp hqs
      subst qs
      have he : p = n := by simpa using hprod
      exact hn (he ▸ hp)
  simp only [gamma,actualPrimeTupleCoefficient,hf]
  by_cases hn : n ∈ B i <;> simp [hn,multiplicity]

/-- The real original per-label coefficient and its literal dyadic carrier. -/
def source (N m : ℕ) (i : Fin (m+1)) (U : ℝ) : Finset ℕ :=
  (commonAlphabet N m i).filter (fun p => U < (p : ℝ) ∧ (p : ℝ) ≤ 2*U)

def coefficient (N m : ℕ) (word : List (Fin (m+1)))
    (Phi : ℝ → ℝ) (t U : ℝ) (n : ℕ) : ℂ :=
  physicalProfile Phi t U n * (gamma (commonAlphabet N m) word n : ℂ)

def clipLo (N m : ℕ) (i : Fin (m+1)) (U : ℝ) : ℝ :=
  max U ((Nat.ceil (lower N m i) : ℝ)-1)

def clipHi (N m : ℕ) (i : Fin (m+1)) (U : ℝ) : ℝ :=
  min (2*U) ((Nat.ceil (upper N m i) : ℝ)-1)

private theorem ceil_window (l h : ℝ) (p : ℕ) :
    l ≤ (p : ℝ) ∧ (p : ℝ) < h ↔
      (Nat.ceil l : ℝ)-1 < p ∧ (p : ℝ) ≤ (Nat.ceil h : ℝ)-1 := by
  rw [← Nat.ceil_le, ← Nat.lt_ceil]
  constructor
  · rintro ⟨hl,hh⟩
    have hl' : (Nat.ceil l : ℝ) ≤ p := by exact_mod_cast hl
    have hh' : (p : ℝ)+1 ≤ Nat.ceil h := by exact_mod_cast hh
    constructor <;> linarith
  · rintro ⟨hl,hh⟩
    have hl' : (Nat.ceil l : ℝ) < (p+1 : ℕ) := by push_cast; linarith
    have hh' : (p : ℝ) < Nat.ceil h := by linarith
    have hl'' : Nat.ceil l < p+1 := by exact_mod_cast hl'
    exact ⟨by omega,by exact_mod_cast hh'⟩

theorem source_nonempty_geometry {N m : ℕ} (hN : 1 < N)
    (i : Fin (m+1)) {U : ℝ} (hU : 1 ≤ U) (hs : (source N m i U).Nonempty) :
    U ≤ clipLo N m i U ∧ clipLo N m i U ≤ clipHi N m i U ∧
      clipHi N m i U ≤ 2*U := by
  obtain ⟨p,hp⟩ := hs
  obtain ⟨hp,hu,hv⟩ := Finset.mem_filter.mp hp
  have hf := (mem_commonAlphabet_iff hN i).mp hp
  have hw := (ceil_window (lower N m i) (upper N m i) p).mp hf.2.2
  exact ⟨le_max_left _ _,
    (max_lt hu hw.1).le.trans (le_min hv hw.2),min_le_left _ _⟩

theorem source_eq_prime_filter {N m : ℕ} (hN : 1 < N)
    (i : Fin (m+1)) {U : ℝ} (hU : 1 ≤ U) (hs : (source N m i U).Nonempty) :
    source N m i U =
      (primeSWInterval (clipLo N m i U) (clipHi N m i U)).filter
        (fun p => p.Prime ∧ ¬p ∣ N) := by
  obtain ⟨hul,hlh,hhu⟩ := source_nonempty_geometry hN i hU hs
  have hl0 : 0 ≤ clipLo N m i U := by linarith
  have hh0 : 0 ≤ clipHi N m i U := by linarith
  ext p
  have hfloor : p ∈ primeSWInterval (clipLo N m i U) (clipHi N m i U) ↔
      clipLo N m i U < (p : ℝ) ∧ (p : ℝ) ≤ clipHi N m i U := by
    simp only [primeSWInterval,Finset.mem_Ioc,Nat.floor_lt hl0]
    constructor
    · rintro ⟨hl,hh⟩
      exact ⟨hl,(show (p : ℝ) ≤ (Nat.floor (clipHi N m i U) : ℝ) by
        exact_mod_cast hh).trans (Nat.floor_le hh0)⟩
    · rintro ⟨hl,hh⟩
      exact ⟨hl,Nat.le_floor hh⟩
  simp only [source,Finset.mem_filter,mem_commonAlphabet_iff hN i,hfloor,
    clipLo,clipHi,max_lt_iff,le_min_iff]
  rw [ceil_window]
  tauto

/-- The prime indicator is only applied after the actual source dictionary.
The target exclusion becomes auxiliary N in BOTH the AP count and mean. -/
theorem source_error_eq_prime {N m : ℕ} (hN : 1 < N)
    (i : Fin (m+1)) {U : ℝ} (hU : 1 ≤ U) (hs : (source N m i U).Nonempty)
    (Phi : ℝ → ℝ) (t : ℝ) (q b : ℕ) :
    auxiliarySWError (source N m i U) (coefficient N m [i] Phi t U) 1 q b =
      auxiliarySWError (primeSWInterval (clipLo N m i U) (clipHi N m i U))
        (mellinPrimeCoefficient Phi t U) N q b := by
  have hc : ∀ p ∈ source N m i U,
      coefficient N m [i] Phi t U p = physicalProfile Phi t U p := by
    intro p hp
    simp only [coefficient,gamma_singleton,if_pos (Finset.mem_filter.mp hp).1,
      Complex.ofReal_one,mul_one]
  unfold auxiliarySWError
  simp_rw [← Finset.sum_filter]
  have hcount : ∀ (P : ℕ → Prop) [DecidablePred P],
      (∑ p ∈ (source N m i U).filter P, coefficient N m [i] Phi t U p) =
      ∑ p ∈ (source N m i U).filter P, physicalProfile Phi t U p := by
    intro P _
    exact Finset.sum_congr rfl (fun p hp => hc p (Finset.mem_filter.mp hp).1)
  rw [hcount,hcount,source_eq_prime_filter hN i hU hs]
  simp only [Finset.sum_filter,Finset.mem_filter,mellinPrimeCoefficient,
    primeSWBeta,Nat.coprime_one_right_eq_true,and_true,one_mul,
    Nat.coprime_mul_iff_right]
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    by_cases hprime : p.Prime
    · have hcop : p.Coprime N ↔ ¬p ∣ N := hprime.coprime_iff_not_dvd
      by_cases hd : p ∣ N <;> by_cases hb : Nat.ModEq q p b <;>
        simp [hprime,hd,hb,hcop]
    · simp [hprime]
  · congr 1
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hprime : p.Prime
    · have hcop : p.Coprime N ↔ ¬p ∣ N := hprime.coprime_iff_not_dvd
      by_cases hd : p ∣ N <;> by_cases hq : p.Coprime q <;>
        by_cases hb : Nat.ModEq q p b <;> simp [hprime,hd,hq,hb,hcop]
    · simp [hprime]

end
end ImbalancedChen.P5Z.OriginalSingletonPrimeSource
