import ImbalancedChen.P2OriginalBankThetaMassLimits
import ImbalancedChen.P5OriginalFeedbackDomains
import ImbalancedChen.P2FrozenReceiverCountActions

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Finite carrier and profile identities. The arrays are arbitrary OLD arrays:
no recurrence, scalar count licence, UpperEndpoints, or feedback estimate
is a premise. Every arithmetic knot uses the adjacent closed-cell minimum.
The half-open lower endpoints are retained as actual finite sums.
-/
namespace ImbalancedChen.P2OriginalHalfOpenProfileCarrier

noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology
open Wu2008DoubleSieve
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open P2OriginalChildPhysicalNormalization P2OriginalBankChildPrimeMass
open P2OriginalBankThetaMassLimits

def singleHalf (lo hi : ℝ) : Set (Coord 1) := {x | lo ≤ x 0 ∧ x 0 < hi}

def pairHalf (p : W2Parameters) : Fin 4 → Set (Coord 2)
  | 0 => {x | a0 p ≤ x 0 ∧ x 0 < x 1 ∧ x 1 < a2 p ∧ x 1 + 2*x 0 < 1}
  | 1 => {x | a0 p ≤ x 0 ∧ x 0 < a1 p ∧ a2 p ≤ x 1 ∧ x 1 < a3 p}
  | 2 => {x | a0 p ≤ x 0 ∧ x 0 < x 1 ∧ x 1 < a1 p}
  | 3 => {x | a0 p ≤ x 0 ∧ x 0 < a1 p ∧ a1 p ≤ x 1 ∧ x 1 < a2 p}

def pairLowerWall (p : W2Parameters) : Fin 4 → Set (Coord 2)
  | 0 => {x | x 0 = a0 p}
  | 1 => {x | x 0 = a0 p ∨ x 1 = a2 p}
  | 2 => {x | x 0 = a0 p}
  | 3 => {x | x 0 = a0 p ∨ x 1 = a1 p}

theorem singleHalf_partition (lo hi : ℝ) (x : Coord 1) :
    x ∈ singleHalf lo hi ↔ x ∈ singleDomain lo hi ∨ (x 0 = lo ∧ x 0 < hi) := by
  simp only [singleHalf,singleDomain,mem_setOf_eq]
  constructor
  · rintro ⟨hl,hh⟩
    rcases hl.eq_or_lt with he | he
    · exact Or.inr ⟨he.symm,hh⟩
    · exact Or.inl ⟨he,hh⟩
  · rintro (⟨hl,hh⟩ | ⟨hl,hh⟩)
    · exact ⟨hl.le,hh⟩
    · exact ⟨hl.ge,hh⟩

theorem pairHalf_partition (p : W2Parameters) (k : Fin 4) (x : Coord 2) :
    x ∈ pairHalf p k ↔
      x ∈ W2PairDomain p k ∨ (x ∈ pairHalf p k ∧ x ∈ pairLowerWall p k) := by
  fin_cases k <;>
    simp only [pairHalf,pairLowerWall,W2PairDomain,W2Pair5,W2Pair6,W2Pair7,W2Pair8,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,mem_setOf_eq] <;>
    constructor
  all_goals first
    | (intro h; by_cases h0 : x 0 = a0 p
       · exact Or.inr ⟨h,by first | exact h0 | exact Or.inl h0⟩
       · first
         | exact Or.inl ⟨lt_of_le_of_ne h.1 (Ne.symm h0),h.2⟩
         | (by_cases h1 : x 1 = a2 p
            · exact Or.inr ⟨h,Or.inr h1⟩
            · exact Or.inl ⟨lt_of_le_of_ne h.1 (Ne.symm h0),h.2.1,
                lt_of_le_of_ne h.2.2.1 (Ne.symm h1),h.2.2.2⟩)
         | (by_cases h1 : x 1 = a1 p
            · exact Or.inr ⟨h,Or.inr h1⟩
            · exact Or.inl ⟨lt_of_le_of_ne h.1 (Ne.symm h0),h.2.1,
                lt_of_le_of_ne h.2.2.1 (Ne.symm h1),h.2.2.2⟩))
    | (rintro (h | ⟨h,_⟩)
       · first
         | exact ⟨h.1.le,h.2⟩
         | exact ⟨h.1.le,h.2.1,h.2.2.1.le,h.2.2.2⟩
       · exact h)

theorem singleHalf_in_cube {lo hi : ℝ} (hlo : (1/5:ℝ) ≤ lo) (hhi : hi ≤ 1/2) :
    singleHalf lo hi ⊆ cube 1 := by
  intro x hx
  apply mem_logPrimeBox.mpr
  intro i
  fin_cases i
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

theorem pairHalf_geometry {p : W2Parameters} (hp : W2Geometry p) (k : Fin 4)
    {x : Coord 2} (hx : x ∈ pairHalf p k) :
    x ∈ pairAmbient ∧ (1/5:ℝ) ≤ 1-x 0-x 1 ∧
      2*x 1 < 1 ∧ 2*x 0+x 1 < 1 := by
  rcases hp with ⟨h0,h01,h12,h23,h3,hb,hg6,hg7,hg8⟩
  fin_cases k
  · rcases hx with ⟨hu,huv,hv,hgate⟩
    refine ⟨⟨?_,?_⟩,by linarith,by linarith,by linarith⟩
    · intro i; fin_cases i <;> linarith
    · intro i; fin_cases i <;> linarith
  · rcases hx with ⟨hu,hu',hv,hv'⟩
    refine ⟨⟨?_,?_⟩,by linarith,by linarith,by linarith⟩
    · intro i; fin_cases i <;> linarith
    · intro i; fin_cases i <;> linarith
  · rcases hx with ⟨hu,huv,hv⟩
    refine ⟨⟨?_,?_⟩,by linarith,by linarith,by linarith⟩
    · intro i; fin_cases i <;> linarith
    · intro i; fin_cases i <;> linarith
  · rcases hx with ⟨hu,hu',hv,hv'⟩
    refine ⟨⟨?_,?_⟩,by linarith,by linarith,by linarith⟩
    · intro i; fin_cases i <;> linarith
    · intro i; fin_cases i <;> linarith

theorem pairHalf_in_cube {p : W2Parameters} (hp : W2Geometry p) (k : Fin 4) :
    pairHalf p k ⊆ cube 2 := by
  intro x hx
  have hg := (pairHalf_geometry hp k hx).1
  apply mem_logPrimeBox.mpr
  intro i
  constructor <;> linarith [hg.1 i,hg.2 i]

/-- The actual prime window, including its real lower endpoint and its
strict upper endpoint. The enumeration ceiling is removed exactly. -/
theorem primeWindow_eq_rough (N : ℕ) (lo hi : ℝ) :
    primeWindow N lo hi = roughPrimeFinset N (Nat.ceil hi) lo hi := by
  ext p
  rw [mem_primeWindow,mem_roughPrimeFinset_iff_of_cutoff_le_cap (Nat.le_ceil hi)]
  constructor
  · rintro ⟨hp,hN,hl,hh⟩
    exact ⟨hp,hp.coprime_iff_not_dvd.mp hN,hl,hh⟩
  · rintro ⟨hp,hN,hl,hh⟩
    exact ⟨hp,hp.coprime_iff_not_dvd.mpr hN,hl,hh⟩

def normalizedLog {d : ℕ} (N : ℕ) (L : ℝ) (p : Fin d → ℕ) : Coord d :=
  L⁻¹ • actualPrimeTupleLog N p

theorem normalizedLog_window {d N : ℕ} (hN : 1 < N) {L : ℝ} (hL : 0 < L)
    (p : Fin d → ℕ) (hp : ∀ i, 0 < p i) (i : Fin d) (lo hi : ℝ) :
    (lo ≤ normalizedLog N L p i ∧ normalizedLog N L p i < hi) ↔
      (N:ℝ)^(L*lo) ≤ p i ∧ (p i:ℝ) < (N:ℝ)^(L*hi) := by
  have hNR : (1:ℝ) < N := by exact_mod_cast hN
  have he : L * normalizedLog N L p i = actualPrimeTupleLog N p i := by
    simp [normalizedLog,Pi.smul_apply,smul_eq_mul,mul_assoc,hL.ne']
  rw [← actualPrimeTupleLog_rpow hN p hp i,
    Real.rpow_le_rpow_left_iff hNR,Real.rpow_lt_rpow_left_iff hNR,← he]
  exact and_congr (mul_le_mul_left hL).symm (mul_lt_mul_left hL).symm

/-- A literal half-open window is a filtered tuple carrier. There is no
new coprimality-to-prefix restriction. -/
theorem single_carrier_membership {N : ℕ} (hN : 1 < N) {L lo hi : ℝ}
    (hL : 0 < L) (hlo : (1/5:ℝ) ≤ lo) (hhi : hi ≤ 1/2) (p : Fin 1 → ℕ) :
    p ∈ (actualPrimeBoxTuples N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5)).filter
      (fun p => normalizedLog N L p ∈ singleHalf lo hi) ↔
        p 0 ∈ primeWindow N ((N:ℝ)^(L*lo)) ((N:ℝ)^(L*hi)) := by
  rw [Finset.mem_filter,mem_primeWindow]
  constructor
  · rintro ⟨hp,hx⟩
    have hh := mem_actualPrimeBoxTuples_iff.mp hp 0
    have hb := (normalizedLog_window hN hL p
      (fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos) 0 lo hi).mp hx
    exact ⟨hh.1,hh.1.coprime_iff_not_dvd.mpr hh.2.1,hb⟩
  · rintro ⟨hp,hpN,hloP,hhiP⟩
    have hpos : ∀ i : Fin 1, 0 < p i := by intro i; fin_cases i; exact hp.pos
    have hx : normalizedLog N L p ∈ singleHalf lo hi :=
      (normalizedLog_window hN hL p hpos 0 lo hi).mpr ⟨hloP,hhiP⟩
    refine ⟨mem_actualPrimeBoxTuples_iff.mpr (fun i => ?_),hx⟩
    fin_cases i
    have hb := (normalizedLog_window hN hL p hpos 0 (1/10) (3/5)).mp
      (show (1/10:ℝ) ≤ normalizedLog N L p 0 ∧ normalizedLog N L p 0 < 3/5 by
        constructor <;> linarith [hx.1,hx.2])
    refine ⟨hp,hp.coprime_iff_not_dvd.mp hpN,?_,?_⟩
    · convert hb.1 using 1 <;> congr 1 <;> ring
    · convert hb.2 using 1 <;> congr 1 <;> ring

theorem single_window_reindex {N : ℕ} (hN : 1 < N) {L lo hi : ℝ}
    (hL : 0 < L) (hlo : (1/5:ℝ) ≤ lo) (hhi : hi ≤ 1/2) (f : ℕ → ℝ) :
    (∑ p ∈ primeWindow N ((N:ℝ)^(L*lo)) ((N:ℝ)^(L*hi)),f p) =
      ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5),
        if normalizedLog N L p ∈ singleHalf lo hi then f (p 0) else 0 := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun p _ => p 0)
  · intro p hp
    exact (single_carrier_membership hN hL hlo hhi p).mp hp
  · intro p hp q hq heq
    funext i
    fin_cases i
    exact heq
  · intro p hp
    refine ⟨fun _ => p,?_,rfl⟩
    exact (single_carrier_membership hN hL hlo hhi (fun _ => p)).mpr hp
  · intro p hp
    rfl

theorem normalizedLog_rpow {k N : ℕ} (hN : 1 < N) {L : ℝ} (hL : 0 < L)
    (p : Fin k → ℕ) (hp : ∀ i, 0 < p i) (i : Fin k) :
    (N:ℝ)^(L*normalizedLog N L p i) = p i := by
  have he : L*normalizedLog N L p i = actualPrimeTupleLog N p i := by
    simp [normalizedLog,Pi.smul_apply,smul_eq_mul,mul_assoc,hL.ne']
  rw [he]
  exact actualPrimeTupleLog_rpow hN p hp i

theorem normalizedLog_order {N : ℕ} (hN : 1 < N) {L : ℝ} (hL : 0 < L)
    (p : Fin 2 → ℕ) (hp : ∀ i, 0 < p i) :
    normalizedLog N L p 0 < normalizedLog N L p 1 ↔ p 0 < p 1 := by
  have hNR : (1:ℝ) < N := by exact_mod_cast hN
  have hh := Real.rpow_lt_rpow_left_iff hNR
  rw [← mul_lt_mul_left hL,← Real.rpow_lt_rpow_left_iff hNR,
    normalizedLog_rpow hN hL p hp 0,normalizedLog_rpow hN hL p hp 1]
  exact Nat.cast_lt

theorem normalizedLog_window_prime {k N : ℕ} (hN : 1 < N) {L : ℝ} (hL : 0 < L)
    (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime ∧ ¬p i ∣ N) (i : Fin k) (lo hi : ℝ) :
    p i ∈ primeWindow N ((N:ℝ)^(L*lo)) ((N:ℝ)^(L*hi)) ↔
      lo ≤ normalizedLog N L p i ∧ normalizedLog N L p i < hi := by
  rw [mem_primeWindow]
  have hh := normalizedLog_window hN hL p (fun j => (hp j).1.pos) i lo hi
  exact ⟨fun h => hh.mpr h.2.2,
    fun h => ⟨(hp i).1,(hp i).1.coprime_iff_not_dvd.mpr (hp i).2,hh.mp h⟩⟩

def pairWindows (N : ℕ) (L : ℝ) (a : W2Parameters) (p : Fin 2 → ℕ) : Fin 4 → Prop
  | 0 => p 0 ∈ primeWindow N ((N:ℝ)^(L*a0 a)) ((N:ℝ)^(L*a2 a)) ∧
      p 1 ∈ primeWindow N ((N:ℝ)^(L*a0 a)) ((N:ℝ)^(L*a2 a))
  | 1 => p 0 ∈ primeWindow N ((N:ℝ)^(L*a0 a)) ((N:ℝ)^(L*a1 a)) ∧
      p 1 ∈ primeWindow N ((N:ℝ)^(L*a2 a)) ((N:ℝ)^(L*a3 a))
  | 2 => p 0 ∈ primeWindow N ((N:ℝ)^(L*a0 a)) ((N:ℝ)^(L*a1 a)) ∧
      p 1 ∈ primeWindow N ((N:ℝ)^(L*a0 a)) ((N:ℝ)^(L*a1 a))
  | 3 => p 0 ∈ primeWindow N ((N:ℝ)^(L*a0 a)) ((N:ℝ)^(L*a1 a)) ∧
      p 1 ∈ primeWindow N ((N:ℝ)^(L*a1 a)) ((N:ℝ)^(L*a2 a))

/-- The literal two-prime windows retain BOTH lower endpoint atoms.
The displayed strict selected-square gate is the original good-D5
gate; the second physical square is proved by pairHalf_geometry. -/
theorem pair_windows_membership {N : ℕ} (hN : 1 < N) {L : ℝ} (hL : 0 < L)
    {a : W2Parameters} (ha : W2Geometry a) (k : Fin 4) (p : Fin 2 → ℕ)
    (hp : ∀ i, (p i).Prime ∧ ¬p i ∣ N) :
    normalizedLog N L p ∈ pairHalf a k ↔
      pairWindows N L a p k ∧ p 0 < p 1 ∧
        2*normalizedLog N L p 0+normalizedLog N L p 1 < 1 := by
  have hw (i : Fin 2) (lo hi : ℝ) := normalizedLog_window_prime hN hL p hp i lo hi
  have ho := normalizedLog_order hN hL p (fun i => (hp i).1.pos)
  constructor
  · intro hx
    have hg := pairHalf_geometry ha k hx
    refine ⟨?_,?_,hg.2.2.2⟩
    · fin_cases k <;> simp only [pairWindows,hw]
      all_goals first
        | exact ⟨⟨hx.1,lt_trans hx.2.1 hx.2.2.1⟩,⟨le_trans hx.1 hx.2.1.le,hx.2.2.1⟩⟩
        | exact ⟨⟨hx.1,hx.2.1⟩,⟨hx.2.2.1,hx.2.2.2⟩⟩
        | exact ⟨⟨hx.1,lt_trans hx.2.1 hx.2.2⟩,⟨le_trans hx.1 hx.2.1.le,hx.2.2⟩⟩
    · apply ho.mp
      rcases ha with ⟨h0,h01,h12,h23,h3,hb,hg6,hg7,hg8⟩
      fin_cases k <;> first
        | exact hx.2.1
        | linarith [hx.2.1,hx.2.2.1]
  · rintro ⟨hwindows,horder,hgate⟩
    have horder' := ho.mpr horder
    fin_cases k <;> simp only [pairWindows,hw] at hwindows
    · exact ⟨hwindows.1.1,horder',hwindows.2.2,by linarith⟩
    · exact ⟨hwindows.1.1,hwindows.1.2,hwindows.2.1,hwindows.2.2⟩
    · exact ⟨hwindows.1.1,horder',hwindows.2.2⟩
    · exact ⟨hwindows.1.1,hwindows.1.2,hwindows.2.1,hwindows.2.2⟩

/-- Exact labelled insertion: equal products belonging to different
parent labels remain different occurrences. -/
theorem labelled_insertion {ι κ : Type*} (T : Finset ι) (S : ι → Finset κ)
    (sigma : ι → ℝ) (f : ι → κ → ℝ) :
    (∑ a ∈ T, sigma a * ∑ p ∈ S a, f a p) =
      ∑ ap ∈ T.sigma S, sigma ap.1 * f ap.1 ap.2 := by
  simp only [Finset.sum_sigma,Finset.mul_sum]

def profileSum {ι X : Type*} (T : Finset ι) (x : ι → X) (weight : ι → ℝ)
    (D : Set X) (lower : Bool) (nums : Fin 200 → ℤ) (rho : X → ℝ) : ℝ :=
  ∑ a ∈ T, D.indicator (fun y => tableFunction lower nums (rho y)) (x a) * weight a

def profileAtomSum {ι X : Type*} (T : Finset ι) (x : ι → X) (weight : ι → ℝ)
    (D : Set X) (lower : Bool) (rho : X → ℝ) (b : FloorAtom) : ℝ :=
  ∑ a ∈ T, (D ∩ tablePullback lower rho b).indicator (fun _ => weight a) (x a)

/-- All 401 atoms are finite ARITHMETIC atoms here, including the 201
possible knot atoms. No atom is deleted by a real null-set argument. -/
theorem profileSum_eq_atoms {ι X : Type*} (T : Finset ι) (x : ι → X)
    (weight : ι → ℝ) (D : Set X) (lower : Bool) (nums : Fin 200 → ℤ) (rho : X → ℝ) :
    profileSum T x weight D lower nums rho =
      ∑ b : FloorAtom, floorAtomValue nums b * profileAtomSum T x weight D lower rho b := by
  unfold profileSum profileAtomSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hx : x a ∈ D
  · rw [indicator_of_mem hx]
    unfold tableFunction
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : rho (x a) ∈ tableAtomSet lower b <;>
      simp [tablePullback,hx,hb,mul_comm]
  · simp [hx]

/-- Replacing a half-open carrier by its strict interior leaves THIS
explicit arithmetic endpoint sum, with the same profile and weight. -/
theorem profileSum_single_endpoint {ι : Type*} (T : Finset ι) (x : ι → Coord 1)
    (weight : ι → ℝ) (lo hi : ℝ) (lower : Bool) (nums : Fin 200 → ℤ)
    (rho : Coord 1 → ℝ) :
    profileSum T x weight (singleHalf lo hi) lower nums rho =
      profileSum T x weight (singleDomain lo hi) lower nums rho +
      profileSum T x weight {y | y 0 = lo ∧ y 0 < hi} lower nums rho := by
  unfold profileSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hs : x a ∈ singleDomain lo hi
  · have hh := (singleHalf_partition lo hi (x a)).mpr (Or.inl hs)
    have he : ¬ ((x a) 0 = lo ∧ (x a) 0 < hi) := by rintro ⟨h,_⟩; linarith [hs.1]
    simp [hh,hs,he]
  · by_cases he : (x a) 0 = lo ∧ (x a) 0 < hi
    · have hh := (singleHalf_partition lo hi (x a)).mpr (Or.inr he)
      simp [hh,hs,he]
    · have hh : x a ∉ singleHalf lo hi := by
        rw [singleHalf_partition]; exact not_or.mpr ⟨hs,he⟩
      simp [hh,hs,he]

theorem profileSum_pair_endpoint {ι : Type*} (T : Finset ι) (x : ι → Coord 2)
    (weight : ι → ℝ) (p : W2Parameters) (k : Fin 4) (lower : Bool)
    (nums : Fin 200 → ℤ) (rho : Coord 2 → ℝ) :
    profileSum T x weight (pairHalf p k) lower nums rho =
      profileSum T x weight (W2PairDomain p k) lower nums rho +
      profileSum T x weight (pairHalf p k ∩ pairLowerWall p k) lower nums rho := by
  unfold profileSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hp := pairHalf_partition p k (x a)
  have hd : ¬ (x a ∈ W2PairDomain p k ∧ x a ∈ pairLowerWall p k) := by
    fin_cases k <;>
      simp only [W2PairDomain,W2Pair5,W2Pair6,W2Pair7,W2Pair8,pairLowerWall,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.cons_val_three,mem_setOf_eq] <;>
      rintro ⟨h,hwall⟩ <;> first
        | (rcases hwall with hwall | hwall <;> linarith [h.1,h.2.2.1])
        | linarith [h.1]
  by_cases hs : x a ∈ W2PairDomain p k
  · have hh := hp.mpr (Or.inl hs)
    have hw : x a ∉ pairLowerWall p k := fun h => hd ⟨hs,h⟩
    simp [hh,hs,hw]
  · by_cases hh : x a ∈ pairHalf p k
    · have hw := (hp.mp hh).resolve_left hs
      simp [hh,hs,hw.2]
    · simp [hh,hs]

/-- The true alpha is independent of the scalar lookup. -/
theorem physical_single_mark {beta L u : ℝ} (hL : 0 < L) (hu : u < 1)
    (s0 : ℝ) :
    markedSingletonChild s0 (alpha beta L) u =
      (s0*(1-u),childAlpha beta L u) := by
  rw [childAlpha_eq hL.ne' (by linarith)]
  rfl

theorem physical_pair_mark {beta L : ℝ} (hL : 0 < L) (p : W2Parameters)
    (k : Fin 4) {x : Coord 2} (hx : x 0+x 1 < 1) :
    markedPairChild p k (alpha beta L) x =
      (pairProfile p k x,childAlpha beta L (x 0+x 1)) := by
  rw [pair_childAlpha hL.ne' (by linarith)]
  rfl

/-- The new primes obey the original physical ceiling on the half-open
carrier, including its lower endpoint. -/
theorem single_ceiling {L lo hi chi : ℝ} (hL : 0 < L) (hc : L*hi ≤ chi)
    {x : Coord 1} (hx : x ∈ singleHalf lo hi) : L*x 0 < chi :=
  (mul_lt_mul_of_pos_left hx.2 hL).trans_le hc

theorem pair_ceiling {p : W2Parameters} (hp : W2Geometry p) (k : Fin 4)
    {L chi : ℝ} (hL : 0 < L) (hc : L*a3 p ≤ chi)
    {x : Coord 2} (hx : x ∈ pairHalf p k) : L*x 0 < chi ∧ L*x 1 < chi := by
  rcases hp with ⟨h0,h01,h12,h23,h3,hb,hg6,hg7,hg8⟩
  have htop : x 0 < a3 p ∧ x 1 < a3 p := by
    fin_cases k
    · rcases hx with ⟨_,huv,hv,_⟩; constructor <;> linarith
    · rcases hx with ⟨_,hu,_,hv⟩; constructor <;> linarith
    · rcases hx with ⟨_,huv,hv⟩; constructor <;> linarith
    · rcases hx with ⟨_,hu,_,hv⟩; constructor <;> linarith
  exact ⟨(mul_lt_mul_of_pos_left htop.1 hL).trans_le hc,
    (mul_lt_mul_of_pos_left htop.2 hL).trans_le hc⟩

/-- Strict sifting is antitone in its physical cutoff, on the literal
receiver-filtered source count, at every finite target. -/
theorem frozenCount_antitone (N d : ℕ) (E : ℕ → Prop) {z w : ℝ} (hzw : z ≤ w) :
    P2FrozenReceiverCountActions.frozenCount N d E w ≤
      P2FrozenReceiverCountActions.frozenCount N d E z := by
  have h := P2FrozenReceiverCountActions.frozen_selected_buchstab N d E hzw
  have hs : 0 ≤ ∑ q ∈ primeWindow (d*N) z w,
      P2FrozenReceiverCountActions.frozenCount N (d*q) E (q:ℝ) := by
    apply Finset.sum_nonneg
    intro q _
    unfold P2FrozenReceiverCountActions.frozenCount
    positivity
  linarith

/-- Below two only cutoff comparison is used. It is a finite count
comparison, with no ordinary density theorem at the smaller argument. -/
theorem below_two_comparison (N d : ℕ) (E : ℕ → Prop) {R w v : ℝ}
    (hR : 1 ≤ R) (hw : 0 < w) (hwv : w ≤ v) :
    P2FrozenReceiverCountActions.frozenCount N d E (R^(1/w)) ≤
      P2FrozenReceiverCountActions.frozenCount N d E (R^(1/v)) := by
  apply frozenCount_antitone
  exact Real.rpow_le_rpow_of_exponent_le hR
    (one_div_le_one_div_of_le hw hwv)

/-- When the ordinary baselines differ, the FULL A(w)-A(v) correction
is retained. Any actual scalar licence at v belongs to the old analytic
count task; this theorem supplies only its exact finite comparison. -/
theorem below_two_defect_transfer (N d : ℕ) (E : ℕ → Prop) {R w v : ℝ}
    (hR : 1 ≤ R) (hw : 0 < w) (hwv : w ≤ v)
    (Theta Aw Av Hv err : ℝ)
    (hv : (P2FrozenReceiverCountActions.frozenCount N d E (R^(1/v)):ℝ) ≤
      Theta*(Av-Hv)+err) :
    (P2FrozenReceiverCountActions.frozenCount N d E (R^(1/w)):ℝ) ≤
      Theta*(Aw-(Hv+Aw-Av))+err := by
  have hmono :
      (P2FrozenReceiverCountActions.frozenCount N d E (R^(1/w)):ℝ) ≤
        P2FrozenReceiverCountActions.frozenCount N d E (R^(1/v)) := by
    exact_mod_cast below_two_comparison N d E hR hw hwv
  have he : Theta*(Aw-(Hv+Aw-Av))+err = Theta*(Av-Hv)+err := by ring
  rw [he]
  exact hmono.trans hv

end
end ImbalancedChen.P2OriginalHalfOpenProfileCarrier

