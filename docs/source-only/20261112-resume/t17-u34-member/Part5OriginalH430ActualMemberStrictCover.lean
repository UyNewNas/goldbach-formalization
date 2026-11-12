import ImbalancedChen.Part5OriginalH430StrictSeedCeiling
import ImbalancedChen.Part5OriginalH430RootSourceDictionary

/-! Pointwise strict analytical cover for every emitted enhanced Member.
The right endpoint v(log_N p) cannot be a rational frozen mesh value:
N and the actual selected prime p are coprime. Two intermediate levels
strictify the complete old square lists without changing physical Q.
This produces no uniform-in-N margin and no distribution estimate. -/
namespace ImbalancedChen.Part5OriginalH430ActualMemberStrictCover
noncomputable section
open scoped Classical BigOperators
open P2EnhancedLowerPhysicalNode P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RootSourceDictionary Part5OriginalH430StrictSeedCeiling

private theorem physical_prime_no_rational {N p : ℕ} (hN : 1 < N)
    (hp : p.Prime) (hc : p.Coprime N) (m b : ℕ) (hb : 0 < b) :
    physicalPrime N p * (b:ℝ) ≠ (m:ℝ) := by
  intro h
  have hrec : (N:ℝ)^physicalPrime N p = (p:ℝ) :=
    actualPrimeTupleLog_rpow hN ![p] (fun i => by fin_cases i; exact hp.pos) 0
  have he : (p:ℝ)^b = (N:ℝ)^m := by
    calc
      (p:ℝ)^b = (N:ℝ)^(physicalPrime N p * (b:ℝ)) := by
        rw [Real.rpow_mul (Nat.cast_nonneg N),Real.rpow_natCast,hrec]
      _ = (N:ℝ)^m := by rw [h,Real.rpow_natCast]
  have hn : p^b = N^m := by exact_mod_cast he
  have hd : p ∣ p^b := by
    cases b with
    | zero => omega
    | succ b => exact ⟨p^b,by rw [pow_succ,Nat.mul_comm]⟩
  rw [hn] at hd
  exact (hp.coprime_iff_not_dvd.mp hc) (hp.dvd_of_dvd_pow hd)

/-- Both active lines of v have nonzero rational slope. Their values
at this original p cannot equal *any* cumulative frozen-level endpoint. -/
theorem enhanced_root_has_buffer {N n p : ℕ} {k : Root} {t : ℝ}
    (hN : 2 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12)
    (hp : p ∈ originalBand N k)
    (he : rootSource k (physicalPrime N p) = .enhanced) :
    (frozenRoot n k t (physicalPrime N p)).physical.total < VariableEnvelope.v (physicalPrime N p) := by
  let x := physicalPrime N p
  have hband := original_band_geometry hN hp
  have hprime := original_band_prime hp
  have hx : 0 < x := Part5OriginalH430PrimeChildAdmission.physicalPrime_pos
    (by omega : 1<N) hprime.1
  have hroot := enhanced_root_total (tau := t) he
  change frozenLevel n (sourceRoot k t x).physical.total < VariableEnvelope.v x
  have hle := (frozenLevel_bounds (root_total_bounds ht hu hband) n).1
  rw [hroot] at hle ⊢
  apply lt_of_le_of_ne hle
  intro eq
  obtain ⟨u,b,hb,hr⟩ := frozen_level_rational n (VariableEnvelope.v x)
  have hbr : 0 < (b:ℝ) := Nat.cast_pos.mpr hb
  have hv : VariableEnvelope.v x * (b:ℝ) = u := by
    rw [← eq,hr,div_mul_cancel₀ _ hbr.ne']
  rw [VariableEnvelope.v_eq_min] at hv
  by_cases hac : VariableEnvelope.A x ≤ VariableEnvelope.C x
  · rw [min_eq_left hac] at hv
    dsimp [VariableEnvelope.A] at hv
    have hle' : (b:ℝ) ≤ 2*(u:ℝ) := by nlinarith [mul_pos hx hbr]
    have hnat : b ≤ 2*u := by exact_mod_cast hle'
    apply physical_prime_no_rational (by omega : 1<N) hprime.1 hprime.2 (2*u-b) b hb
    change x*(b:ℝ) = _
    rw [Nat.cast_sub hnat,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith
  · rw [min_eq_right (le_of_not_ge hac)] at hv
    dsimp [VariableEnvelope.C] at hv
    have hle' : 64*(u:ℝ) ≤ 57*(b:ℝ) := by nlinarith [mul_pos hx hbr]
    have hnat : 64*u ≤ 57*b := by exact_mod_cast hle'
    apply physical_prime_no_rational (by omega : 1<N) hprime.1 hprime.2 (57*b-64*u)
      (96*b) (Nat.mul_pos (by decide) hb)
    change x*((96*b:ℕ):ℝ) = _
    rw [Nat.cast_sub hnat]
    push_cast
    nlinarith

/-- Strict counterpart of the actual complete list, with the same root or
selected-product starting exponent T and every remaining slot in order. -/
def strictSquares (nu T : ℝ) : List ℝ → Prop
  | [] => True
  | x::xs => T+2*x < nu ∧ strictSquares nu (T+x) xs

private theorem strictify {a b : ℝ} (h : a < b) (xs : List ℝ) (T : ℝ)
    (hs : SquareGates a T xs) : strictSquares b T xs := by
  induction xs generalizing T with
  | nil => trivial
  | cons x xs ih => exact ⟨hs.1.trans_lt h, ih (T+x) hs.2⟩

/-- Both strict lists on this ACTUAL occurrence at a common auxiliary
cover strictly inside the original tent. No full square is required at
the smaller frozen physical level. Q is still the initial frozen Q. -/
theorem enhanced_actual_member_strict_cover {N n p : ℕ} {k : Root} {t : ℝ}
    {o : Occurrence N} (hN : 2 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ originalBand N k)
    (he : rootSource k (physicalPrime N p) = .enhanced)
    (ho : o ∈ rootHistory N n k t p) :
    let x := physicalPrime N p
    let L := (frozenRoot n k t x).physical.total
    let A := (bufferedRootCover x L + VariableEnvelope.v x)/2
    L < A ∧ A < VariableEnvelope.v x ∧
      strictSquares A 0 (word o.current.node.physical) ∧
      strictSquares A (selectedWord o.current.node.physical.slots).sum
        (remainingWord o.current.node.physical.slots) ∧
      (N:ℝ)^o.current.node.physical.total = rootQ N n k t p := by
  dsimp only
  have hband := original_band_geometry hN hp
  have hmem := rootHistory_member 0 (by omega : 1<N) ht hu hn (original_band_prime hp) hband ho
  have hstrict := enhanced_root_has_buffer (n := n) hN ht hu hp he
  have hcov := enhanced_frozen_descendant_buffered_cover he hband hstrict hmem
  dsimp only at hcov
  have hid := (rootHistory_realization 0 ho).1
  have hg := hcov.2.2
  change coverGates _ (historyNode N n k t p (pathCode 0 o.path)
      (pathPrimes o.path)).physical at hg
  rw [hid] at hg
  have hl := hcov.1
  have hr := hcov.2.1
  refine ⟨by linarith only [hl,hr],by linarith only [hr],?_,?_,rootHistory_sameQ ho⟩
  · exact strictify (by linarith only [hr]) _ _ hg.1
  · exact strictify (by linarith only [hr]) _ _ hg.2

end
end ImbalancedChen.Part5OriginalH430ActualMemberStrictCover
