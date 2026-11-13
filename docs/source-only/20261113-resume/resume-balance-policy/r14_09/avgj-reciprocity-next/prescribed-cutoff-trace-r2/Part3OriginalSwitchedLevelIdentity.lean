import ImbalancedChen.Part3OriginalSwitchedPrescribedTrace

/-! Swap the two physical positive divisors on the prescribed
same-infinity trace. Both occurrences of the full spectra are retained. -/
namespace ImbalancedChen.Part3.OriginalSwitchedLevelIdentity20261113
noncomputable section
open Finset Set Complex
open scoped BigOperators
open OriginalSwitchedCutoffFamily20261113 (profile)
open OriginalSwitchedPrescribedTrace20261113 (same_infinity_cutoff_trace)
open OriginalSwitchedMaassExchange20261113 (mass)
open OriginalSameInfinityWeightedHol20261113 (holSum)
open OriginalSwitchedExceptionalTransform20261113 (switchedTest)
open OriginalSameInfinityScalarGeometry20261113 (term)
open OriginalInfinitySwitchedGeometry20261113 (argument)
open OriginalSmoothPoissonTail (kloosterman) CommonSmoothCutoff (dyadicCutoff)
open private reindex_multiples from ImbalancedChen.Part3OriginalInfinitySwitchedGeometry

def spectral (q m n : ℕ+) (Φ : ℝ→ℂ) := mass q m n Φ+holSum q m n Φ
def single (Y : ℝ) (x : ℝ) : ℂ := dyadicCutoff (Y*x)
def levelWeight (Q : ℝ) (q : ℕ+) : ℂ := dyadicCutoff ((q.val:ℝ)/Q)

private theorem cut_eq (m n d : ℕ+) {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q) :
    (fun x => profile true (Y*(4*Real.pi*Real.sqrt ((m.val:ℝ)*(n.val:ℝ)))/((d.val:ℝ)*Q)) (Y*x))=
      switchedTest Y ((d.val:ℝ)*Q) m.val n.val := by
  funext x
  have p : (d.val:ℝ)≠0 := by exact_mod_cast d.property.ne'
  have E : (Y*(4*Real.pi*Real.sqrt ((m.val:ℝ)*(n.val:ℝ)))/((d.val:ℝ)*Q))/(Y*x)=
      4*Real.pi*Real.sqrt ((m.val:ℝ)*(n.val:ℝ))/(((d.val:ℝ)*Q)*x) := by
    by_cases z : x=0
    · simp [z]
    · field_simp [yp.ne',qp.ne',p,z] <;> ring
  simp only [profile,ite_true,switchedTest,E]

private def orbit (Φ : ℝ→ℂ) (m n k : ℕ+) :=
  (kloosterman k.val (m.val:ℤ) (n.val:ℤ)/(k.val:ℂ))*Φ (argument m n k)

/-- Same-infinity trace applied twice. The finite range is picked from
the first bump's support at the actual marks, before the level scale Q.
It permits all q and d that contribute to the two full sums. -/
theorem level_switch (m n : ℕ+) {Y : ℝ} (yp : 0<Y) :
    ∃ C : ℕ+,∀ Q : ℝ,0<Q →
    (∀ k∉Finset.Icc 1 C,spectral k m n (single Y)=0 ∧
      spectral k m n (switchedTest Y ((k.val:ℝ)*Q) m.val n.val)=0) ∧
    (∑' q : ℕ+,levelWeight Q q*spectral q m n (single Y))=
      ∑' d : ℕ+,spectral d m n (switchedTest Y ((d.val:ℝ)*Q) m.val n.val) := by
  classical
  let A := 4*Real.pi*Real.sqrt ((m.val:ℝ)*(n.val:ℝ))
  have ap : 0<A := by dsimp [A];positivity
  obtain ⟨T,t⟩ := exists_nat_gt (2*Y*A)
  let C : ℕ+ := ⟨T+1,Nat.succ_pos _⟩
  let S := Finset.Icc (1:ℕ+) C
  have zero (k : ℕ+) (hk : k∉S) : single Y (argument m n k)=0 := by
    by_contra nz
    have lo := (CommonSmoothCutoff.dyadicCutoff_tsupport_subset (subset_tsupport _
      (show dyadicCutoff (Y*argument m n k)≠0 from fun h => nz (by simp [single,h])))).1
    have kp : 0<(k.val:ℝ) := by exact_mod_cast k.property
    change 1/2 ≤ Y*(A/(k.val:ℝ)) at lo
    have h := (le_div_iff₀ kp).mp (show 1/2≤Y*A/(k.val:ℝ) by linarith only [lo,show Y*A/(k.val:ℝ)=Y*(A/(k.val:ℝ)) by ring])
    have lt : (k.val:ℝ)<T := by linarith only [h,t]
    have h' : k.val<T := by exact_mod_cast lt
    have le : k.val≤T+1 := by omega
    exact hk (Finset.mem_Icc.mpr ⟨k.property,le⟩)
  refine ⟨C,fun Q qp => ?_⟩
  let w := fun d : ℕ+ => switchedTest Y ((d.val:ℝ)*Q) m.val n.val
  have first (q : ℕ+) : spectral q m n (single Y)=
      ∑ d ∈ S,if q*d≤C then orbit (single Y) m n (q*d) else 0 := by
    have X := (same_infinity_cutoff_trace q m n false 0 Y yp).2.symm
    simp only [profile,Bool.false_eq_true,ite_false,mul_one] at X
    have a : (∑' k : ℕ+,term (single Y) q m n k)=∑ k ∈ S,term (single Y) q m n k :=
      tsum_eq_sum (fun k hk => by simp [term,zero k hk])
    exact X.trans (a.trans (reindex_multiples C q (orbit (single Y) m n)))
  have second (d : ℕ+) : spectral d m n (w d)=
      ∑ q ∈ S,if d*q≤C then orbit (w d) m n (d*q) else 0 := by
    have X := (same_infinity_cutoff_trace d m n true (Y*A/((d.val:ℝ)*Q)) Y yp).2.symm
    rw [show (fun x => profile true (Y*A/((d.val:ℝ)*Q)) (Y*x))=w d from cut_eq m n d yp qp] at X
    have a : (∑' k : ℕ+,term (w d) d m n k)=∑ k ∈ S,term (w d) d m n k := by
      apply tsum_eq_sum
      intro k hk
      have z : w d (argument m n k)=0 := by
        change single Y (argument m n k)*_=0
        rw [zero k hk,zero_mul]
      simp [term,z]
    exact X.trans (a.trans (reindex_multiples C d (orbit (w d) m n)))
  have outside (k : ℕ+) (hk : k∉S) : spectral k m n (single Y)=0 ∧ spectral k m n (w k)=0 := by
    have cut (u : ℕ+) : ¬k*u≤C := by
      intro le
      have km : k.val≤(k*u).val := by simpa only [PNat.coe_mul,Nat.mul_one] using Nat.mul_le_mul_left k.val u.property
      exact hk (Finset.mem_Icc.mpr ⟨k.property,km.trans le⟩)
    simp only [first,second,if_neg (cut _),Finset.sum_const_zero,and_self]
  refine ⟨outside,?_⟩
  rw [tsum_eq_sum (s:=S) (fun k hk => by rw [(outside k hk).1,mul_zero]),
    tsum_eq_sum (s:=S) (fun k hk => (outside k hk).2)]
  change (∑ q ∈ S,_)=∑ d ∈ S,_
  simp_rw [first,second,Finset.mul_sum]
  rw [Finset.sum_comm (s:=S) (t:=S)]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro q _
  rw [mul_comm d q]
  by_cases h : q*d≤C
  · simp only [if_pos h,orbit,w,switchedTest,single,levelWeight]
    have arg : A/(((d.val:ℝ)*Q)*argument m n (q*d))=(q.val:ℝ)/Q := by
      change A/(((d.val:ℝ)*Q)*(A/((q*d).val:ℝ)))=_
      rw [PNat.coe_mul,Nat.cast_mul]
      field_simp [qp.ne',ap.ne',show (q.val:ℝ)≠0 by exact_mod_cast q.property.ne',
        show (d.val:ℝ)≠0 by exact_mod_cast d.property.ne'] <;> ring
    change _=_*((dyadicCutoff (Y*argument m n (q*d)):ℂ)*(dyadicCutoff (A/(((d.val:ℝ)*Q)*argument m n (q*d))):ℂ))
    rw [arg]
    ring
  · simp [h]

end
end ImbalancedChen.Part3.OriginalSwitchedLevelIdentity20261113
