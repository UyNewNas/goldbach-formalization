import ImbalancedChen.P4AOrderedThirdSameCoefficient
import ImbalancedChen.ActualPrimeFineWordSlotRegrouping

namespace ImbalancedChen.P4AOrderedThirdPhysicalAtoms
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler
open P4AFull87TaggedAtomValue (admit occupied literal_value)
open P4AOriginalOrderedThirdActualCoefficient (keep)

def boxScalar (f : List ℕ → Bool) (N cap : ℕ) (w z tau : ℝ) (J : List ℕ) : ℝ :=
  if admit f (fun _ => []) N cap w z tau ([],J.map (fun j => (j:ℤ))) then 1 else 0

theorem prime_label {N p j : ℕ} (hN : 1<N) {tau : ℝ} (ht : 0<tau)
    (hp : p∈actualPrimeFineLabelFinset N tau j) : primeLabel N tau p=(j:ℤ) := by
  obtain ⟨hp',_,hl,hu⟩ := mem_actualPrimeFineLabelFinset.mp hp
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hlog := Real.log_pos hn
  have hpn : (0:ℝ)<p := by exact_mod_cast hp'.pos
  have hNpos := zero_lt_one.trans hn
  have hlo := Real.log_le_log (Real.rpow_pos_of_pos hNpos _) hl
  have hhi := Real.log_lt_log hpn hu
  rw [Real.log_rpow hNpos] at hlo hhi
  change ⌊(Real.log (p:ℝ)/Real.log (N:ℝ))/tau⌋=(j:ℤ)
  have ha : (j:ℝ)≤(Real.log (p:ℝ)/Real.log (N:ℝ))/tau := by
    rw [le_div_iff₀ ht,le_div_iff₀ hlog]
    linarith only [show (j:ℝ)*tau*Real.log (N:ℝ)=tau*j*Real.log (N:ℝ) by ring,hlo]
  have hb : (Real.log (p:ℝ)/Real.log (N:ℝ))/tau<(j:ℝ)+1 := by
    rw [div_lt_iff₀ ht,div_lt_iff₀ hlog]
    linarith only [show ((j:ℝ)+1)*tau*Real.log (N:ℝ)=tau*(j+1)*Real.log (N:ℝ) by ring,hhi]
  apply le_antisymm
  · have H : ⌊(Real.log (p:ℝ)/Real.log (N:ℝ))/tau⌋<(j:ℤ)+1 := Int.floor_lt.mpr (by exact_mod_cast hb)
    omega
  · exact Int.le_floor.mpr (by exact_mod_cast ha)

theorem sorted_label (N : ℕ) (hN : 1<N) (tau : ℝ) (ht : 0<tau) (J ps : List ℕ)
    (hp : ps∈actualPrimeSlotBox (actualPrimeFineLabelFinset N tau) J) (hs : ps.SortedGT) :
    primeWordLabel N tau ps.prod=J.map (fun j => (j:ℤ)) := by
  have primes := actualPrimeSlotBox_prime _ J (fun j _ p hp => (mem_actualPrimeFineLabelFinset.mp hp).1) ps hp
  have hperm := (Nat.primeFactorsList_unique (rfl : ps.prod=ps.prod) primes).trans (List.reverse_perm ps.prod.primeFactorsList).symm
  have hseq := hperm.eq_of_pairwise' (hs.pairwise.imp (fun h => h.le)) (Nat.primeFactorsList_sorted _).reverse.pairwise
  change ps.prod.primeFactorsList.reverse.map _=_
  rw [← hseq]
  clear hperm hseq primes hs
  induction J generalizing ps with
  | nil => simpa only [actualPrimeSlotBox,Finset.mem_singleton] using congrArg (List.map (primeLabel N tau))
        (show ps=[] by simpa [actualPrimeSlotBox] using hp)
  | cons j js ih =>
    obtain ⟨⟨p,qs⟩,hm,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨h0,h1⟩ := Finset.mem_product.mp hm
    simp only [List.map_cons,prime_label hN ht h0,ih _ h1]

theorem outside_scalar (f : List ℕ → Bool) (N cap : ℕ) (hN : 1<N) (w z tau : ℝ) (ht : 0<tau)
    (J : List ℕ) {d : ℕ} (hd : d∈((actualPrimeSlotBox (actualPrimeFineLabelFinset N tau) J).filter List.SortedGT).image List.prod) :
    coefficient f (fun _ => []) N cap w z tau d=
      boxScalar f N cap w z tau J*(ArithmeticFunction.moebius d:ℝ)*(if d∈universe N cap w z then 1 else 0) := by
  obtain ⟨ps,hp,rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hbox,hs⟩ := Finset.mem_filter.mp hp
  have hl := sorted_label N hN tau ht J ps hbox hs
  rw [literal_value]
  by_cases hm : ps.prod∈universe N cap w z <;> by_cases hb : admit f (fun _ => []) N cap w z tau ([],J.map (fun j => (j:ℤ))) <;>
    simp [occupied,boxScalar,label,hl,hm,hb]

theorem original_factorial (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ)
    (hN : 1<N) (tau : ℝ) (ht : 0<tau) (J : List ℕ) (hJ : J.Pairwise (· ≥ ·)) (H : ℕ → ℝ) :
    let f := keep r n e q a omega N
    let w := (N:ℝ)^omega
    let z := P4AOriginalFull87RawChronology.cutoff N
    let U := universe N N w z
    let B := actualPrimeSlotBox (actualPrimeFineLabelFinset N tau) J
    (boxScalar f N N w z tau J/(actualPrimeFineWordMultiplicity J:ℝ))*
      (∑ ps∈B,(ArithmeticFunction.moebius ps.prod:ℝ)*(if ps.prod∈U then 1 else 0)*H ps.prod)=
      ∑ d∈(B.filter List.SortedGT).image List.prod,coefficient f (fun _ => []) N N w z tau d*H d := by
  dsimp only
  let f := keep r n e q a omega N
  let w := (N:ℝ)^omega
  let z := P4AOriginalFull87RawChronology.cutoff N
  let U := universe N N w z
  have h := actualPrimeFineWord_original_scalar (by omega : 1≤N) ht.le J hJ 1
    (boxScalar f N N w z tau J) (fun d => (if d∈U then 1 else 0)*H d)
  simp only [one_mul,← mul_assoc] at h
  rw [h,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [outside_scalar f N N hN w z tau ht J hd]
  ring

end
end ImbalancedChen.P4AOrderedThirdPhysicalAtoms
