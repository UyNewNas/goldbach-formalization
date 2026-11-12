import ImbalancedChen.P4BOriginalMediumTriplePowers

/-! Exhaust the two remaining slots after the actual low first slot has
been placed in the middle group. -/
namespace ImbalancedChen.P4BOriginalMediumTripleAllocation
noncomputable section
open P4BUpperSelectedBoxCapacity (endpoint)
open P4BOriginalMediumTriplePowers

private theorem possibilities (H : ℕ→ℕ) (j k : ℕ) {x A : ℝ}
    (hx : 1<x) (hA : 0<A) (hj : 0<(H j:ℝ)) (hk : 0<(H k:ℝ)) :
    let ac := actualTwoCapacityGreedy (fun i => (H i:ℝ)) A [j,k]
    let f := power x (endpoint H ac.1)
    let r := power x (endpoint H ac.2)
    let b := power x (H j)
    let c := power x (H k)
    (f=b+c ∧ r=0) ∨ (f=b ∧ r=c ∧ power x A<b+c) ∨
      (f=c ∧ r=b ∧ power x A<b) ∨ (f=0 ∧ r=b+c ∧ power x A<c) := by
  dsimp only
  by_cases h1 : (H j:ℝ)≤A
  · by_cases h2 : (H j:ℝ)*(H k:ℝ)≤A
    · left
      simp [actualTwoCapacityGreedy,actualTwoCapacityStep,endpoint,h1,h2,power_mul hj hk,power_one]
    · right; left
      have h := lt_of_not_ge (fun hh => h2 ((positive_le_iff hx (mul_pos hj hk) hA).mpr hh))
      rw [power_mul hj hk] at h
      simp [actualTwoCapacityGreedy,actualTwoCapacityStep,endpoint,h1,h2,h]
  · have hb := lt_of_not_ge (fun hh => h1 ((positive_le_iff hx hj hA).mpr hh))
    by_cases h2 : (H k:ℝ)≤A
    · right; right; left
      simp [actualTwoCapacityGreedy,actualTwoCapacityStep,endpoint,h1,h2,hb]
    · right; right; right
      have hc := lt_of_not_ge (fun hh => h2 ((positive_le_iff hx hk hA).mpr hh))
      simp [actualTwoCapacityGreedy,actualTwoCapacityStep,endpoint,h1,h2,hc,power_mul hj hk,power_one]

theorem three_monomials (H : ℕ→ℕ) (i j k : ℕ) {x U eta n q1 q2 q3 : ℝ}
    (hx : 1<x) (hU : 0<U) (hu : power x U≤167/500)
    (he : eta≤1/20000) (hn : (7/32:ℝ)*n≤11/50)
    (hj : 0<(H j:ℝ)) (hk : 0<(H k:ℝ))
    (h0 : power x (H i)≤49/250) (h1 : power x (H j)≤49/250) (h2 : power x (H k)≤49/250)
    (h3 : power x (H i)+power x (H j)+3*power x (H k)≤3/5)
    (hQ : let ac := actualTwoCapacityGreedy (fun t => (H t:ℝ)) (U/x^eta) [j,k]
          q1≤power x (endpoint H ac.1) ∧ q2≤power x (H i) ∧
            q3≤eta/16+power x (endpoint H ac.2)) :
    2*power x U+q2+2*q3<1-8*(eta/2000) ∧
    (7/32:ℝ)*n+power x U+q1+5*q2+2*q3<2-15*(eta/2000) ∧
    (23/16:ℝ)*power x U+q1+(73/16:ℝ)*q2+(39/16:ℝ)*q3<2-15*(eta/2000) := by
  let A := U/x^eta
  let ac := actualTwoCapacityGreedy (fun t => (H t:ℝ)) A [j,k]
  let a := power x (H i)
  let b := power x (H j)
  let c := power x (H k)
  let f := power x (endpoint H ac.1)
  let r := power x (endpoint H ac.2)
  obtain ⟨hf,ha,hr⟩ : q1≤f ∧ q2≤a ∧ q3≤eta/16+r := hQ
  change a≤49/250 at h0
  change b≤49/250 at h1
  change c≤49/250 at h2
  change a+b+3*c≤3/5 at h3
  have hd : power x A=power x U-eta := cap_power hx hU
  have cases' : (f=b+c ∧ r=0) ∨ (f=b ∧ r=c ∧ power x A<b+c) ∨
      (f=c ∧ r=b ∧ power x A<b) ∨ (f=0 ∧ r=b+c ∧ power x A<c) :=
    possibilities H j k hx (div_pos hU (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _)) hj hk
  rcases cases' with ⟨hF,hR⟩|⟨hF,hR,hT⟩|⟨hF,hR,hT⟩|⟨hF,hR,hT⟩
  all_goals constructor
  all_goals first | constructor <;> linarith | linarith

end
end ImbalancedChen.P4BOriginalMediumTripleAllocation
