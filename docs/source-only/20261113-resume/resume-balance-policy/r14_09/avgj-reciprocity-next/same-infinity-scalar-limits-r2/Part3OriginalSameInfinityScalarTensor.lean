import ImbalancedChen.Part3OriginalSameInfinityFullModulus
import ImbalancedChen.Part3OriginalPositiveCompactPretrace

/-! The scalar two-height packet against the full progression of
same-infinity moduli and the actual two compact spectral coordinates. -/
namespace ImbalancedChen.Part3.OriginalSameInfinityScalarTensor20261113
noncomputable section
open Set Finset MeasureTheory Complex
open scoped Topology BigOperators
open OriginalSameInfinityScalarGeometry20261113 OriginalSameInfinityFullModulus20261113
open OriginalSameInfinityCompactTrace20261113 OriginalPositiveScalarGeometry20261112
open RadialSchrodingerL2Form20261025a OriginalPositiveHeightTest20261112
open ActualPositiveTensorIntegral20261112 ActualPositiveTensorGeometry20261112
open PrescribedLogTensorCoefficients20261112 (Modes)
open PrescribedLogTensorWindows20261112 PrescribedLogTensorExpansion20261112 (productAt)
open ActualInfinityCuspAnnihilator20261026b
open OriginalOppositeMarkedKuznetsov20261112 (modulusTerm)
open private scale scale_pos from ImbalancedChen.Part3OriginalPositiveOrbitModuli

def pair (q m n : ℕ+) (G : ℝ→ℝ→ℂ) :=
  diagonal G 1 m.val (n.val:ℤ)+∑' k : ℕ+,term (induced G) q m n k

private theorem sum_moduli (η H : RadialTest) (R : ℝ) (q m n : ℕ+) :
    HasSum (fun v : Modes => coeff η H R v*∑' k : ℕ+,term (induced (productAt v)) q m n k)
      (∑' k : ℕ+,term (induced (height η H R)) q m n k) := by
  classical
  obtain ⟨δ,dp,cut⟩ := small η H R
  let A := scale m.val (n.val:ℤ)
  have ap : 0<A := scale_pos m.property (by exact_mod_cast n.property : (0:ℤ)<n.val)
  obtain ⟨T,t⟩ := exists_nat_gt (A/δ)
  let U := Icc (1:ℕ+) (⟨T+1,Nat.succ_pos _⟩:ℕ+)
  have arg (k : ℕ+) : OriginalInfinitySwitchedGeometry20261113.argument m n k=A/(k.val:ℝ) := by
    simp [OriginalInfinitySwitchedGeometry20261113.argument,A,scale]
  have outside (k : ℕ+) (h : k∉U) : A/(k.val:ℝ)<δ := by
    have gt : T<k.val := by
      by_contra! le
      exact h (mem_Icc.mpr ⟨k.property,le.trans (Nat.le_succ _)⟩)
    have kp : (0:ℝ)<k.val := by exact_mod_cast k.property
    have Ak := (div_lt_iff₀ dp).mp (t.trans (by exact_mod_cast gt : (T:ℝ)<k.val))
    exact (div_lt_iff₀ kp).mpr (by simpa only [mul_comm δ (k.val:ℝ)] using Ak)
  have zeroA (k : ℕ+) (hk : k∉U) := cut (A/(k.val:ℝ)) (div_pos ap (by exact_mod_cast k.property))
    (outside k hk)
  have eq (v : Modes) : coeff η H R v*(∑' k : ℕ+,term (induced (productAt v)) q m n k)=
      ∑ k ∈ U,coeff η H R v*term (induced (productAt v)) q m n k := by
    rw [←tsum_mul_left]
    apply tsum_eq_sum
    intro k hk
    unfold term
    split_ifs
    · rw [arg,mul_left_comm,(zeroA k hk).1 v,mul_zero]
    · rw [mul_zero]
  have eh : (∑' k : ℕ+,term (induced (height η H R)) q m n k)=
      ∑ k ∈ U,term (induced (height η H R)) q m n k := by
    apply tsum_eq_sum
    intro k hk
    simp [term,arg,(zeroA k hk).2]
  rw [eh]
  simp_rw [eq]
  apply hasSum_sum
  intro k _
  unfold term
  by_cases good : q.val∣k.val
  · simp only [if_pos good]
    exact ((orbit η H R (OriginalInfinitySwitchedGeometry20261113.argument m n k)).mul_left
      (OriginalSmoothPoissonTail.kloosterman k.val (m.val:ℤ) (n.val:ℤ)/(k.val:ℂ))).congr_fun
        (fun v => by ring)
  · simp [good]

def left (v : Modes) : HeightSeed :=
  let h := pattern_test v.1.1 v.2.1
  ⟨pattern v.1.1 v.2.1,h.1,h.2.1,h.2.2⟩
def right (v : Modes) : HeightSeed :=
  let h := right_test v.1.2 v.2.2
  ⟨rightPattern v.1.2 v.2.2,h.1,h.2.1,h.2.2⟩

/-- Nuclear sum through the actual scalar tensor on the geometric
side. The right side is a single sum over the true q|k sequence. -/
theorem scalar_tensor (η H : RadialTest) (R : ℝ) (q m n : ℕ+) :
    HasSum (fun v : Modes => coeff η H R v*star
      ((∑' i,atom q m (left v) i*star (atom q n (right v) i))+
        (∫ t,eisenstein q m n (left v) (right v) t)))
      (pair q m n (height η H R)) := by
  have S := (diagonal_sum η H R 1 m.val (n.val:ℤ)).add (sum_moduli η H R q m n)
  apply S.congr_fun
  intro v
  rw [←(full_rank_one_trace q m n (left v) (right v)).2,mul_add]
  rfl

end
end ImbalancedChen.Part3.OriginalSameInfinityScalarTensor20261113
