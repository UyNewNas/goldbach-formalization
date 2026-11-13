import ImbalancedChen.Part3OriginalSameInfinityScalarGeometry

/-! Reopen the common cutoff for the canonical full-modulus series.
The equality is independent of the cutoff chosen for each compact pair. -/
namespace ImbalancedChen.Part3.OriginalSameInfinityFullModulus20261113
noncomputable section
open Set Finset Complex Filter MeasureTheory
open scoped Topology BigOperators MatrixGroups
open OriginalSameInfinityScalarGeometry20261113 OriginalPositiveScalarGeometry20261112
open OriginalSameInfinityCompactSpectrum20261113 OriginalSameInfinityCompactTrace20261113
open OriginalInfinitySwitchedGeometry20261113 ActualInfinityCuspAnnihilator20261026b
open CompactCuspGeometricFubini20261025a CompactCuspParabolicPairing20261025a
open CompactCuspQuotientGeometricPairing20261025a CompactCuspFiniteGeometricIntegral20261025a
open ActualCompactBruhatKernel20261025a ActualCompactBruhatAllModuli20261025a
open OriginalSmoothPoissonTail OriginalContinuousPoincarePackets20261110
open private probe packetVector integral_at_modulus from ImbalancedChen.Part3OriginalInfinitySwitchedGeometry
open private native_diag from ImbalancedChen.Part3OriginalSameInfinityScalarGeometry
open private positiveIndex singleton_vector from ImbalancedChen.Part3OriginalSameInfinityCompactTrace

local instance (k : ℕ+) : NeZero k.val := ⟨k.property.ne'⟩

private theorem all_moduli (q m n : ℕ+) (ψ φ : HeightSeed) :
    HasSum (fun k : ℕ+ => if q.val∣k.val then orbital m n k ψ φ else 0) (offDiagonal q m n ψ φ) := by
  let u := probe m ψ
  let w := probe n φ
  obtain ⟨a,ha,hfa⟩ := radial_support_positive_floor w.toFun w.compact w.positive
  obtain ⟨b,hb,hfb⟩ := radial_support_positive_floor u.toFun u.compact u.positive
  obtain ⟨C,hC⟩ := exists_positive_modulus_cutoff a b ha hb
  let f (k : ℕ+) := if q.val∣k.val then orbital m n k ψ φ else 0
  have small (k : ℕ+) (hk : k∉Icc 1 C) : f k=0 := by
    have high : C<k := lt_of_not_ge (fun h => hk (mem_Icc.mpr ⟨k.property,h⟩))
    by_cases good : q.val∣k.val
    · rw [f,if_pos good,orbital,←integral_at_modulus]
      have zero (x y : ℝ) : geometricPairKernel (k.val:ℝ) (m.val:ℤ) (n.val:ℤ) u.toFun w.toFun (x,y)=0 := by
        by_cases nz : u.toFun y=0
        · simp [geometricPairKernel,radialWeight,nz]
        · have by' := hfb y nz
          have yp := hb.trans_le by'
          have hlarge := large_modulus_of_cutoff a y ha yp C k
            ((one_div_le_one_div_of_le (mul_pos ha hb) (mul_le_mul_of_nonneg_left by' ha.le)).trans_lt hC) high
          have kn : (k.val:ℝ)≠0 := by exact_mod_cast k.property.ne'
          rw [geometricPairKernel,rawBruhatKernel_eq_actual _ kn _ _ y yp x,
            actualKernel_zero_of_large_modulus _ kn y yp _ w.toFun a ha hfa hlarge x,mul_zero]
      simp only [show ∀ x y : ℝ,geometricPairKernel (k.val:ℝ) (m.val:ℤ) (n.val:ℤ)
        (probe m ψ).toFun (probe n φ).toFun (x,y)=0 from zero,integral_zero,mul_zero]
    · simp [f,good]
  have val : (∑ k ∈ Icc 1 C,f k)=offDiagonal q m n ψ φ := by
    have A := compactCuspPoincareL2_inner_unfolding q.val (m.val:ℤ) (n.val:ℤ) u.toFun w.toFun
      u.continuous u.compact u.positive w.continuous w.compact w.positive
    have B := compactCusp_strip_pairing_eq_weightedFourier q.val (m.val:ℤ) (n.val:ℤ) u.toFun w.toFun
      u.continuous u.compact u.positive w.continuous w.compact w.positive
    have G := integrated_actualFourier_eq_finite_geometric q.val (m.val:ℤ) (n.val:ℤ)
      u.toFun w.toFun u.continuous u.compact u.positive w.continuous w.compact w.positive a b ha hb hfa hfb C hC
    change _ = inner ℂ (packetVector q m ψ) (packetVector q n φ) -
      (if (m.val:ℤ)=(n.val:ℤ) then ∫ y : ℝ,radialWeight u.toFun y*w.toFun y else 0)
    rw [A.trans (B.trans G),add_sub_cancel_left]
    apply sum_congr rfl
    intro k _
    by_cases good : q.val∣k.val
    · simp only [f,if_pos good,orbital,←integral_at_modulus]
    · simp [f,good]
  rw [←val]
  exact hasSum_sum_of_ne_finset_zero small

/-- Conjugate-first pretrace with the physical full modulus sum. This
form can be summed over the nuclear tensor of the two compact probes. -/
theorem full_rank_one_trace (q m n : ℕ+) (ψ φ : HeightSeed) :
    let P := fun a b => ψ.toFun a*star (φ.toFun b)
    Summable (term (induced P) q m n) ∧
    diagonal P 1 m.val (n.val:ℤ)+(∑' k,term (induced P) q m n k)=
        star ((∑' i,atom q m ψ i*star (atom q n φ i))+(∫ t,eisenstein q m n ψ φ t)) := by
  have S := (all_moduli q m n ψ φ).star
  have E := S.congr_fun (fun k => rank_one_term q m n k ψ φ)
  refine ⟨E.summable,?_⟩
  rw [E.tsum_eq,native_diag,←star_add,offDiagonal]
  apply congrArg (star : ℂ→ℂ)
  rw [add_comm,sub_add_cancel]
  have B := compact_spectrum q.val {m.val} {n.val} (fun _ => 1) (fun _ => 1)
    (fun a => (a:ℤ)) (fun b => (b:ℤ)) (positiveIndex m) (positiveIndex n) ψ φ
  simpa only [singleton_vector,discrete,continuousCoord,OriginalContinuousClassRemoval20261110.markedRow,
    sum_singleton,one_mul] using B.2.2

end
end ImbalancedChen.Part3.OriginalSameInfinityFullModulus20261113
