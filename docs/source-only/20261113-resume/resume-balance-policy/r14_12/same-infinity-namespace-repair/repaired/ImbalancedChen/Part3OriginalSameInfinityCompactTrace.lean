import ImbalancedChen.Part3OriginalSameInfinityCompactSpectrum

/-! The finite same-frame geometry is the same spatial Gram as the Maass
and native Eisenstein resolution. This identity is for genuine pairs of
compact height probes and retains the diagonal at every level. -/
namespace ImbalancedChen.Part3.OriginalSameInfinityCompactTrace20261113
noncomputable section
open Finset MeasureTheory Matrix
open scoped BigOperators MatrixGroups
open OriginalSameInfinityCompactSpectrum20261113 OriginalInfinitySwitchedGeometry20261113
open ActualInfinityCuspAnnihilator20261026b ActualContinuousPoincarePairing20261110 OriginalContinuousPoincarePackets20261110
open CompactCuspParabolicL220261025a CompactCuspParabolicPairing20261025a CompactCuspGeometricFubini20261025a
open ActualFullCuspEigenbasis20261026b ActualCuspBasisWhittakerCoefficients20261102 OriginalCuspidalPoincareTrace20261110
open OriginalContinuousCuspGram20261110 OriginalContinuousClassRemoval20261110
open private probe packetVector common_cutoff from ImbalancedChen.Part3OriginalInfinitySwitchedGeometry

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

private theorem positiveIndex (m : ℕ+) (n : ℕ) (h : n∈({m.val}:Finset ℕ)) : (n:ℤ)≠0 := by
  obtain rfl := mem_singleton.mp h
  exact_mod_cast m.property.ne'

private theorem singleton_vector (q m : ℕ+) (ψ : HeightSeed) :
    vector q.val {m.val} (fun _ => 1) (fun n => (n:ℤ)) (positiveIndex m) ψ = packetVector q m ψ := by
  let f := packet q.val false {m.val} (fun _ => 1) (fun n => (n:ℤ)) ψ.toFun
  have h := packet_L2 q.val false {m.val} (fun _ => 1) (fun n => (n:ℤ)) (positiveIndex m)
    ψ.toFun ψ.continuous ψ.compact ψ.positive
  let s := probe m ψ
  have h' := compactCuspPoincare_memLp_two q.val (m.val:ℤ) s.toFun s.continuous s.compact s.positive
  apply Lp.ext
  filter_upwards [h.coeFn_toLp,h'.coeFn_toLp] with u hu hv
  change (h.toLp f) u=(h'.toLp _) u
  rw [hu,hv]
  simp [f,packet,originalPoincare,s,probe]

def atom (q m : ℕ+) (ψ : HeightSeed) (i : actualCuspBasisIndex q.val (NeZero.pos q.val)) :=
  orderProbe 1 ψ.toFun (basisOrder q.val (NeZero.pos q.val) i)*
    basisR q.val (NeZero.pos q.val) i (1 : SL(2,ℤ)) (m.val:ℤ)

def eisenstein (q m n : ℕ+) (ψ φ : HeightSeed) (t : ℝ) :=
  nativeProduct q.val (fun a => radialProbe 1 φ.toFun t*ImbalancedChen.Part3.ActualContinuousClassFourier20261110.nativeR a false (n.val:ℤ) t)
    (fun a => radialProbe 1 ψ.toFun t*ImbalancedChen.Part3.ActualContinuousClassFourier20261110.nativeR a false (m.val:ℤ) t)

/-- Common support cutoff before q, untampered modulus condition q|k,
literal Fourier coefficients at infinity on both legs. -/
theorem same_infinity_compact_trace (m n : ℕ+) (ψ φ : HeightSeed) :
    ∃ C : ℕ+, ∀ q : ℕ+,
      Summable (fun i => atom q m ψ i*star (atom q n φ i)) ∧ Integrable (eisenstein q m n ψ φ) ∧
      (if (m.val:ℤ)=(n.val:ℤ) then ∫ y : ℝ, radialWeight (probe m ψ).toFun y*(probe n φ).toFun y else 0)+
        (∑ k ∈ Icc 1 C, if q.val ∣ k.val then orbital m n k ψ φ else 0) =
        (∑' i, atom q m ψ i*star (atom q n φ i))+(∫ t : ℝ,eisenstein q m n ψ φ t) := by
  obtain ⟨C,hC⟩ := common_cutoff m n ψ φ
  refine ⟨C,fun q => ?_⟩
  have B := compact_spectrum q.val {m.val} {n.val} (fun _ => 1) (fun _ => 1)
    (fun a => (a:ℤ)) (fun b => (b:ℤ)) (positiveIndex m) (positiveIndex n) ψ φ
  simp only [singleton_vector,discrete,continuousCoord,markedRow,sum_singleton,one_mul] at B
  refine ⟨B.1,B.2.1,?_⟩
  rw [←hC q,offDiagonal,add_comm,sub_add_cancel]
  exact B.2.2

end
end ImbalancedChen.Part3.OriginalSameInfinityCompactTrace20261113
