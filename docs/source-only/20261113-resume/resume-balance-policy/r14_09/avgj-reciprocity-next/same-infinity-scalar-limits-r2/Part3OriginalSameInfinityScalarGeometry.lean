import ImbalancedChen.Part3OriginalSameInfinityCompactTrace
import ImbalancedChen.Part3OriginalPositiveOrbitModuli
import ImbalancedChen.Part3KloostermanConjugation
import Batteries.Tactic.OpenPrivate

/-! Same-frame transfer of the scalar induced orbital test. Only the
arithmetic moduli and the diagonal depend on the observations. -/
namespace ImbalancedChen.Part3.OriginalSameInfinityScalarGeometry20261113
noncomputable section
open Set Filter MeasureTheory Complex Finset
open scoped Topology BigOperators
open OriginalInfinitySwitchedGeometry20261113 OriginalSameInfinityCompactTrace20261113
open ActualInfinityCuspAnnihilator20261026b CompactCuspGeometricFubini20261025a
open ActualMarkedGeometricSeries20261112 ActualCuspOneGeometricPairing20261112
open OriginalContinuousPoincarePackets20261110 OriginalPositiveScalarGeometry20261112
open OriginalNonzeroCuspOneSource20261102 OriginalSignedTraceInput20261102
open OriginalSmoothPoissonTail OriginalOppositeMarkedKuznetsov20261112
open P3Period64NativeReconstructionSourceOnly (e)
open private probe from ImbalancedChen.Part3OriginalInfinitySwitchedGeometry

local instance (k : ℕ+) : NeZero k.val := ⟨k.property.ne'⟩

def term (Φ : ℝ→ℂ) (q m n k : ℕ+) : ℂ :=
  if q.val∣k.val then (kloosterman k.val (m.val:ℤ) (n.val:ℤ)/(k.val:ℂ))*
    Φ (argument m n k) else 0

private theorem one_sum (m n k : ℕ+) (h : Nat.Coprime 1 k.val) :
    cuspOneMatrixSum 1 k.val h (m.val:ℤ) (n.val:ℤ)=kloosterman k.val (m.val:ℤ) (n.val:ℤ) := by
  rw [cuspOneMatrixSum_eq_phase_mul_kloosterman 1 k.val (by decide) h]
  have phase : e ((n.val:ℤ):ℝ)=1 := by
    unfold e
    rw [mul_comm _ ((((n.val:ℤ):ℝ):ℂ))]
    simpa using Complex.exp_nat_mul_two_pi_mul_I n.val
  simp only [Nat.cast_one,div_one,phase,one_mul]
  rw [Physical.kloosterman_eq_zmod,Physical.kloosterman_eq_zmod]
  simp [inverseResidue]

/-- The level-one comparison supplies only a majorant for each classical
Kloosterman summand. The genuine level q remains in the divisibility gate. -/
theorem term_filter (Φ : ℝ→ℂ) (q m n k : ℕ+) :
    term Φ q m n k=if q.val∣k.val then modulusTerm Φ 1 m.val (n.val:ℤ) k else 0 := by
  have cop : Nat.Coprime 1 k.val := Nat.coprime_one_left _
  simp [term,modulusTerm,cop,one_sum,traceModulus,argument]

private theorem native_diag (m n : ℕ+) (ψ φ : HeightSeed) :
    diagonal (fun a b => ψ.toFun a*star (φ.toFun b)) 1 m.val (n.val:ℤ)=
      star (if (m.val:ℤ)=(n.val:ℤ) then
        ∫ y : ℝ,radialWeight (probe m ψ).toFun y*(probe n φ).toFun y else 0) := by
  rw [diagonal_rank_one ψ.toFun φ.toFun ψ.positive 1 m.val m.property (n.val:ℤ)]
  have ph : e ((n.val:ℝ))=1 := by
    unfold e
    rw [mul_comm _ (((n.val:ℝ):ℂ))]
    simpa using Complex.exp_nat_mul_two_pi_mul_I n.val
  simp [pairDiagonal,sourceDiagonal,probe,ph]

theorem rank_one_term (q m n k : ℕ+) (ψ φ : HeightSeed) :
    term (induced (fun a b => ψ.toFun a*star (φ.toFun b))) q m n k=
      star (if q.val∣k.val then orbital m n k ψ φ else 0) := by
  by_cases good : q.val∣k.val
  · simp only [term,if_pos good,orbital,rank_one _ _ ψ.positive,star_mul',star_div₀,star_star,
      KloostermanConjugation.star_kloosterman_eq,star_natCast]
    ring
  · simp [term,good]

end
end ImbalancedChen.Part3.OriginalSameInfinityScalarGeometry20261113
