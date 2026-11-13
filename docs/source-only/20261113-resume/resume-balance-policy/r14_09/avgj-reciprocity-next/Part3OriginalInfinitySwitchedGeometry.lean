import ImbalancedChen.Part3ActualMarkedBruhatTest
import ImbalancedChen.Part3CompactCuspQuotientGeometricPairing
import ImbalancedChen.Part3ActualInfinityCuspAnnihilator

/-! The common positive-modulus cutoff and change of summation level on the
actual infinity/infinity pairing. The single real archimedean argument is
the argument to which the switched Mellin cutoff is applied. -/
namespace ImbalancedChen.Part3.OriginalInfinitySwitchedGeometry20261113
noncomputable section
open Set MeasureTheory Finset
open scoped BigOperators
open ActualInfinityCuspAnnihilator20261026b CompactCuspParabolicL220261025a
open CompactCuspGeometricFubini20261025a CompactCuspParabolicPairing20261025a
open CompactCuspQuotientGeometricPairing20261025a CompactCuspFiniteGeometricIntegral20261025a
open ActualCompactBruhatKernel20261025a ActualCompactBruhatAllModuli20261025a
open OriginalSmoothPoissonTail OriginalContinuousPoincarePackets20261110
open ActualMarkedBruhatTest20261112 OriginalSignedTraceInput20261102
open InfinityZeroActualFiberGeometricPair20261026a InfinityZeroActualFiberFourier20261026a

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

private def probe (m : ℕ+) (s : HeightSeed) : HeightSeed :=
  let h := scaled_test (m.val : ℤ) (by exact_mod_cast m.property.ne') s.toFun
    s.continuous s.compact s.positive
  ⟨scaledSeed (m.val : ℤ) s.toFun, h.1, h.2.1, h.2.2⟩

private def packetVector (q m : ℕ+) (s : HeightSeed) :=
  compactCuspPoincareL2 q.val (m.val : ℤ) (probe m s).toFun
    (probe m s).continuous (probe m s).compact (probe m s).positive

/-- Subtract just the identity double coset of the two actual packet vectors. -/
def offDiagonal (q m n : ℕ+) (s v : HeightSeed) : ℂ :=
  inner ℂ (packetVector q m s) (packetVector q n v) -
    (if (m.val : ℤ) = (n.val : ℤ) then
      ∫ y : ℝ, radialWeight (probe m s).toFun y * (probe n v).toFun y else 0)

def argument (m n k : ℕ+) : ℝ :=
  4 * Real.pi * Real.sqrt ((m.val : ℝ) * (n.val : ℝ)) / (k.val : ℝ)

def orbital (m n k : ℕ+) (s v : HeightSeed) : ℂ :=
  kloosterman k.val (m.val : ℤ) (n.val : ℤ) *
    (star (orbitTest (1 : ℤ) s.toFun v.toFun (argument m n k)) / (k.val : ℂ))

private theorem integral_at_modulus (m n k : ℕ+) (s v : HeightSeed) :
    (∫ x : ℝ, ∫ y : ℝ, geometricPairKernel (k.val : ℝ) (m.val : ℤ) (n.val : ℤ)
        (probe m s).toFun (probe n v).toFun (x,y)) =
      star (orbitTest 1 s.toFun v.toFun (argument m n k)) / (k.val : ℂ) := by
  have hn : (0 : ℤ) < (n.val : ℤ) := by exact_mod_cast n.property
  have h := congrArg (star : ℂ → ℂ)
    (orbit_integral 1 k m.val m.property (n.val : ℤ) hn.ne' s.toFun v.toFun)
  simpa [probe, argument, mixedOrbitKernel_eq_realC, traceModulus, zeroModulus,
    Int.sign_eq_one_of_pos hn, Complex.star_def] using h

/-- Compact support supplies a single C before *any* original level is
selected. The level gate is literal divisibility of the full modulus. -/
private theorem common_cutoff (m n : ℕ+) (s v : HeightSeed) :
    ∃ C : ℕ+, ∀ q : ℕ+, offDiagonal q m n s v =
      ∑ k ∈ Icc 1 C, if q.val ∣ k.val then orbital m n k s v else 0 := by
  let u := probe m s
  let w := probe n v
  obtain ⟨a,ha,hfa⟩ := radial_support_positive_floor w.toFun w.compact w.positive
  obtain ⟨b,hb,hfb⟩ := radial_support_positive_floor u.toFun u.compact u.positive
  obtain ⟨C,hC⟩ := exists_positive_modulus_cutoff a b ha hb
  refine ⟨C, fun q => ?_⟩
  have pair := compactCuspPoincareL2_inner_unfolding q.val (m.val : ℤ) (n.val : ℤ)
    u.toFun w.toFun u.continuous u.compact u.positive w.continuous w.compact w.positive
  have strip := compactCusp_strip_pairing_eq_weightedFourier q.val (m.val : ℤ) (n.val : ℤ)
    u.toFun w.toFun u.continuous u.compact u.positive w.continuous w.compact w.positive
  have h := integrated_actualFourier_eq_finite_geometric q.val (m.val : ℤ) (n.val : ℤ)
    u.toFun w.toFun u.continuous u.compact u.positive w.continuous w.compact w.positive
    a b ha hb hfa hfb C hC
  have ident := pair.trans (strip.trans h)
  unfold offDiagonal packetVector
  rw [ident, add_sub_cancel_left]
  apply sum_congr rfl
  intro k hk
  by_cases hd : q.val ∣ k.val
  · simp only [if_pos hd, orbital]
    exact congrArg (fun w : ℂ => kloosterman k.val (m.val : ℤ) (n.val : ℤ) * w)
      (integral_at_modulus m n k s v)
  · simp [hd]

private theorem reindex_multiples (C q : ℕ+) (f : ℕ+ → ℂ) :
    (∑ k ∈ Icc 1 C, if q.val ∣ k.val then f k else 0) =
      ∑ d ∈ Icc 1 C, if q*d ≤ C then f (q*d) else 0 := by
  classical
  rw [← sum_filter, ← sum_filter]
  symm
  apply sum_bij (fun d _ => q*d)
  · intro d hd
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(q*d).property, (mem_filter.mp hd).2⟩,
      ⟨d.val,rfl⟩⟩
  · intro a _ b _ he
    apply Subtype.ext
    exact Nat.eq_of_mul_eq_mul_left q.property (congrArg Subtype.val he)
  · intro k hk
    obtain ⟨hkC,d,hd⟩ := mem_filter.mp hk
    have hpos : 0 < d := by
      by_contra! hz
      have he : d = 0 := by omega
      have hzero : k.val = 0 := by simpa [he] using hd
      exact k.property.ne' hzero
    let d' : ℕ+ := ⟨d,hpos⟩
    have heq : q*d' = k := Subtype.ext hd.symm
    have hle : d' ≤ C := by
      change d ≤ C.val
      calc
        d ≤ q.val*d := by simpa using Nat.mul_le_mul_right d q.property
        _ = k.val := hd.symm
        _ ≤ C.val := (mem_Icc.mp hkC).2
    exact ⟨d',mem_filter.mpr ⟨mem_Icc.mpr ⟨hpos,hle⟩, heq.le.trans (mem_Icc.mp hkC).2⟩,heq⟩
  · intro d hd
    rfl

/-- At the geometric argument of modulus q*d the switched cutoff recovers
exactly the original level q/Q. The new summation level is d. -/
theorem switched_pair (m n : ℕ+) (s v : HeightSeed) :
    ∃ C : ℕ+, ∀ (S : Finset ℕ+) (Q : ℝ) (g : ℝ → ℂ),
      (∑ q ∈ S, g ((q.val : ℝ)/Q) * offDiagonal q m n s v) =
        ∑ d ∈ Icc 1 C, ∑ q ∈ S, if q*d ≤ C then
          g (4*Real.pi*Real.sqrt ((m.val : ℝ)*(n.val : ℝ)) /
            ((d.val : ℝ)*Q*argument m n (q*d))) * orbital m n (q*d) s v else 0 := by
  classical
  obtain ⟨C,hC⟩ := common_cutoff m n s v
  refine ⟨C, fun S Q g => ?_⟩
  rw [sum_comm (s := Icc 1 C) (t := S)]
  apply sum_congr rfl
  intro q hq
  rw [hC, reindex_multiples, mul_sum]
  apply sum_congr rfl
  intro d hd
  split_ifs with hcut
  · congr 2
    by_cases hQ : Q = 0
    · simp [hQ]
    · have hm : (0 : ℝ) < m.val := by exact_mod_cast m.property
      have hn : (0 : ℝ) < n.val := by exact_mod_cast n.property
      have hq' : (0 : ℝ) < q.val := by exact_mod_cast q.property
      have hd' : (0 : ℝ) < d.val := by exact_mod_cast d.property
      simp only [argument, PNat.coe_mul, Nat.cast_mul]
      field_simp [hQ,Real.pi_ne_zero,hq'.ne',hd'.ne',(Real.sqrt_pos.mpr (mul_pos hm hn)).ne']
      <;> ring
  · simp

end
end ImbalancedChen.Part3.OriginalInfinitySwitchedGeometry20261113
