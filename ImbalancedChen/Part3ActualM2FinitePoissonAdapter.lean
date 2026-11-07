import ImbalancedChen.Part3ActualSeparatedRowLogModeSupplier
import ImbalancedChen.Part3ActualReciprocalSquarePoisson

/-!
SOURCEONLY / UNCOMPILED. Actual M2 d78396829cbd5257345423f03dd39b4a3abace23f596466a906d330a20b89bb8
is ROOT-qualified209. Actual P2 619ad4f5d3d3976ce185b7f33e75b99c73eaed35f1bae2c4f9afeccff3739e4b
exists, but its P0/P1/P2 closure is not yet qualified. Both imports are real.
This is a bounded actual normalizedRow -> two-branch finite reciprocal kernel
-> same six completed Poisson pieces adapter, NOT a spectral estimate.
The common lambda includes original gamma2(q*t), never its branch conjugate.
The exact signed block/residue indicator is in common omega. Re/2, T0*coeff
and actual outer alpha remain literal; future completed m runs over all Z.
No row matching, coefficient bound, Poisson conclusion or P8 premise is added.
The initial local definitions/proofs are extracted from reviewed d5814deb
L23–194, with only namespace/open cleanup; no failed M2 prefix is copied.
-/

namespace ImbalancedChen.Part3.ActualM2FinitePoissonAdapterSourceOnly
noncomputable section
attribute [local instance] Classical.propDecidable
open Classical Finset CommonSmoothCutoff
open GeneralDGateNormalization GeneralDActiveOuterEnergySourceOnly
open ActualFixedFeaturePacketPushforwardSourceOnly ActualSeparatedRowPacketMatchSourceOnly
open ActualPositiveLatticeSmoothCoverSourceOnly
open ActualReciprocalSquarePoissonSourceOnly
open scoped BigOperators

theorem signedResidue_natAbs (negative : Bool) (a : ℤ) :
    (signedResidue negative a).natAbs = a.natAbs := by
  cases negative <;> simp [signedResidue]

/-- The old reciprocal character is exactly the character consumed by the
literal finite Poisson row. No invertibility or sign hypothesis is needed
for this elementary identity of real arguments. -/
theorem reciprocal_eq_physical_phase (a : ℤ) (p : Packet) (t : ℕ) (h : ℤ) :
    reciprocal a p t h =
      fourier (a*h*p.2)
        (((CanonicalReciprocalPhase.wPhaseInverse (p.1.1*t) p.1.2 : ℝ) /
          (p.1.2 : ℝ) : ℝ) : UnitAddCircle) := by
  simp only [reciprocal, fourier_coe_apply]
  congr 1
  push_cast
  ring

def actualModePacket (e : MediumAtom) (D delta g l : ℕ) [NeZero (g*l)]
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) : Packet → ℂ :=
  packetJ e D delta g l e.residue negative u k
    (ActualLogModePacketInstanceSourceOnly.modeW e m negative)
    (ActualLogModePacketInstanceSourceOnly.modeOmega e D Z tag m negative)
    (_root_.P3ActualLogAdapterSourceOnly.block e D Z tag)

/-- In particular gamma2(q*t) is NOT a newly independent coefficient.
The root phase and the actual log multiplier are fixed on this u,k,m fibre. -/
def actualModeLambda (e : MediumAtom) (D delta g l : ℕ) [NeZero (g*l)]
    (m : ℤ × ℤ) (negative : Bool) (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) : ℕ → ℂ :=
  commonLambda D delta g l e.residue negative u k
    (ActualLogModePacketInstanceSourceOnly.modeW e m negative)

/-- The final shortened signed dyadic block and the actual residue class
are BOTH in one common h coefficient. There is no b,c or completed-m argument. -/
def actualModeOmega (e : MediumAtom) (D g l : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool) (k : ZMod (g*l)) (h : ℤ) : ℂ :=
  if h ∈ _root_.P3ActualLogAdapterSourceOnly.block e D Z tag then
    commonOmega g l k (ActualLogModePacketInstanceSourceOnly.modeOmega e D Z tag m negative) h
  else 0

/-- The ACTUAL mode packet, not an assumed packet descent, equals the row
already completed by 86340f2e. The extra a-unit mask is licensed by the
original gamma2 support and does not conjugate that coefficient. -/
theorem actual_modePacket_eq_finiteRow
    {B0 : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B0 sigma kappa c0 e)
    (D delta g l : ℕ) [NeZero (g*l)]
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (p : Packet) :
    actualModePacket e D delta g l Z tag m negative u k p =
      finiteReciprocalRow (g*l) (signedResidue negative e.residue)
        (baseCarrier e (D/delta)) (e.sharedSmoothFrequencyBound Z D)
        (actualModeLambda e D delta g l m negative u k)
        (actualModeOmega e D g l Z tag m negative k) p := by
  unfold actualModePacket
  change packetJ e D delta g l e.residue negative u k
      (fun s => e.gamma2 s * branch negative
        (_root_.P3ActualLogAdapterSourceOnly.innerMultiplier e s m.2))
      (ActualLogModePacketInstanceSourceOnly.modeOmega e D Z tag m negative)
      (_root_.P3ActualLogAdapterSourceOnly.block e D Z tag) p = _
  rw [actual_packetJ_eq_unit_filtered he D delta g l negative u k]
  unfold packetJUnit finiteReciprocalRow
  rw [signedResidue_natAbs]
  apply sum_congr rfl
  intro t _
  by_cases hunit : t.Coprime ((g*l)*p.1.2) ∧ t.Coprime (e.residue.natAbs*p.1.2)
  · rw [if_pos hunit, if_pos hunit, mul_sum]
    rw [_root_.P3ActualLogAdapterSourceOnly.block, sum_filter]
    apply sum_congr rfl
    intro h hh
    have hhwin : h ∈ _root_.P3ActualLogAdapterSourceOnly.window e D Z := hh
    by_cases htag : _root_.P3ActualLogAdapterSourceOnly.dyadicKey h = tag
    · have hmem : h ∈ _root_.P3ActualLogAdapterSourceOnly.block e D Z tag :=
        mem_filter.mpr ⟨hhwin, htag⟩
      by_cases hk : (h : ZMod (g*l)) = k
      · rw [branch_reciprocal]
        simp only [if_pos htag, if_pos hk, actualModeOmega, if_pos hmem,
          commonOmega, actualModeLambda, commonLambda,
          ActualLogModePacketInstanceSourceOnly.modeW,
          reciprocal_eq_physical_phase]
        ring
      · simp only [if_pos htag, if_neg hk, actualModeOmega, if_pos hmem,
          commonOmega, zero_mul, mul_zero]
    · have hnot : h ∉ _root_.P3ActualLogAdapterSourceOnly.block e D Z tag := by
        simpa only [_root_.P3ActualLogAdapterSourceOnly.block, mem_filter, hhwin, true_and] using htag
      simp only [if_neg htag, actualModeOmega, if_neg hnot, zero_mul, mul_zero]
  · simp only [if_neg hunit]

/-- A literal M2 row on an actual outer label. The common T0*coeff and the
outer label multiplier stay OUTSIDE the genuine finite reciprocal row. -/
theorem actualModeRow_eq_trueFiniteRow
    {B0 : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B0 sigma kappa c0 e) (Yb Ys : ℝ)
    {D delta g l : ℕ} [NeZero (g*l)] (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool) (k : ZMod (g*l)) :
    ActualLogModePacketInstanceSourceOnly.actualModeRow e D Z tag m negative k
        (_root_.P3ActualLogAdapterSourceOnly.block e D Z tag) o =
      ActualLogModePacketInstanceSourceOnly.modeCoefficient e D Z tag m negative *
        ActualLogModePacketInstanceSourceOnly.modeAlpha e m negative o *
        finiteReciprocalRow (g*l) (signedResidue negative e.residue)
          (baseCarrier e (D/delta)) (e.sharedSmoothFrequencyBound Z D)
          (actualModeLambda e D delta g l m negative (rootFeature D delta g l o) k)
          (actualModeOmega e D g l Z tag m negative k) (packetKey D delta g l o) := by
  have hj := actual_modePacket_eq_finiteRow he D delta g l Z tag m negative
    (rootFeature D delta g l o) k (packetKey D delta g l o)
  unfold actualModePacket at hj
  rw [ActualLogModePacketInstanceSourceOnly.actualModeRow_eq_packetJ e he.1 he.2.2.1
    he.2.2.2.2.1 he.2.2.2.1 Yb Ys hD hg hl ho, hj]

def completedModePiece (e : MediumAtom) (D delta g l : ℕ) [NeZero (g*l)]
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (M N : ℝ) : ℂ :=
  completedPiece (g*l) (signedResidue negative e.residue)
    (baseCarrier e (D/delta)) (e.sharedSmoothFrequencyBound Z D)
    (actualModeLambda e D delta g l m negative u k)
    (actualModeOmega e D g l Z tag m negative k)
    M N (scaleB e delta l) (scaleC e D g l) (scaleF e D g)

def completedModeSix (e : MediumAtom) (D delta g l : ℕ) [NeZero (g*l)]
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) : ℂ :=
  let B := scaleB e delta l
  let C := scaleC e D g l
  completedModePiece e D delta g l Z tag m negative u k B C +
    completedModePiece e D delta g l Z tag m negative u k B (2*C) +
    completedModePiece e D delta g l Z tag m negative u k B (4*C) +
    completedModePiece e D delta g l Z tag m negative u k (2*B) C +
    completedModePiece e D delta g l Z tag m negative u k (2*B) (2*C) +
    completedModePiece e D delta g l Z tag m negative u k (2*B) (4*C)

/-- Exact completion of all SIX actual smooth pieces. Future completed
frequency runs over ALL integers, including zero. No extra factor6. -/
theorem actual_mode_Mass6_eq_completed
    {B0 : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B0 sigma kappa c0 e) (D delta g l : ℕ) [NeZero (g*l)]
    (hdelta : 0 < delta) (hl : 0 < l)
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) :
    (sixSmoothMass (scaleB e delta l) (scaleC e D g l)
      (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g))
      (actualModePacket e D delta g l Z tag m negative u k) : ℂ) =
      completedModeSix e D delta g l Z tag m negative u k := by
  have hB : 0 < scaleB e delta l := by
    have hN : 0 < e.U := zero_lt_one.trans_le he.1
    have hR : 0 < e.Q3 := zero_lt_one.trans_le he.2.2.2.2.1
    have hlR : (0 : ℝ) < l := by exact_mod_cast hl
    have hdR : (0 : ℝ) < delta := by exact_mod_cast hdelta
    unfold scaleB
    positivity
  have hj : actualModePacket e D delta g l Z tag m negative u k =
      finiteReciprocalRow (g*l) (signedResidue negative e.residue)
        (baseCarrier e (D/delta)) (e.sharedSmoothFrequencyBound Z D)
        (actualModeLambda e D delta g l m negative u k)
        (actualModeOmega e D g l Z tag m negative k) := by
    funext p
    exact actual_modePacket_eq_finiteRow he D delta g l Z tag m negative u k p
  rw [hj]
  exact sixSmoothMass_eq_completed (g*l) (signedResidue negative e.residue)
    (baseCarrier e (D/delta)) (e.sharedSmoothFrequencyBound Z D)
    (actualModeLambda e D delta g l m negative u k)
    (actualModeOmega e D g l Z tag m negative k) hB (scaleC e D g l) (scaleF e D g)

/-- Only this complete mass is positive. This local proof consumes the ACTUAL
P1 public cover equality; it does not reference the omitted old nonneg helper. -/
theorem completedModeSix_real_nonneg
    {B0 : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B0 sigma kappa c0 e) (D delta g l : ℕ) [NeZero (g*l)]
    (hdelta : 0 < delta) (hl : 0 < l)
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) :
    (completedModeSix e D delta g l Z tag m negative u k).im = 0 ∧
      0 ≤ (completedModeSix e D delta g l Z tag m negative u k).re := by
  have hm := actual_mode_Mass6_eq_completed he D delta g l hdelta hl Z tag m negative u k
  constructor
  · exact (congrArg Complex.im hm).symm
  · have hre := congrArg Complex.re hm
    rw [← hre]
    rw [← cover_mass_eq_six]
    exact sum_nonneg (fun p _ =>
      mul_nonneg (packetWeight_nonneg _ _ p) (sq_nonneg _))

/-- The actual outer scale and actual Fourier coefficient are outside the row;
all original inner coefficients and both t-unit tests remain inside. -/
def actualFiniteBranch (e : MediumAtom) (D delta g l : ℕ) [NeZero (g*l)]
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (k : ZMod (g*l)) (o : OuterIndex) : ℂ :=
  ActualLogModePacketInstanceSourceOnly.modeCoefficient e D Z tag m negative *
    ActualLogModePacketInstanceSourceOnly.modeAlpha e m negative o *
    finiteReciprocalRow (g*l) (signedResidue negative e.residue)
      (baseCarrier e (D/delta)) (e.sharedSmoothFrequencyBound Z D)
      (actualModeLambda e D delta g l m negative (rootFeature D delta g l o) k)
      (actualModeOmega e D g l Z tag m negative k) (packetKey D delta g l o)

/-- Literal gamma2-outside-Re half-sum; this is not Re of the entire complex row. -/
def actualFiniteRealMode (e : MediumAtom) (D delta g l : ℕ) [NeZero (g*l)]
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (k : ZMod (g*l)) (o : OuterIndex) : ℂ :=
  (actualFiniteBranch e D delta g l Z tag m false k o +
    actualFiniteBranch e D delta g l Z tag m true k o) / 2

/-- Both real-projection branches have the SAME original gamma2. -/
theorem actualRealModeRow_eq_finiteRealMode
    {B0 : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B0 sigma kappa c0 e) (Yb Ys : ℝ)
    {D delta g l : ℕ} [NeZero (g*l)] (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (k : ZMod (g*l)) :
    ActualLogModePacketInstanceSourceOnly.actualRealModeRow e D Z tag m k o =
      actualFiniteRealMode e D delta g l Z tag m k o := by
  rw [ActualLogModePacketInstanceSourceOnly.actualRealModeRow_eq_half_branches]
  unfold actualFiniteRealMode actualFiniteBranch
  rw [actualModeRow_eq_trueFiniteRow he Yb Ys hD hg hl ho,
    actualModeRow_eq_trueFiniteRow he Yb Ys hD hg hl ho]

/-- Actual M2 reconstruction composed with the proved finite-kernel equality.
The harmless M2 Schwartz index is instantiated to0, not assumed as a new bound. -/
theorem actualBlockRow_hasSum_finiteRealMode
    {B0 : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B0 sigma kappa c0 e) (Yb Ys : ℝ)
    {D delta g l : ℕ} [NeZero (g*l)] (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
    (Z : ℝ) (hZ : 0 < Z) (tag : ℕ × Bool) (k : ZMod (g*l)) :
    HasSum (fun m : ℤ × ℤ => actualFiniteRealMode e D delta g l Z tag m k o)
      (ActualLogModePacketInstanceSourceOnly.actualBlockRow e D Z tag k o) := by
  have hs := ActualLogModePacketInstanceSourceOnly.actualBlockRow_hasSum
    he he.1 he.2.2.1 he.2.2.2.2.1 he.2.2.2.1 Yb Ys hD hg hl ho 0 Z hZ tag k
  simpa only [actualModeRow_eq_trueFiniteRow he Yb Ys hD hg hl ho,
    actualFiniteRealMode, actualFiniteBranch] using hs

/-- The literal normalized row is the exact finite block/residue sum of the
convergent Fourier series of these two actual finite reciprocal branches. -/
theorem normalizedRow_eq_finiteReciprocal_series
    {B0 : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B0 sigma kappa c0 e) (Yb Ys : ℝ)
    {D delta g l : ℕ} [NeZero (g*l)] (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l) (Z : ℝ) (hZ : 0 < Z) :
    normalizedRow e Z o =
      ∑ tag ∈ (_root_.P3ActualLogAdapterSourceOnly.window e D Z).image
        _root_.P3ActualLogAdapterSourceOnly.dyadicKey,
        ∑ k : ZMod (g*l), ∑' m : ℤ × ℤ,
          actualFiniteRealMode e D delta g l Z tag m k o := by
  rw [ActualLogModePacketInstanceSourceOnly.normalizedRow_eq_blocks_residues e Yb Ys ho Z]
  apply sum_congr rfl
  intro tag _
  apply sum_congr rfl
  intro k _
  exact (actualBlockRow_hasSum_finiteRealMode he Yb Ys hD hg hl ho Z hZ tag k).tsum_eq.symm

/-- Equivalent HasSum form. Only FINITE block/residue sums are interchanged
with the mode series; no independent absolute-convergence premise is inserted. -/
theorem normalizedRow_hasSum_finiteReciprocal_modes
    {B0 : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B0 sigma kappa c0 e) (Yb Ys : ℝ)
    {D delta g l : ℕ} [NeZero (g*l)] (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l) (Z : ℝ) (hZ : 0 < Z) :
    HasSum (fun m : ℤ × ℤ =>
      ∑ tag ∈ (_root_.P3ActualLogAdapterSourceOnly.window e D Z).image
        _root_.P3ActualLogAdapterSourceOnly.dyadicKey,
        ∑ k : ZMod (g*l), actualFiniteRealMode e D delta g l Z tag m k o)
      (normalizedRow e Z o) := by
  rw [ActualLogModePacketInstanceSourceOnly.normalizedRow_eq_blocks_residues e Yb Ys ho Z]
  exact hasSum_sum (s := (_root_.P3ActualLogAdapterSourceOnly.window e D Z).image
      _root_.P3ActualLogAdapterSourceOnly.dyadicKey) (fun tag _ =>
    hasSum_sum (s := (univ : Finset (ZMod (g*l)))) (fun k _ =>
      actualBlockRow_hasSum_finiteRealMode he Yb Ys hD hg hl ho Z hZ tag k))

end
end ImbalancedChen.Part3.ActualM2FinitePoissonAdapterSourceOnly
