import ImbalancedChen.Part3OriginalExceptionalProbeFloor
import ImbalancedChen.Part3OriginalHighStripPacketBudget
import ImbalancedChen.Part3ActualUnitBandSpectralMass
import Batteries.Tactic.OpenPrivate

/-! The fixed-level exceptional coefficient inequality in §10(vii).
The finite support consists of distinct signed integers with L < |m| ≤ 2L.
Levels, both actual observation frames, coefficients and the spectral index
all refer to the original quotient and its original Whittaker normalization. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalFixedLevelExceptionalSieve20261113
open Set Filter MeasureTheory Complex
open scoped MatrixGroups BigOperators Classical
open ActualFullCuspEigenbasis20261026b ActualCuspEigenbasisNativeLabels20261026b
open ActualCuspBasisWhittakerCoefficients20261102 Gamma0ActualConstantMode20261025a
open ActualContinuousPoincarePairing20261110 OriginalContinuousPoincarePackets20261110
open OriginalExceptionalHeightWindow20261112 OriginalExceptionalProbeFloor20261113
open OriginalUnitStripPacketMass20261113 OriginalHighStripPacketBudget20261113
open ActualUnitBandSpectralMass20261112
open private discrete_coordinate from ImbalancedChen.Part3ActualSingleModeSpectralEnergy
open private nonnegative_sum from ImbalancedChen.Part3ActualUnitBandSpectralMass

variable (N : ℕ) [NeZero N]
local notation "Idx" => actualCuspBasisIndex N (NeZero.pos N)

def alpha (i : Idx) : ℝ := Real.sqrt (1/4-actualCuspNativeEigenvalue N (NeZero.pos N) i)

def functional (one : Bool) (s : Finset ℤ) (a : ℤ→ℂ) (i : Idx) : ℂ :=
  ∑ m∈s,a m*basisR N (NeZero.pos N) i (originalFrame one) m

def term (one : Bool) (X : ℝ) (s : Finset ℤ) (a : ℤ→ℂ) (i : Idx) : ℝ :=
  if exceptional N i then X^(2*alpha N i)*‖functional N one s a i‖^2 else 0

private theorem term_nonneg (one : Bool) {X : ℝ} (hX : 0<X) (s : Finset ℤ) (a : ℤ→ℂ) (i : Idx) :
    0≤term N one X s a i := by
  unfold term; split <;> positivity

private theorem coordinate (one : Bool) (H : ℝ) (s : Finset ℤ) (a : ℤ→ℂ)
    (nonzero : ∀ m∈s,m≠0) (i : Idx) :
    inner ℂ (packetVector N one H s (fun m => star (a m)))
      (actualCuspHilbertBasis N (NeZero.pos N) i : QuotientL2 N) =
      orderProbe 1 (seed H).toFun (basisOrder N (NeZero.pos N) i)*functional N one s a i := by
  rw [packetVector,sum_inner,functional,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  let ξ := seed (H*|(m:ℝ)|)
  rw [inner_smul_left]
  change (star (star (a m)))*inner ℂ (modeVector N one H m) _=_
  rw [star_star,show inner ℂ (modeVector N one H m)
    (actualCuspHilbertBasis N (NeZero.pos N) i : QuotientL2 N)=_ from
      discrete_coordinate N (originalFrame one) m (nonzero m hm) ξ i,
    show orderProbe m ξ.toFun (basisOrder N (NeZero.pos N) i)=_ from
      probe_common H m (nonzero m hm) _]
  ring

private theorem factor (one : Bool) {X H : ℝ} (hX : 0<X) (hH : 1≤H) (XH : X≤H)
    (s : Finset ℤ) (a : ℤ→ℂ) (nonzero : ∀ m∈s,m≠0) (i : Idx) :
    probeConstant^2*term N one X s a i ≤
      ‖inner ℂ (packetVector N one H s (fun m => star (a m)))
        (actualCuspHilbertBasis N (NeZero.pos N) i : QuotientL2 N)‖^2 := by
  rw [coordinate N one H s a nonzero i,term]
  by_cases h : exceptional N i
  · have hp : 0<H := zero_lt_one.trans_le hH
    have a0 : 0≤alpha N i := Real.sqrt_nonneg _
    have ord : basisOrder N (NeZero.pos N) i=(alpha N i:ℂ) := if_pos h.le
    rw [if_pos h,ord,norm_mul,mul_pow]
    have k := original_probe_floor hH a0
    have floorSq := pow_le_pow_left₀ (mul_nonneg probeConstant_pos.le (Real.rpow_nonneg hp.le _)) k 2
    have xh := Real.rpow_le_rpow hX.le XH (mul_nonneg (by norm_num : (0:ℝ)≤2) a0)
    have pw : H^(2*alpha N i) = (H^(alpha N i))^2 := by
      rw [two_mul,Real.rpow_add hp,sq (H^(alpha N i))]
    rw [pw] at xh
    rw [mul_pow] at floorSq
    calc
      _ = (probeConstant^2*X^(2*alpha N i))*‖functional N one s a i‖^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left xh (sq_nonneg _)).trans floorSq) (sq_nonneg _)
  · simp [h]

def sieveConstant : ℝ := 32/probeConstant^2
theorem sieveConstant_pos : 0<sieveConstant := div_pos (by norm_num) (sq_pos_of_pos probeConstant_pos)

/-- The weight X is arbitrary and positive. Summability is proved on the
entire original Hilbert-basis index by finite Bessel and monotone sums. -/
theorem full_weight (one : Bool) {L X : ℝ} (hL : 0<L) (hX : 0<X) (s : Finset ℤ) (a : ℤ→ℂ)
    (band : ∀ m∈s,L<|(m:ℝ)| ∧ |(m:ℝ)|≤2*L) :
    Summable (term N one X s a) ∧ (∑' i,term N one X s a i) ≤
      sieveConstant*(1+L*max 1 X/(N:ℝ))*coeffMass s a := by
  classical
  let H := max 1 X
  let b := fun m => star (a m)
  let v := packetVector N one H s b
  let B := actualCuspHilbertBasis N (NeZero.pos N)
  have np : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  have H1 : 1≤H := le_max_left _ _
  have Hp : 0<H := zero_lt_one.trans_le H1
  have nz (m) (hm : m∈s) : m≠0 := by
    intro e
    have h := hL.trans (band m hm).1
    simpa [e] using h
  have orth : Orthonormal ℂ (fun i => (B i : QuotientL2 N)) :=
    orthonormal_iff_ite.mpr (fun i j => (orthonormal_iff_ite.mp B.orthonormal) i j)
  have budget := packet_norm_budget N one Hp hL s b
    (fun m hm => ⟨(band m hm).1.le,(band m hm).2⟩)
  have mass : coeffMass s b=coeffMass s a := by simp only [coeffMass,b,norm_star]
  have price : overlap N (bottom H L)=2+8*(L*H/(N:ℝ)) := by
    unfold overlap bottom
    field_simp [np.ne',hL.ne',Hp.ne'] <;> ring
  rw [mass,price] at budget
  apply nonnegative_sum (term_nonneg N one hX s a)
  intro S
  have comp : probeConstant^2*(∑ i∈S,term N one X s a i)≤‖v‖^2 := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum (fun i (_ : i∈S) => factor N one hX H1
      (le_max_right 1 X) s a nz i)).trans ?_
    calc
      _ = ∑ i∈S,‖inner ℂ (B i : QuotientL2 N) v‖^2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun t : ℝ => t^2) (norm_inner_symm (𝕜:=ℂ) v (B i : QuotientL2 N))
      _ ≤ _ := orth.sum_inner_products_le (s:=S) v
  have small : (2+8*(L*H/(N:ℝ)))*(4*coeffMass s a)≤32*(1+L*H/(N:ℝ))*coeffMass s a := by
    nlinarith only [coeffMass_nonneg s a]
  have all := (comp.trans budget).trans small
  have K : 0<probeConstant^2 := sq_pos_of_pos probeConstant_pos
  calc
    _ ≤ (32*(1+L*H/(N:ℝ))*coeffMass s a)/probeConstant^2 :=
      (le_div_iff₀ K).mpr (by rw [mul_comm]; exact all)
    _ = _ := by unfold sieveConstant; dsimp only [H]; ring

private theorem range_cost {L X A : ℝ} (hL : 0<L) (bound : X≤A*max 1 ((N:ℝ)/L)) :
    1+L*max 1 X/(N:ℝ) ≤ (1+max 1 A)*(1+L/(N:ℝ)) := by
  let M := max 1 A
  let Z := max 1 ((N:ℝ)/L)
  have np : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  have m1 : 1≤M := le_max_left _ _
  have mp : 0≤M := zero_le_one.trans m1
  have z1 : 1≤Z := le_max_left _ _
  have xh : max 1 X≤M*Z := max_le
    (by simpa using mul_le_mul m1 z1 zero_le_one mp)
    (bound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans z1)))
  have lz : L*Z ≤ (N:ℝ)+L := by
    rcases le_total 1 ((N:ℝ)/L) with h|h
    · rw [show Z=(N:ℝ)/L from max_eq_right h,
        show L*((N:ℝ)/L)=(N:ℝ) by field_simp [hL.ne']]
      linarith
    · rw [show Z=1 from max_eq_left h,mul_one]; linarith
  have t : L*max 1 X ≤ M*((N:ℝ)+L) := by
    calc
      _ ≤ L*(M*Z) := mul_le_mul_of_nonneg_left xh hL.le
      _ = M*(L*Z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left lz mp
  have q := div_le_div_of_nonneg_right t np.le
  have id : M*((N:ℝ)+L)/(N:ℝ)=M*(1+L/(N:ℝ)) := by field_simp [np.ne'] <;> ring
  rw [id] at q
  change 1+L*max 1 X/(N:ℝ)≤(1+M)*(1+L/(N:ℝ))
  nlinarith only [q,div_nonneg hL.le np.le]

/-- The exact manuscript range, with any fixed implied constant A.
The function a is chosen after the level and is shared by every basis index. -/
theorem manuscript_range (one : Bool) {L X A : ℝ} (hL : 0<L) (hX : 0<X)
    (range : X≤A*max 1 ((N:ℝ)/L)) (s : Finset ℤ) (a : ℤ→ℂ)
    (band : ∀ m∈s,L<|(m:ℝ)| ∧ |(m:ℝ)|≤2*L) :
    Summable (term N one X s a) ∧ (∑' i,term N one X s a i) ≤
      (sieveConstant*(1+max 1 A))*(1+L/(N:ℝ))*coeffMass s a := by
  obtain ⟨summ,bound⟩ := full_weight N one hL hX s a band
  exact ⟨summ,bound.trans (by
    rw [mul_assoc sieveConstant (1+max 1 A)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (range_cost N hL range) sieveConstant_pos.le) (coeffMass_nonneg s a))⟩

/-- The manuscript's epsilon convention, including z=1 and L=1/2. -/
theorem manuscript_epsilon (one : Bool) {L X A ε : ℝ} (hL : 1/2≤L) (hX : 0<X)
    (hε : 0≤ε) (range : X≤A*max 1 ((N:ℝ)/L)) (s : Finset ℤ) (a : ℤ→ℂ)
    (band : ∀ m∈s,L<|(m:ℝ)| ∧ |(m:ℝ)|≤2*L) :
    Summable (term N one X s a) ∧ (∑' i,term N one X s a i) ≤
      (2^ε*sieveConstant*(1+max 1 A))*((N:ℝ)*L)^ε*(1+L/(N:ℝ))*coeffMass s a := by
  have lpos : 0<L := by linarith
  have n1 : (1:ℝ)≤N := by exact_mod_cast Nat.succ_le_of_lt (NeZero.pos N)
  have npos : 0<(N:ℝ) := zero_lt_one.trans_le n1
  have zl : 1 ≤ 2*((N:ℝ)*L) := by
    nlinarith only [mul_le_mul_of_nonneg_right n1 lpos.le,hL]
  have weight := Real.one_le_rpow zl hε
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (mul_nonneg npos.le lpos.le)] at weight
  obtain ⟨sum,bound⟩ := manuscript_range N one lpos hX range s a band
  refine ⟨sum,bound.trans ?_⟩
  let D := (sieveConstant*(1+max 1 A))*(1+L/(N:ℝ))*coeffMass s a
  have pA : 0≤max 1 A := zero_le_one.trans (le_max_left _ _)
  have dp : 0≤D := mul_nonneg
    (mul_nonneg (mul_nonneg sieveConstant_pos.le (add_nonneg zero_le_one pA))
      (add_nonneg zero_le_one (div_nonneg lpos.le npos.le))) (coeffMass_nonneg s a)
  calc
    _ = 1*D := (one_mul D).symm
    _ ≤ (2^ε*((N:ℝ)*L)^ε)*D := mul_le_mul_of_nonneg_right weight dp
    _ = _ := by dsimp [D]; ring

end ImbalancedChen.Part3.OriginalFixedLevelExceptionalSieve20261113
end
