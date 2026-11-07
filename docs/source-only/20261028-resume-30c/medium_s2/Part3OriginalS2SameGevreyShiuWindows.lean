import ImbalancedChen.Part3OriginalS2SameGevreyPacket
import ImbalancedChen.Part3MediumPrimitiveShiuWindowGate
import ImbalancedChen.Part3MediumPrimitiveShiuEulerTotient
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-!
Apply the original primitive Shiu boundary to the ACTUAL same-Gevrey
positive product progression. The signed residue has its genuine least
nonnegative representative; its reduction and coprimality are proved.
Four concrete dyadic intervals cover every nonzero Gevrey product.
Only the named original X,H,q,b Shiu primitive is a boundary hypothesis.
Its native threshold and modulus margin remain explicit in the public
statement, rather than replacing them by an assumed progression bound.
SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
-/

namespace ImbalancedChen.Part3OriginalS2SameGevreyShiuWindows

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalS2ActualBlockPacketBound
open ImbalancedChen.Part3OriginalS2ActualBlockGeometry
open ImbalancedChen.Part3OriginalS2SameGevreyPacket
open ImbalancedChen.Part3.MediumPrimitiveShiuWindow20261028
open ImbalancedChen.Part3.MediumPrimitiveShiuEuler20261028
open Classical Finset
open scoped BigOperators

noncomputable section

def naturalResidue (a : ℤ) (l : ℕ) : ℕ := (a % (l : ℤ)).toNat

theorem naturalResidue_cast (a : ℤ) (l : ℕ) (hl : 0 < l) :
    (naturalResidue a l : ℤ) = a % (l : ℤ) := by
  exact Int.toNat_of_nonneg
    (Int.emod_nonneg a (by exact_mod_cast hl.ne'))

theorem naturalResidue_modEq (a : ℤ) (l : ℕ) (hl : 0 < l) :
    Int.ModEq l (naturalResidue a l : ℤ) a := by
  change (naturalResidue a l : ℤ) % (l : ℤ) = a % (l : ℤ)
  rw [naturalResidue_cast a l hl, Int.emod_emod]

theorem movingResidue_nat_iff (a : ℤ) (l v : ℕ) (hl : 0 < l) :
    Int.ModEq l (v : ℤ) a ↔ Nat.ModEq l v (naturalResidue a l) := by
  have hb := naturalResidue_modEq a l hl
  constructor
  · intro h
    exact Int.natCast_modEq_iff.mp (h.trans hb.symm)
  · intro h
    exact (Int.natCast_modEq_iff.mpr h).trans hb

theorem naturalResidue_coprime (a : ℤ) (l : ℕ) (hl : 0 < l)
    (hcop : Nat.Coprime l a.natAbs) : Nat.Coprime l (naturalResidue a l) := by
  have hga : Int.gcd a l = 1 := by
    simpa [Int.gcd, Nat.gcd_comm] using hcop
  have hgb : Int.gcd (naturalResidue a l : ℤ) l = 1 := by
    rw [naturalResidue_cast a l hl, Int.gcd_emod]
    exact hga
  simpa [Int.gcd, Nat.gcd_comm] using hgb

def firstWindowScale (d : MediumAtom) : ℕ := Nat.floor (d.scale / 2)

def dyadicStart (d : MediumAtom) (j : ℕ) : ℕ := 2 ^ j * firstWindowScale d

def dyadicWindow (d : MediumAtom) (j : ℕ) : Finset ℕ :=
  Finset.Ico (dyadicStart d j) (dyadicStart d j + dyadicStart d j)

theorem firstWindowScale_bounds (d : MediumAtom) (hx : 6 ≤ d.scale) :
    d.scale / 3 ≤ (firstWindowScale d : ℝ) ∧
      (firstWindowScale d : ℝ) ≤ d.scale / 2 ∧ 0 < firstWindowScale d := by
  have hfloor := Nat.lt_floor_add_one (d.scale / 2)
  have hlo : d.scale / 3 ≤ (firstWindowScale d : ℝ) := by
    dsimp [firstWindowScale]
    linarith
  have hhi : (firstWindowScale d : ℝ) ≤ d.scale / 2 :=
    Nat.floor_le (by linarith)
  exact ⟨hlo, hhi, by exact_mod_cast (by linarith : (0 : ℝ) < firstWindowScale d)⟩

theorem psiMNImage_has_window
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hx : 6 ≤ d.scale)
    {v : ℕ} (hv : v ∈ psiMNImage d) :
    ∃ j ∈ Finset.range 4, v ∈ dyadicWindow d j := by
  obtain ⟨hvlo, hvhi, _⟩ := psiMNImage_physical_interval hd hv
  obtain ⟨hKlo, hKhi, hKpos⟩ := firstWindowScale_bounds d hx
  have hvK : firstWindowScale d ≤ v := by exact_mod_cast hKhi.trans hvlo
  have hv16 : v < 16 * firstWindowScale d := by
    have hR : (v : ℝ) < 16 * (firstWindowScale d : ℝ) := by linarith
    exact_mod_cast hR
  by_cases h₂ : v < 2 * firstWindowScale d
  · exact ⟨0, by norm_num, by simpa [dyadicWindow, dyadicStart] using
      Finset.mem_Ico.mpr ⟨hvK, h₂⟩⟩
  · by_cases h₄ : v < 4 * firstWindowScale d
    · refine ⟨1, by norm_num, ?_⟩
      simp only [dyadicWindow, dyadicStart, pow_one, Finset.mem_Ico]
      omega
    · by_cases h₈ : v < 8 * firstWindowScale d
      · refine ⟨2, by norm_num, ?_⟩
        norm_num [dyadicWindow, dyadicStart, Finset.mem_Ico]
        omega
      · refine ⟨3, by norm_num, ?_⟩
        norm_num [dyadicWindow, dyadicStart, Finset.mem_Ico]
        omega

theorem psiDivisorProgression_le_four_windows
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hx : 6 ≤ d.scale)
    (l : ℕ) (hl : 0 < l) :
    psiDivisorProgression d l ≤
      ∑ j ∈ Finset.range 4, ∑ v ∈ dyadicWindow d j,
        if Nat.ModEq l v (naturalResidue d.residue l) then
          (v.divisors.card : ℝ) else 0 := by
  let F : ℕ → ℝ := fun v =>
    if Nat.ModEq l v (naturalResidue d.residue l) then (v.divisors.card : ℝ) else 0
  have hF (v : ℕ) : 0 ≤ F v := by dsimp [F]; split_ifs <;> positivity
  have hpoint (v : ℕ) (hv : v ∈ psiMNImage d) :
      F v ≤ ∑ j ∈ Finset.range 4, if v ∈ dyadicWindow d j then F v else 0 := by
    obtain ⟨j, hj, hvj⟩ := psiMNImage_has_window hd hx hv
    have hs := Finset.single_le_sum
      (fun k (_hk : k ∈ Finset.range 4) => show 0 ≤
        (if v ∈ dyadicWindow d k then F v else 0) by split_ifs <;> positivity) hj
    simpa only [if_pos hvj] using hs
  calc
    psiDivisorProgression d l = ∑ v ∈ psiMNImage d, F v := by
      unfold psiDivisorProgression
      simp only [movingResidue_nat_iff d.residue l _ hl, F]
    _ ≤ ∑ v ∈ psiMNImage d, ∑ j ∈ Finset.range 4,
        if v ∈ dyadicWindow d j then F v else 0 := Finset.sum_le_sum hpoint
    _ = ∑ j ∈ Finset.range 4, ∑ v ∈ (psiMNImage d).filter
        (fun v => v ∈ dyadicWindow d j), F v := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ ∑ j ∈ Finset.range 4, ∑ v ∈ dyadicWindow d j, F v := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro v hv
        exact (Finset.mem_filter.mp hv).2
      · intro v hv hnot
        exact hF v

def originalShiuWindowBudget {α κ : ℝ}
    (hShiu : PrimitiveShiuTauBoundary 1 α κ) (d : MediumAtom) (l j : ℕ) : ℝ :=
  hShiu.A * (dyadicStart d j : ℝ) / (l.totient : ℝ) /
    Real.log (dyadicStart d j) *
      Real.exp ((2 : ℝ) ^ (1 : ℕ) *
        ∑ p ∈ (Finset.range (dyadicStart d j + 1)).filter
          (fun p => p.Prime ∧ ¬p ∣ l), (1 : ℝ) / p)

/-- Exact use of the original primitive, with threshold BEFORE all varying
residues. The residue here is computed from this very atom's signed a. -/
theorem psiDivisorProgression_le_originalShiu
    {B : ℕ} {sigma kappa c0 α κ : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hx : 6 ≤ d.scale)
    (hShiu : PrimitiveShiuTauBoundary 1 α κ)
    (l : ℕ) (hl : 0 < l) (hcop : Nat.Coprime l d.residue.natAbs)
    (hthreshold : hShiu.X0 ≤ (firstWindowScale d : ℝ))
    (hmod : (l : ℝ) < (firstWindowScale d : ℝ) ^ (1 - α)) :
    psiDivisorProgression d l ≤
      ∑ j ∈ Finset.range 4, originalShiuWindowBudget hShiu d l j := by
  have hKpos := (firstWindowScale_bounds d hx).2.2
  have hKone : (1 : ℝ) ≤ firstWindowScale d := by exact_mod_cast hKpos
  have hcopb := naturalResidue_coprime d.residue l hl hcop
  refine (psiDivisorProgression_le_four_windows hd hx l hl).trans ?_
  apply Finset.sum_le_sum
  intro j hj
  have hpow1 : 1 ≤ (2 : ℕ) ^ j := by
    have hpos : 0 < (2 : ℕ) ^ j := by positivity
    omega
  have hstart : firstWindowScale d ≤ dyadicStart d j := by
    dsimp [dyadicStart]
    simpa only [one_mul] using Nat.mul_le_mul_right (firstWindowScale d) hpow1
  have hstartR : (firstWindowScale d : ℝ) ≤ dyadicStart d j := by exact_mod_cast hstart
  have hXone : (1 : ℝ) ≤ dyadicStart d j := hKone.trans hstartR
  have hXpos : 0 < dyadicStart d j := hKpos.trans_le hstart
  have hκ : (dyadicStart d j : ℝ) ^ κ ≤ (dyadicStart d j : ℝ) := by
    calc
      _ ≤ (dyadicStart d j : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXone (by linarith [hShiu.kappa_half])
      _ = _ := by simp
  have hα : (l : ℝ) < (dyadicStart d j : ℝ) ^ (1 - α) :=
    hmod.trans_le (Real.rpow_le_rpow (by positivity) hstartR
      (by linarith [hShiu.alpha_half]))
  have h := hShiu.bound (dyadicStart d j) (dyadicStart d j) l
    (naturalResidue d.residue l) (hthreshold.trans hstartR) hXpos hl hκ
    (Nat.le_refl _) hα hcopb
  simpa only [dyadicWindow, originalShiuWindowBudget, pow_one] using h

theorem dyadicStart_bounds (d : MediumAtom) (hx : 6 ≤ d.scale)
    (j : ℕ) (hj : j ∈ Finset.range 4) :
    2 ≤ dyadicStart d j ∧ dyadicStart d j ≤ 8 * firstWindowScale d := by
  have hKlo := (firstWindowScale_bounds d hx).1
  have hKtwo : 2 ≤ firstWindowScale d := by exact_mod_cast (by linarith :
    (2 : ℝ) ≤ firstWindowScale d)
  have hjlt := Finset.mem_range.mp hj
  interval_cases j <;> norm_num [dyadicStart] <;> omega

theorem originalShiuWindowBudget_le_log
    {α κ : ℝ} (hShiu : PrimitiveShiuTauBoundary 1 α κ)
    (d : MediumAtom) (hx : 6 ≤ d.scale) (l : ℕ) (hl : 0 < l)
    (j : ℕ) (hj : j ∈ Finset.range 4) :
    originalShiuWindowBudget hShiu d l j ≤
      (hShiu.A * uniformEulerConstant 1 *
        ((l.divisors.card : ℝ) / (l : ℝ)) *
        Real.log (16 * (firstWindowScale d : ℝ))) * (dyadicStart d j : ℝ) := by
  have hbounds := dyadicStart_bounds d hx j hj
  have hXtwo : (2 : ℝ) ≤ dyadicStart d j := by exact_mod_cast hbounds.1
  have hXpos : (0 : ℝ) < dyadicStart d j := by linarith
  have hlogX : 0 < Real.log (dyadicStart d j) := Real.log_pos (by linarith)
  have hXupper : (dyadicStart d j : ℝ) ≤ 16 * (firstWindowScale d : ℝ) := by
    have h := hbounds.2
    exact_mod_cast (h.trans (Nat.mul_le_mul_right _ (by norm_num : 8 ≤ 16)))
  have hlogUpper : Real.log (dyadicStart d j) ≤
      Real.log (16 * (firstWindowScale d : ℝ)) :=
    Real.log_le_log hXpos hXupper
  have hEuler : Real.exp ((2 : ℝ) ^ (1 : ℕ) *
      ∑ p ∈ (Finset.range (dyadicStart d j + 1)).filter
        (fun p => p.Prime ∧ ¬p ∣ l), (1 : ℝ) / p) ≤
      uniformEulerConstant 1 * Real.log (dyadicStart d j) ^ 2 := by
    simpa only [pow_one, Real.rpow_two] using
      uniformEulerConstant_bound 1 (dyadicStart d j) l hbounds.1
  have hphi : (0 : ℝ) < l.totient := by exact_mod_cast Nat.totient_pos.mpr hl
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hratio := totient_ratio_le_divisor_count l hl
  have hrec : (1 : ℝ) / l.totient ≤ (l.divisors.card : ℝ) / l := by
    apply (div_le_div_iff₀ hphi hlR).mpr
    simpa only [one_mul] using (div_le_iff₀ hphi).mp hratio
  have hA := hShiu.A_pos.le
  have hE := (uniformEulerConstant_pos 1).le
  unfold originalShiuWindowBudget
  calc
    _ ≤ hShiu.A * (dyadicStart d j : ℝ) / (l.totient : ℝ) /
        Real.log (dyadicStart d j) *
          (uniformEulerConstant 1 * Real.log (dyadicStart d j) ^ 2) :=
        mul_le_mul_of_nonneg_left hEuler (by positivity)
    _ = (hShiu.A * uniformEulerConstant 1 * (dyadicStart d j : ℝ)) *
        (1 / (l.totient : ℝ)) * Real.log (dyadicStart d j) := by
          field_simp [hphi.ne', hlogX.ne']
          ring
    _ ≤ (hShiu.A * uniformEulerConstant 1 * (dyadicStart d j : ℝ)) *
        ((l.divisors.card : ℝ) / (l : ℝ)) * Real.log (dyadicStart d j) := by
          gcongr <;> first | exact hrec | positivity
    _ ≤ (hShiu.A * uniformEulerConstant 1 * (dyadicStart d j : ℝ)) *
        ((l.divisors.card : ℝ) / (l : ℝ)) *
        Real.log (16 * (firstWindowScale d : ℝ)) := by
          gcongr <;> first | exact hlogUpper | positivity
    _ = _ := by ring

def progressionLogBudget {α κ : ℝ}
    (hShiu : PrimitiveShiuTauBoundary 1 α κ) (d : MediumAtom) (l : ℕ) : ℝ :=
  ((15 / 2 : ℝ) * hShiu.A * uniformEulerConstant 1) *
    (d.scale / (l : ℝ)) * (l.divisors.card : ℝ) * Real.log (8 * d.scale)

theorem sum_originalShiuWindowBudget_le
    {α κ : ℝ} (hShiu : PrimitiveShiuTauBoundary 1 α κ)
    (d : MediumAtom) (hx : 6 ≤ d.scale) (l : ℕ) (hl : 0 < l) :
    (∑ j ∈ Finset.range 4, originalShiuWindowBudget hShiu d l j) ≤
      progressionLogBudget hShiu d l := by
  have hK := firstWindowScale_bounds d hx
  have hKposR : (0 : ℝ) < firstWindowScale d := by exact_mod_cast hK.2.2
  have hA := hShiu.A_pos.le
  have hE := (uniformEulerConstant_pos 1).le
  have hlogK : 0 ≤ Real.log (16 * (firstWindowScale d : ℝ)) :=
    Real.log_nonneg (by
      have hKone : (1 : ℝ) ≤ firstWindowScale d := by exact_mod_cast hK.2.2
      linarith)
  have hlogUpper : Real.log (16 * (firstWindowScale d : ℝ)) ≤
      Real.log (8 * d.scale) :=
    Real.log_le_log (by positivity) (by linarith [hK.2.1])
  have hlogx : 0 ≤ Real.log (8 * d.scale) := Real.log_nonneg (by linarith)
  have hsum : (∑ j ∈ Finset.range 4, (dyadicStart d j : ℝ)) =
      15 * (firstWindowScale d : ℝ) := by
    norm_num [Finset.sum_range_succ, dyadicStart, Nat.cast_mul] <;> ring
  calc
    _ ≤ ∑ j ∈ Finset.range 4,
        (hShiu.A * uniformEulerConstant 1 *
          ((l.divisors.card : ℝ) / (l : ℝ)) *
          Real.log (16 * (firstWindowScale d : ℝ))) * (dyadicStart d j : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact originalShiuWindowBudget_le_log hShiu d hx l hl j hj
    _ = (hShiu.A * uniformEulerConstant 1 *
          ((l.divisors.card : ℝ) / (l : ℝ)) *
          Real.log (16 * (firstWindowScale d : ℝ))) *
          (15 * (firstWindowScale d : ℝ)) := by rw [← Finset.mul_sum, hsum]
    _ ≤ (hShiu.A * uniformEulerConstant 1 *
          ((l.divisors.card : ℝ) / (l : ℝ)) * Real.log (8 * d.scale)) *
          (15 * (d.scale / 2)) := by
      gcongr <;> first | exact hlogUpper | exact hK.2.1 | positivity
    _ = progressionLogBudget hShiu d l := by
      unfold progressionLogBudget
      ring

theorem psiDivisorProgression_le_logBudget
    {B : ℕ} {sigma kappa c0 α κ : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hx : 6 ≤ d.scale)
    (hShiu : PrimitiveShiuTauBoundary 1 α κ)
    (l : ℕ) (hl : 0 < l) (hcop : Nat.Coprime l d.residue.natAbs)
    (hthreshold : hShiu.X0 ≤ (firstWindowScale d : ℝ))
    (hmod : (l : ℝ) < (firstWindowScale d : ℝ) ^ (1 - α)) :
    psiDivisorProgression d l ≤ progressionLogBudget hShiu d l :=
  (psiDivisorProgression_le_originalShiu hd hx hShiu l hl hcop hthreshold hmod).trans
    (sum_originalShiuWindowBudget_le hShiu d hx l hl)

/-- The original Shiu window bounds are now attached to the actual
same-Gevrey packet and the actual H geometry. This does not assume V/l. -/
theorem samePsiPacket_le_originalShiu_geometry
    {B : ℕ} {sigma kappa c0 α κ : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hx : 6 ≤ d.scale)
    (hShiu : PrimitiveShiuTauBoundary 1 α κ)
    (x z D R : ℝ) (hD : 0 < D) (l : ℕ) (hl : 0 < l)
    (hthreshold : hShiu.X0 ≤ (firstWindowScale d : ℝ))
    (hmod : (l : ℝ) < (firstWindowScale d : ℝ) ^ (1 - α)) :
    ‖samePsiBlockPacket d x z D R l‖ ≤
      (∑ j ∈ Finset.range 4, originalShiuWindowBudget hShiu d l j) *
        geometryFactor d D l := by
  have hgeom : 0 ≤ geometryFactor d D l := by
    unfold geometryFactor
    have hU : 0 ≤ d.U := by linarith [hd.1]
    have hQ : 0 ≤ d.Q1 := by linarith [hd.2.2.1]
    have hlog := ImbalancedChen.P5Z.RoughSquareWeightedBudget.logBudget_nonneg
      (physicalCap d)
    positivity
  by_cases hzero : samePsiBlockPacket d x z D R l = 0
  · rw [hzero, norm_zero]
    apply mul_nonneg _ hgeom
    apply Finset.sum_nonneg
    intro j hj
    unfold originalShiuWindowBudget
    have hKpos := (firstWindowScale_bounds d hx).2.2
    have hstart : 0 < dyadicStart d j := Nat.mul_pos (by positivity) hKpos
    have hX : (2 : ℝ) ≤ dyadicStart d j := by
      have hKlo := (firstWindowScale_bounds d hx).1
      have hKtwo : 2 ≤ firstWindowScale d := by
        exact_mod_cast (by linarith : (2 : ℝ) ≤ firstWindowScale d)
      have hjpow : 1 ≤ (2 : ℕ) ^ j := by
        have hpos : 0 < (2 : ℕ) ^ j := by positivity
        omega
      have hstart : firstWindowScale d ≤ dyadicStart d j := by
        dsimp [dyadicStart]
        simpa only [one_mul] using Nat.mul_le_mul_right (firstWindowScale d) hjpow
      exact_mod_cast hKtwo.trans hstart
    have hlogX := Real.log_nonneg (show (1 : ℝ) ≤ dyadicStart d j by linarith)
    have hA := hShiu.A_pos.le
    positivity
  · have hcop := nonzero_samePsiBlockPacket_coprime hd x z D R l hzero
    exact (samePsiBlockPacket_norm_le_geometry hd x z D R hD l hl).trans
      (mul_le_mul_of_nonneg_right
        (psiDivisorProgression_le_originalShiu hd hx hShiu l hl hcop hthreshold hmod)
        hgeom)

/-- The returned scale is literally V/l with V=M*N^2/Y, N=U, M=V,
Y=Q1*D. The Shiu threshold and native modulus margin remain visible. -/
theorem samePsiPacket_le_V_over_l
    {B : ℕ} {sigma kappa c0 α κ : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hx : 6 ≤ d.scale)
    (hShiu : PrimitiveShiuTauBoundary 1 α κ)
    (x z D R : ℝ) (hD : 0 < D) (l : ℕ) (hl : 0 < l)
    (hthreshold : hShiu.X0 ≤ (firstWindowScale d : ℝ))
    (hmod : (l : ℝ) < (firstWindowScale d : ℝ) ^ (1 - α)) :
    ‖samePsiPaperBlockPacket d x z D R l‖ ≤
      (90 * hShiu.A * uniformEulerConstant 1) *
        (d.V * d.U ^ 2 / ((d.Q1 * D) * (l : ℝ))) *
        (l.divisors.card : ℝ) ^ 5 *
        ImbalancedChen.P5Z.RoughSquareWeightedBudget.logBudget (physicalCap d) *
        (1 + Real.log (roughCap d)) ^ 4 * Real.log (8 * d.scale) := by
  rw [samePsiPaperBlockPacket_eq_packet]
  calc
    _ ≤ (∑ j ∈ Finset.range 4, originalShiuWindowBudget hShiu d l j) *
        geometryFactor d D l :=
      samePsiPacket_le_originalShiu_geometry hd hx hShiu x z D R hD l hl
        hthreshold hmod
    _ ≤ progressionLogBudget hShiu d l * geometryFactor d D l := by
      apply mul_le_mul_of_nonneg_right
        (sum_originalShiuWindowBudget_le hShiu d hx l hl)
      unfold geometryFactor
      have hU : 0 ≤ d.U := by linarith [hd.1]
      have hQ : 0 ≤ d.Q1 := by linarith [hd.2.2.1]
      have hlog := ImbalancedChen.P5Z.RoughSquareWeightedBudget.logBudget_nonneg
        (physicalCap d)
      positivity
    _ = _ := by
      unfold progressionLogBudget geometryFactor MediumAtom.scale
        ImbalancedChen.Part3.OriginalMediumS1SeparatedDivisorMean.tauR
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The manuscript's full modulus range x^(4/5) fits the original Shiu
margin with alpha=1/10, uniformly once x>3^9. -/
theorem physical_modulus_shiu_margin (d : MediumAtom) (hx : 6 ≤ d.scale)
    (hlarge : (3 : ℝ) ^ (9 : ℕ) < d.scale) (l : ℕ)
    (hl : (l : ℝ) ≤ d.scale ^ ((4 : ℝ) / 5)) :
    (l : ℝ) < (firstWindowScale d : ℝ) ^ (1 - (1 / 10 : ℝ)) := by
  have hxpos : 0 < d.scale := by linarith
  have hroot := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ (3 : ℝ) ^ (9 : ℕ))
    hlarge (by norm_num : (0 : ℝ) < 1 / 10)
  have hthree : ((3 : ℝ) ^ (9 : ℕ)) ^ (1 / 10 : ℝ) =
      (3 : ℝ) ^ (9 / 10 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [hthree] at hroot
  have hsplit : d.scale ^ (9 / 10 : ℝ) =
      d.scale ^ ((4 : ℝ) / 5) * d.scale ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    norm_num
  have hdiv : d.scale ^ ((4 : ℝ) / 5) <
      (d.scale / 3) ^ (9 / 10 : ℝ) := by
    rw [Real.div_rpow hxpos.le (by norm_num : (0 : ℝ) ≤ 3)]
    apply (lt_div_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _)).mpr
    rw [hsplit]
    exact mul_lt_mul_of_pos_left hroot (Real.rpow_pos_of_pos hxpos _)
  have hKlo := (firstWindowScale_bounds d hx).1
  exact (hl.trans_lt hdiv).trans_le (by
    norm_num only [show (1 - (1 / 10 : ℝ)) = 9 / 10 by norm_num]
    exact Real.rpow_le_rpow (by positivity) hKlo (by norm_num))

/-- A uniform-in-l source-form return on the original x^(4/5) modulus
range. The same original Shiu constants precede every atom and residue. -/
theorem samePsiPacket_physical_modulus_return
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (hx : 6 ≤ d.scale) (hlarge : (3 : ℝ) ^ (9 : ℕ) < d.scale)
    (hthreshold : 3 * hShiu.X0 ≤ d.scale)
    (z D R : ℝ) (hD : 0 < D) (l : ℕ) (hl : 0 < l)
    (hmod : l ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5))) :
    ‖samePsiPaperBlockPacket d d.scale z D R l‖ ≤
      (90 * hShiu.A * uniformEulerConstant 1) *
        (d.V * d.U ^ 2 / ((d.Q1 * D) * (l : ℝ))) *
        (l.divisors.card : ℝ) ^ 5 *
        ImbalancedChen.P5Z.RoughSquareWeightedBudget.logBudget (physicalCap d) *
        (1 + Real.log (roughCap d)) ^ 4 * Real.log (8 * d.scale) := by
  have hX0 : hShiu.X0 ≤ (firstWindowScale d : ℝ) := by
    have hKlo := (firstWindowScale_bounds d hx).1
    linarith
  have hmodR : (l : ℝ) ≤ d.scale ^ ((4 : ℝ) / 5) :=
    (show (l : ℝ) ≤ (Nat.floor (d.scale ^ ((4 : ℝ) / 5)) : ℝ) by
      exact_mod_cast hmod).trans
        (Nat.floor_le (Real.rpow_nonneg (by linarith : 0 ≤ d.scale) _))
  exact samePsiPacket_le_V_over_l hd hx hShiu d.scale z D R hD l hl hX0
    (physical_modulus_shiu_margin d hx hlarge l hmodR)

end
end ImbalancedChen.Part3OriginalS2SameGevreyShiuWindows
