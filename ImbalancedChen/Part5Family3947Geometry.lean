import ImbalancedChen.Part5OriginalOmegaGridCoreModular


/- SOURCEONLY / UNCOMPILED.
Append after the frozen 6b25... COMPLETE source. No Lean invocation is made.
These are real calculus lemmas for the four original weak-order patterns,
not numerical identities with a stored value substituted for an integral. -/

namespace ImbalancedChen.Certificates.SavedParentFamily3947SourceOnly

open Set MeasureTheory
open scoped Interval

noncomputable section

def inverseSquareMass (a b : ℝ) : ℝ := ∫ x in a..b, 1 / x^2
def lowerTriangleMass (a b : ℝ) : ℝ :=
  ∫ x in a..b, (1 / x) * (1 / a - 1 / x)
def tripleTriangleMass (a b : ℝ) : ℝ :=
  ∫ x in a..b, (1 / x) * (1 / a - (1 + Real.log (x/a)) / x)

theorem inverseSquareMass_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    inverseSquareMass a b = 1/a - 1/b := by
  have hx : ∀ x ∈ uIcc a b, 0 < x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hd : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => -1/y) (1/x^2) x := by
    intro x hxx
    have h := (hasDerivAt_const x (-1 : ℝ)).div (hasDerivAt_id x) (hx x hxx).ne'
    convert h using 1 <;> dsimp <;> field_simp [(hx x hxx).ne'] <;> ring
  have hi : IntervalIntegrable (fun x : ℝ => 1/x^2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun x hxx => pow_ne_zero 2 (hx x hxx).ne')
  rw [inverseSquareMass, intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  ring

theorem lowerTriangleMass_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    lowerTriangleMass a b = Real.log (b/a)/a - 1/a + 1/b := by
  let F : ℝ → ℝ := fun x => Real.log x/a + 1/x
  have hx : ∀ x ∈ uIcc a b, 0 < x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hd : ∀ x ∈ uIcc a b,
      HasDerivAt F ((1/x)*(1/a-1/x)) x := by
    intro x hxx
    have h := ((Real.hasDerivAt_log (hx x hxx).ne').div_const a).add
      ((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) (hx x hxx).ne')
    convert h using 1 <;> dsimp [F] <;>
      field_simp [ha.ne', (hx x hxx).ne'] <;> ring
  have hi : IntervalIntegrable (fun x : ℝ => (1/x)*(1/a-1/x)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    have hI : ContinuousOn (fun x : ℝ => 1/x) (uIcc a b) :=
      continuousOn_const.div continuousOn_id (fun x hxx => (hx x hxx).ne')
    exact hI.mul (continuousOn_const.sub hI)
  rw [lowerTriangleMass, intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  dsimp [F]
  rw [Real.log_div (ha.trans_le hab).ne' ha.ne']
  ring

theorem tripleTriangleMass_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    tripleTriangleMass a b =
      (Real.log (b/a)-2)/a + (Real.log (b/a)+2)/b := by
  let F : ℝ → ℝ := fun x =>
    (Real.log x-Real.log a)/a + (2+Real.log x-Real.log a)/x
  have hx : ∀ x ∈ uIcc a b, 0 < x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hd : ∀ x ∈ uIcc a b,
      HasDerivAt F ((1/x)*(1/a-(1+Real.log (x/a))/x)) x := by
    intro x hxx
    have hl := Real.hasDerivAt_log (hx x hxx).ne'
    have h := ((hl.sub_const (Real.log a)).div_const a).add
      ((((hasDerivAt_const x (2 : ℝ)).add hl).sub_const (Real.log a)).div
        (hasDerivAt_id x) (hx x hxx).ne')
    convert h using 1 <;> dsimp [F] <;>
      simp only [Real.log_div (hx x hxx).ne' ha.ne'] <;>
      field_simp [ha.ne', (hx x hxx).ne'] <;> ring
  have hi : IntervalIntegrable
      (fun x : ℝ => (1/x)*(1/a-(1+Real.log (x/a))/x)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    have hI : ContinuousOn (fun x : ℝ => 1/x) (uIcc a b) :=
      continuousOn_const.div continuousOn_id (fun x hxx => (hx x hxx).ne')
    have hL : ContinuousOn (fun x : ℝ => Real.log (x/a)) (uIcc a b) :=
      (continuousOn_id.div_const a).log
        (fun x hxx => (div_pos (hx x hxx) ha).ne')
    exact hI.mul (continuousOn_const.sub
      ((continuousOn_const.add hL).div continuousOn_id
        (fun x hxx => (hx x hxx).ne')))
  rw [tripleTriangleMass, intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  dsimp [F]
  rw [Real.log_div (ha.trans_le hab).ne' ha.ne']
  ring

inductive OrderPattern where
  | strict
  | zwTie
  | uzTie
  | uzwTie
  deriving DecidableEq, Repr

/-- Four genuinely different original ordered integrals. In particular the
distinguished z^-1 is not symmetrized within an equal-bin block. -/
def orderedReferenceMass (p : OrderPattern) (tl tr ul ur zl zr wl wr : ℝ) : ℝ :=
  match p with
  | .strict => ∫ t in tl..tr, ∫ u in ul..ur, ∫ z in zl..zr, ∫ w in wl..wr,
      pairedFibreKernel t u z w
  | .zwTie => pairedLocalIntegral 80 zl tl tr ul ur zr
  | .uzTie => ∫ t in tl..tr, ∫ u in ul..ur, ∫ z in ul..u, ∫ w in wl..wr,
      pairedFibreKernel t u z w
  | .uzwTie => ∫ t in tl..tr, ∫ u in ul..ur, ∫ z in ul..u, ∫ w in ul..z,
      pairedFibreKernel t u z w

theorem orderedReferenceMass_strict_eq
    {tl tr ul ur zl zr wl wr : ℝ}
    (htl : 0 < tl) (htr : 0 < tr) (hul : 0 < ul) (hur : 0 < ur)
    (hzl : 0 < zl) (hz : zl ≤ zr) (hwl : 0 < wl) (hwr : 0 < wr) :
    orderedReferenceMass .strict tl tr ul ur zl zr wl wr =
      Real.log (tr/tl)*Real.log (ur/ul)*(1/zl-1/zr)*Real.log (wr/wl) := by
  have hi : (∫ z in zl..zr, 1/z^2) = 1/zl-1/zr := inverseSquareMass_eq hzl hz
  unfold orderedReferenceMass pairedFibreKernel
  simp only [← mul_assoc, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_mul_const]
  rw [integral_one_div_of_pos htl htr, integral_one_div_of_pos hul hur,
    integral_one_div_of_pos hwl hwr, hi]
  ring

theorem orderedReferenceMass_zwTie_eq
    {tl tr ul ur zl zr wl wr : ℝ}
    (htl : 0 < tl) (htr : 0 < tr) (hul : 0 < ul) (hur : 0 < ur)
    (hzl : 0 < zl) (hz : zl ≤ zr) :
    orderedReferenceMass .zwTie tl tr ul ur zl zr wl wr =
      Real.log (tr/tl)*Real.log (ur/ul)*(1/zl-(1+Real.log (zr/zl))/zr) := by
  simpa [orderedReferenceMass] using
    pairedLocalIntegral_eq (80 : ℝ) hzl hz htl htr hul hur

theorem orderedReferenceMass_uzTie_eq
    {tl tr ul ur zl zr wl wr : ℝ}
    (htl : 0 < tl) (htr : 0 < tr) (hul : 0 < ul) (hu : ul ≤ ur)
    (hwl : 0 < wl) (hwr : 0 < wr) :
    orderedReferenceMass .uzTie tl tr ul ur zl zr wl wr =
      Real.log (tr/tl)*Real.log (wr/wl)*
        (Real.log (ur/ul)/ul-1/ul+1/ur) := by
  have hi : (∫ u in ul..ur, (1/u)*(∫ z in ul..u, 1/z^2)) =
      lowerTriangleMass ul ur := by
    apply intervalIntegral.integral_congr
    intro u hu'
    rw [uIcc_of_le hu] at hu'
    rw [show (∫ z in ul..u, 1/z^2) = 1/ul-1/u from inverseSquareMass_eq hul hu'.1]
    rfl
  unfold orderedReferenceMass pairedFibreKernel
  simp only [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_mul_const]
  rw [integral_one_div_of_pos htl htr, integral_one_div_of_pos hwl hwr]
  simp only [← mul_assoc, intervalIntegral.integral_mul_const]
  rw [hi, lowerTriangleMass_eq hul hu]
  ring

theorem orderedReferenceMass_uzwTie_eq
    {tl tr ul ur zl zr wl wr : ℝ}
    (htl : 0 < tl) (htr : 0 < tr) (hul : 0 < ul) (hu : ul ≤ ur) :
    orderedReferenceMass .uzwTie tl tr ul ur zl zr wl wr =
      Real.log (tr/tl)*((Real.log (ur/ul)-2)/ul+(Real.log (ur/ul)+2)/ur) := by
  have hi : (∫ u in ul..ur, (1/u)*
      (∫ z in ul..u, (1/z^2)*(∫ w in ul..z, 1/w))) =
      tripleTriangleMass ul ur := by
    apply intervalIntegral.integral_congr
    intro u hu'
    rw [uIcc_of_le hu] at hu'
    rw [pairedFibreIntegral_eq_iterated hul hu'.1, pairedFibreIntegral_eq hul hu'.1]
    rfl
  unfold orderedReferenceMass pairedFibreKernel
  simp only [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_mul_const]
  rw [integral_one_div_of_pos htl htr, hi, tripleTriangleMass_eq hul hu]
  ring

end
end ImbalancedChen.Certificates.SavedParentFamily3947SourceOnly


/- SOURCEONLY / UNCOMPILED. Depends on the preceding reference-calculus
fragment. Finite checks use only rational data and real-log certificates. -/

namespace ImbalancedChen.Certificates.SavedParentFamily3947SourceOnly

structure ReferenceBox where
  pattern : OrderPattern
  tl : ℚ
  tr : ℚ
  ul : ℚ
  ur : ℚ
  zl : ℚ
  zr : ℚ
  wl : ℚ
  wr : ℚ
  deriving DecidableEq, Repr

def ReferenceBox.Valid (b : ReferenceBox) : Prop :=
  0 < b.tl ∧ b.tl ≤ b.tr ∧ 0 < b.ul ∧ b.ul ≤ b.ur ∧
  0 < b.zl ∧ b.zl ≤ b.zr ∧ 0 < b.wl ∧ b.wl ≤ b.wr

instance (b : ReferenceBox) : Decidable b.Valid := by
  unfold ReferenceBox.Valid
  infer_instance

structure MassLowerCertificate where
  box : ReferenceBox
  logT : RationalLogCertificate
  logU : RationalLogCertificate
  logZ : RationalLogCertificate
  logW : RationalLogCertificate
  lower : ℚ
  deriving DecidableEq, Repr

def MassLowerCertificate.profileLower (c : MassLowerCertificate) : ℚ :=
  match c.box.pattern with
  | .strict => 1/c.box.zl-1/c.box.zr
  | .zwTie => 1/c.box.zl-(1+c.logZ.upper)/c.box.zr
  | .uzTie => c.logU.lower/c.box.ul-1/c.box.ul+1/c.box.ur
  | .uzwTie => (c.logU.lower-2)/c.box.ul+(c.logU.lower+2)/c.box.ur

def MassLowerCertificate.productLower (c : MassLowerCertificate) : ℚ :=
  match c.box.pattern with
  | .strict => c.logT.lower*c.logU.lower*c.profileLower*c.logW.lower
  | .zwTie => c.logT.lower*c.logU.lower*c.profileLower
  | .uzTie => c.logT.lower*c.logW.lower*c.profileLower
  | .uzwTie => c.logT.lower*c.profileLower

def MassLowerCertificate.Valid (c : MassLowerCertificate) : Prop :=
  c.box.Valid ∧ c.logT.argument=c.box.tr/c.box.tl ∧
    c.logU.argument=c.box.ur/c.box.ul ∧ c.logZ.argument=c.box.zr/c.box.zl ∧
    c.logW.argument=c.box.wr/c.box.wl ∧
    c.logT.check=true ∧ c.logU.check=true ∧ c.logZ.check=true ∧ c.logW.check=true ∧
    0≤c.logT.lower ∧ 0≤c.logU.lower ∧ 0≤c.logW.lower ∧
    0≤c.profileLower ∧ 0<c.lower ∧ c.lower≤c.productLower

instance (c : MassLowerCertificate) : Decidable c.Valid := by
  unfold MassLowerCertificate.Valid
  infer_instance

def MassLowerCertificate.check (c : MassLowerCertificate) : Bool := decide c.Valid

noncomputable section

/-- A literal real iterated integral, retaining the correct equal-bin pattern. -/
def ReferenceBox.actualMass (b : ReferenceBox) : ℝ :=
  orderedReferenceMass b.pattern b.tl b.tr b.ul b.ur b.zl b.zr b.wl b.wr

def ReferenceBox.realProfile (b : ReferenceBox) : ℝ :=
  match b.pattern with
  | .strict => 1/(b.zl:ℝ)-1/(b.zr:ℝ)
  | .zwTie => 1/(b.zl:ℝ)-(1+Real.log ((b.zr:ℝ)/b.zl))/b.zr
  | .uzTie => Real.log ((b.ur:ℝ)/b.ul)/b.ul-1/(b.ul:ℝ)+1/(b.ur:ℝ)
  | .uzwTie => (Real.log ((b.ur:ℝ)/b.ul)-2)/b.ul+
      (Real.log ((b.ur:ℝ)/b.ul)+2)/b.ur

def ReferenceBox.realFormula (b : ReferenceBox) : ℝ :=
  match b.pattern with
  | .strict => Real.log ((b.tr:ℝ)/b.tl)*Real.log ((b.ur:ℝ)/b.ul)*
      b.realProfile*Real.log ((b.wr:ℝ)/b.wl)
  | .zwTie => Real.log ((b.tr:ℝ)/b.tl)*Real.log ((b.ur:ℝ)/b.ul)*b.realProfile
  | .uzTie => Real.log ((b.tr:ℝ)/b.tl)*Real.log ((b.wr:ℝ)/b.wl)*b.realProfile
  | .uzwTie => Real.log ((b.tr:ℝ)/b.tl)*b.realProfile

theorem ReferenceBox.actualMass_eq_formula (b : ReferenceBox) (hb : b.Valid) :
    b.actualMass=b.realFormula := by
  rcases hb with ⟨htl,ht,hul,hu,hzl,hz,hwl,hw⟩
  have htlR : (0:ℝ)<(b.tl:ℝ) := by exact_mod_cast htl
  have htrR : (0:ℝ)<(b.tr:ℝ) := by exact_mod_cast htl.trans_le ht
  have hulR : (0:ℝ)<(b.ul:ℝ) := by exact_mod_cast hul
  have hurR : (0:ℝ)<(b.ur:ℝ) := by exact_mod_cast hul.trans_le hu
  have huR : (b.ul:ℝ)≤(b.ur:ℝ) := by exact_mod_cast hu
  have hzlR : (0:ℝ)<(b.zl:ℝ) := by exact_mod_cast hzl
  have hzR : (b.zl:ℝ)≤(b.zr:ℝ) := by exact_mod_cast hz
  have hwlR : (0:ℝ)<(b.wl:ℝ) := by exact_mod_cast hwl
  have hwrR : (0:ℝ)<(b.wr:ℝ) := by exact_mod_cast hwl.trans_le hw
  cases hp : b.pattern with
  | strict =>
      simpa [ReferenceBox.actualMass,ReferenceBox.realFormula,ReferenceBox.realProfile,hp] using
        orderedReferenceMass_strict_eq
          (tl:=(b.tl:ℝ)) (tr:=(b.tr:ℝ)) (ul:=(b.ul:ℝ)) (ur:=(b.ur:ℝ))
          (zl:=(b.zl:ℝ)) (zr:=(b.zr:ℝ)) (wl:=(b.wl:ℝ)) (wr:=(b.wr:ℝ))
          htlR htrR hulR hurR hzlR hzR hwlR hwrR
  | zwTie =>
      simpa [ReferenceBox.actualMass,ReferenceBox.realFormula,ReferenceBox.realProfile,hp] using
        orderedReferenceMass_zwTie_eq
          (tl:=(b.tl:ℝ)) (tr:=(b.tr:ℝ)) (ul:=(b.ul:ℝ)) (ur:=(b.ur:ℝ))
          (zl:=(b.zl:ℝ)) (zr:=(b.zr:ℝ)) (wl:=(b.wl:ℝ)) (wr:=(b.wr:ℝ))
          htlR htrR hulR hurR hzlR hzR
  | uzTie =>
      simpa [ReferenceBox.actualMass,ReferenceBox.realFormula,ReferenceBox.realProfile,hp] using
        orderedReferenceMass_uzTie_eq
          (tl:=(b.tl:ℝ)) (tr:=(b.tr:ℝ)) (ul:=(b.ul:ℝ)) (ur:=(b.ur:ℝ))
          (zl:=(b.zl:ℝ)) (zr:=(b.zr:ℝ)) (wl:=(b.wl:ℝ)) (wr:=(b.wr:ℝ))
          htlR htrR hulR huR hwlR hwrR
  | uzwTie =>
      simpa [ReferenceBox.actualMass,ReferenceBox.realFormula,ReferenceBox.realProfile,hp] using
        orderedReferenceMass_uzwTie_eq
          (tl:=(b.tl:ℝ)) (tr:=(b.tr:ℝ)) (ul:=(b.ul:ℝ)) (ur:=(b.ur:ℝ))
          (zl:=(b.zl:ℝ)) (zr:=(b.zr:ℝ)) (wl:=(b.wl:ℝ)) (wr:=(b.wr:ℝ))
          htlR htrR hulR huR

/-- Certificate -> true reference-mass bound, with no integral bound premise. -/
theorem MassLowerCertificate.check_sound (c : MassLowerCertificate)
    (hc : c.check=true) : (c.lower:ℝ)≤c.box.actualMass := by
  have hv : c.Valid := of_decide_eq_true hc
  rcases hv with ⟨hbox,haT,haU,haZ,haW,hcT,hcU,hcZ,hcW,
    hnT,hnU,hnW,hnP,hlpos,hlo⟩
  have hT := c.logT.check_sound hcT
  have hU := c.logU.check_sound hcU
  have hZ := c.logZ.check_sound hcZ
  have hW := c.logW.check_sound hcW
  rw [haT,Rat.cast_div] at hT
  rw [haU,Rat.cast_div] at hU
  rw [haZ,Rat.cast_div] at hZ
  rw [haW,Rat.cast_div] at hW
  have hnTR : (0:ℝ)≤(c.logT.lower:ℝ) := by exact_mod_cast hnT
  have hnUR : (0:ℝ)≤(c.logU.lower:ℝ) := by exact_mod_cast hnU
  have hnWR : (0:ℝ)≤(c.logW.lower:ℝ) := by exact_mod_cast hnW
  have hnPR : (0:ℝ)≤(c.profileLower:ℝ) := by exact_mod_cast hnP
  have hulR : (0:ℝ)<(c.box.ul:ℝ) := by exact_mod_cast hbox.2.2.1
  have hurR : (0:ℝ)<(c.box.ur:ℝ) := by
    exact_mod_cast hbox.2.2.1.trans_le hbox.2.2.2.1
  have hzrR : (0:ℝ)<(c.box.zr:ℝ) := by
    exact_mod_cast hbox.2.2.2.2.1.trans_le hbox.2.2.2.2.2.1
  have hP : (c.profileLower:ℝ)≤c.box.realProfile := by
    cases hp : c.box.pattern with
    | strict => simp [MassLowerCertificate.profileLower,ReferenceBox.realProfile,hp]
    | zwTie =>
        simp only [MassLowerCertificate.profileLower,ReferenceBox.realProfile,hp,
          Rat.cast_sub,Rat.cast_div,Rat.cast_add,Rat.cast_one]
        exact sub_le_sub_left (div_le_div_of_nonneg_right
          (add_le_add_left hZ.2 1) hzrR.le) _
    | uzTie =>
        simp only [MassLowerCertificate.profileLower,ReferenceBox.realProfile,hp,
          Rat.cast_sub,Rat.cast_div,Rat.cast_add,Rat.cast_one]
        exact add_le_add_right (sub_le_sub_right
          (div_le_div_of_nonneg_right hU.1 hulR.le) _) _
    | uzwTie =>
        simp only [MassLowerCertificate.profileLower,ReferenceBox.realProfile,hp,
          Rat.cast_sub,Rat.cast_div,Rat.cast_add,Rat.cast_ofNat]
        exact add_le_add
          (div_le_div_of_nonneg_right (sub_le_sub_right hU.1 2) hulR.le)
          (div_le_div_of_nonneg_right (add_le_add_right hU.1 2) hurR.le)
  have hTN : 0≤Real.log ((c.box.tr:ℝ)/c.box.tl) := hnTR.trans hT.1
  have hUN : 0≤Real.log ((c.box.ur:ℝ)/c.box.ul) := hnUR.trans hU.1
  have hWN : 0≤Real.log ((c.box.wr:ℝ)/c.box.wl) := hnWR.trans hW.1
  have hPN : 0≤c.box.realProfile := hnPR.trans hP
  have hp : (c.productLower:ℝ)≤c.box.realFormula := by
    cases hs : c.box.pattern with
    | strict =>
        have hTU := mul_le_mul hT.1 hU.1 hnUR hTN
        have hTUP := mul_le_mul hTU hP hnPR (mul_nonneg hTN hUN)
        have hTUPW := mul_le_mul hTUP hW.1 hnWR
          (mul_nonneg (mul_nonneg hTN hUN) hPN)
        simpa [MassLowerCertificate.productLower,ReferenceBox.realFormula,hs] using hTUPW
    | zwTie =>
        have hTU := mul_le_mul hT.1 hU.1 hnUR hTN
        have hTUP := mul_le_mul hTU hP hnPR (mul_nonneg hTN hUN)
        simpa [MassLowerCertificate.productLower,ReferenceBox.realFormula,hs] using hTUP
    | uzTie =>
        have hTW := mul_le_mul hT.1 hW.1 hnWR hTN
        have hTWP := mul_le_mul hTW hP hnPR (mul_nonneg hTN hWN)
        simpa [MassLowerCertificate.productLower,ReferenceBox.realFormula,hs] using hTWP
    | uzwTie =>
        have hTP := mul_le_mul hT.1 hP hnPR hTN
        simpa [MassLowerCertificate.productLower,ReferenceBox.realFormula,hs] using hTP
  rw [ReferenceBox.actualMass_eq_formula c.box hbox]
  exact (show (c.lower:ℝ)≤(c.productLower:ℝ) by exact_mod_cast hlo).trans hp

theorem MassLowerCertificate.mass_pos (c : MassLowerCertificate) (hc : c.check=true) :
    0<c.box.actualMass := by
  have hv : c.Valid := of_decide_eq_true hc
  have hp : (0:ℝ)<(c.lower:ℝ) := by
    rcases hv with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hp,_⟩
    exact_mod_cast hp
  exact hp.trans_le (c.check_sound hc)

end
end ImbalancedChen.Certificates.SavedParentFamily3947SourceOnly


/- SOURCEONLY / UNCOMPILED. The family is exactly outer xy=(39,47), with
0≤iw≤iz≤47. No other method or priority branch is licensed. No1176 run.
OriginalRow retains the original seven-column schema (last integer was a
decimal string in JSON). Provenance equations are metadata, not estimates
for a density or for Buchstab. The actual finite certificates are separate. -/

namespace ImbalancedChen.Certificates.SavedParentFamily3947SourceOnly

open scoped BigOperators
open SavedParent394700ActualBuchstabSourceOnly

structure ParentIndex where
  z : Fin 48
  w : Fin 48
  hwz : w.val≤z.val
  deriving DecidableEq

def canonicalKey (i : ParentIndex) : List ℕ := [1,39,47,i.z.val,i.w.val]

theorem canonicalKey_injective : Function.Injective canonicalKey := by
  intro i j h
  have hz : i.z.val=j.z.val := by
    have h' := congrArg (fun a : List ℕ => a[3]!) h
    simpa [canonicalKey] using h'
  have hw : i.w.val=j.w.val := by
    have h' := congrArg (fun a : List ℕ => a[4]!) h
    simpa [canonicalKey] using h'
  have hz' : i.z=j.z := Fin.ext hz
  have hw' : i.w=j.w := Fin.ext hw
  cases i
  cases j
  cases hz'
  cases hw'
  rfl

def parentPairEquiv : ParentIndex ≃
    {p : Fin 48×Fin 48 // p.2.val≤p.1.val} where
  toFun i := ⟨(i.z,i.w),i.hwz⟩
  invFun p := ⟨p.val.1,p.val.2,p.property⟩
  left_inv i := by cases i; rfl
  right_inv p := by cases p; rfl

/-- Original combinations_with_replacement order: iw outer, then iz,
then iy. The selected iy=47 is NOT moved to a different enumeration. -/
def canonicalRank (i : ParentIndex) : ℕ :=
  (∑ a∈Finset.range i.w.val, Nat.fast_choose (49-a) 2) +
    (∑ b∈Finset.Ico i.w.val i.z.val, 48-b) + (47-i.z.val)
def canonicalOriginalIndex (i : ParentIndex) : ℕ :=
  249900+39*19600+canonicalRank i

structure OriginalRow where
  term : ℕ
  ix : ℕ
  iy : ℕ
  iz : ℕ
  iw : ℕ
  method : ℕ
  savingNumerator : ℤ
  deriving DecidableEq, Repr

def OriginalRow.key (r : OriginalRow) : List ℕ := [r.term,r.ix,r.iy,r.iz,r.iw]

/-- A future typed extraction supplies these EXACT original metadata equations.
This does not assert that an arbitrary rowAt or digest is the original file.
No full original row array is materialized by this generic theorem. -/
structure OriginalProvenance (rowAt : ℕ→Option OriginalRow) (priorityAt : ℕ→Bool)
    (i : ParentIndex) (r : OriginalRow) : Prop where
  rowEq : rowAt (canonicalOriginalIndex i)=some r
  keyEq : r.key=canonicalKey i
  methodEq : r.method=0
  priorityEq : priorityAt (canonicalOriginalIndex i)=false

def qScale : ℚ := 1208925819614629174706176
def anchorK : ℚ := 67619/10000
def currentK : ℚ := 8452171/1250000
def uniformC : ℚ := 70893/125000
def tlQ : ℚ := 881/4000
def trQ : ℚ := 111/500
def ulQ : ℚ := 36137/240000
def urQ : ℚ := 19/125
def binLo (j : ℕ) : ℚ := ((20016+343*j:ℕ):ℚ)/240000
def binHi (j : ℕ) : ℚ := ((20359+343*j:ℕ):ℚ)/240000

def familyPattern (i : ParentIndex) : OrderPattern :=
  if i.z.val<47 then
    if i.w.val<i.z.val then .strict else .zwTie
  else if i.w.val<47 then .uzTie else .uzwTie

def schemaBox (i : ParentIndex) : ReferenceBox where
  pattern := familyPattern i
  tl := tlQ
  tr := trQ
  ul := ulQ
  ur := urQ
  zl := binLo i.z.val
  zr := binHi i.z.val
  wl := binLo i.w.val
  wr := binHi i.w.val

def tieDivisor (i : ParentIndex) : ℕ :=
  match familyPattern i with
  | .strict => 1
  | .zwTie => 2
  | .uzTie => 2
  | .uzwTie => 6

/-- Original constant reciprocal lower-volume proxy, including the actual
2! or3! for each equal-bin block and the distinguished z slot squared. -/
def originalZProxy (i : ParentIndex) : ℚ :=
  (240000*420*343^3:ℚ)/
    ((tieDivisor i:ℚ)*53280*36480*((20359+343*i.z.val:ℕ):ℚ)^2*
      ((20359+343*i.w.val:ℕ):ℚ))

def originalSaving (r : OriginalRow) : ℚ := (r.savingNumerator:ℚ)/qScale
def queryMin (i : ParentIndex) : ℚ :=
  (1-trQ-urQ-binHi i.z.val-binHi i.w.val)/binHi i.z.val
def queryMax (i : ParentIndex) : ℚ :=
  (1-tlQ-ulQ-binLo i.z.val-binLo i.w.val)/binLo i.z.val

def ceilDiv (a b : ℤ) : ℤ := -((-a)/b)
def mesh : ℕ := 4096
def queryFirst (i : ParentIndex) : ℕ := (⌊queryMin i*mesh⌋:ℤ).toNat
def queryLast (i : ParentIndex) : ℕ := max (queryFirst i)
  ((⌈queryMax i*mesh⌉:ℤ).toNat-1)

structure OriginalUpperPrefix where
  lastNode : ℕ
  values : List ℤ
  deriving DecidableEq, Repr

def OriginalUpperPrefix.Valid (p : OriginalUpperPrefix) : Prop :=
  p.values.length=p.lastNode+1 ∧ ∀ k : Fin (p.lastNode+1),
    p.values.getD k.val 0 = if k.val≤2*mesh then (qScale:ℚ).num else
      let j := k.val-mesh
      p.values.getD (k.val-1) 0 +
        ceilDiv (ceilDiv (p.values.getD (j-1) 0*(mesh:ℤ)) ((j-1:ℕ):ℤ) +
          ceilDiv (p.values.getD j 0*(mesh:ℤ)) (j:ℤ)) (2*(mesh:ℤ)) +
        ceilDiv (qScale:ℚ).num (6*(mesh:ℤ)^3)

instance (p : OriginalUpperPrefix) : Decidable p.Valid := by
  unfold OriginalUpperPrefix.Valid
  infer_instance
def OriginalUpperPrefix.check (p : OriginalUpperPrefix) : Bool := decide p.Valid

/-- Exact source-recurrence uniqueness on any shared prefix. This statement
is about ORIGINAL INTEGER TABLE DATA; no Buchstab enclosure is inferred. -/
theorem OriginalUpperPrefix.same_entry (p q : OriginalUpperPrefix)
    (hp : p.Valid) (hq : q.Valid) :
    ∀ k : ℕ, k≤p.lastNode → k≤q.lastNode →
      p.values.getD k 0=q.values.getD k 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hkP hkQ
      let kp : Fin (p.lastNode+1) := ⟨k,by omega⟩
      let kq : Fin (q.lastNode+1) := ⟨k,by omega⟩
      have hpe := hp.2 kp
      have hqe := hq.2 kq
      change p.values.getD k 0 = _ at hpe
      change q.values.getD k 0 = _ at hqe
      rw [hpe,hqe]
      by_cases hk : k≤2*mesh
      · simp only [if_pos hk]
      · simp only [if_neg hk]
        have hprev := ih (k-1) (by norm_num [mesh] at hk; omega)
          (by omega) (by omega)
        have hdel := ih (k-mesh) (by norm_num [mesh] at hk ⊢; omega)
          (by omega) (by omega)
        have hdelprev := ih (k-mesh-1) (by norm_num [mesh] at hk ⊢; omega)
          (by omega) (by omega)
        simpa only [hprev,hdel,hdelprev]

/-- This reproduces the old one-dimensional QUERY EXPRESSION only. Its
soundness for the ACTUAL function comes from OmegaCoverCertificate, not
from the old trapezoid routine or the uniform cap in this expression. -/
def originalOmegaQuery (i : ParentIndex) (p : OriginalUpperPrefix) : ℤ :=
  let point := fun j : ℕ => ceilDiv (p.values.getD j 0*(mesh:ℤ)) (j:ℤ)
  let cap := ceilDiv (uniformC.num*(qScale:ℚ).num) uniformC.den
  let error := ceilDiv (qScale:ℚ).num (4*(mesh:ℤ)^2)
  ((List.range (queryLast i+1-queryFirst i)).map
    (fun k => let j:=queryFirst i+k; min cap (max (point j) (point (j+1))+error))).foldl max 0

/-- The ORIGINAL max(0,floor) rule, including zero-feedback cells. -/
def originalFeedbackFloor (i : ParentIndex) (r : OriginalRow) : ℤ :=
  max 0 (⌊qScale*(anchorK*uniformC*originalZProxy i-originalSaving r)/67619⌋:ℤ)
def originalSlopeQ (i : ParentIndex) (r : OriginalRow) : ℚ :=
  10000*(originalFeedbackFloor i r:ℚ)/qScale

structure SavedParentCertificate where
  mass : MassLowerCertificate
  omega : OmegaCoverCertificate
  originalUpper : OriginalUpperPrefix
  deriving DecidableEq, Repr

def SavedParentCertificate.Valid (c : SavedParentCertificate) (i : ParentIndex)
    (r : OriginalRow) : Prop :=
  c.mass.box=schemaBox i ∧ c.mass.check=true ∧
    c.omega.check (queryMin i) (queryMax i)=true ∧
    c.originalUpper.check=true ∧ queryLast i+1≤c.originalUpper.lastNode ∧
    c.omega.numerator=originalOmegaQuery i c.originalUpper ∧
    0≤r.savingNumerator ∧ 0≤c.omega.numerator ∧
    (c.omega.numerator:ℚ)/qScale≤uniformC ∧
    originalZProxy i≤c.mass.lower ∧
    originalSaving r≤anchorK*(uniformC-(c.omega.numerator:ℚ)/qScale)*c.mass.lower

instance (c : SavedParentCertificate) (i : ParentIndex) (r : OriginalRow) :
    Decidable (c.Valid i r) := by
  unfold SavedParentCertificate.Valid
  infer_instance
def SavedParentCertificate.check (c : SavedParentCertificate) (i : ParentIndex)
    (r : OriginalRow) : Bool := decide (c.Valid i r)

end ImbalancedChen.Certificates.SavedParentFamily3947SourceOnly


/- SOURCEONLY / UNCOMPILED. Append after the family schema/checker fragments.
The public theorem's numerical inputs are finite certificate checks and
the original record/method/priority METADATA equations. Neither an actual
density bound, actual omega enclosure, A/A' inequality nor integral lower
bound is an input. Original max(0,floor) feedback is preserved. -/

namespace ImbalancedChen.Certificates.SavedParentFamily3947SourceOnly

open Set MeasureTheory
open SavedParent394700ActualBuchstabSourceOnly

noncomputable section

theorem schemaBox_valid (i : ParentIndex) : (schemaBox i).Valid := by
  have hzl : 0<binLo i.z.val := by unfold binLo; positivity
  have hwl : 0<binLo i.w.val := by unfold binLo; positivity
  have hz : binLo i.z.val≤binHi i.z.val := by
    unfold binLo binHi
    push_cast
    linarith
  have hw : binLo i.w.val≤binHi i.w.val := by
    unfold binLo binHi
    push_cast
    linarith
  exact ⟨by norm_num [schemaBox,tlQ],by norm_num [schemaBox,tlQ,trQ],
    by norm_num [schemaBox,ulQ],by norm_num [schemaBox,ulQ,urQ],hzl,hz,hwl,hw⟩

private theorem binHi_le_ur {j : ℕ} (hj : j≤47) : binHi j≤urQ := by
  have hjR : (j:ℚ)≤47 := by exact_mod_cast hj
  unfold binHi urQ
  push_cast
  linarith

theorem query_bounds_nonneg (i : ParentIndex) : 0≤queryMin i ∧ 0≤queryMax i := by
  have hbox := schemaBox_valid i
  have hzr : 0<binHi i.z.val := hbox.2.2.2.2.1.trans_le hbox.2.2.2.2.2.1
  have hzU := binHi_le_ur (show i.z.val≤47 by omega)
  have hwU := binHi_le_ur (show i.w.val≤47 by omega)
  have hzlU : binLo i.z.val≤urQ := hbox.2.2.2.2.2.1.trans hzU
  have hwlU : binLo i.w.val≤urQ := hbox.2.2.2.2.2.2.2.trans hwU
  constructor
  · apply div_nonneg _ hzr.le
    norm_num [trQ,urQ] at hzU hwU ⊢
    linarith
  · apply div_nonneg _ hbox.2.2.2.2.1.le
    norm_num [tlQ,ulQ,urQ] at hzlU hwlU ⊢
    linarith

/-- The original Buchstab.upper guard is legal for every family member,
and the SAME eight actual-DDE rows through6 suffice for the whole family.
This is symbolic endpoint arithmetic, not a1176-certificate replay. -/
theorem family_query_inside_actual_DDE_range (i : ParentIndex) :
    2<queryMin i ∧ queryMax i<6 := by
  have hb := schemaBox_valid i
  have hzR : 0<binHi i.z.val := hb.2.2.2.2.1.trans_le hb.2.2.2.2.2.1
  have hzU := binHi_le_ur (show i.z.val≤47 by omega)
  have hwU := binHi_le_ur (show i.w.val≤47 by omega)
  have hzL : binLo 0≤binLo i.z.val := by
    unfold binLo
    push_cast
    have h : (0:ℚ)≤(i.z.val:ℚ) := by positivity
    linarith
  have hwL : binLo 0≤binLo i.w.val := by
    unfold binLo
    push_cast
    have h : (0:ℚ)≤(i.w.val:ℚ) := by positivity
    linarith
  constructor
  · apply (lt_div_iff₀ hzR).2
    norm_num [trQ,urQ] at hzU hwU ⊢
    linarith
  · apply (div_lt_iff₀ hb.2.2.2.2.1).2
    norm_num [tlQ,ulQ,binLo] at hzL hwL ⊢
    linarith
/-- Literal closure of the ORIGINAL U11 weak-index parent, including the
u/z/w tie walls. The data box/key is not replaced by a coarse rectangle. -/
def parentClosure (i : ParentIndex) : Set (Fin 4→ℝ) := {p |
  (tlQ:ℝ)≤p 0 ∧ p 0≤(trQ:ℝ) ∧ (ulQ:ℝ)≤p 1 ∧ p 1≤(urQ:ℝ) ∧
  (binLo i.z.val:ℝ)≤p 2 ∧ p 2≤(binHi i.z.val:ℝ) ∧
  (binLo i.w.val:ℝ)≤p 3 ∧ p 3≤(binHi i.w.val:ℝ) ∧
  p 3≤p 2 ∧ p 2≤p 1 ∧ p 1≤p 0}

def parentOpen (i : ParentIndex) : Set (Fin 4→ℝ) := {p |
  (tlQ:ℝ)<p 0 ∧ p 0<(trQ:ℝ) ∧ (ulQ:ℝ)<p 1 ∧ p 1<(urQ:ℝ) ∧
  (binLo i.z.val:ℝ)<p 2 ∧ p 2<(binHi i.z.val:ℝ) ∧
  (binLo i.w.val:ℝ)<p 3 ∧ p 3<(binHi i.w.val:ℝ) ∧
  p 3<p 2 ∧ p 2<p 1 ∧ p 1<p 0}

theorem parentOpen_subset_closure (i : ParentIndex) : parentOpen i⊆parentClosure i := by
  intro p hp
  rcases hp with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  exact ⟨h0.le,h1.le,h2.le,h3.le,h4.le,h5.le,h6.le,h7.le,h8.le,h9.le,h10.le⟩

theorem coordinates_pos {i : ParentIndex} {p : Fin 4→ℝ} (hp : p∈parentClosure i) :
    0<p 0 ∧ 0<p 1 ∧ 0<p 2 ∧ 0<p 3 := by
  have hbox := schemaBox_valid i
  have hzlR : (0:ℝ)<(binLo i.z.val:ℝ) := by exact_mod_cast hbox.2.2.2.2.1
  have hwlR : (0:ℝ)<(binLo i.w.val:ℝ) := by exact_mod_cast hbox.2.2.2.2.2.2.1
  exact ⟨(show (0:ℝ)<(tlQ:ℝ) by norm_num [tlQ]).trans_le hp.1,
    (show (0:ℝ)<(ulQ:ℝ) by norm_num [ulQ]).trans_le hp.2.2.1,
    hzlR.trans_le hp.2.2.2.2.1,hwlR.trans_le hp.2.2.2.2.2.2.1⟩

def argument (p : Fin 4→ℝ) : ℝ := (1-p 0-p 1-p 2-p 3)/p 2

theorem argument_range {i : ParentIndex} {p : Fin 4→ℝ} (hp : p∈parentClosure i) :
    argument p∈Icc (queryMin i:ℝ) (queryMax i:ℝ) := by
  have hzpos := (coordinates_pos hp).2.2.1
  have hb := schemaBox_valid i
  have hzl : (0:ℝ)<(binLo i.z.val:ℝ) := by exact_mod_cast hb.2.2.2.2.1
  have hzr : (0:ℝ)<(binHi i.z.val:ℝ) := by
    exact_mod_cast hb.2.2.2.2.1.trans_le hb.2.2.2.2.2.1
  have hmin0 : (0:ℝ)≤(queryMin i:ℝ) := by exact_mod_cast (query_bounds_nonneg i).1
  have hmax0 : (0:ℝ)≤(queryMax i:ℝ) := by exact_mod_cast (query_bounds_nonneg i).2
  rcases hp with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  have hminEq : (queryMin i:ℝ)*(binHi i.z.val:ℝ)=
      1-(trQ:ℝ)-(urQ:ℝ)-(binHi i.z.val:ℝ)-(binHi i.w.val:ℝ) := by
    simp only [queryMin,Rat.cast_div,Rat.cast_sub,Rat.cast_one]
    field_simp [hzr.ne']
    <;> ring
  have hmaxEq : (queryMax i:ℝ)*(binLo i.z.val:ℝ)=
      1-(tlQ:ℝ)-(ulQ:ℝ)-(binLo i.z.val:ℝ)-(binLo i.w.val:ℝ) := by
    simp only [queryMax,Rat.cast_div,Rat.cast_sub,Rat.cast_one]
    field_simp [hzl.ne']
    <;> ring
  constructor
  · apply (le_div_iff₀ hzpos).2
    have hm := mul_le_mul_of_nonneg_left h5 hmin0
    nlinarith only [hm,hminEq,h1,h3,h5,h7]
  · apply (div_le_iff₀ hzpos).2
    have hm := mul_le_mul_of_nonneg_left h4 hmax0
    nlinarith only [hm,hmaxEq,h0,h2,h4,h6]

/-- Genuine reference mass of the corresponding four original ordered
simplex/rectangle patterns. The following formulas are proved by real FTC. -/
def referenceMass (i : ParentIndex) : ℝ := (schemaBox i).actualMass
def K0 : ℝ := (anchorK:ℝ)
def K : ℝ := (currentK:ℝ)
def C : ℝ := (uniformC:ℝ)
def saving (r : OriginalRow) : ℝ := (originalSaving r:ℝ)
def slope (i : ParentIndex) (r : OriginalRow) : ℝ := (originalSlopeQ i r:ℝ)
def anchorMass (i : ParentIndex) (r : OriginalRow) : ℝ :=
  K0*C*referenceMass i-saving r
def currentMass (i : ParentIndex) (r : OriginalRow) : ℝ :=
  anchorMass i r-(K0-K)*slope i r
def savedDensity (i : ParentIndex) (r : OriginalRow) (z : ℝ) : ℝ :=
  currentMass i r/(referenceMass i*z)
def actualChenDensity (i : ParentIndex) (r : OriginalRow) (p : Fin 4→ℝ) : ℝ :=
  savedDensity i r (p 2)/(4*p 0*p 1*p 2*p 3)

private theorem slope_nonneg (i : ParentIndex) (r : OriginalRow) : 0≤slope i r := by
  have hd : 0≤originalFeedbackFloor i r := le_max_left _ _
  have hdQ : (0:ℚ)≤(originalFeedbackFloor i r:ℚ) := by exact_mod_cast hd
  have hs : (0:ℚ)≤originalSlopeQ i r :=
    div_nonneg (mul_nonneg (by norm_num) hdQ) (by norm_num [qScale])
  exact_mod_cast hs

/-- Pure exact original-floor arithmetic. This is used only for the nonzero
floor branch; the zero branch is handled separately using the actual A≥0. -/
private theorem slope_le_proxy_of_nonzero (i : ParentIndex) (r : OriginalRow)
    (hd0 : originalFeedbackFloor i r≠0) :
    originalSlopeQ i r≤uniformC*originalZProxy i-originalSaving r/anchorK := by
  let x : ℚ := qScale*(anchorK*uniformC*originalZProxy i-originalSaving r)/67619
  have hf0 : 0≤(⌊x⌋:ℤ) := by
    by_contra hn
    have hz : max 0 (⌊x⌋:ℤ)=0 := max_eq_left (le_of_not_ge hn)
    exact hd0 (by simpa [originalFeedbackFloor,x] using hz)
  have he : originalFeedbackFloor i r=(⌊x⌋:ℤ) := by
    exact max_eq_right hf0
  have hf : (originalFeedbackFloor i r:ℚ)≤x := by
    rw [he]
    exact Int.floor_le x
  unfold originalSlopeQ
  calc
    10000*(originalFeedbackFloor i r:ℚ)/qScale≤10000*x/qScale :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hf (by norm_num))
        (by norm_num [qScale])
    _=uniformC*originalZProxy i-originalSaving r/anchorK := by
      dsimp [x]
      norm_num [qScale,anchorK]
      <;> ring

structure ParentLicense (i : ParentIndex) (r : OriginalRow) (num : ℤ) : Prop where
  mass_pos : 0<referenceMass i
  original_slope_nonneg : 0≤slope i r
  original_slope_le_anchor : slope i r≤anchorMass i r/K0
  anchor_ge_original_omega : K0*((num:ℝ)/(qScale:ℝ))*referenceMass i≤anchorMass i r
  current_ge_scaled_anchor : (K/K0)*anchorMass i r≤currentMass i r
  current_ge_original_omega : K*((num:ℝ)/(qScale:ℝ))*referenceMass i≤currentMass i r
  actual_density : ∀ p∈parentClosure i,
    (K/4)*LiLiuPrereqBuchstab.buchstab (argument p)*
      pairedFibreKernel (p 0) (p 1) (p 2) (p 3)≤actualChenDensity i r p

/-- Reusable original method0/no-priority certificate -> ACTUAL density.
The rowAt/priorityAt equations are the exact source metadata interface.
All numerical estimates are derived from finite log/omega/List checks. -/
theorem SavedParentCertificate.check_sound
    (rowAt : ℕ→Option OriginalRow) (priorityAt : ℕ→Bool)
    (i : ParentIndex) (r : OriginalRow) (c : SavedParentCertificate)
    (hp : OriginalProvenance rowAt priorityAt i r) (hc : c.check i r=true) :
    ParentLicense i r c.omega.numerator := by
  have hv : c.Valid i r := of_decide_eq_true hc
  rcases hv with ⟨hbox,hmass,homega,hprefix,hprefixlen,hnumEq,hg0,hn0,hnC,hproxy,hg⟩
  have hL : (c.mass.lower:ℝ)≤referenceMass i := by
    have h := c.mass.check_sound hmass
    rw [hbox] at h
    exact h
  have hZ : 0<referenceMass i := by
    have h := c.mass.mass_pos hmass
    rw [hbox] at h
    exact h
  have hProxyZ : (originalZProxy i:ℝ)≤referenceMass i :=
    (show (originalZProxy i:ℝ)≤(c.mass.lower:ℝ) by exact_mod_cast hproxy).trans hL
  have hK0 : 0<K0 := by norm_num [K0,anchorK]
  have hK : 0<K ∧ K≤K0 := by norm_num [K,K0,currentK,anchorK]
  have hC : 0≤C := by norm_num [C,uniformC]
  let W : ℝ := (c.omega.numerator:ℝ)/(qScale:ℝ)
  have hW0 : 0≤W := by
    have hnR : (0:ℝ)≤(c.omega.numerator:ℝ) := by exact_mod_cast hn0
    exact div_nonneg hnR (by norm_num [qScale])
  have hWC : W≤C := by exact_mod_cast hnC
  have hDelta : 0≤K0*(C-W) := mul_nonneg hK0.le (sub_nonneg.mpr hWC)
  have hgR : saving r≤K0*(C-W)*(c.mass.lower:ℝ) := by
    exact_mod_cast hg
  have hgZ : saving r≤K0*(C-W)*referenceMass i :=
    hgR.trans (mul_le_mul_of_nonneg_left hL hDelta)
  have hA : K0*W*referenceMass i≤anchorMass i r := by
    unfold anchorMass
    nlinarith only [hgZ]
  have hA0 : 0≤anchorMass i r :=
    (mul_nonneg (mul_nonneg hK0.le hW0) hZ.le).trans hA
  have hSlope : slope i r≤anchorMass i r/K0 := by
    by_cases hd0 : originalFeedbackFloor i r=0
    · have hs0 : slope i r=0 := by simp [slope,originalSlopeQ,hd0]
      rw [hs0]
      exact div_nonneg hA0 hK0.le
    · have hsq := slope_le_proxy_of_nonzero i r hd0
      have hsR : slope i r≤C*(originalZProxy i:ℝ)-saving r/K0 := by
        exact_mod_cast hsq
      calc
        slope i r≤C*(originalZProxy i:ℝ)-saving r/K0 := hsR
        _≤C*referenceMass i-saving r/K0 :=
          sub_le_sub_right (mul_le_mul_of_nonneg_left hProxyZ hC) _
        _=anchorMass i r/K0 := by
          unfold anchorMass
          field_simp [hK0.ne']
          <;> ring
  have hScale : (K/K0)*anchorMass i r≤currentMass i r := by
    have hm : 0≤(K0-K)*(anchorMass i r/K0-slope i r) :=
      mul_nonneg (sub_nonneg.mpr hK.2) (sub_nonneg.mpr hSlope)
    have he : currentMass i r-(K/K0)*anchorMass i r=
        (K0-K)*(anchorMass i r/K0-slope i r) := by
      unfold currentMass
      field_simp [hK0.ne']
      <;> ring
    linarith only [hm,he]
  have hCurrent : K*W*referenceMass i≤currentMass i r := by
    calc
      K*W*referenceMass i=(K/K0)*(K0*W*referenceMass i) := by
        field_simp [hK0.ne']
        <;> ring
      _≤(K/K0)*anchorMass i r :=
        mul_le_mul_of_nonneg_left hA (div_nonneg hK.1.le hK0.le)
      _≤currentMass i r := hScale
  refine ⟨hZ,slope_nonneg i r,hSlope,hA,hScale,hCurrent,?_⟩
  intro p hparent
  rcases coordinates_pos hparent with ⟨ht,hu,hz,hw⟩
  have hOm0 := c.omega.check_sound (queryMin i) (queryMax i) homega (argument_range hparent)
  have hOm : LiLiuPrereqBuchstab.buchstab (argument p)≤W := by
    convert hOm0 using 1 <;> norm_num [W,qScale,SavedParent394700ActualBuchstabSourceOnly.scale]
  have hdens : K*W/p 2≤savedDensity i r (p 2) := by
    unfold savedDensity
    apply (le_div_iff₀ (mul_pos hZ hz)).2
    have he : K*W/p 2*(referenceMass i*p 2)=K*W*referenceMass i := by
      field_simp [hz.ne']
      <;> ring
    rw [he]
    exact hCurrent
  have hdensActual : K*LiLiuPrereqBuchstab.buchstab (argument p)/p 2≤savedDensity i r (p 2) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hOm hK.1.le) hz.le).trans hdens
  have hf : 0≤1/(4*p 0*p 1*p 2*p 3) := by positivity
  calc
    (K/4)*LiLiuPrereqBuchstab.buchstab (argument p)*
        pairedFibreKernel (p 0) (p 1) (p 2) (p 3)=
        (K*LiLiuPrereqBuchstab.buchstab (argument p)/p 2)*
          (1/(4*p 0*p 1*p 2*p 3)) := by
      rw [pairedFibreKernel_eq]
      field_simp [ht.ne',hu.ne',hz.ne',hw.ne']
      <;> ring
    _≤savedDensity i r (p 2)*(1/(4*p 0*p 1*p 2*p 3)) :=
      mul_le_mul_of_nonneg_right hdensActual hf
    _=actualChenDensity i r p := by rw [actualChenDensity]; ring

end
end ImbalancedChen.Certificates.SavedParentFamily3947SourceOnly


/- SOURCEONLY / UNCOMPILED. Geometry and reference-mass pairing for the
original schema; this is not a coarse inventory-count density assertion. -/

namespace ImbalancedChen.Certificates.SavedParentFamily3947SourceOnly

open Set MeasureTheory
open scoped Interval

noncomputable section

private theorem binHi_le_binLo_of_lt {j k : ℕ} (hjk : j<k) : binHi j≤binLo k := by
  have hR : (j:ℚ)+1≤(k:ℚ) := by exact_mod_cast (Nat.succ_le_iff.mpr hjk)
  unfold binHi binLo
  push_cast
  linarith

private theorem binOpen_index_unique {j k : ℕ} {x : ℝ}
    (hj : (binLo j:ℝ)<x ∧ x<(binHi j:ℝ))
    (hk : (binLo k:ℝ)<x ∧ x<(binHi k:ℝ)) : j=k := by
  rcases lt_trichotomy j k with h | h | h
  · have hc : (binHi j:ℝ)≤(binLo k:ℝ) := by exact_mod_cast binHi_le_binLo_of_lt h
    exact False.elim (by linarith [hj.2,hk.1])
  · exact h
  · have hc : (binHi k:ℝ)≤(binLo j:ℝ) := by exact_mod_cast binHi_le_binLo_of_lt h
    exact False.elim (by linarith [hk.2,hj.1])

/-- Distinct original refinement keys give disjoint open physical parents. -/
theorem parentOpen_disjoint {i j : ParentIndex} (hij : i≠j) :
    Disjoint (parentOpen i) (parentOpen j) := by
  apply Set.disjoint_left.mpr
  intro p hi hj
  have hz := binOpen_index_unique
    ⟨hi.2.2.2.2.1,hi.2.2.2.2.2.1⟩ ⟨hj.2.2.2.2.1,hj.2.2.2.2.2.1⟩
  have hw := binOpen_index_unique
    ⟨hi.2.2.2.2.2.2.1,hi.2.2.2.2.2.2.2.1⟩
    ⟨hj.2.2.2.2.2.2.1,hj.2.2.2.2.2.2.2.1⟩
  apply hij
  apply canonicalKey_injective
  simp only [canonicalKey,hz,hw]

/-- Actual cylindrical ordered-parent reference integral. The two minima
retain the original u>z>w constraints even when bins coincide. -/
def originalOrderedReferenceMass (i : ParentIndex) : ℝ :=
  ∫ t in (tlQ:ℝ)..(trQ:ℝ), ∫ u in (ulQ:ℝ)..(urQ:ℝ),
    ∫ z in (binLo i.z.val:ℝ)..min (binHi i.z.val:ℝ) u,
      ∫ w in (binLo i.w.val:ℝ)..min (binHi i.w.val:ℝ) z,
        pairedFibreKernel t u z w

private theorem last_bin : binLo 47=ulQ ∧ binHi 47=urQ := by
  norm_num [binLo,binHi,ulQ,urQ]

/-- The four real FTC models are exactly paired with the ORIGINAL parent,
including both the two-slot and three-slot ties. No reference-mass estimate
is assumed when proving this equality. -/
theorem referenceMass_eq_original_ordered (i : ParentIndex) :
    referenceMass i=originalOrderedReferenceMass i := by
  have hbox := schemaBox_valid i
  have huR : (ulQ:ℝ)≤(urQ:ℝ) := by norm_num [ulQ,urQ]
  have hzR : (binLo i.z.val:ℝ)≤(binHi i.z.val:ℝ) := by
    exact_mod_cast hbox.2.2.2.2.2.1
  symm
  by_cases hz : i.z.val<47
  · have hzU : (binHi i.z.val:ℝ)≤(ulQ:ℝ) := by
      have h := binHi_le_binLo_of_lt hz
      rw [last_bin.1] at h
      exact_mod_cast h
    by_cases hw : i.w.val<i.z.val
    · have hwZ : (binHi i.w.val:ℝ)≤(binLo i.z.val:ℝ) := by
        exact_mod_cast binHi_le_binLo_of_lt hw
      have hpat : familyPattern i=.strict := by simp [familyPattern,hz,hw]
      simp only [originalOrderedReferenceMass,referenceMass,ReferenceBox.actualMass,
        schemaBox,hpat,orderedReferenceMass]
      apply intervalIntegral.integral_congr
      intro t ht
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le huR] at hu
      rw [min_eq_left (hzU.trans hu.1)]
      apply intervalIntegral.integral_congr
      intro z hzz
      rw [uIcc_of_le hzR] at hzz
      rw [min_eq_left (hwZ.trans hzz.1)]
    · have hwe : i.w.val=i.z.val := by have h := i.hwz; omega
      have hpat : familyPattern i=.zwTie := by simp [familyPattern,hz,hw]
      simp only [originalOrderedReferenceMass,referenceMass,ReferenceBox.actualMass,
        schemaBox,hpat,orderedReferenceMass,pairedLocalIntegral]
      norm_num only [show (80:ℝ)/80=1 by norm_num,one_mul]
      rw [hwe]
      apply intervalIntegral.integral_congr
      intro t ht
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le huR] at hu
      rw [min_eq_left (hzU.trans hu.1)]
      apply intervalIntegral.integral_congr
      intro z hzz
      rw [uIcc_of_le hzR] at hzz
      rw [min_eq_right hzz.2]
  · have hze : i.z.val=47 := by have h := i.z.isLt; omega
    by_cases hw : i.w.val<47
    · have hwU : (binHi i.w.val:ℝ)≤(ulQ:ℝ) := by
        have h := binHi_le_binLo_of_lt hw
        rw [last_bin.1] at h
        exact_mod_cast h
      have hpat : familyPattern i=.uzTie := by simp [familyPattern,hz,hw]
      simp only [originalOrderedReferenceMass,referenceMass,ReferenceBox.actualMass,
        schemaBox,hpat,orderedReferenceMass,hze,last_bin.1,last_bin.2]
      apply intervalIntegral.integral_congr
      intro t ht
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le huR] at hu
      rw [min_eq_right hu.2]
      apply intervalIntegral.integral_congr
      intro z hzz
      rw [uIcc_of_le hu.1] at hzz
      rw [min_eq_left (hwU.trans hzz.1)]
    · have hwe : i.w.val=47 := by have h := i.w.isLt; omega
      have hpat : familyPattern i=.uzwTie := by simp [familyPattern,hz,hw]
      simp only [originalOrderedReferenceMass,referenceMass,ReferenceBox.actualMass,
        schemaBox,hpat,orderedReferenceMass,hze,hwe,last_bin.1,last_bin.2]
      apply intervalIntegral.integral_congr
      intro t ht
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le huR] at hu
      rw [min_eq_right hu.2]
      apply intervalIntegral.integral_congr
      intro z hzz
      rw [uIcc_of_le hu.1] at hzz
      rw [min_eq_right (hzz.2.trans hu.2)]

end
end ImbalancedChen.Certificates.SavedParentFamily3947SourceOnly

/- SOURCEONLY mathematical tail; exactly one new lemma.
Append this tail once after the frozen family V3 context (SHA recorded in CP).
It uses only the existing public geometric definitions. No data-table hash is
used as a Lean proof premise. This closes one original physical-domain bridge;
it does not prove a complete typed cover, a numerical total, or full C. -/

namespace ImbalancedChen.Certificates.SavedParentFamily3947SourceOnly

/-- The generic family's first weak-index parent is exactly the original
closed U11 parent with key [1,39,47,0,0]. The extra generic order constraints
follow from the original, unchanged endpoint gaps. -/
theorem first_original_parent_closed_domain_exact :
    parentClosure (⟨0, 0, by decide⟩ : ParentIndex) =
      SavedParent394700SourceOnly.parentClosure := by
  ext p
  change
    ((tlQ : ℝ) ≤ p 0 ∧ p 0 ≤ (trQ : ℝ) ∧
      (ulQ : ℝ) ≤ p 1 ∧ p 1 ≤ (urQ : ℝ) ∧
      (binLo 0 : ℝ) ≤ p 2 ∧ p 2 ≤ (binHi 0 : ℝ) ∧
      (binLo 0 : ℝ) ≤ p 3 ∧ p 3 ≤ (binHi 0 : ℝ) ∧
      p 3 ≤ p 2 ∧ p 2 ≤ p 1 ∧ p 1 ≤ p 0) ↔
    (SavedParent394700SourceOnly.tl ≤ p 0 ∧
      p 0 ≤ SavedParent394700SourceOnly.tr ∧
      SavedParent394700SourceOnly.ul ≤ p 1 ∧
      p 1 ≤ SavedParent394700SourceOnly.ur ∧
      SavedParent394700SourceOnly.a ≤ p 3 ∧ p 3 ≤ p 2 ∧
      p 2 ≤ SavedParent394700SourceOnly.b)
  have htl : (tlQ : ℝ) = SavedParent394700SourceOnly.tl := by
    norm_num [tlQ, SavedParent394700SourceOnly.tl]
  have htr : (trQ : ℝ) = SavedParent394700SourceOnly.tr := by
    norm_num [trQ, SavedParent394700SourceOnly.tr]
  have hul : (ulQ : ℝ) = SavedParent394700SourceOnly.ul := by
    norm_num [ulQ, SavedParent394700SourceOnly.ul]
  have hur : (urQ : ℝ) = SavedParent394700SourceOnly.ur := by
    norm_num [urQ, SavedParent394700SourceOnly.ur]
  have hlo : (binLo 0 : ℝ) = SavedParent394700SourceOnly.a := by
    norm_num [binLo, SavedParent394700SourceOnly.a]
  have hhi : (binHi 0 : ℝ) = SavedParent394700SourceOnly.b := by
    norm_num [binHi, SavedParent394700SourceOnly.b]
  rw [htl, htr, hul, hur, hlo, hhi]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h0, h1, h2, h3, h6, h8, h5⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
    have hbu : SavedParent394700SourceOnly.b ≤
        SavedParent394700SourceOnly.ul := by
      norm_num [SavedParent394700SourceOnly.b, SavedParent394700SourceOnly.ul]
    have hut : SavedParent394700SourceOnly.ur ≤
        SavedParent394700SourceOnly.tl := by
      norm_num [SavedParent394700SourceOnly.ur, SavedParent394700SourceOnly.tl]
    exact ⟨h0, h1, h2, h3, h4.trans h5, h6, h4, h5.trans h6, h5,
      h6.trans (hbu.trans h2), h3.trans (hut.trans h0)⟩

end ImbalancedChen.Certificates.SavedParentFamily3947SourceOnly

/- SOURCEONLY / UNCOMPILED. Append once after frozen family V3 and the
first_original_parent_closed_domain_exact tail. This pays the CLOSED COVER
obligation for ALL original outer-(39,47) weak-index parents. It does not
materialize the original rowAt/priorityAt arrays or certify all branches.
The closed-bin overlap at knots is retained; no integral is summed here. -/

namespace ImbalancedChen.Certificates.SavedParentFamily3947SourceOnly

open Set

/-- A finite contiguous CLOSED chain covers its entire endpoint interval.
The witness need not be unique at a knot. No coverage is a premise. -/
theorem closed_chain_cover
    (lo hi : ℕ → ℝ) (hadj : ∀ j, hi j = lo (j+1)) :
    ∀ k x, lo 0 ≤ x → x ≤ hi k →
      ∃ j, j ≤ k ∧ lo j ≤ x ∧ x ≤ hi j := by
  intro k
  induction k with
  | zero =>
      intro x hlo hhi
      exact ⟨0, le_rfl, hlo, hhi⟩
  | succ k ih =>
      intro x hlo hhi
      by_cases hx : x ≤ hi k
      · rcases ih x hlo hx with ⟨j, hj, hjlo, hjhi⟩
        exact ⟨j, Nat.le_succ_of_le hj, hjlo, hjhi⟩
      · refine ⟨k+1, le_rfl, ?_, hhi⟩
        have hx' : hi k < x := lt_of_not_ge hx
        rw [hadj k] at hx'
        exact hx'.le

theorem original_closed_bin_adjacent (j : ℕ) :
    (binHi j : ℝ) = (binLo (j+1) : ℝ) := by
  have hQ : binHi j = binLo (j+1) := by
    unfold binHi binLo
    push_cast
    ring
  exact_mod_cast hQ

theorem original_closed_bin_first_le (j : ℕ) :
    (binLo 0 : ℝ) ≤ (binLo j : ℝ) := by
  have hQ : binLo 0 ≤ binLo j := by
    unfold binLo
    push_cast
    have hj : (0 : ℚ) ≤ (j : ℚ) := by positivity
    linarith
  exact_mod_cast hQ

theorem original_closed_bin_last : (binHi 47 : ℝ) = (urQ : ℝ) := by
  norm_num [binHi, urQ]

/-- An actual coordinate in an original prefix receives an original bin.
In particular, choosing w only after z gives iw≤iz even at a knot. -/
theorem original_closed_bin_prefix (k : ℕ) (x : ℝ)
    (hlo : (binLo 0 : ℝ) ≤ x) (hhi : x ≤ (binHi k : ℝ)) :
    ∃ j, j ≤ k ∧ (binLo j : ℝ) ≤ x ∧ x ≤ (binHi j : ℝ) := by
  exact closed_chain_cover (fun j => (binLo j : ℝ))
    (fun j => (binHi j : ℝ)) original_closed_bin_adjacent k x hlo hhi

/-- The original U11 retained slab when the x bin is39 and the u bin47.
Its lower boundary is20016/240000, its u endpoints36137/240000 and
36480/240000, and its x endpoints52860/240000 and53280/240000.
The inequalities are the original physical ordering, all CLOSED. -/
def originalFamilyClosedDomain : Set (Fin 4 → ℝ) := {p |
  (tlQ : ℝ) ≤ p 0 ∧ p 0 ≤ (trQ : ℝ) ∧
  (ulQ : ℝ) ≤ p 1 ∧ p 1 ≤ (urQ : ℝ) ∧
  (binLo 0 : ℝ) ≤ p 3 ∧ p 3 ≤ p 2 ∧ p 2 ≤ p 1 ∧ p 1 ≤ p 0}

/-- Typed compiler from the ORIGINAL physical slab to its complete weak
index family. The unchanged ParentIndex/canonicalKey/canonicalRank interface
retains all iw≤iz≤47 parents, including zw, uz and uzw tied simplices. -/
theorem originalFamilyClosedDomain_mem_iff (p : Fin 4 → ℝ) :
    p ∈ originalFamilyClosedDomain ↔ ∃ i : ParentIndex, p ∈ parentClosure i := by
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    have hz0 : (binLo 0 : ℝ) ≤ p 2 := h4.trans h5
    have hz47 : p 2 ≤ (binHi 47 : ℝ) := by
      rw [original_closed_bin_last]
      exact h6.trans h3
    rcases original_closed_bin_prefix 47 (p 2) hz0 hz47 with
      ⟨iz, hiz, hzlo, hzhi⟩
    rcases original_closed_bin_prefix iz (p 3) h4 (h5.trans hzhi) with
      ⟨iw, hiw, hwlo, hwhi⟩
    let i : ParentIndex :=
      ⟨⟨iz, by omega⟩, ⟨iw, by omega⟩, hiw⟩
    refine ⟨i, ?_⟩
    exact ⟨h0, h1, h2, h3, hzlo, hzhi, hwlo, hwhi, h5, h6, h7⟩
  · rintro ⟨i, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h0, h1, h2, h3,
      (original_closed_bin_first_le i.w.val).trans h6, h8, h9, h10⟩

/-- Exact set equality; the right side ranges over every original family
index. It is a closed cover and does not assert disjointness at knots. -/
theorem originalFamilyClosedDomain_eq_iUnion :
    originalFamilyClosedDomain = ⋃ i : ParentIndex, parentClosure i := by
  ext p
  simp only [Set.mem_iUnion]
  exact originalFamilyClosedDomain_mem_iff p

/-- The actual argument on the entire retained slab passes the unchanged
original rational query guard and stays in the existing DDE range. -/
theorem originalFamily_actual_argument_range
    (p : Fin 4 → ℝ) (hp : p ∈ originalFamilyClosedDomain) :
    2 < argument p ∧ argument p < 6 := by
  rcases (originalFamilyClosedDomain_mem_iff p).1 hp with ⟨i, hi⟩
  have hr := argument_range hi
  have hq := family_query_inside_actual_DDE_range i
  have hlo : (2 : ℝ) < (queryMin i : ℝ) := by exact_mod_cast hq.1
  have hhi : (queryMax i : ℝ) < (6 : ℝ) := by exact_mod_cast hq.2
  exact ⟨hlo.trans_le hr.1, hr.2.trans_lt hhi⟩

/-- Consumer bridge: the finite checks and exact original row/priority
metadata suffice on the whole retained family domain, with no COVER
hypothesis. This is conditional on the existing per-index metadata/checks;
it does not assert that all original rows select the method0 branch. -/
theorem originalFamily_checked_density_on_closed_domain
    (rowAt : ℕ → Option OriginalRow) (priorityAt : ℕ → Bool)
    (row : ParentIndex → OriginalRow) (cert : ParentIndex → SavedParentCertificate)
    (hrow : ∀ i, OriginalProvenance rowAt priorityAt i (row i))
    (hcheck : ∀ i, (cert i).check i (row i) = true)
    (p : Fin 4 → ℝ) (hp : p ∈ originalFamilyClosedDomain) :
    ∃ i : ParentIndex, p ∈ parentClosure i ∧
      (K/4)*LiLiuPrereqBuchstab.buchstab (argument p)*
        pairedFibreKernel (p 0) (p 1) (p 2) (p 3) ≤
          actualChenDensity i (row i) p := by
  rcases (originalFamilyClosedDomain_mem_iff p).1 hp with ⟨i, hi⟩
  refine ⟨i, hi, ?_⟩
  exact (SavedParentCertificate.check_sound rowAt priorityAt i (row i)
    (cert i) (hrow i) (hcheck i)).actual_density p hi

end ImbalancedChen.Certificates.SavedParentFamily3947SourceOnly
