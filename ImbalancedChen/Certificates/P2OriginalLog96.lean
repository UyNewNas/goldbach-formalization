import ImbalancedChen.Certificates.P2OriginalLog96Series

/-!
# The author's 96-term W224-to-P160 logarithm producer

Literal source: `corpus-renewal-paired-certificate-v2-20261010.py`,
blob `ad918b5084fb83ff58d7cbb8cb23fa3e4e47ddce`, lines 50–61, in the
frozen 1106 manuscript repository at `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`.
The integer updates, their order, and the final directed shift are retained.
The source-shaped fold is related to structural recursion for every input.
Soundness uses the existing rational logarithm certificate and its remainder.
-/

namespace ImbalancedChen.Certificates.P2OriginalLog96

open scoped BigOperators

/-- The exact upper division expression appearing in the original loop. -/
def upperDiv (n d : ℤ) : ℤ := (n + d - 1) / d

private theorem lower_div_le (n d : ℤ) (hd : 0 < d) :
    ((n / d : ℤ) : ℚ) ≤ (n : ℚ) / (d : ℚ) := by
  have h := Int.floor_le ((n : ℚ) / (d : ℚ))
  rw [Int.floor_div_cast_of_nonneg hd.le, Int.floor_intCast] at h
  exact h

private theorem le_upper_div (n d : ℤ) (hd : 0 < d) :
    (n : ℚ) / (d : ℚ) ≤ (upperDiv n d : ℚ) := by
  have hr := Int.emod_lt_of_pos (n + d - 1) hd
  have he := Int.emod_add_mul_ediv (n + d - 1) d
  have hi : n ≤ ((n + d - 1) / d) * d := by nlinarith
  apply (div_le_iff₀ (show (0 : ℚ) < d by exact_mod_cast hd)).mpr
  exact_mod_cast hi

def decode (n : ℤ) : ℚ := (n : ℚ) / (workScale : ℚ)

structure Bounds where
  lo : ℤ
  hi : ℤ

def Bounds.Contains (b : Bounds) (x : ℚ) : Prop :=
  decode b.lo ≤ x ∧ x ≤ decode b.hi

def Bounds.add (a b : Bounds) : Bounds := ⟨a.lo + b.lo, a.hi + b.hi⟩

private theorem add_contains {a b : Bounds} {x y : ℚ}
    (ha : a.Contains x) (hb : b.Contains y) : (a.add b).Contains (x + y) := by
  constructor
  · simpa only [Bounds.add, decode, Int.cast_add, add_div] using add_le_add ha.1 hb.1
  · simpa only [Bounds.add, decode, Int.cast_add, add_div] using add_le_add ha.2 hb.2

def positiveMul (a b : Bounds) : Bounds :=
  ⟨a.lo * b.lo / workScale, upperDiv (a.hi * b.hi) workScale⟩

private theorem positiveMul_lo_nonneg {a b : Bounds}
    (ha : 0 ≤ a.lo) (hb : 0 ≤ b.lo) : 0 ≤ (positiveMul a b).lo :=
  Int.ediv_nonneg (mul_nonneg ha hb) workScale_pos.le

private theorem positiveMul_contains {a b : Bounds} {x y : ℚ}
    (ha : a.Contains x) (hb : b.Contains y) (ha0 : 0 ≤ a.lo) (hb0 : 0 ≤ b.lo) :
    (positiveMul a b).Contains (x * y) := by
  have hW : (0 : ℚ) < workScale := by exact_mod_cast workScale_pos
  have hal : 0 ≤ decode a.lo := div_nonneg (by exact_mod_cast ha0) hW.le
  have hbl : 0 ≤ decode b.lo := div_nonneg (by exact_mod_cast hb0) hW.le
  have hx := hal.trans ha.1
  have hy := hbl.trans hb.1
  constructor
  · calc
      decode (positiveMul a b).lo ≤
          (((a.lo * b.lo : ℤ) : ℚ) / (workScale : ℚ)) / (workScale : ℚ) :=
        div_le_div_of_nonneg_right (lower_div_le _ _ workScale_pos) hW.le
      _ = decode a.lo * decode b.lo := by simp only [decode, Int.cast_mul]; ring
      _ ≤ x * y := mul_le_mul ha.1 hb.1 hbl hx
  · calc
      x * y ≤ decode a.hi * decode b.hi := mul_le_mul ha.2 hb.2 hy (hx.trans ha.2)
      _ = (((a.hi * b.hi : ℤ) : ℚ) / (workScale : ℚ)) / (workScale : ℚ) := by
        simp only [decode, Int.cast_mul]; ring
      _ ≤ decode (positiveMul a b).hi :=
        div_le_div_of_nonneg_right (le_upper_div _ _ workScale_pos) hW.le

def divNat (b : Bounds) (n : ℕ) : Bounds := ⟨b.lo / (n : ℤ), upperDiv b.hi n⟩

private theorem divNat_contains {b : Bounds} {x : ℚ}
    (hb : b.Contains x) {n : ℕ} (hn : 0 < n) :
    (divNat b n).Contains (x / (n : ℚ)) := by
  have hni : (0 : ℤ) < n := by exact_mod_cast hn
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hW : (0 : ℚ) < workScale := by exact_mod_cast workScale_pos
  constructor
  · calc
      decode (divNat b n).lo ≤ ((b.lo : ℚ) / (n : ℚ)) / (workScale : ℚ) :=
        div_le_div_of_nonneg_right (lower_div_le _ _ hni) hW.le
      _ = decode b.lo / (n : ℚ) := by unfold decode; ring
      _ ≤ x / (n : ℚ) := div_le_div_of_nonneg_right hb.1 hnq.le
  · calc
      x / (n : ℚ) ≤ decode b.hi / (n : ℚ) := div_le_div_of_nonneg_right hb.2 hnq.le
      _ = ((b.hi : ℚ) / (n : ℚ)) / (workScale : ℚ) := by unfold decode; ring
      _ ≤ decode (divNat b n).hi :=
        div_le_div_of_nonneg_right (le_upper_div _ _ hni) hW.le

def oddSum (z : ℚ) (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, z ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℚ)

structure State where
  power : Bounds
  total : Bounds

def start (zl zh : ℤ) : State := ⟨⟨zl, zh⟩, ⟨0, 0⟩⟩

def step (square : Bounds) (j : ℕ) (s : State) : State :=
  ⟨positiveMul s.power square, s.total.add (divNat s.power (2 * j + 1))⟩

def loop (square : Bounds) (zl zh : ℤ) : ℕ → State :=
  Nat.rec (motive := fun _ => State) (start zl zh)
    (fun j s => step square j s)

/-- The invariant follows the old power when adding the next summand. -/
theorem loop_invariant {zl zh : ℤ} {z : ℚ}
    (hz : (Bounds.mk zl zh).Contains z) (hzl : 0 ≤ zl) (n : ℕ) :
    let square := positiveMul ⟨zl, zh⟩ ⟨zl, zh⟩
    let s := loop square zl zh n
    s.power.Contains (z ^ (2 * n + 1)) ∧ 0 ≤ s.power.lo ∧
      s.total.Contains (oddSum z n) := by
  have hsquare : (positiveMul ⟨zl, zh⟩ ⟨zl, zh⟩).Contains (z ^ 2) := by
    simpa only [pow_two] using positiveMul_contains hz hz hzl hzl
  have hsquare0 : 0 ≤ (positiveMul ⟨zl, zh⟩ ⟨zl, zh⟩).lo :=
    positiveMul_lo_nonneg hzl hzl
  induction n with
  | zero =>
      refine ⟨?_, hzl, ?_⟩
      · change (Bounds.mk zl zh).Contains (z ^ (1 : ℕ))
        simpa only [pow_one] using hz
      · simp [loop, start, oddSum, Bounds.Contains, decode]
  | succ n ih =>
      obtain ⟨hp, hp0, ht⟩ := ih
      have hprod := positiveMul_contains hp hsquare hp0 hsquare0
      have he : z ^ (2 * n + 1) * z ^ 2 = z ^ (2 * (n + 1) + 1) := by
        rw [← pow_add]
        congr 1
      refine ⟨?_, positiveMul_lo_nonneg hp0 hsquare0, ?_⟩
      · simpa only [loop, step, he] using hprod
      · have hadd := add_contains ht (divNat_contains hp (by omega : 0 < 2 * n + 1))
        simpa only [loop, step, oddSum, Finset.sum_range_succ] using hadd

/-- The two returned integers, without any post-processing of their width. -/
def logInterval (q : ℚ) : ℤ × ℤ :=
  let z := logParameter q
  let zl := ⌊z * (workScale : ℚ)⌋
  let zh := ⌈z * (workScale : ℚ)⌉
  let s := loop (positiveMul ⟨zl, zh⟩ ⟨zl, zh⟩) zl zh 96
  (2 * s.total.lo / outputShift, upperDiv (2 * s.total.hi + tail) outputShift)

/-- A fold with the original Python expressions and its original range. -/
def sourceLogInterval (q : ℚ) : ℤ × ℤ :=
  let z := (q - 1) / (q + 1)
  let zl := ⌊z * (workScale : ℚ)⌋
  let zh := ⌈z * (workScale : ℚ)⌉
  let z2l := zl * zl / workScale
  let z2h := (zh * zh + workScale - 1) / workScale
  let s := (List.range 96).foldl (fun (s : State) j =>
    let k := (2 * j + 1 : ℕ)
    { power := ⟨s.power.lo * z2l / workScale,
        (s.power.hi * z2h + workScale - 1) / workScale⟩
      total := ⟨s.total.lo + s.power.lo / (k : ℤ),
        s.total.hi + (s.power.hi + (k : ℤ) - 1) / (k : ℤ)⟩ })
    { power := ⟨zl, zh⟩, total := ⟨0, 0⟩ }
  (2 * s.total.lo / outputShift, (2 * s.total.hi + tail + outputShift - 1) / outputShift)

private theorem loop_eq_fold (square : Bounds) (zl zh : ℤ) (n : ℕ) :
    loop square zl zh n =
      (List.range n).foldl (fun s j => step square j s) (start zl zh) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [loop, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, ← ih]

/-- Universal equivalence to the literal source-shaped integer fold. -/
theorem logInterval_eq_source (q : ℚ) : logInterval q = sourceLogInterval q := by
  simp only [logInterval, sourceLogInterval, loop_eq_fold, logParameter,
    positiveMul, upperDiv, step, Bounds.add, divNat, start]

def certificate (q : ℚ) : RationalLogCertificate :=
  ⟨q, 96, ((logInterval q).1 : ℚ) / (outputScale : ℚ),
    ((logInterval q).2 : ℚ) / (outputScale : ℚ)⟩

/-- Every original output pair satisfies the existing rational checker. -/
theorem certificate_valid (q : ℚ) (h1 : 1 ≤ q) (h2 : q ≤ 2) :
    (certificate q).Valid := by
  let z := logParameter q
  let zl : ℤ := ⌊z * (workScale : ℚ)⌋
  let zh : ℤ := ⌈z * (workScale : ℚ)⌉
  let square := positiveMul ⟨zl, zh⟩ ⟨zl, zh⟩
  let s := loop square zl zh 96
  have hW : (0 : ℚ) < workScale := by exact_mod_cast workScale_pos
  have hP : (0 : ℚ) < outputScale := by exact_mod_cast outputScale_pos
  have hH : (0 : ℚ) < outputShift := by exact_mod_cast outputShift_pos
  have hscale : (workScale : ℚ) = (outputScale : ℚ) * (outputShift : ℚ) := by
    exact_mod_cast workScale_eq_mul
  have hz : (Bounds.mk zl zh).Contains z := by
    constructor
    · exact (div_le_iff₀ hW).mpr (Int.floor_le (z * (workScale : ℚ)))
    · exact (le_div_iff₀ hW).mpr (Int.le_ceil (z * (workScale : ℚ)))
  have hzl : 0 ≤ zl := by
    apply Int.floor_nonneg.mpr
    exact mul_nonneg (logParameter_nonneg q h1) hW.le
  obtain ⟨_, _, ht⟩ := loop_invariant hz hzl 96
  change s.total.Contains (oddSum z 96) at ht
  have hlo : ((2 * s.total.lo / outputShift : ℤ) : ℚ) / (outputScale : ℚ) ≤
      2 * decode s.total.lo := by
    calc
      _ ≤ (((2 * s.total.lo : ℤ) : ℚ) / (outputShift : ℚ)) / (outputScale : ℚ) :=
        div_le_div_of_nonneg_right (lower_div_le _ _ outputShift_pos) hP.le
      _ = _ := by
        simp only [decode, Int.cast_mul, Int.cast_ofNat, hscale]
        field_simp
  have hhi : 2 * decode s.total.hi + (tail : ℚ) / (workScale : ℚ) ≤
      (upperDiv (2 * s.total.hi + tail) outputShift : ℚ) / (outputScale : ℚ) := by
    calc
      _ = (((2 * s.total.hi + tail : ℤ) : ℚ) / (outputShift : ℚ)) /
          (outputScale : ℚ) := by
        simp only [decode, Int.cast_add, Int.cast_mul, Int.cast_ofNat, hscale]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (le_upper_div _ _ outputShift_pos) hP.le
  have hresult : logInterval q =
      (2 * s.total.lo / outputShift, upperDiv (2 * s.total.hi + tail) outputShift) := rfl
  refine ⟨h1, ?_, ?_⟩
  · change ((logInterval q).1 : ℚ) / (outputScale : ℚ) ≤ logSeriesLower q 96
    rw [hresult]
    exact hlo.trans (mul_le_mul_of_nonneg_left ht.1 (by norm_num))
  · change logSeriesUpper q 96 ≤ ((logInterval q).2 : ℚ) / (outputScale : ℚ)
    rw [hresult]
    have hsum := mul_le_mul_of_nonneg_left ht.2 (by norm_num : (0 : ℚ) ≤ 2)
    have htail := remainder_le_tail q h1 h2
    exact (add_le_add hsum htail).trans hhi

/-- The actual original integers enclose the real logarithm on its full domain. -/
theorem logInterval_contains (q : ℚ) (h1 : 1 ≤ q) (h2 : q ≤ 2) :
    ((logInterval q).1 : ℝ) / (outputScale : ℝ) ≤ Real.log (q : ℝ) ∧
      Real.log (q : ℝ) ≤ ((logInterval q).2 : ℝ) / (outputScale : ℝ) := by
  have hc : (certificate q).check = true := by
    simpa only [RationalLogCertificate.check, decide_eq_true_eq] using
      certificate_valid q h1 h2
  simpa only [certificate, Rat.cast_div, Rat.cast_intCast] using
    (certificate q).check_sound hc

end ImbalancedChen.Certificates.P2OriginalLog96
