import ImbalancedChen.Part5OriginalH430ActualInitialTwoExtensionMass

/-!
P5.6 / h34: factor the TWO ORIGINAL prime contributions out of the
genuine depth-k first-exit native weight, while retaining all later
physical Fin occurrences and arbitrary SIGNED full-prefix weights.

The real recursion stores selectedPrefix in reverse selection order.
Thus the ordered pair (p, ell) is selectedPrefix.reverse.take 2 and
the remaining factors are selectedPrefix.reverse.drop 2.  Unlike
rank-two position uniqueness, the latter list can have any length.

This is an exact identity at one genuine physical Q and original z0.
It DOES NOT turn q/tag receipts into native histories, identify an
upper H430 full/selected/inherited owner, or license any signed
first-excluded Euler-suffix payment.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualInitialTwoSignedRootFactor

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430ActualAllDepthFullPrefix
open Part5OriginalH430ActualInitialTwoExtensionMass

/-- The literal two-prime native factor. This is NOT the original
arithmetic U3/U4 root count weight or a replacement for its sign. -/
def actualInitialTwoRootFactor (p ell : ℕ) : ℝ :=
  (1 / ((p : ℝ) - 1)) * (1 / ((ell : ℝ) - 1))

/-- The native mass of later-selected ORIGINAL primes. At depth two
this is an empty product; at greater depths no extension is removed. -/
def actualFirstTwoSuffixWeight (s : FirstExitDepthState ℕ) : ℝ :=
  ((s.selectedPrefix.reverse.drop 2).map
    (fun r : ℕ => 1 / ((r : ℝ) - 1))).prod

/-- The physical first-exit state mass factors at its TRUE ordered
initial pair, for any actual admitted depth-k state.  No invented
owner or nonnegative signed test is an assumption. -/
theorem actual_depth_first_two_mass_factor_of_mem
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (p ell : ℕ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ actualPhysicalDepthList k N cap z0 Q lower)
    (hp : actualFirstTwoOriginal s = [p, ell]) :
    s.mass = actualInitialTwoRootFactor p ell *
      actualFirstTwoSuffixWeight s := by
  let f : ℕ → ℝ := fun r => 1 / ((r : ℝ) - 1)
  have hm : s.mass = (s.selectedPrefix.map f).prod :=
    mem_firstExitDepthFrontier_mass_eq_selected_prod k
      (ordinaryRosserRetainedPolicy lower Q) f
      (roughPrimeUniverse N cap 0 z0) s
      (by simpa only [actualPhysicalDepthList] using hs)
  have hr : (s.selectedPrefix.map f).prod =
      (s.selectedPrefix.reverse.map f).prod := by
    simp only [List.map_reverse, List.prod_reverse]
  have hsplit :
      (s.selectedPrefix.reverse.map f).prod =
        ((s.selectedPrefix.reverse.take 2).map f).prod *
        ((s.selectedPrefix.reverse.drop 2).map f).prod := by
    calc
      (s.selectedPrefix.reverse.map f).prod =
          (((s.selectedPrefix.reverse.take 2) ++
            (s.selectedPrefix.reverse.drop 2)).map f).prod := by
              simp only [List.take_append_drop]
      _ = ((s.selectedPrefix.reverse.take 2).map f).prod *
          ((s.selectedPrefix.reverse.drop 2).map f).prod := by
              simp only [List.map_append, List.prod_append]
  have hp' : s.selectedPrefix.reverse.take 2 = [p, ell] := by
    simpa only [actualFirstTwoOriginal] using hp
  calc
    s.mass = (s.selectedPrefix.map f).prod := hm
    _ = (s.selectedPrefix.reverse.map f).prod := hr
    _ = ((s.selectedPrefix.reverse.take 2).map f).prod *
          ((s.selectedPrefix.reverse.drop 2).map f).prod := hsplit
    _ = actualInitialTwoRootFactor p ell *
          actualFirstTwoSuffixWeight s := by
            simp [hp', actualInitialTwoRootFactor,
              actualFirstTwoSuffixWeight, f, mul_assoc]

private theorem real_list_sum_left_mul (c : ℝ) (xs : List ℝ) :
    (xs.map (fun x => c * x)).sum = c * xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, mul_add]

/-- Every REAL history occurrence at one Q is retained in this
signed suffix total. An arbitrary signed F is evaluated on the
complete reverse-stored selectedPrefix, not just its initial pair. -/
def actualDepthFirstTwoSignedSuffixMass
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (p ell : ℕ) (F : List ℕ → ℝ) : ℝ :=
  ((actualPhysicalDepthList k N cap z0 Q lower).map (fun s =>
    if actualFirstTwoOriginal s = [p, ell]
    then actualFirstTwoSuffixWeight s * F s.selectedPrefix
    else 0)).sum

/-- The signed full-prefix mass splits into the literal two original
prime factors and a STILL-SIGNED sum over all true later histories.
No positivity, owner uniqueness or cancellation hypothesis is used. -/
theorem actual_depth_first_two_signed_root_factor
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (p ell : ℕ) (F : List ℕ → ℝ) :
    ((actualPhysicalDepthList k N cap z0 Q lower).map (fun s =>
      s.mass * (if actualFirstTwoOriginal s = [p, ell]
                then F s.selectedPrefix else 0))).sum =
      actualInitialTwoRootFactor p ell *
        actualDepthFirstTwoSignedSuffixMass k N cap z0 Q lower p ell F := by
  let L := actualPhysicalDepthList k N cap z0 Q lower
  let c := actualInitialTwoRootFactor p ell
  let g : FirstExitDepthState ℕ → ℝ := fun s =>
    if actualFirstTwoOriginal s = [p, ell]
    then actualFirstTwoSuffixWeight s * F s.selectedPrefix else 0
  change (L.map (fun s =>
      s.mass * (if actualFirstTwoOriginal s = [p, ell]
                then F s.selectedPrefix else 0))).sum =
    c * (L.map g).sum
  have heq : (L.map (fun s =>
      s.mass * (if actualFirstTwoOriginal s = [p, ell]
                then F s.selectedPrefix else 0))).sum =
      (L.map (fun s => c * g s)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro s hs
    by_cases hp : actualFirstTwoOriginal s = [p, ell]
    · have hm := actual_depth_first_two_mass_factor_of_mem
        k N cap z0 Q lower p ell s hs hp
      simp only [hp, ite_true, mul_one, g]
      rw [hm]
      simp only [c, mul_assoc]
    · simp [hp, g]
  calc
    _ = (L.map (fun s => c * g s)).sum := heq
    _ = ((L.map g).map (fun x => c * x)).sum := by
        simp only [List.map_map, Function.comp_def]
    _ = c * (L.map g).sum :=
        real_list_sum_left_mul c (L.map g)

/-- The UNWEIGHTED actual native mass is a specialization of the
signed identity. The factor is exact for every true finite depth,
not a claim about an arithmetic q/tag receiver's count weight. -/
theorem actual_depth_first_two_native_root_factor
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (p ell : ℕ) :
    actualDepthFirstTwoNativeMass k N cap z0 Q lower p ell =
      actualInitialTwoRootFactor p ell *
        actualDepthFirstTwoSignedSuffixMass k N cap z0 Q lower
          p ell (fun _ => (1 : ℝ)) := by
  simpa only [actualDepthFirstTwoNativeMass, mul_ite, mul_one, mul_zero] using
    (actual_depth_first_two_signed_root_factor
      k N cap z0 Q lower p ell (fun _ => (1 : ℝ)))

/-- Reuse the exact genuine ordinary-Rosser ADMITTED-TUPLE enumeration:
the initial p,ell root factor is explicit while the rest of the
true histories remain in their native, potentially multiple positions. -/
theorem actual_depth_first_two_admitted_tuple_root_factor
    (k N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (p ell : ℕ) :
    (∑ t ∈ firstExitAdmittedTuples k
        (ordinaryRosserRetainedPolicy lower Q)
        (roughPrimeUniverse N cap 0 z0),
      (∏ j, 1 / ((t j : ℝ) - 1)) *
        (if (List.ofFn t).reverse.reverse.take 2 = [p, ell]
         then (1 : ℝ) else 0)) =
      actualInitialTwoRootFactor p ell *
        actualDepthFirstTwoSignedSuffixMass k N cap z0 Q lower
          p ell (fun _ => (1 : ℝ)) := by
  calc
    _ = actualDepthFirstTwoNativeMass k N cap z0 Q lower p ell :=
      (actual_depth_first_two_native_mass_eq_admitted_tuples
        k N cap z0 Q lower p ell).symm
    _ = _ := actual_depth_first_two_native_root_factor
      k N cap z0 Q lower p ell

end
end ImbalancedChen.Part5OriginalH430ActualInitialTwoSignedRootFactor
