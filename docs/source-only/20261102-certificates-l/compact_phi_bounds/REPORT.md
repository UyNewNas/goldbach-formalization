# L / compact_phi_bounds

Strict source candidates now supply the literal original `phiRange.hi` bound and both original `lowerDifference` candidates. The local pointwise step is complete as written; elaboration and kernel verification have not been performed. **compiled=false, kernel_verified=false, formal_credit=0.** P2.4.leaf_integrals and P2.4.endpoint remain OPEN pending companion composition and verification. Every decisive finite guard is **UNEVALUATED**.

Only this assigned directory was written. No Lean, lake, compiler, build, CI, meta elaborator, numerical producer, finite checker, bulk literal generator, Git operation, subagent or quota call was run. The delivery consists of two modules, this report and REGISTRY.json.

## Exact target and source

The original producer is `../chen-imbalanced-semiprimes/verification/data/certify_extended_prefix.py`, SHA256 `1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`. Its actual `SieveTable(16384,12)`, `v_point_hi`, `v_hi`, `phi_range` and `enclosure` were read. Its imported arithmetic producer `certify_conservative_chen.py` was read through the actual Q80 interval and 32-term logarithm implementations. The actual L Table, Encloser, Arithmetic and Leaf sources were read, along with the historical table/log interpreters and the J cap-floor predecessor. No P112 or P160 query output is used by the new proofs.

The current manuscript body was read at lines 360–509 and 1310–1435. The original `proof-library/source/extended-prefix-upper.tex` lines 6–40 fix the actual cap dispatch and signed third correction: the full gated envelope at x<=mu, v(x) above mu, min(Theta,envelope), and fbar(new)-fbar(old) with factor 4/(xyz^2). The current numerical-completion module was also inspected. The exact parameters remain theta=299/500, mu=25/128, rho=19/96, cutoff=1/100, coordinate denominator 48000*2^24, Q=2^80, original c=49044063/25000000 and K=8452171/1250000. This delivery proves no new endpoint and does not evaluate 144590669409566793572719/2^80.

The original scalar phi branch begins at x0>=mu, whereas the analytic gated envelope retains equality at x=mu. This is handled explicitly: `original_mu_left` proves the full envelope is exactly 153/256 on that face, equal to v(mu). The endpoint is not deleted as a null exception and the analytic dispatch is not altered.

## New proof bodies

`P2OriginalCompactQ80PhiBounds.lean` imports the parent-owned Leaf and the existing actual VariableEnvelopeConsequences module.

* `vPointUpper_sound` pays both endpoint ceilings inside their original minimum. `vUpper_sound` treats the inclusive peak guard, otherwise the monotone rising or falling segment. `rawValue` denotes n/D and is kept distinct from Q80 `val`=n/Q.
* `sumRanges_eq_authorSums` retains the exact x,y,xy,xyz,xz,yz operand list. `six_le_belowUpper` pays every term of that source maximum and the B(z0) ceiling on a rectangle. It does not require the true gated cap to agree off its ordered domain.
* `actualEnvelope_eq_v_of_mu_le` proves the actual above-mu/equality dispatch identity from original ordered geometry and the proved envelope value at mu.
* `cap_ceiling_on_actual_intersection` proves actualCap(t)<=phiRange.hi/D on `rootCell box` from `Geometry box` alone. The below-mu case uses the six-envelope identity only on its valid ordered domain. The above-mu case includes the closed wall.
* `phiRange_contains_actual_cap` combines this new upper proof with the actual original lower-floor theorem already supplied by the parent/J chain. `phiRange_upper_le_theta` supplies the nonnegative minimum-increment numerator without a numeric assertion.

`P2OriginalCompactQ80LowerDifference.lean` imports only the preceding companion.

* `upper_cap_residual_positive` derives cap_hi-x0-y0>0 from the true two-sided cap bounds, original `Geometry.residual`, and endpoint widths. No computed cap-order guard is accepted as an assumption.
* `new_argument_ge_source_lower` and `old_argument_le_source_ceiling` prove the exact nlo/z1 and ohi/z0 endpoints. They first divide the positive residual before subtracting 1; they do not assume the signed final numerators are nonnegative.
* `argument_gap_ge_source_delta` proves `(Theta-cap_hi)/z1 <= new-old`, with the original z1 denominator. Positivity follows from phiRange.hi<=Theta and positive raw coordinates.
* `rawLower_pointwise` applies the actual original `point_contains_actual` at `(nlo,z1)` and `(ohi,z0)`, keeps the original low-minus-high subtraction, and pays max(0,...) by actual gap nonnegativity.
* `pairedLower_query_argument` proves the exact original correlated query identity `(ohi*z1+(Theta-cap_hi)*z0)/(z0*z1)=ohi/z0+(Theta-cap_hi)/z1`.
* `pairedLower_pointwise` uses the literal `2*z1<=olo` guard and the existing original lower-cap endpoint to prove actualOld>=2. Then `fixed_increment_antitone` gives the correlated lower direction, and global monotonicity enlarges its increment to the actual new argument. Concavity is never applied across the zero clamp at 2. Both query endpoints are the actual max12 Q80 output, including its existing signed/zero/tail behavior.
* `lowerDifference_source_formula` is definitional equality with the literal parent's nested guards, maxima and operand order. `lowerDifference_nonnegative`, `lowerDifference_value_nonnegative` and `lowerDifference_pointwise` prove the entire original lowerDifference expression, including the zero branch when `inside` fails.

The main export is:

```lean
lowerDifference_pointwise (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ rootCell box) :
  val (lowerDifference box) <=
    actualExtendedThirdLowerFactor (newArgument t) -
      actualExtendedThirdLowerFactor (actualOldArgument t)
```

This is an actual internal estimate derived from source primitives. Its inputs are endpoint geometry and point membership, not any cap, query, factor-gap, leaf or integral estimate.

## Dependency and external-input boundary

The actual source query chain is Encloser.point -> historical max12 point -> Table.point12_contains_actual -> state_encloses actualTrapezoidIncrements. The historical table's nested floors/ceilings, interpolation allowance and maximum-twelve tail are preserved. The parent Arithmetic module identifies these values with its literal Q80 point function. No saved query interval or finite acceptance predicate is supplied by callers.

The logarithm interpreter's `real_le_ceilDiv` is used only as the already proved integer ceiling rule for coordinate rounding. Logarithmic mass is handled by the parent and symmetry companion; it is not an extra premise of either new module. The analytical fixed-increment theorem is reused from `ActualThirdOriginalP4AOriginalClippedGapLeaf`; although that existing file also has separate P160 consumers, this particular theorem concerns only the true normalized lower function and has no table/reader parameter. No P160 value, cost or comparison is imported into the new result statements.

There are no new external assumptions, axioms or desired internal estimate hypotheses. Existing actual-factor sources remain inherited dependencies: true clamped normalized lower-factor monotonicity, actual coupled-source concavity on [2,infinity), and original gated-envelope identities. Their proofs and actual mathematical domains were inspected. This source-only delivery does not claim a complete transitive axiom audit or inherited kernel verification.

## What remains

The new modules remove the original phi upper/equality-wall proof, the new-low/old-high/minimum-increment sign-and-division steps, and both actual lowerDifference candidate estimates. They do not assume or discharge any historical finite output guard.

The symmetry companion owns the actual ordered-domain mass, sorted symmetric extensions where required, full/half mass integration, odd integer half rounding, and final source selection. The Jensen companion owns the selected affine/Jensen upper candidate and its source moments and divisions. The parent-owned separate CompleteSoundness module must compose these with the already proved raw/paired/decay upper candidates and early exits. The main true cap/kernel is not asserted symmetric by these files.

The original adaptive run, successful source operation guards at every visited box, complete integer endpoint certificate, resource feasibility, source-only installation, independent review and user-owned elaboration/kernel verification remain outside this local delivery. No integral lower bound, full enclose theorem, historical charge list or final endpoint is claimed here.

## Actual local Mathlib and installation

The repository's `.lake/packages/mathlib` path is absent, but an actual local checkout is available read-only at `\\wsl.localhost\Debian\home\slava\codex-lean-ve\native-packages\mathlib`. Its `.git/HEAD` contains exactly `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; its `lean-toolchain` is `leanprover/lean4:v4.33.0-rc1`. The actual `Algebra/Order/GroupWithZero/Basic.lean` division-order API and `Analysis/Convex/Function.lean` concavity definition were read, as was `Algebra/Order/Field/Basic.lean`. Their exact raw SHA256 pins are in REGISTRY. No WSL process, Lean toolchain or elaborator was started.

Install the parent Table -> Encloser -> Arithmetic -> Leaf chain and its registered predecessors first. Install this PhiBounds module as `ImbalancedChen/P2OriginalCompactQ80PhiBounds.lean`, then LowerDifference as `ImbalancedChen/P2OriginalCompactQ80LowerDifference.lean`. Companions/final composition import these; these files do not import symmetry, Jensen or CompleteSoundness, so the proposed graph is acyclic. Nothing was copied over production.

REGISTRY.json pins exact draft paths, direct imports, inspected support sources, provenance, declarations and installation targets. Imported L files are under their owner's control; the recorded hashes are the bytes observed at this delivery and must be repinned if that owner changes them. Static review used text reads/searches, arithmetic reasoning and raw-file hashing only. It is not an elaboration or proof-acceptance result.

## Final dependency metadata repin

After the parent owner's explicit dependency freeze and root's metadata-only instruction, the final Leaf and Arithmetic sources were reread and the consumed APIs checked. The parent's Leaf header was updated from the previously registered SHA256 `e8024b2df23deac2944683ade08d97ea51a516a9d2b30e48f6d0895de8a43ef3` to `22625cbdbd57f6412e0074440fc30723e7c868506ec297026986368dd393bad4` (34491 bytes). The existing `OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly` namespace fix remains present. The consumed `Geometry`, coordinate positivity/width, residual, cap floor, old-floor argument and actual gap nonnegativity signatures and proof bodies remain compatible with both frozen companions. This is the parent's reported header-only change, checked against the final actual source and APIs, not a new compilation claim.

Arithmetic is unchanged at `63f4bb94e59d26128bda0a24fa6be3ac0ce482084ac80d00d90280083d607821`; its `contains_iff`, value arithmetic and actual max12 `point_contains_actual` interfaces were reread. Table remains `e9f37ac098bb46dc8befa0211d7c39ac8a0907ef675b9ebca824ffa58d49e66a`, and Encloser remains `9a83abd21750ff9ed799dc283e4c3130fc02749eedc9ef246d98af0b310ae9f8`.

Only REGISTRY and this report change in this repin. PhiBounds remains `acb8dc99b75592174915fdca5472aeca0c9c19e868313fab6cd5a57b9299e034`, and LowerDifference remains `c56e1db1552a7c14ec5cc79147745b276e8fcf5a0926129b8cb14108ebdcbff8`. The earlier independent review gave the narrow pointwise source step SOURCE_REVIEW_PASS with no required proof correction; its metadata binding must be updated to these final parent bytes and the new report/registry hashes. All source-only, UNEVALUATED, uncompiled, kernel-unchecked and credit-zero qualifications remain unchanged.
