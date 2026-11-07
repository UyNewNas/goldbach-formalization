# L / compact_symmetry — original Q80 half mass and final selection

Source proofs supplied; original whole-run endpoint remains OPEN. `compiled=false`, `kernel_verified=false`, `formal_credit=0`. No Lean, lake, compiler, build, meta elaborator, checker, numerical replay, finite guard, generator, Git operation, quota query or subagent was executed. Only this task directory was written.

## Exact scope

The producer is `../chen-imbalanced-semiprimes/verification/data/certify_extended_prefix.py`, SHA256 `1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`. The second inspected original copy in `../goldbach-research/certify_extended_prefix.py` has the same hash. Relevant source lines are 133–161 (actual cap range and the above-mu symmetric extension), 167–178 (full reciprocal mass), 226–273 (selected affine/Jensen branch), and 276–336 (outside/full-cap/zero-loss exits, inside/symmetric flags, candidate minima and final floor/ceiling).

The current manuscript is `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`, SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`; lines 1310–1389 retain the original compact third cost, complete negative-cost coverage, directed arithmetic and limits of finite reproduction. The selected numerical completion module, lines 61–64 and 106–113, identifies the same compact term and boundary coverage. Its separate factorial-symmetry discussion at lines 200–205 is not used as a theorem about the present kernel.

The exact original parameters remain Q=2^80, D=48000*2^24, Theta=299/500, mu=25/128, rho=19/96 and cutoff=1/100. Neither the true cap/history kernel, original point/log/table interpreter, branch tests, queue rules, nor the integer bound definitions are changed. c=49044063/25000000 and K=8452171/1250000 remain unchanged.

## What the proofs establish

`P2OriginalCompactQ80Symmetry.lean` imports the actual L Q80 leaf and the existing `ActualThirdOriginalSymmetricJensenLeaf`. It introduces only analytic companion objects:

* `rectangle box` is the decoded closed Cartesian box.
* `chargeDomain box` is that rectangle, or its closed y<=x half when the literal `symmetricHalf` flag holds.
* `realChargedMass box` is 4*boxMass, or exactly half that real mass under the same source flag.

`rootCell_subset_chargeDomain` holds for every raw box. For an original positive-width `Geometry`, `chargeDomain_eq_rootCell_of_inside` derives equality from the actual source inside predicate. Every weak order comparison is retained, including z1=y0, y1=x0 and equal x/y intervals. `source_symmetricFullBox` supplies the existing analytic geometry from the original raw integer coordinates, including the preserved mu cut.

The half-mass theorem does **not** assume the actual cap or compactKernel is symmetric. `integral_density_orderedHalf` transports the genuine Fin3 Lebesgue integral through the existing volume-preserving `finPrismEquiv` and uses the proved reciprocal-triangle integral. It allows weak side widths, including degenerate sides. `integral_chargeDomain_density` then proves the exact full/half density mass on every original box, including boundary boxes whose raw-cube wall clips the actual domain. The constant density envelopes used by the four pre-Jensen pointwise candidates are nonnegative and symmetric; extending their integral from rootCell to chargeDomain is justified by set-integral monotonicity. `upperBeforeJensen_integral` therefore supplies the **actual all-four-candidate original** upper bound times the correct real charged mass. It does not substitute the larger full-rectangle charge at symmetric cells.

`integral_lower_of_pointwise` uses inside equality and the same positive density to integrate an upstream pointwise lower gap. The lower coefficient may be signed in that generic theorem; the literal lowerDifference is separately nonnegative. Boundary lowerDifference is exactly zero.

`source_sorted_half_integral` also binds the existing correct sorted extension to the original decoded inside square. Its equality is between the actual ordered-domain integral and half the **sortedKernel** rectangle integral, never half the asymmetric literal compactKernel rectangle integral. This is available to the Jensen companion. The predecessor explicitly contains a counterexample to the latter false symmetry claim.

`half_contains` preserves exactly `m.lo/2` and `up m.hi 2`. `half_even_integer` and `half_odd_integer` prove their signed even/odd formulas for every integer; no divisibility/parity premise is imposed. `chargedMass_contains` invokes the actual Q80 log/product/z-rational mass enclosure and then this exact one-time half rounding. Literal lower-mass nonnegativity is derived from the proved original computed lower logs and positive integer divisors, not inferred incorrectly from containment of a positive real mass.

`flat_rootCell_null`, `touching_xy_rootCell_null`, and `touching_yz_rootCell_null` prove the corresponding equality faces null by proper affine walls. Their actual integrals are zero even though a touching cell is not outside under the producer's strict test. `reversed_rootCell_empty` covers reversed raw sides. These auxiliary analytic statements do not assert Python validity for degenerate/reversed inputs: the original encloser theorem retains its original strict-width `Geometry`. Original outside, full-cap and zero-loss exits are consumed as their own exact source branches.

`P2OriginalCompactQ80Selection.lean` imports only the symmetry companion. It proves the optional Jensen minimum directly by the actual integer ordering of `upperBeforeJensen` and the selected `j`, retaining `none`, `some`, ties and the inside gate. A selected candidate's value is nonnegative as a consequence of the nonnegative actual integral and positive real mass. It then multiplies by the rounded mass in the correct direction and applies the original single Q80 floor or ceiling. Thus the source's min occurs before the final integer product exactly as written.

`enclose_contains_from_candidates` consumes all original early exits and proves the final **actual** `enclose` result from two explicit upstream sub-obligations:

1. At each point of rootCell, `val (lowerDifference box)` is at most the actual NEW–OLD lower-factor gap.
2. For each `j` selected by `jensenDifferenceUpper box = some j` on an inside cell, the actual rootCell integral is at most `val j * realChargedMass box` before mass/product rounding.

These are candidate-specific ports, not a field or assumption asserting the desired whole leaf enclosure. The phi owner has supplied a draft of the first pointwise theorem. The Jensen owner and parent must supply/instantiate the second from the actual selected affine/minorant/mean/chord proof. `enclose_integer_order_from_candidates` derives `0 <= enclose.lower <= enclose.upper` afterward; that producer assertion is not used circularly in any enclosure proof.

`boundary_enclose_contains_integral` has **no candidate estimate premise**: it closes the actual original enclosure for every `Geometry box` with `¬ inside box`, including the previously open symmetric boundary branch. The four original upper candidate minima are proved by the Q80 Leaf, the half mass by this companion, the lower is the original zero, and every original zero exit remains active.

## Dependency and installation map

Install unchanged L predecessor modules first: `P2OriginalCompactQ80Table`, `P2OriginalCompactQ80Encloser`, `P2OriginalCompactQ80Arithmetic`, `P2OriginalCompactQ80Leaf`, with their own declared prerequisites. Then install this directory's `P2OriginalCompactQ80Symmetry.lean` as `ImbalancedChen/P2OriginalCompactQ80Symmetry.lean`, followed by `P2OriginalCompactQ80Selection.lean` as `ImbalancedChen/P2OriginalCompactQ80Selection.lean`.

The symmetry module imports no phi/Jensen companion. The Jensen companion may therefore import symmetry without a cycle. Selection also imports no Jensen companion. The separate parent-owned `CompleteSoundness` is the sole intended final composition point for phi, Jensen and selection. No shared definitions or installation targets were edited here.

The registry pins every direct import's actual current source file, all four L executable/analytic predecessor files, the inspected geometric/measure suppliers, manuscript, original producer copies, shared policy and Mathlib API files. The L predecessor REGISTRY/REPORT were not yet present when inspected; the actual proof files were present and used. The older J compact_leaf REGISTRY/REPORT were read and pinned as historical provenance only: their P160 alternative-cost route is not used to replace the actual Q80 output.

Local Mathlib was inspected read-only at `\\wsl.localhost\Debian\home\slava\codex-lean-ve\native-packages\mathlib\Mathlib`, despite the repository-local `.lake/packages/mathlib` being absent. In particular `MeasurePreserving.setIntegral_preimage_emb`, `setIntegral_mono_set`, `integral_mul_const`, `MeasurePreserving.integrableOn_comp_preimage`, and the measure restriction/zero-integral interfaces were read. The project manifest requests Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; the inspected local toolchain text is Lean v4.33.0-rc1. Exact local API file hashes, rather than an unverified claim about its checkout commit, are recorded. Source presence grants no elaboration credit.

## Eliminated and remaining obligations

Eliminated in source: original equal-square charged geometry; correct reciprocal half mass at boundary/interior cells; integration of all four proved pointwise original upper candidates using half mass where selected; lower integration on the actual inside carrier; zero lower on boundary; signed odd/even half rounding; exact optional candidate minimum and final Q80 floor/ceiling; exact early source exits; final bound-order assertion once analytic candidate suppliers are instantiated; original symmetric boundary enclosure without extra integral assumptions; proper handling of closed equality faces and degenerate analytic masses.

Remaining: instantiate the lower/Jensen candidate ports in the parent-owned all-interior proof; complete all original primitive Jensen operation guards where needed; install and independently review these uncompiled sources; user-owned elaboration/kernel verification; the actual finite adaptive history/cache/run and aggregate endpoint guards. The historical compact numerator, whole run, first-plus-tail endpoint, and original endpoint theorem are not established here. Every decisive finite guard remains **UNEVALUATED**.

No new external analytic assumption, new axiom, whole-leaf estimate premise or P160-to-Q80 comparison is introduced. This delivery proves no successful finite evaluation and receives zero formal credit. A source review finding, if any, is distinct from a compiler or kernel result.
