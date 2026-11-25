# Original U5: every actual last source and the complete signed square word

Base inspected: `e4ad395e4901628d85a27d17d0f87a16ea943433`.

Status: **source only, uncompiled, kernel unverified**. No Lean invocation or
compiler task was made. The candidate modules are not selected by this
directory. The existing receiver, frozen fresh-fifth source, main carrier
cap and manifest were not edited by this work.

## Frozen implementation

| File | SHA-256 |
| --- | --- |
| `ImbalancedChen/P3OriginalU5AllSourceSquares.lean` | `08533e66a1407643170456b72b1d7aff945f2c57ad3f301c0b249492b66dd243` |
| `ImbalancedChen/P3OriginalU5AllSignedSquares.lean` | `40407b717cf912873229eb0c2cb15a6069a5ec9469f0e5b404887a69fff1c361` |
| `public-receiver-helpers.patch` | `81937ad17e0ba5c93dafbf730f22815aeb8e3f8a10839334c45a86c72987f25b` |
| `public-native-carrier-helpers.patch` | `8b74b35aaf6242d0e9487225c5e981cd0e6a5591857b4b426984d23fa90304b7` |

The rough module imports only the already selected
`P2OriginalPairBufferedRootProvenance`. The signed module imports that new
rough module and the already selected `P3OriginalU5FreshFifthSquareSupplier`.
No new external source or large arithmetic dependency chain is introduced.

### Minimal compatibility patches, not repeated proofs

The old public PairRange point-square theorem only handles rank five. The
new general-rank transfer needs its existing endpoint and monotonicity
helpers. `public-receiver-helpers.patch` removes only `private` from:

- `P2OriginalPairSourceReceiver.exponent_upper`;
- `P2OriginalPairSourceReceiver.squareGates_mono`;
- `P2OriginalPairSourceReceiver.sum_le`;
- `P2OriginalPairSourceReceiver.slot_words_mono`.

The signed consumer likewise reuses the frozen fresh-fifth carrier facts
and integer gate monotonicity. `public-native-carrier-helpers.patch` removes
only `private` from:

- `P3OriginalU5FreshFifthSquareSupplier.integer_gates_mono`;
- `P3OriginalU5FreshFifthSquareSupplier.original_word_data`.

All six statements and proof bodies are byte-identical after removing that
modifier. `HELPER_VISIBILITY.json` and `NATIVE_CARRIER_VISIBILITY.json`
record the original/patched source hashes and each preserved declaration's
hash. The old `qPoint_cast` remains private and is used by the original
endpoint proof in its original module. No unstable `_private` name is used.
Both independent patch files passed `git apply --check`; neither was
applied to the main sources. These patches must be applied in the subsequent
integration before the new public names can elaborate. Changed dependency
sources require their own fresh compilation receipt.

## What the rough module actually supplies

`actual_U5_all_source_integer_squares` starts with an original U5 pair,
the actual roughUniverse subword, and acceptance of the literal run

```text
pairPlan R bank (2*buffer) (rootSeed false buffer N t)
```

from the unchanged pair root. It returns an `Origin`, the actual tagged
integer slots, and an `IntegerSupply` containing:

1. the root/fresh/inherited provenance of that last source;
2. equality of the final actual trace cap with that source's stored cap;
3. the exact chronological values `t.2 :: t.1 :: chosen`;
4. full integer prefix squares at that stored cap;
5. selected-complement integer squares at that same stored cap.

`native_U5_nonzero_all_source_squares` starts directly at the original
nonzero native rho. The existing `native_U5_nonzero_word` supplies its
same small factor `s`, chronological rough word `chosen`, original carrier
membership, `k=s*chosen.prod`, and actual acceptance. The theorem returns
these identities together with the preceding all-source supply. There is
no incoming square, selected mask, source cap identity or `FreshFifth`
premise.

### Literal source identity and mask

`Origin.root` has the original two selected root primes and seed.
`Origin.row` contains the actual rank, code, selected branch and prefix
prime vector. A `Provenance.fresh` constructor requires the exact
`select = some branch`, its `freshCheck` against the actual incoming cap,
and the actual `actionChoice = fresh ...` equality. Its slots are the
existing `integerPrefixSlots` for that row's own support mask.

An inherited constructor requires the actual `actionChoice = inherit 2`
and appends an unselected prime to the preceding source. The post-five
constructor retains the source and appends only unselected primes.
`provenance_mask` proves that the selected-prime list is still exactly that
last source's selected list. A genuine fresh action may select a new source
mask; it is not falsely identified with the root mask or Trace's all-false
coding tags. Unused vector entries for short words are padding, excluded by
the actual rank and prefix code; the source's used prime vector is tied to
the literal original prefix.

### Finite branch assembly

| Actual full rank | Existing evidence consumed | New finite connection |
| --- | --- | --- |
| 2, no rough primes | `fifth_buffered_root_squares` and the original selector's triangle | The original root slots and cap are retained. |
| 3 | Original root first-head reserve, with the actual rough prime below `N^(417/5000)` | Inherit via `appendOne_gates`, or use the actual selected rank-three source check. |
| 4 | The accepted trace's genuine incoming cube | Inherit via `appendOne_gates`, or use the actual selected rank-four source; carry the cube reserve at the new cap. |
| 5 | The preceding rank-four cube and decreasing rough-prime order | Inherit via `appendOne_gates`, or use the actual selected rank-five source; no odd cube is inserted. |
| After 5 | `actual_postfive_integer_gates` and `run_cap_after_five` | Pass the actual H5 source, its mask and cap to the already proved arbitrary-tail consumer. |

Writing `S_j` for the actual full prefix sum and `c_j` for its stored cap,
the rank-four test gives `S_3+3*x_4<c_3`. The actual checked source action
gives `c_3<=c_4`; hence `S_4+2*x_4<c_4`. At rank five the actual order
`x_5<=x_4` supplies `S_4+2*x_5<c_4`. This is the odd bypass's square reserve,
not a new odd admission test.

`finite_lookups` proves that the rank 3/4/5 source lookups use the actual
incoming trace cap, including prefix-code transport of the earlier frozen
rows. It does not assume a row-to-trace cap identity. The original trace
algorithm is evaluated directly; no alternative retain predicate is built.

The relevant generic interfaces were checked before this construction:
`appendOne_gates` is the existing one-prime invariant;
`actual_postfive_integer_gates` is the existing complete tail invariant;
`select_some_source` is the actual PairRange source entrance. The general
rank point transfer derives its squares from that entrance's whole-box
checks, using the existing helpers made public by the minimal patch.

## Complete signed small attachment

`native_U5_nonzero_all_signed_squares` is the final actual entrance. Its
inputs are the literal `R`, `bank`, `buffer`, `epsilon`, `N`, original pair
membership and nonzero native rho, with scalar allocations

```text
0 <= buffer <= 1/1000
0 < epsilon < 1/8
R.epsilon <= attachmentNu * epsilon^2
attachmentNu * epsilon <= buffer.
```

No source decision, gate list, cap identity or small budget is an input.
The source may be the root or any actual fresh rank 3/4/5 source, with any
subsequent inherited actions. The same concrete word supplies both square
lists after the actual small factor is attached.

The proof calls the rough entry, then the already proved
`original_word_data` for prime activity, decreasing order, small/rough
separation and grid membership. The original rho and the same `s/r` witness
activate the exact pair using `rho_at_pair`. The proof then calls
`actual_signed_small_extension`; it does not repeat that theorem's sign,
factorization, canonical-word or small-tail arguments.

For the actual stored cap `C`, full rough integer squares and primes greater
than one give `B*r<N^C`. The existing scalar allocation gives `L<=N^buffer`.
Consequently

\[
(B r)L<N^{C+\mathrm{buffer}}.
\]

This is the budget actually required by the small-word consumer, which is
stronger than a bound only on the observed `(B*r)*s`. The source cover is
evaluated exactly:

\[
C+\mathrm{buffer}
=\begin{cases}
\operatorname{rootLevel}(N,t)-\mathrm{buffer},&\text{root source},\\
\operatorname{rowCap}(R,\mathrm{code},\mathrm{buffer},\mathrm{branch}),
&\text{actual fresh source}.
\end{cases}
\]

The returned `SignedSupply` contains the rough provenance, both complete
square lists, the last source's exact selected-prime list, the equality of
the complete word to `(fullModulus t k).primeFactorsList.reverse`, and the
same original signed rho/active-pair coefficient identity.

This cover is auxiliary support data. It is not identified with the
density's physical common Q, and the global carrier exponent `.599` is not
substituted for a local `theta_cov`.

## Manuscript location and remaining boundary

Frozen manuscript:
`UyNewNas/chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`.

- [coefficient-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/coefficient-appendix.tex), `coef:full-squares`, `coef:selected-squares`: full and selected-complement prefix squares persist when a smaller unselected prime is appended; the actual preceding cube provides the odd-step square reserve.
- The same appendix's signed small beta attachment and physical/auxiliary level distinction: keep the actual factor witness and sign, and pay the small-level reserve without redefining the original coefficient or density.
- The same appendix, `coef:prime-product-insertion`: the local selected-subproduct and rescaling conditions remain separate from the square lists supplied here.
- [sieve-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/sieve-appendix.tex), `sv:finite-feedback`: the actual incoming state and source history are kept. No physical common-Q reset is introduced.
- [argument.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/argument.tex), `eq:current-PP`: the target discrepancy and coprime mean still use the same signed rho; this candidate supplies support, not its PP estimate.

The previous short/inherited/fresh square-provenance omission is addressed
by this source candidate, and the signed consumer reaches the complete
canonical modulus word. Full (F) is still not a conclusion. The actual
local rescaling, selected-subproduct interval, strict reserves and fixed
whole-atom three-factor representation must be matched to the complete
same-rho family. Adoption of the full original bank, including the separate
W licences, is also not proved here. Existing actual compact-upper/W
suppliers are genuine prior work; their identity with this lower U5
coefficient family is a separate adaptation obligation, not an absent
external theorem.

## Validation boundary

Checked: exact helper proof preservation, patch applicability, public
entrance quantifiers and original policy identity, source import locations,
file hashes, and absence of proof placeholders or unstable private-name
access. The main receiver, frozen fresh source and main cap hashes remain
unchanged in this workspace.

These checks do not establish Lean elaboration, kernel replay, an axiom
audit or whole P3.6 acceptance. Both new modules and both visibility changes
need a separate compilation/verification receipt. The current main compiler
queue was not touched.
