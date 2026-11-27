# P3.1 common hard-tail increment: formally accepted

The source commit is **a7e34b33f540dff1e507909f8ba42cea446e87cb**, tree
**c90325b7694b9bda4e8826cedd7f74cec2d21889**. This documentation descendant
preserves all Lean sources, verifier code, configuration and dependencies from
that exact accepted commit.

## Observed result

P1 task `job_28e57945095143718c0740f77e4d33fd` completed successfully:

- 44 of 44 stages passed.
- All six target modules passed fresh strict compilation with warnings as errors.
- All six modules passed individual bundled kernel replay.
- The complete defining-module inventory contains 62 declarations: 39 source
  declarations and 23 generated declarations. Generated helpers are not counted
  as independently authored proofs.
- The transitive axiom set is limited to `Classical.choice`, `Quot.sound`, `propext`.
- All 15 existing source/object gate regression tests passed.
- The complete project closure contains 81 modules. Every one of the 75 prior
  provider source files and compiled object bindings matches the previous formal
  acceptance. The compiler and checker binary hashes also match that installation.
- The actual run starts and ends with a clean worktree and pinned clean dependencies.

The formal report SHA256 is
`7be50291894ce63a85afc2c1dbbd9828f1c35abb0434a31eefa64b68d3a3ad51`.
The full archive is 154435 bytes, SHA256
`8c89d53add3d28366703f344e601268ce7c58b72d00e42fd50c50661edee88e1`.
All archive members, stage logs and frozen paths were independently checked.

## Mathematical increment

For every natural `r >= 2`, one constant `A_r > 0` precedes every scale and every
source/coefficient parameter. With `B,C,R > 0`, all six actual smooth pieces use
the single cutoff `J = ceil(10*C*R/B)` and satisfy

\[
\|\operatorname{sixSmoothMass}-\operatorname{actualTruncatedSix}_{J}\|
\leq \frac{6A_r C^2}{R^{r-1}}
\operatorname{sourceAbsMass}(\operatorname{nonzeroSource}S,\lambda,\omega).
\]

The true complementary-subtype frequency series is matched to the literal hard
window. The finite kernel is explicitly the zero-m term plus both signed common
dyadic blocks. The primary partition is combined before taking norms, yielding
one weighted sum over the original nonzero source. No primary-block-count loss
is introduced. The zero-y contribution retains its complete frequency kernel;
the zero-m contribution inside the nonzero-y kernel remains present.

Twenty-one original supplier declarations were recovered. Fourteen original
fragments remain byte-exact; seven use ten fixed mechanical proof-expression
adaptations, fully pinned to the original blobs and byte slices. The new consumer
adds 14 theorems and 4 definitions. Existing source and smooth-mass providers
were reused without alteration.

## Evidence

- [Formal report](verification/report.json)
- [Full declaration inventory](verification/declarations.json)
- [Source/generated declaration classification](DECLARATION_CLASSIFICATION.json)
- [Independent formal acceptance review](FORMAL_ACCEPTANCE_REVIEW.json)
- [Mathematical review binding](MATHEMATICAL_ACCEPTANCE_BINDING.json)
- [Accepted scope](ACCEPTED_SCOPE.json)
- [Compiler run metadata](RUN.json)
- [Complete evidence archive](verification-attempts/formal-a7e34b33-evidence.zip)
- [All failed and passing attempts](verification-attempts/ATTEMPTS.md)

The old shared report's generic object-scope sentence says "only new consumer
replayed". Its explicit target arrays and all six replay logs are authoritative
for this round. The unchanged shared gate is retained, and no replay of every
external imported module is claimed.

## Remaining original P3.1 work

**This completes the common hard-tail increment, not the whole P3.1 node.**
The coefficient mass is still explicit. The next existing suppliers are
`rawLabelBudget`, `sourceAbsMass_le_rawLabelBudget`, and the actual lambda/omega
norm bounds. Their true definition closure must be reused and connected to the
nonzero-source filter and the present six-piece bound. The original family
scales, permitted frequency parameter and outer reconstruction costs then need
an actual uniform x-budget. `OriginalData`/`FixedBlock` identities and the two
distinct zero contributions retain their separate obligations. External Shiu,
ABL, Kim–Sarnak and spectral J/A inputs remain explicit boundaries.

The exact source locations and manuscript passages for the next step are in
[NEXT_P31_STEP.md](NEXT_P31_STEP.md). No new target-shaped assumption is introduced
to replace any of those obligations, and the complete P3.1 node is not marked
finished by this receipt.
