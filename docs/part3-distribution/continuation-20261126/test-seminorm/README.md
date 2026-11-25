# P3.5 actual Fourier test seminorm — accepted component

**The two owned modules passed exact-head strict compilation, bundled kernel
replay and the complete declaration/type/transitive-axiom gate. P3.5 remains open.**

- Mathematical commit: `0ef2ad29bfa30917b3b9ec7008cb831ad1af9408`.
- Branch: `codex/p3-5-full-kernel-20261125`.
- P3 task: `83126d04315b4091805fa85e6da8d6e7`; exit 0, 167.09 seconds,
  peak process-tree RSS 5,730,811,904 bytes.
- Complete owned inventory: **40 declarations**, comprising 32 theorem records
  and 8 definitions. The inventory includes generated/private helpers.
- Transitive axioms: only `Classical.choice`, `Quot.sound`, `propext`.
- Evidence: [receipt](RECEIPT.json), [original report](report.json),
  [complete declarations](declarations.json), [full theorem types](theorem-types.txt),
  [original verification ZIP](p35-test-seminorm-0ef2ad29.zip).

## Mathematical result

For each mode `ell : Fin 4 → ℤ` of the actual period-64 Fourier expansion, define

```text
S_d(ell,Y) = ∑ n=0..d, sup over q∈ℝ of
  Y^n * ‖iteratedDeriv n (spectralTest ell Y) q‖.
```

The code proves that every supremum range is nonempty and, for `Y > 0`, bounded
above. It proves nonnegativity and domination of every evaluation. With the
existing fixed-cutoff jet constant, it bounds `S_d` by a fixed constant times
`(1 + |ell 0|)^d`.

The terminal theorem is
`ImbalancedChen.Part3.ActualSpectralTestSeminorm.actual_uniform_testSeminorm_budget`.
For every fixed natural `d`, it chooses `C > 0` before all moving parameters and
then proves, for `rho ≥ 0`, `|sigma| ≤ 1`, and `Y > 0`, both

```text
Summable (ell ↦ ‖actualCoeff rho sigma ell‖ * S_d(ell,Y))

∑' ell, ‖actualCoeff rho sigma ell‖ * S_d(ell,Y)
  ≤ C * (1 + rho)^(4*(d+3)).
```

The suprema are inside the Fourier sum and are chosen per mode. Summability is
proved by domination using the already accepted actual weighted Fourier bound;
it is not an added hypothesis. The constant is independent of `rho`, `sigma`,
`Y` and the actual mode. All finite derivative orders through `d` use a single
highest-order weight. The order remains arbitrary: this component does not assert
that order four suffices for the external Pascadi test theorem.

This implements the fixed-order Fourier payment in frozen Appendix A.5,
lines 705–717. [Manuscript correspondence and remaining interfaces](MANUSCRIPT_BOUNDARY.md)

## Source reuse and owned scope

| Owned module | Complete serialized declarations | Role |
| --- | ---: | --- |
| [Part3ActualSpectralTestJets](../../../../ImbalancedChen/Part3ActualSpectralTestJets.lean) | 27 | Selected historical phase and all-order actual jet proofs, including generated helpers |
| [Part3ActualSpectralTestSeminorm](../../../../ImbalancedChen/Part3ActualSpectralTestSeminorm.lean) | 13 | Reused finite constant plus the per-mode supremum and actual Fourier payment |

There are 33 written declarations: 22 selected from existing M/R20/S22 sources
and 11 in the new supremum derivation. Their original public names are preserved.
This selection does not promote the complete historical source-only modules.
The 55 project dependencies retain identical bytes and normal imported-environment
trust. Previous continuous Cauchy and whole-height acceptance are reused.

[Donor excerpts](DONOR_EXCERPTS.json), [frozen extraction](SELECTED_SUPPLIER.lean.txt),
[exact repairs](SOURCE_REPAIRS.patch), [source manifest](SOURCE_REUSE.json), and
[dependency closure](DEPENDENCY_CLOSURE.json) preserve the provenance.
The exploratory handoff `remaining-math.md` calls this same 55-entry closure
`jet-supplier-closure.json`; its published filename is `DEPENDENCY_CLOSURE.json`.
The repairs
respond to the actual P3 diagnostics: phase-name ambiguity, explicit coercion
simplification, an unavailable absolute-value lemma, compactness method syntax, and
explicit real-to-complex smooth composition. No hypothesis or conclusion was
weakened. The native smooth composition proof was itself reused from the accepted
reconstruction source.

The provenance gate additionally checks all six donor excerpts against their
intended extraction bytes. The earlier source review's finding is resolved;
[the scoped rereview](PROVENANCE_REVIEW.md) and
[targeted provenance checks](PROVENANCE_FIX_REPORT.md) retain the record.

## Verification evidence

The original cloud report records 35 successful stages and 107 source/configuration
hashes. Every recorded source hash was checked against the current candidate;
every stage log hash and the generated audit hash were checked against the
extracted evidence. The ZIP is 35,063 bytes with 39 members and SHA-256
`4941a7950ca6850f7f6e922f435db473b22c2f2379b0161582a131feef14ae67`.
[Archive member manifest](ARCHIVE_MANIFEST.json) · [Cloud task metadata](CLOUD_TASKS.json)

The source manifest's pending status describes the earlier preflight snapshot.
It is deliberately preserved because the verifier hashed it. The later
`PASSED` report and acceptance receipt give the final status.

Check out the mathematical commit in a clean isolated worktree using the
unchanged pinned environment, then verify these two modules:

```bash
LEAN_NUM_THREADS=1 python3 verification/verify_part3_continuation.py \
  --group p35-test-seminorm \
  --expected-head 0ef2ad29bfa30917b3b9ec7008cb831ad1af9408 \
  --output-dir .lake/p35-test-seminorm-verification-0ef2ad29
```

## Remaining P3.5 boundary

The actual positive/negative Bessel transforms still need their uniform
application of the manuscript's external test estimates, with matching
normalizations and sufficient fixed derivative order. The actual Y04 spectral
row closure still needs six registered source files whose bytes were not
recovered from the checked local/remote/archive scope. P1 found no matching current filenames in its checked scope; the P2 inventory
remains queued. [The cloud source record](CLOUD_SOURCE_RECOVERY.md) retains the
actual result and the pending task ID.
The code does not introduce a replacement spectral-row premise or prove ABL,
Kim–Sarnak or Pascadi. It does not mark the full P3.5 node compiled.

[Source inventory](new-source-inventory.md) · [Remaining mathematical obligations](remaining-math.md)
