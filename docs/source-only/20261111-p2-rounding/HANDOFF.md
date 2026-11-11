# P2 paired certificate rounding consumer, 2026-11-11

Status: SOURCE ONLY, UNCOMPILED. No Lean, lake, Elan, native evaluator, CI, or user-computer execution was performed. No blue/green promotion.

## Baseline, ownership and provenance
- Parent source commit: 3a46b3f0a4ee8ee7e628c9234717fae03064a52b; sealed branch remains unchanged.
- Read the sealed ROUND_PAUSE_CHECKPOINT.md, DISPATCH.json and docs/part2/ADOPTED_EVIDENCE_CATALOG.md. P1.4 owns actual history/full87/saved87; P4 owns complete tails and All22 attachment; P3/P5 own their separate distribution/lower-count routes.
- Lean leanprover/lean4:v4.33.0-rc1; mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1; goldbach 09b97db5764ade1246bfb77206baa1b124760958. No toolchain/dependency edits.
- Manuscript verification/data/corpus-renewal-paired-certificate-v2-20261010.json has the SAME Git blob 49499697cca96de5f7b779e95077874ce5f9d119 (3604398 bytes) at both historical ba6ec11d800eccc54406490631895e174de85766 and current route pin 9731290e8f53cffda44129906cde6a965eaa869b. Historical recorded SHA256 f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7 was read from the existing catalog, not rehashed from full JSON this run.
- Read current paper/source/modules/corpus-renewal-paired-certificate-v2-20261010.txt: 6091 + 11481 = 17572; old 17772 is a transcription error. 7/3 replaces 12/5, not an additional gain. K/80 is K*(1/20)*(1/4), no permutation factor.
- Independently decoded firstU from the existing FullMaskData source: 186 entries, min321/max511, sum(512-firstU)=17572. Did NOT rerun the expensive finite row checker or replace it by this count.
- New file ownership: only ImbalancedChen/Certificates/P2PairedRoundingLedger.lean and this report.

## Duplicate-work check and reuse
Inspected existing FullMask/FullCertificate, FullMaskData, StripCertificates, FullCertificateData, PairedFibreIntegral, GlobalGeometry, P2AdoptedRowsActualEnclosure, P2AdoptedUnionIntegral, P2PairedSupportFubini, P2SemanticGainSetIntegral, P2PairedSemanticRestrictionError, P2PairedBoundaryCollarReserve, P2PairedFibreScaleNormalization, P2OriginalCertificateBudgetAssembly.
These already supply source candidates for checked actual row integrals, pointwise comparison, positivity, compact integrability, seven null walls, genuine set-integral Fubini and finite union, scaling and collar limits. This run does NOT recreate them.
Verified pinned external goldbach theorem buchstab_le_one derives from buchstab_bounds; reuse occurs through the existing region_gain_le_half supplier. No new external theorem is formalized.
Inspected current source directories and P2 branch search; the old chatgpt/chen-p2-certificates only reaches Prefix192 and is not used as baseline. GitHub code search for the new ledger symbol and exact accumulated-width numerator returned no result (not an exhaustive all-branch proof). No connected local checkout existed; user-local materials and sealed unpublished packets remain unverified, not presumed absent.

## Actual new deductions
Let I denote the actual normalized constant-minorant union integral, S the actual Buchstab semantic gain.
L = 55858378943374979/10^20; U = 55858409959907296/10^20; F = 558583/10^9.
- All-row sum of certificate widths is exactly W = U-L = 31016532317/10^20.
- For every finite row subset, summed lower and upper directed integral errors are nonnegative and add to exactly the summed certificate widths.
- R = L-F = 78943374979/10^20 > 0, hence R <= I-F <= R+W.
- Actual semantic density <= 10 times the constant certificate density (omega-1/2 <= 1/2). Integrating with already-proved integrability gives L <= S <= 10U.
- Crucially W is NOT a bound on S-I. The narrow U is NOT an upper bound on S.
- For a measurable actual retained subset s of region, if the observable geometric bound densityBound * volume(region minus s) fits R, then retained actual semantic gain >= F.
- The existing seven-wall collar limit with error R/2 supplies a positive buffer with actual retained gain strictly > F. No historical parent inclusion, explicit buffer rate, prime-box identity or saved87 licence is asserted.

These are minimal consumers of the adopted manuscript's safe rounded gain and error ledger, not additional gains, not an All22 upper-policy entry, and not a replacement for P1/P4/P5 obligations. P4 can consume the explicit directed-error accounting where a matching component/domain is established; the paired correction belongs to the lower ledger.

## Validation performed
- Exact Python Fraction assertions: U-L, L-F positivity, half-reserve strict-floor inequality, and 10/80 = (1/4)*(1/2).
- Independent static arithmetic count of 186 strips /17572 rows.
- Lexical source guard: no sorry, admit, axiom declaration, native_decide or unsafe.
- Independent read-only mathematical/source review: no mathematical direction error found; its suggestion to expose numeric endpoints before exact_mod_cast was applied.
- NO Lean elaboration, kernel replay, axiom audit or CI. Imported source candidates likewise remain unaccepted here.
- No workflows changed; publication message contains [skip ci].

## Remaining obligations and exact next entry
1. Existing compilation-repair flow must validate this exact module plus its imported baseline chain under the fixed toolchain, kernel and axiom gates. First likely interface checks: Rat.cast/Finset sums, setIntegral_mono_on and collar supplier types.
2. Do not reopen already-written Fubini/checker proofs as new work. Repair only actual diagnostics.
3. P1 supplies actual historical parent retention/ownership and saved-floor licences; this module's subset/volume premises do not supply them.
4. P4 supplies complete noncompact-tail and signed All22 component attachments; none is proved by the paired mask.
5. P2 broader adopted catalog still has other actual-integral and historical-query obligations. No whole-line source closure or completion is claimed.
6. Next source entry: bind the appropriate actual retained subset to the explicit rounding reserve, only after the owning history route supplies its genuine domain. Otherwise progress other adopted catalog integral gaps rather than duplicate the existing paired bridge.
