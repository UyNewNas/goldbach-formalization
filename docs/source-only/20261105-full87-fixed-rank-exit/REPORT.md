# P1.4 — finite odd-exit square-test potential and owned87 level floor

## What changed mathematically

Earlier `P4AOriginalFull87EighthCutoff` only controlled the eighth
prefix prime p8. It could NOT bound the last prime at deeper ordinary
first exits. The new source establishes a generic fixed-rank lemma that
uses **successive odd full-square tests at one real level**, without
using the rank-eight last prime as a surrogate for later exit primes.

For j=2m+1, write a_i=log_N(p_i) in actual *processing order*,
S_{2k}=sum_(i<2k)a_i. The passed odd tests are
`S_{2k}+3*a_{2k}<beta`, k<m, while the exiting odd test satisfies
`beta<=S_{2m}+3*a_{2m}`.  Sorting gives a_{2k+1}<=a_{2k}.

The *exact* potential inequality is:
`beta <= 3^k*(beta-S_{2k})` for all k<=m.
It yields `a_{2m} >= beta/3^(m+1)`. This is quantitatively stronger
than manuscript beta/(3*2^(j-1)) because 3^m<=4^m.
It uses no asymptotics, Lebesgue integral or external analytic theorem.

The integer-power adapter derives N<p_last^K from the exact logarithmic
identity p_last=N^a_last, beta>=betaFloor>0 and
3^(m+1)<betaFloor*K. It calls the existing exact finite
`target_deletion_power_gap_sandwich`; it does not invent a factor.

Separately the old original87 `Source` inequality forces
`comparison c t > 9*cutoff`, and the SAME realized own-sixth parent
and finite eighth cap satisfy `>9*cutoff`. The actual source cutoff is
53/13824. The scale choice `30*3^(m+1)` is target-independent since
`30*9*cutoff = 1+9/256 >1`.

The concrete `owned_eighth_ordinary_fixed_rank_deletion` selects
either actualParent or the existing finiteCap, not a caller-invented
level, and makes all still-required ordinary square checks explicit.
The finite budget is conservative by one extra factor count.

## Verification and honesty

- 9 Lean theorem candidates, 1 local definition, 280 source lines.
- Local exact Fraction cases: 10,093 successful-prefix, of which
  8,359 first-exit cases; 172,368 finite prime-deletion cases.
- Independent linear-programming shape diagnostics: ranks j=1..15 odd.
  These diagnostics do NOT verify universal Lean statements.
- Source/commit/tree and branch checked through the GitHub connector.
- All candidate proof terms are **uncompiled and unevaluated**.
  No CI or numerical certificate rerun, no kernel proof or independent review.

## Correctness boundary — P1.4 stays yellow

The missing **manuscript-internal** step is to derive
`hprior`, `hpair`, `hexit` and log reconstruction from the
*actual* ordinary policy, retained states, inherited original87 source
and frozen old/new cap. Earlier odd tests were made at historical
levels and cannot silently be identified with tests at the final cap.
The signed full-modulus beta and occurrence multiplicities remain unchanged;
the new lemma makes no claim about their asymptotic error.

Still open: common-source ordinary exit-series/residual integral
asymptotics; primitive/centre error and sixth filtering loss; saved
original87 archive/endpoints; two compiler/density reserves; same-rho
assembly; staging and Lean/kernel/axiom verification.

No new theorem or axiom is inserted for an external analytic input.
The external-input register records future citations as unused.
