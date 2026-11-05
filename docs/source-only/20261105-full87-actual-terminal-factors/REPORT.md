# P1.4 run 4 — exact full-q prime factors of actual ORDINARY terminal leaves

Date 2026-11-05. Parent 615fe5a2326618699b57044068eb93fb5383ca88.
Status **SOURCE_ONLY, UNCOMPILED, UNEVALUATED, ZERO FORMAL CREDIT**.

## Actual increment and point of difficulty

The previous factor population packet bounded a full modulus d by omega(d). This run identifies omega(d) on the ACTUAL changed original87 state source, including EVERY descendant selected by either the original own-sixth-parent ordinary policy or the saved-eighth ordinary policy. It does not substitute the rank-eight prefix for the full terminal selected history.

- \`changed_mem_real_frontier\`: each changed occurrence belongs to the *existing* filtered-sixth rank-eight frontier (owner and strict trim are unchanged).
- \`actual_terminal_selected_sublist\`: the terminal leaf's entire selected prime history (not merely its first eight primes) remains an ordered sublist of the original \`roughPrimeUniverse N cap w z\`. The proof composes the existing frontier selected/remaining sublist invariant with the existing retained-leaf invariant.
- \`actual_terminal_metadata\`: the terminal selected history is duplicate-free, excludes primes dividing N, and every selected prime lies in [w,cap).
- \`actual_terminal_full_factor_set\` and \`actual_terminal_full_factor_card\`: for each ACTUAL small-support divisor a and actual terminal leaf, the complete physical modulus d=a*leaf.selected.prod has
  \`d.primeFactors = a.primeFactors ∪ leaf.selected.toFinset\` and
  \`omega(d)=omega(a)+leaf.selected.length\`.
  This uses strict-small versus inclusive-rough support disjointness, rather than assuming a and the rough product are coprime.
- \`actual_terminal_factor_budget\`: inserts this exact count into the EXISTING \`factorModulusBudgetTest\`, so on genuine terminal leaf moduli the nonnegative envelope is at most
  \`(omega(a)+terminal selected length)/phi(d)\`. It is not a signed-saving monotonicity statement.
- \`actual_terminal_prime_population_of_cap_le_N\`: if \`cap≤N\` then every prime factor of d is in the original inclusive prime prefix, giving exact \`chenPrimeDivisorCount N d = omega(a)+leaf.selected.length\`, EVEN when d>N. The cap condition is explicit and unproven in the global schedule; no invalid conclusion \`d≤N\` is used.
- \`original_sixth_terminal_factor_card\` and \`saved_eighth_terminal_factor_card\` are literal old/new ordinary level instances. Same changedStates, dynamic own-sixth parent, sign-dependent beta terminal and full-q source as the preceding packet.

The bound \`omega(a)+8\` cannot be applied to a terminal full modulus: later ordinary continuation branches may select further rough primes. The newly precise per-leaf count exposes that remaining obstacle instead of hiding it.

## Mathematical and validation limits

The theorem is about exact FINITE support/factor populations, not a uniform bound on the signed attached variation, nor o(1) after normalization. The leaf's selected length can exceed 8. For the actual common schedule one must (1) establish the enumeration cap relationship or use filtered <=N factors, (2) bound the depth-weighted signed beta variations with the SAME old/new policies, (3) bridge the genuine ordinary continuation mean to the residual integral and pay the sixth/filter and independent reserves.

No original87 certificate array replay, numeric endpoint, external number theory proof, new axiom, parameter change, policy change, or workflow execution is included.

Verification performed: connector-side static structural checks on the 1-module candidate and 28,000 synthetic finite factor/selection cases (including d>N, N=0, and large terminal depth). Those checks do not parse Lean or run the mathlib kernel. No Lean/Lake/CI, proof-term evaluation, transitive axiom audit or independent review.

## Next precise action

Use the above full-modulus factor identification to develop a depth-weighted \`absoluteSignedTest\` terminal-envelope induction on the existing actual leaf lists, preserving both sign-specific beta attachments and N-dependent small support. Keep the actual terminal depth in the bound, and do not assert a normalized small-o payment without the integral/distribution bridge.
