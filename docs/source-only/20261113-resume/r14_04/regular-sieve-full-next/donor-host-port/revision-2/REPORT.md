# Selected OAI sources for the pinned host

These four postimages replace the named donor modules at their original OAI import paths. Together with the other 14 donor modules they supply the OAI portion of the six-source and all-parameter arithmetic proof candidates. `REGISTRY.json` lists the original raw and selected hashes and every substitution. All four statement types are preserved, as are the arguments to the affected proof steps.

Three spellings of conditional-reduction lemmas are mapped to `if_pos`, `if_neg` and `dif_pos` from the host core. The product monotonicity application uses `Finset.prod_le_prod` from the pinned host mathlib. There are 11 identifier replacements and no mathematical changes. The first port handled the product spelling alone. This selection supersedes it. The native six-source generation remains `revision-3`.

The unported donor uses Lean 4.34.1 with mathlib d13f23b7, while the host uses 4.33.0-rc1 and e4c91783. Source review identified these concrete differences. The selected sources have no compiler or kernel result.
