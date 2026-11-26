# ShapeArrays source repair

The original normal compilation failed at the two fixed-size transport lemmas.
Its exact 3700-byte diagnostic is retained under the original failure-inspection
folder. The old `simpa only [h.1]` left the universal hypothesis indexed by
`Fin n` while the goal used the actual facet or face-vertex array size.

The replacement introduces the actual array index `i`, builds an index in
`Fin n` from the same natural value, and transports only its bound proof with
`h.1 ▸ i.isLt`. Applying the original hypothesis gives the required inequality
at exactly `i.val`; no theorem statement, array, data input, imported module,
audit, resource option, or other proof is changed.

The original main source and frozen fourteen-target stage are retained. This
separate candidate must pass its own normal, kernel, and complete owned audit
checks before it receives credit. No already accepted proof is rerun.
