# Counterexample to the full penultimate-negative-column repair

Let P_h set every dummy-row × negative-variable-column cell at depth h−1
to zero, with no restriction on the node or clone, and retain every other
cell of the pinned host. `PenultimateRepair.repairedMatrix` is this matrix.

At h=4, m=16 and n=928, select zero-based physical rows
`[800,802,804,912]` and columns `[836,864,868,880]` on the independent axes.
They are increasing. The selected matrix changes from
`0110 / 1001 / 1010 / 1111` to `0110 / 1001 / 1010 / 0111`.
Exactly the selected bottom-left cell (912,836) changes. Consequently P_4
contains H4 and is not H4-free, despite making 256 edits in the full class.

`OrderedMatrixRemoval4/PenultimateRepair.lean` proves the descriptors,
increasing embeddings, all sixteen matching bits, ordered copy and
non-freeness at depth four with ordinary kernel reduction. The separate
`checkers/IndependentDepth4.lean` rechecks the literal copy without using
the supplied descriptor/matching/copy lemmas. Its generic support and
changed-cell characterization apply to arbitrary h; **its copy and
non-freeness conclusions are restricted to h=4**. The 256-cell count here is
an independent bounded physical check, not an all-depth counting theorem
for this failed repair.

Failure of P_4 does not exclude other 256-cell repairs. The terminal-anchor
repair in the companion proof attains 256 edits and is free at depth four,
and attains (2^h)^2 edits for every h≥1.
