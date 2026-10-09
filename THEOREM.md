# Exact ordered removal theorem

For a binary n by n matrix A, an H4 occurrence is a pair of independently strictly increasing functions from Fin 4 to Fin n whose sixteen entries match H4 exactly. Each pair counts once, with no symmetry quotient or restriction to consecutive indices. An H4-free matrix has no occurrence. The edit count between two matrices is the number of unequal physical cells, allowing both zero-to-one and one-to-zero changes anywhere. Distance is the minimum of that count over all H4-free matrices, divided by n squared.

`OrderedMatrixRemoval4.Removal.no_polynomial_removal` proves that there are no real c > 0 and C > 0 for which the following holds for every n >= 1, every real 0 < epsilon < 1, and every binary matrix A of order n:

```text
epsilon <= distance(A)
    implies
c * Real.rpow epsilon C * n^8 <= copyCount(A).
```

`OrderedMatrixRemoval4.Removal.counterexample` proves the stronger formulation: for every positive real c, C and eta, and every function threshold from real numbers to natural numbers, there exist 0 < epsilon < 1 with epsilon < eta, an order n >= 1 with threshold(epsilon) <= n, and a binary matrix A with distance(A) >= epsilon and strictly fewer than c times epsilon^C times n^8 copies.

The core host has order n_h = (14h+2)2^h for every integer h >= 1. Its all-copy localization theorem pins the pattern zero (3,4), with one-based pattern indices, to a shared leaf row and its own parent-minus column. The resulting physical sparse set has exactly 2 times 2^h cells. Its ordinary copy count is at most 2 times 2^h times n_h^6. Every pattern-free binary repair changes at least (2^h)^2 entries. Consecutive uniform blowups preserve the required normalized bounds and allow orders beyond any threshold depending on epsilon. The common leaf on each axis is literally shared between its two sign views; the two axes remain independent.

Named formal results include `Host.all_copy_localization`, `Host.sparseCells_length`, `Host.copy_count_bound`, `Host.arbitrary_edit_distance`, `Blowup.arbitrary_edit_distance`, `Blowup.copy_count_bound`, `Removal.counterexample` and `Removal.no_polynomial_removal`. The unchanged statement checker and independent audit checker make their ordinary-copy and actual-minimum-edit meanings explicit.

The Lean-certified result does not assert exact copy-count formulas from the paper, minimum possible pattern size, global priority or human peer-review endorsement. All positive real constants and exponents are covered; the theorem is not restricted to rational or integer exponents.

## Follow-up exact repair theorem

Write A_h=`Host.matrix h`, m=2^h, n=`Host.size h`=(14h+2)m. Define B_h as
`Host.TerminalAnchorRepair.matrix h`: set every nonanchor-row entry in the
first column groups of terminal modes W⁻_{h,0}, W⁻_{h,1} to false; retain
all other entries. Equivalently, the only changed descriptor pairs are

```text
(.variable h true p 0, .anchor h (4+p%2) 0 a), 0≤p,a<m.
```

Every changed entry was one. `TerminalAnchorCount.lean` proves:

```lean
theorem exact_minimum (h : Nat) (hh : 1 ≤ h) :
  HFree H4 (matrix h) ∧ Host.editCount h (matrix h) = (2^h)^2 ∧
  ∀ B : BinaryMatrix (size h), HFree H4 B → (2^h)^2 ≤ Host.editCount h B
```

Full namespace: `OrderedMatrixRemoval4.Host.TerminalAnchorRepair`.
`free`, `no_new_copy`, `original_first_column_terminal`, `changed_iff_tags`
and `edit_count` are named supporting theorems. The exact normalized
distance is 1/(14h+2)². The separately written reviewer checker
`checkers/ExpectedTerminalStatement.lean` proves the release definitions
`Removal.repairCount (Host.matrix h) = (2^h)^2` and
`Removal.distance (Host.matrix h) = 1 / (14*(h:ℝ)+2)^2`, named
`IndependentAudit.actual_minimum` and `normalized_actual_minimum`.
The all-depth no-new-copy proof uses anchor-row agreement to restrict the
last two rows, then shows every candidate copy avoids all changed columns.
Original-host localization is applied only to the resulting original copy.

## Follow-up counterexample theorem (depth four)

`Host.PenultimateRepair.repairedMatrix h` zeros the complete
dummy-row × depth-(h−1) negative-variable-column class, retaining everything
else. `orderedCopy_depth4` and `not_hFree_depth4` prove a copy and non-freeness
at h=4. Their increasing physical embeddings are rows `[800,802,804,912]`,
columns `[836,864,868,880]`. The selected bottom-left entry newly becomes zero.
This result is fixed-depth. It does not claim that this repair fails at every
depth, or that all m²-size repairs fail.
