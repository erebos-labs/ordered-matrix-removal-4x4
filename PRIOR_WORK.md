# Focused prior-work check for the terminal-anchor repair

Scope: the specific H4 terminal-anchor repair and equality of unrestricted
repair distance with m². This is a bounded source check, not a priority search
over all literature, forks, or unpublished work.

The public v1.0.0 baseline at
[`45248e57ab1c2197419981bba04e1cde050494ca`](https://github.com/erebos-labs/ordered-matrix-removal-4x4/tree/45248e57ab1c2197419981bba04e1cde050494ca)
contains the host, all-copy localization, and arbitrary-edit lower bound.
Its paper explicitly refrains from claiming an m² upper bound or exact repair
distance for this two-group host. A public GitHub API read of its pinned paper matched the local Git-object
bytes (SHA-256 c1acaf9709bb1741a56ccdeb0e6576e77a67ca95084645f8786ba1d0bf816e51).

The closest located source is ProveIt's
[5×5 obstruction, pinned 7 October 2026](https://github.com/VladimirReshetnikov/ProveIt/tree/bfbfe915186310fdf745a7a089e7dd88eeb773b1/Combinatorics/OrderedMatrices/Research/ordered-matrix-removal).
Fresh reads of the main manuscript, `sections/exact_and_sampling.tex`, and
`sections/generalization_and_research.tex` show an exact m² repair theorem
for the three-anchor, 5×5 construction. Its repair zeros the dummy-row-by-leaf-
column rectangle. The same source describes the displayed H4 candidate and
the failure of that rectangle repair for its two-anchor construction. The
new terminal-first-anchor-column repair is a different edit set.

A fresh path-filtered public commit-history read returns only the original
`bfbfe915186310fdf745a7a089e7dd88eeb773b1` intake commit for that research
directory. Its pinned generalization section still presents control of H4's
extra copies as a research question. This supports comparison with the known
published source, not absence of other solutions.

Targeted GitHub code search for `"ordered-matrix-removal" "anchor" "repair"`
returns one catalogue README, and `"ordered-matrix-removal" "m^2"` returns
zero items. A broader search using ordered/matrix/terminal/repair returns
92,709 mostly irrelevant matches; its first 20 hits are not an absence test.
General web searches located the OpenAI family title and the established
ordered-removal literature, rather than an independent proof of this repair.
The check was performed on 9 October 2026. Search is default-branch
and phrase dependent; raw responses are retained outside this public candidate.

The mathematical foundations remain attributed to the pinned host sources:
OpenAI/math's signed-tree, role, threshold, and propagation construction;
ProveIt's explicit H4 candidate and smaller-anchor obstacle; and the v1.0.0
all-depth localization and lower bound. Exact m² repair distance as a general
phenomenon is already present in the 5×5 source. The new result concerns this
particular 4×4 host and terminal-anchor repair. **No global novelty, priority,
minimality among patterns, or uniqueness claim is made.**
