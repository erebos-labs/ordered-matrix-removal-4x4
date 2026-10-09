# All-depth terminal-anchor repair: ordinary proof

This argument concerns the pinned host A_h of release
`45248e57ab1c2197419981bba04e1cde050494ca`. Fix h ≥ 1, m = 2^h,
n = (14h+2)m. The pattern is H4 = 0110 / 1001 / 1010 / 0111.
Row and column embeddings increase independently and match all sixteen bits.

## Definition and count

Let T_h be the two first anchor-column groups of terminal minus-horizontal
modes W⁻_{h,0} and W⁻_{h,1}. Define B_h by retaining every anchor row of A_h
and replacing its entire nonanchor-row-by-T_h submatrix by zeros. This
description is equivalent to the proposed repair: in A_h, a column of the
first group of W⁻_{h,d} has nonanchor positive neighborhood exactly the
leaf rows R_h(p) with p mod 2 = d. No other nonanchor row is positive there.

Equivalently, change exactly

```
(.variable h true p 0, .anchor h (4 + p % 2) 0 a),
0 ≤ p < m, 0 ≤ a < m,
```

from one to zero, and retain all other cells. There are m leaf rows, each
changing exactly m entries in its parity's first anchor-column group. All
these cells are distinct and initially one. The exact edit count is m².

The proof separates **no new copies** from **all old copies are destroyed**.
It never applies original localization directly to B_h.

## Lemma 1: anchor-row agreement forces nonanchor third and fourth rows

Let B be any matrix on the host axes that agrees with A_h on every anchor
row, without restrictions elsewhere. Any ordered H4 copy in B has nonanchor
rows in pattern positions 2 and 3 (zero-based).

Suppose its third row r_2 is anchor. Since all anchor rows precede all
nonanchor rows, r_0 and r_1 are anchor too. Entries on these three rows
therefore agree with A_h.

If the first selected column c_0 is anchor, the ones at (r_1,c_0) and
(r_2,c_0) force r_1 and r_2 into the same complementary anchor group of
c_0's mode. Anchor rows in one group are full twins in A_h and in B.
But H4 has different values at (r_1,c_3) and (r_2,c_3): 1 and 0.
Contradiction.

If c_0 is nonanchor, every selected column is nonanchor by their order.
The ones in anchor row r_0 at c_1,c_2 put those two columns in one
nonanchor class. The ones in anchor row r_2 at c_0,c_2 put those columns
in one class too. Thus c_0,c_1,c_2 belong to the same nonanchor class.
Every such class has at most two full signatures on the anchor rows:
variable signatures depend only on node parity; dummy signatures are fixed.
Their traces on r_0,r_1,r_2, however, are respectively 011, 100, and 101,
three distinct signatures. Contradiction.

Hence r_2 is nonanchor, and the later row r_3 is nonanchor as well.
Only the unchanged anchor rows and original class/signature facts were used.

Lean dependencies for this step are the established original-host facts
`anchor_rows_common_one_twins`, `anchor_row_connects`,
`same_class_three_column_signatures`, and the anchor-prefix ordering facts.

## Lemma 2: every copy in B_h would already be a copy in A_h

Apply Lemma 1 to B_h. Its two last selected rows are nonanchor. Every
column of H4 has a one in at least one of these two rows: their union
of positive positions is 1111. In B_h every column of T_h is zero on
every nonanchor row. Thus none of the four selected columns lies in T_h.

The matrices B_h and A_h agree on every column outside T_h, on every row.
All sixteen copy entries consequently agree, so the same independently
increasing embedding is a copy in A_h. This proves the no-new-copy assertion
at all depths; it does not rely on localization after editing.

## Lemma 3: every original copy uses T_h as its first column

Take a copy in A_h. The established original shape theorem gives two
anchor rows, a first anchor column, and nonanchor third/fourth columns.
Write the second row's anchor tag as (l,k,g,a) and the first column's tag
as (u,v,w,b). The established orientation theorem
`second_row_first_column_groups` gives l=u, k=v, g=1, w=0, where Lean's
group numbering is zero-based. Thus the second row is group 2 and the
first column group 1 of one common mode (l,k).

Original all-depth localization gives

```
r_2 = R_h(p),    c_3 = C⁻_{h-1}(floor(p/2)).
```

The pattern ones A_h(r_2,c_0)=1 and A_h(r_1,c_3)=1 imply that this
leaf row lies in row role 1 of (l,k), and that this negative-parent column
lies in column role 2 of (l,k). Inspect the six-mode role table:

- A leaf can have row role 1 only in V⁺_h, W⁺_{h,d}, or W⁻_{h,d}.
  The V⁻ possibility would require l=h+1, outside the host's mode levels.
- A depth-(h−1) negative column can have column role 2, in one of those
  possible modes, only in W⁻_{h,d}. Its negative sign excludes V⁺ and W⁺.

Therefore l=h and k=4+(p mod 2). The first selected column is a column
of T_h. In particular its pattern one at r_2 is one of the repaired cells.
This role-table deduction handles h=1 too, since h−1<h and the two root
signs remain distinct. The Lean proof uses six finite mode cases and integer arithmetic,
without a new classification assumption.

## Theorem: exact all-depth repair distance

If B_h contained H4, Lemma 2 would make its embedding an original copy in
A_h. Lemma 3 would place its first selected column in T_h. Lemma 2 already
proved no selected column can lie in T_h. Contradiction. Thus B_h is H4-free
for every h≥1.

Its exact m² edit count is proved above. The inherited theorem
`Host.arbitrary_edit_distance` applies to every H4-free binary matrix on
these physical axes, with edits anywhere and in either direction, and gives
edit count at least m². Combining the valid upper and lower bounds yields

```
min { editCount(A_h,B) : B is H4-free } = (2^h)^2, for every h ≥ 1.
```

The normalized exact distance is 1/(14h+2)². This concerns the specified host,
not uniqueness of repairs or a classification of all equality cases.


## Formal statements and finite checks

`OrderedMatrixRemoval4/TerminalAnchorRepair.lean` formalizes the three lemmas
and freeness; `TerminalAnchorCount.lean` proves the physical edit support and
the exact optimum. The theorem `Host.TerminalAnchorRepair.exact_minimum`
supplies an attaining H4-free matrix and an unrestricted lower bound for every
H4-free binary matrix. It is valid for every natural h ≥ 1.

`checkers/check_terminal_anchor.py` is a separately written finite checker.
It reconstructs the pinned host, scans every compressed column quadruple at
h=1,2,3,4, and compares a literal full physical scan at h=1. The candidate is
block-constant; the four distinct pattern row and column signatures require
four distinct blocks, so compression is valid for this candidate's copy test.
This does not assert that arbitrary optimal repairs can be compressed.
These finite checks support implementation consistency; the all-depth result
is the ordinary argument and Lean theorem above.
