"""Independent finite audit, written from the frozen Host.lean definitions.

No researcher generator, scanner, compiled proof, or certificate is imported.
Execute: python3 checkers/check_terminal_anchor.py
"""
from itertools import combinations
from pathlib import Path
import hashlib
import json
import math
import random
import time

PATTERN = ('0110', '1001', '1010', '0111')


def axes(h, physical=False):
    m = 1 << h
    def copies(tag, count):
        return [tag + (a,) for a in range(count if physical else 1)]
    anchors = [x for level in range(1, h + 1) for kind in range(6)
               for group in range(2)
               for x in copies(('A', level, kind, group), m)]
    dummy = copies(('D',), m)
    def tree(column, depth, node):
        if depth == h:
            return [('V', depth, True, node, 0)]
        sign = column
        return (copies(('V', depth, sign, node), 1 << (h - depth))
                + tree(column, depth + 1, 2 * node)
                + tree(column, depth + 1, 2 * node + 1)
                + copies(('V', depth, not sign, node), 1 << (h - depth)))
    return anchors + tree(False, 0, 0) + dummy, anchors + dummy + tree(True, 0, 0)


def role(h, column, level, kind, group, x):
    if x[0] == 'A':
        return False
    if x[0] == 'D':
        return (kind < 2 and group == 0) if column else (kind >= 2 and group == 1)
    _, depth, sign, node, _ = x
    signed = lambda want: sign == want or depth == h
    if column:
        if kind < 2:
            return group == 1 and depth + 1 == level and signed(kind == 0)
        if kind < 4:
            return signed(True) and ((group == 0 and depth + 1 == level)
                   or (group == 1 and depth == level and node % 2 == kind - 2))
        return signed(False) and ((group == 0 and depth == level and node % 2 == kind - 4)
               or (group == 1 and depth + 1 == level))
    if kind == 0:
        return signed(True) and ((group == 0 and depth == level)
               or (group == 1 and depth + 1 == level))
    if kind == 1:
        return signed(False) and ((group == 0 and depth + 1 == level)
               or (group == 1 and depth == level))
    return group == 0 and depth == level and signed(kind < 4) and node % 2 == kind % 2


def entry(h, r, c):
    if r[0] == c[0] == 'A':
        return r[1:3] == c[1:3] and r[3] != c[3]
    if r[0] == 'A':
        return role(h, True, *r[1:4], c)
    if c[0] == 'A':
        return role(h, False, *c[1:4], r)
    if r[0] == 'D' or c[0] == 'D':
        return True
    _, i, s, p, _ = r
    _, j, t, q, _ = c
    return ((i == j and (s or i == h) and (t or j == h) and p <= q)
            or (i == j and i < h and not s and not t and p < q)
            or (i == j + 1 and (s or i == h) and t and p // 2 <= q)
            or (i == j + 1 and (not s or i == h) and not t and p // 2 < q))


def matrices(h, physical=False):
    rows, cols = axes(h, physical)
    a = [[int(entry(h, r, c)) for c in cols] for r in rows]
    b = [line[:] for line in a]
    changes = []
    weight = lambda x: (1 if physical else ((1 << h) if x[0] != 'V' else 1 << (h-x[1])))
    for i, r in enumerate(rows):
        for j, c in enumerate(cols):
            if c[0] == 'A' and c[1] == h and c[2] in (4, 5) and c[3] == 0 and r[0] != 'A':
                b[i][j] = 0
            if b[i][j] != a[i][j]:
                assert r == ('V', h, True, r[3], 0)
                assert c[:4] == ('A', h, 4 + r[3] % 2, 0)
                changes.append((i, j, weight(r) * weight(c)))
    assert sum(w for _, _, w in changes) == (1 << h)**2
    assert sum(map(weight, rows)) == (14*h+2)*(1 << h)
    assert len(set(rows)) == len(rows) and len(set(cols)) == len(cols)
    return rows, cols, a, b, changes


def literal_scan(a):
    """Independent literal cell scan; earliest matching row chain is complete."""
    checked = 0
    for cc in combinations(range(len(a[0])), 4):
        checked += 1
        k = 0
        rr = []
        for r, line in enumerate(a):
            if ''.join(str(line[c]) for c in cc) == PATTERN[k]:
                rr.append(r)
                k += 1
                if k == 4:
                    return checked, (rr, cc)
    return checked, None


def bit_scan(a, limit_rows=None, prefix=False, original_tags=None, h=None):
    """Unbounded Python integer masks; no machine-word boundaries or pair cache."""
    nr, nc = len(a), len(a[0])
    if limit_rows is not None:
        nr = limit_rows
    full = (1 << nr) - 1
    masks = [sum(a[r][c] << r for r in range(nr)) for c in range(nc)]
    signatures = PATTERN[:3] if prefix else PATTERN
    checked, copies = 0, 0
    for cc in combinations(range(nc), 4):
        checked += 1
        lower, rr = 0, []
        for sig in signatures:
            matches = full
            for c, bit in zip(cc, sig):
                matches &= masks[c] if bit == '1' else full ^ masks[c]
            matches &= ~((1 << lower) - 1)
            if not matches:
                break
            r = (matches & -matches).bit_length() - 1
            rr.append(r)
            lower = r + 1
        else:
            copies += 1
            if original_tags is None:
                return checked, copies, (rr, cc)
            rows, cols = original_tags
            assert rows[rr[2]][:3] == ('V', h, True)
            p = rows[rr[2]][3]
            assert cols[cc[3]][:4] == ('V', h-1, False, p//2)
            assert cols[cc[0]][:4] == ('A', h, 4+p%2, 0)
    return checked, copies, None


def brute(a):
    for rr in combinations(range(len(a)), 4):
        for cc in combinations(range(len(a[0])), 4):
            if tuple(''.join(str(a[r][c]) for c in cc) for r in rr) == PATTERN:
                return rr, cc
    return None


def main():
    rng = random.Random(913721)
    controls = [([list(map(int, row)) for row in PATTERN], True)]
    for r in range(4):
        for c in range(4):
            a = [list(map(int, row)) for row in PATTERN]
            a[r][c] ^= 1
            controls.append((a, False))
    for _ in range(100):
        a = [[rng.randrange(2) for _ in range(7)] for _ in range(6)]
        controls.append((a, brute(a) is not None))
    for a, expected in controls:
        assert (bit_scan(a)[2] is not None) == expected
        assert (literal_scan(a)[1] is not None) == expected
    records = []
    for h in range(1, 5):
        start = time.monotonic()
        rows, cols, a, b, changes = matrices(h)
        checked, count, witness = bit_scan(b)
        assert witness is None and count == 0
        anchor_count = 12*h
        prefix_checked, prefix_count, witness = bit_scan(a, anchor_count, True)
        assert witness is None and prefix_count == 0
        old_checked, old_column_quads, _ = bit_scan(a, original_tags=(rows, cols), h=h)
        assert old_column_quads > 0
        assert checked == prefix_checked == old_checked == math.comb(len(cols), 4)
        # Physical expansion comparison and direct literal checks at the boundary h=1.
        if h == 1:
            pr, pc, pa, pb, edits = matrices(h, True)
            literal_checked, witness = literal_scan(pb)
            assert witness is None and literal_checked == math.comb(32, 4)
            rindex = {r:i for i,r in enumerate(rows)}
            cindex = {c:i for i,c in enumerate(cols)}
            for i,r in enumerate(pr):
                for j,c in enumerate(pc):
                    assert pb[i][j] == b[rindex[r[:-1]+(0,)]][cindex[c[:-1]+(0,)]]
        record = dict(h=h, n=(14*h+2)*(1<<h), blocks=len(rows),
                      physical_edits=sum(w for _,_,w in changes),
                      column_quadruples=checked, repair_free=True,
                      anchor_three_row_prefix_impossible=True,
                      original_column_quadruples_with_copies=old_column_quads,
                      original_first_column_terminal=True,
                      repair_block_sha256=hashlib.sha256(bytes(sum(b,[]))).hexdigest(),
                      seconds=round(time.monotonic()-start, 4))
        records.append(record)
        print(json.dumps(record), flush=True)
    result = dict(controls_passed=len(controls), literal_physical_h1_quadruples=math.comb(32,4),
                  depths=records, limits='Finite checks only; all-depth conclusion uses ordinary proof.')
    (Path(__file__).resolve().parents[1] / 'evidence/terminal-anchor-finite.json').write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
