"""Bounded physical-semantics audit using the release's independent interval axes.

This supplements the Lean proof; it is not a proof certificate or proof premise.
Only the audit's interval-axis and literal entry-table definitions are loaded.
"""
import ast
import json
from pathlib import Path
from fractions import Fraction

root = Path(__file__).resolve().parents[1]
audit = root / 'audit/checkers/compare_hosts.py'
source = ast.parse(audit.read_text())
definitions = [node for node in source.body if isinstance(node, ast.FunctionDef)
               and node.name in {'axes', 'role', 'entry'}]
assert len(definitions) == 3
context = {'Fraction': Fraction}
exec(compile(ast.Module(body=definitions, type_ignores=[]), str(audit), 'exec'), context)
axes, entry = context['axes'], context['entry']
h = 4
rr, cc = axes(h, False), axes(h, True)
rows, cols = [800, 802, 804, 912], [836, 864, 868, 880]
assert len(rr) == len(cc) == 928
assert all(a < b for a, b in zip(rows, rows[1:]))
assert all(a < b for a, b in zip(cols, cols[1:]))
expected_rows = [('T', 3, 1, 0, 0), ('T', 3, 0, 1, 0),
                 ('T', 4, 1, 2, 0), ('D', 0)]
expected_cols = [('T', 3, 0, 2, 0), ('T', 2, 1, 2, 0),
                 ('T', 3, 1, 4, 0), ('T', 2, 0, 2, 0)]
assert [rr[r] for r in rows] == expected_rows
assert [cc[c] for c in cols] == expected_cols

def targeted(r, c):
    return rr[r][0] == 'D' and cc[c][0:3] == ('T', h - 1, 0)

before = [''.join(str(entry(h, rr[r], cc[c])) for c in cols) for r in rows]
after = [''.join('0' if targeted(r, c) else str(entry(h, rr[r], cc[c]))
                 for c in cols) for r in rows]
assert before == ['0110', '1001', '1010', '1111']
assert after == ['0110', '1001', '1010', '0111']
selected = [(r, c) for r in rows for c in cols if targeted(r, c)]
assert selected == [(912, 836)]
all_targets = [(r, c) for r in range(928) for c in range(928) if targeted(r, c)]
assert len(all_targets) == 256
assert all(entry(h, rr[r], cc[c]) == 1 for r, c in all_targets)
result = {'h': h, 'm': 16, 'n': 928, 'rows': rows, 'cols': cols,
          'row_descriptors': expected_rows, 'col_descriptors': expected_cols,
          'before': before, 'after': after, 'selected_changed_cells': selected,
          'full_class_edit_count': len(all_targets), 'passed': True,
          'method': 'independent rational interval axes and literal entry tables'}
(root / 'evidence/penultimate-physical-audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
