"""Verify saved B132 data against its proved recurrence; generate no rows."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent
source = root / 'rr132-extended-E-B.json'
raw = source.read_bytes()
data = json.loads(raw)
e, b = data['E'], data['B']


def coefficient(row, k):
    return row[k] if 0 <= k < len(row) else 0


assert e[1] == e[2] == [1]
assert b[0] == b[1] == [1]
for n in range(2, len(e) - 1):
    for k in range(max(len(e[n + 1]), len(e[n]) + 1, len(e[n - 1]) + 1)):
        assert (n + 1) * coefficient(e[n + 1], k) == (
            (4 + 6 * k) * coefficient(e[n], k)
            + (4 * n - 6 * k) * coefficient(e[n], k - 1)
            + (n - 3) * (coefficient(e[n - 1], k) - coefficient(e[n - 1], k - 1))
        ), (n, k)

for n in range(2, len(b)):
    for k in range(max(len(b[n]), len(e[n + 1]), len(b[n - 1]) + 1)):
        assert coefficient(b[n], k) == (
            coefficient(e[n + 1], k) + coefficient(b[n - 1], k)
            - coefficient(b[n - 1], k - 1)
        ), (n, k)
for n, row in enumerate(b):
    assert row[0] > 0 and row[-1] > 0 and all(c >= 0 for c in row)
    assert len(row) - 1 == (0 if n == 0 else 2 * (n - 1) // 3)

input_rows = (root / 'rr132-finite-rows.txt').read_text().splitlines()
assert len(input_rows) == 100
assert [[int(x) for x in row.split(',')] for row in input_rows] == b[:100]
counts = [json.loads(line) for line in
          (root / 'rr132-finite-root-count.jsonl').read_text().splitlines()]
assert len(counts) == 100
for n, record in enumerate(counts):
    assert record == {'n': n, 'degree': len(b[n]) - 1,
                      'distinct_real_roots': len(b[n]) - 1}

print(json.dumps({'verified': True, 'rows_sha256': hashlib.sha256(raw).hexdigest(),
                  'recurrence_indices': [2, len(e) - 2],
                  'finite_root_counts': [0, 99],
                  'nonnegative_coefficients_positive_constant': True}, indent=2))
