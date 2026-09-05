#!/usr/bin/env python3
"""Exact bounded checks for fusion_revised.tex; not a geometry certificate.

Standard-library only. Exits nonzero on any failed invariant. JSON is stable
across runs with the same source files; --output writes the report to that path.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import sys


if sys.flags.optimize or not __debug__:
    raise SystemExit(
        "Fusion checks require assertions and cannot run with optimized Python. "
        "Remove -O/-OO and PYTHONOPTIMIZE, or use scripts/replay_certificates.py."
    )


def zero(n):
    return [[F(0) for _ in range(n)] for _ in range(n)]


def identity(n):
    a = zero(n)
    for i in range(n):
        a[i][i] = F(1)
    return a


def mul(a, b):
    n = len(a)
    out = zero(n)
    for i in range(n):
        for k, aik in enumerate(a[i]):
            if aik:
                for j, bkj in enumerate(b[k]):
                    if bkj:
                        out[i][j] += aik * bkj
    return out


def add(a, b):
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def scale(a, c):
    return [[c * x for x in row] for row in a]


def power(a, exponent):
    out = identity(len(a))
    for _ in range(exponent):
        out = mul(out, a)
    return out


def kron(a, b):
    return [[x * y for x in ar for y in br] for ar in a for br in b]


def cyclotomic_matrix(p):
    """Multiplication by zeta in Q[zeta], basis 1,...,zeta^(p-2)."""
    n = p - 1
    t = zero(n)
    for j in range(n - 1):
        t[j + 1][j] = F(1)
    for i in range(n):
        t[i][n - 1] = F(-1)
    assert power(t, p) == identity(n)
    return t


def matching_projector(t, p):
    n = len(t)
    e = zero(n * n)
    for a in range(p):
        e = add(e, kron(power(t, a), power(t, (-a) % p)))
    return scale(e, F(1, p))


def trace(a):
    return sum(a[i][i] for i in range(len(a)))


def swap_matrix(n):
    s = zero(n * n)
    for i, j in product(range(n), repeat=2):
        s[j * n + i][i * n + j] = F(1)
    return s


def check_projectors():
    results = []
    for p in (3, 5, 7):
        t = cyclotomic_matrix(p)
        e = matching_projector(t, p)
        s = swap_matrix(p - 1)
        assert mul(e, e) == e
        assert mul(s, e) == mul(e, s)
        assert trace(e) == p - 1
        results.append({"p": p, "tensor_dimension": (p - 1) ** 2,
                        "matching_projector_rank": int(trace(e)),
                        "idempotent": True, "commutes_with_swap": True})

    # A genuine determinant summand: V=K^2 at p=3, so V_Q has dimension 4.
    p = 3
    t = kron(identity(2), cyclotomic_matrix(p))
    e = matching_projector(t, p)
    alt = scale(add(identity(16), scale(swap_matrix(4), F(-1))), F(1, 2))
    d = mul(e, alt)
    assert mul(d, d) == d
    assert mul(e, alt) == mul(alt, e)
    assert trace(d) == 2  # (p-1) * binomial(rank_K(V), 2)
    one_slot = mul(d, mul(kron(t, identity(4)), d))
    all_slots = mul(d, mul(kron(t, t), d))
    assert one_slot != all_slots
    assert power(one_slot, p) == d

    # Exhaustive embedding-label tests. Evaluation is exact: the root average
    # is 1 iff the exponent is 0 mod p (a polynomial identity in Phi_p).
    bad_naive = []
    tested = 0
    for p, ranks in ((3, (3, 3)), (5, (5, 5)), (5, (1, 3)), (7, (7, 7))):
        correct = []
        naive = []
        for labels in product(range(1, p), repeat=2):
            tested += 1
            if labels[0] == labels[1]:
                correct.append(labels)
            if (ranks[0] * labels[0] - ranks[1] * labels[1]) % p == 0:
                naive.append(labels)
        assert len(correct) == p - 1
        assert set(correct) != set(naive)
        if all(h % p == 0 for h in ranks):
            assert len(naive) == (p - 1) ** 2
        bad_naive.append({"p": p, "K_ranks": list(ranks),
                          "correct_dimension": len(correct),
                          "naive_exterior_deck_dimension": len(naive),
                          "naive_selects_wrong_subspace": True})
    # Compare all three choices of star anchor on every triple of labels.
    star_cases = 0
    for p in (3, 5, 7):
        for labels in product(range(1, p), repeat=3):
            values = [all(labels[r] == labels[a] for r in range(3))
                      for a in range(3)]
            assert values[0] == values[1] == values[2]
            star_cases += 1
    return {"rational_matrices": results,
            "rank_two_determinant": {"p": 3, "rational_dimension": 2,
                                     "scalar_differs_from_exterior_deck": True},
            "naive_projector_counterexamples": bad_naive,
            "two_label_cases": tested, "three_label_cases": star_cases}


def signatures(p, row):
    return [len(row) - 1 - sum((b * a) % p for a in row) // p
            for b in range(1, p)]


def check_tuple_case(case):
    p, rows, pairs = case["p"], case["rows"], case["pairs"]
    assert p > 2 and all(p % q for q in range(2, int(p ** .5) + 1))
    assert rows and all(len(row) >= 3 for row in rows)
    assert all(all(0 < a < p for a in row) and sum(row) % p == 0
               for row in rows)
    all_slots = {(j, i) for j, row in enumerate(rows) for i in range(len(row))}
    used = []
    parent = list(range(len(rows)))

    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x

    tree = []
    for left, right in pairs:
        u, i = left
        v, j = right
        used.extend((tuple(left), tuple(right)))
        assert (rows[u][i] + rows[v][j]) % p == 0
        # Inertia and tangent exponents must both be inverse across the node.
        assert (pow(rows[u][i], -1, p) + pow(rows[v][j], -1, p)) % p == 0
        ru, rv = find(u), find(v)
        if ru != rv:
            parent[ru] = rv
            tree.append((tuple(left), tuple(right)))
    assert len(used) == len(all_slots) and set(used) == all_slots
    s = sum(map(len, rows))
    h = s - 2 * len(rows)
    assert s % 2 == 0 and h > 0 and h % 2 == 0
    assert all(2 * sum((b * a) % p for row in rows for a in row) == p * s
               for b in range(1, p))
    groups = {}
    for j in range(len(rows)):
        groups.setdefault(find(j), []).append(j)
    removed = {slot for edge in tree for slot in edge}
    components = []
    for vertices in sorted(groups.values()):
        remaining = [a for j in vertices for i, a in enumerate(rows[j])
                     if (j, i) not in removed]
        counts = Counter(remaining)
        hi = sum(len(rows[j]) - 2 for j in vertices)
        assert all(counts[a] == counts[p - a] for a in counts)
        assert len(remaining) == hi + 2 and hi >= 2 and hi % 2 == 0
        assert sum(1 for edge in tree if edge[0][0] in vertices) == len(vertices) - 1
        # Every old target marking becomes either a marking or a node.
        for j in vertices:
            nodes = sum(slot[0] == j for edge in tree for slot in edge)
            marks = sum((j, i) not in removed for i in range(len(rows[j])))
            assert nodes + marks == len(rows[j]) >= 3
        components.append({"vertices": vertices, "remaining_tuple": remaining,
                           "fused_K_rank": hi, "fused_genus": (p - 1) * hi // 2})
    sigs = [signatures(p, row) for row in rows]
    assert [sum(ss[b] for ss in sigs) for b in range(p - 1)] == [h // 2] * (p - 1)
    return {"name": case["name"], "p": p, "K_ranks": [len(r) - 2 for r in rows],
            "genera": [(p - 1) * (len(r) - 2) // 2 for r in rows],
            "H10_multiplicities": sigs, "codimension": h // 2,
            "components": components, "component_count": len(components),
            "unprojected_product_dimension": (p - 1) ** len(components),
            "matching_embedding_dimension": p - 1}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    script = Path(__file__).resolve()
    fixture = script.parent / "fixtures" / "fusion_cases.json"
    data = json.loads(fixture.read_text())
    report = {"schema_version": 1, "status": "bounded_checks_passed",
              "scope": "Exact finite projector and branch/graph checks; no geometry certification",
              "script_sha256": sha256(script.read_bytes()).hexdigest(),
              "fixtures_sha256": sha256(fixture.read_bytes()).hexdigest(),
              "source_sha256": {
                  "manuscripts/fusion_revised.tex": sha256(
                      (script.parent.parent / "manuscripts/fusion_revised.tex").read_bytes()
                  ).hexdigest()
              },
              "projectors": check_projectors(),
              "cases": [check_tuple_case(case) for case in data["cases"]]}
    # A valid pair of cyclic covers that does NOT satisfy the theorem's balance
    # hypothesis. Repetition alone must not be accepted as a balanced word.
    unbalanced_rows = [[1, 1, 3], [1, 1, 3]]
    sums = [sum((b * a) % 5 for row in unbalanced_rows for a in row)
            for b in range(1, 5)]
    assert sums != [15] * 4
    report["negative_balance_case"] = {
        "p": 5, "rows": unbalanced_rows,
        "residue_sums": sums, "required_sums": [15] * 4,
        "excluded_by_balance": True}
    # The p=5 manuscript example has a selected 3-to-2 gluing edge.
    example = report["cases"][0]
    assert sorted(example["components"][0]["remaining_tuple"]) == [1, 1, 1, 4, 4, 4]
    assert example["genera"] == [2, 6] and example["codimension"] == 2
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
