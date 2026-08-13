#!/usr/bin/env python3
"""Exact-arithmetic regression certificate for the elementary-p Phase II theorem.

The written proof establishes the theorems.  This script independently checks the
finite linear-algebra and combinatorial interfaces used by the paper:

1. construction of the cyclotomic signature matrix from a p-ary branch code;
2. exact rational relation lattices for a collection of representative codes;
3. equivalence between a signature relation and a balanced concatenated residue word;
4. the prime-exponent opposite-pair conclusion on every tested relation;
5. the compact-type fusion rank formula component by component;
6. the first mixed p=5 determinant relation and its fused six-point cover;
7. the isolated-disk saturation criterion through p=19;
8. vanishing of the signature torus for the split elementary-p family.

No finite computation substitutes for the Hodge-group, invariant-theoretic,
admissible-cover, specialization, or Schoen-cycle arguments in the manuscript.
"""
from __future__ import annotations

from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from hashlib import sha256
from itertools import product
import json
from math import gcd, lcm
from pathlib import Path
from typing import Iterable, Sequence

import sympy as sp
from sympy import ZZ
from sympy.polys.matrices import DomainMatrix
from sympy.polys.matrices.normalforms import smith_normal_decomp

HERE = Path(__file__).resolve().parent
OUT = HERE / "phase_II_certificate_report.json"


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def span_code(generators: Sequence[Sequence[int]], p: int) -> list[tuple[int, ...]]:
    if not generators:
        return [tuple()]
    r = len(generators[0])
    assert all(len(row) == r for row in generators)
    return sorted({
        tuple(sum(coeff[j] * generators[j][i] for j in range(len(generators))) % p
              for i in range(r))
        for coeff in product(range(p), repeat=len(generators))
    })


def support_size(c: Sequence[int]) -> int:
    return sum((x != 0) for x in c)


def negative(c: Sequence[int], p: int) -> tuple[int, ...]:
    return tuple((-x) % p for x in c)


def sign_representatives(code: Iterable[Sequence[int]], p: int) -> list[tuple[int, ...]]:
    seen: set[tuple[int, ...]] = set()
    reps: list[tuple[int, ...]] = []
    for raw in code:
        c = tuple(x % p for x in raw)
        if not any(c) or support_size(c) < 3 or c in seen:
            continue
        nc = negative(c, p)
        rep = min(c, nc)
        reps.append(rep)
        seen.add(c)
        seen.add(nc)
    reps.sort()
    return reps


def q_value(c: Sequence[int], a: int, p: int) -> int:
    numerator = sum((a * x) % p for x in c)
    assert numerator % p == 0
    return numerator // p


def signature_column(c: Sequence[int], p: int) -> tuple[int, ...]:
    s = support_size(c)
    assert s >= 3
    return tuple(s - 2 * q_value(c, a, p) for a in range(1, p))


def signature_matrix(code: Iterable[Sequence[int]], p: int) -> tuple[list[tuple[int, ...]], sp.Matrix]:
    reps = sign_representatives(code, p)
    if not reps:
        return reps, sp.zeros(p - 1, 0)
    return reps, sp.Matrix.hstack(*(sp.Matrix(signature_column(c, p)) for c in reps))


def smith_integer_kernel(matrix: sp.Matrix) -> tuple[list[tuple[int, ...]], list[int]]:
    """Return a certified Z-basis of ker(matrix: Z^n -> Z^m) using Smith form.

    SymPy returns D = S * matrix * T with S and T unimodular.  If r is the
    rank, the last n-r columns of T form a basis of the integral kernel.
    """
    if matrix.cols == 0:
        return [], []
    domain_matrix = DomainMatrix.from_Matrix(matrix).convert_to(ZZ)
    diagonal, left, right = smith_normal_decomp(domain_matrix)
    D = diagonal.to_Matrix()
    S = left.to_Matrix()
    T = right.to_Matrix()
    assert S * matrix * T == D
    assert abs(int(S.det())) == 1
    assert abs(int(T.det())) == 1
    rank = matrix.rank()
    diagonal_entries = [
        abs(int(D[i, i])) for i in range(min(D.rows, D.cols)) if D[i, i] != 0
    ]
    assert len(diagonal_entries) == rank
    assert all(
        diagonal_entries[i + 1] % diagonal_entries[i] == 0
        for i in range(len(diagonal_entries) - 1)
    )
    kernel_matrix = T[:, rank:]
    assert matrix * kernel_matrix == sp.zeros(matrix.rows, kernel_matrix.cols)
    basis = [
        tuple(int(kernel_matrix[i, j]) for i in range(kernel_matrix.rows))
        for j in range(kernel_matrix.cols)
    ]
    return basis, diagonal_entries


def effective_word(
    representatives: Sequence[Sequence[int]], relation: Sequence[int], p: int
) -> list[tuple[int, ...]]:
    words: list[tuple[int, ...]] = []
    for c, coefficient in zip(representatives, relation):
        oriented = tuple(c) if coefficient >= 0 else negative(c, p)
        words.extend([oriented] * abs(coefficient))
    return words


def concatenated_residues(words: Sequence[Sequence[int]]) -> list[int]:
    return [x for word in words for x in word if x]


def verify_balanced(words: Sequence[Sequence[int]], p: int) -> dict[str, object]:
    residues = concatenated_residues(words)
    S = len(residues)
    assert S % 2 == 0
    sums = [sum((a * x) % p for x in residues) for a in range(1, p)]
    target = p * S // 2
    assert all(value == target for value in sums)
    counts = Counter(residues)
    assert all(counts[x] == counts[(-x) % p] for x in range(1, p))
    return {
        "branch_occurrences": S,
        "target_residue_sum": target,
        "galois_residue_sums": sums,
        "opposite_multiplicities": {str(x): counts[x] for x in range(1, p)},
    }


@dataclass(frozen=True)
class HalfEdge:
    vertex: int
    local_index: int
    residue: int


class UnionFind:
    def __init__(self, n: int) -> None:
        self.parent = list(range(n))
        self.rank = [0] * n

    def find(self, x: int) -> int:
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, a: int, b: int) -> bool:
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return False
        if self.rank[ra] < self.rank[rb]:
            ra, rb = rb, ra
        self.parent[rb] = ra
        if self.rank[ra] == self.rank[rb]:
            self.rank[ra] += 1
        return True


def opposite_pairing(words: Sequence[Sequence[int]], p: int) -> list[tuple[HalfEdge, HalfEdge]]:
    queues: dict[int, deque[HalfEdge]] = defaultdict(deque)
    for vertex, word in enumerate(words):
        for local_index, residue in enumerate(word):
            if residue:
                queues[residue].append(HalfEdge(vertex, local_index, residue))
    edges: list[tuple[HalfEdge, HalfEdge]] = []
    done: set[int] = set()
    for x in range(1, p):
        if x in done:
            continue
        y = (-x) % p
        done.add(x)
        done.add(y)
        assert len(queues[x]) == len(queues[y])
        while queues[x]:
            edges.append((queues[x].popleft(), queues[y].popleft()))
    return edges


def fusion_check(words: Sequence[Sequence[int]], p: int) -> dict[str, object]:
    """Check the compact-type fusion bookkeeping for one balanced word."""
    if not words:
        return {"components": [], "total_K_rank": 0}
    edges = opposite_pairing(words, p)
    graph_uf = UnionFind(len(words))
    for left, right in edges:
        if left.vertex != right.vertex:
            graph_uf.union(left.vertex, right.vertex)
    components: dict[int, list[int]] = defaultdict(list)
    for vertex in range(len(words)):
        components[graph_uf.find(vertex)].append(vertex)

    component_rows: list[dict[str, object]] = []
    total_rank = 0
    for vertices in components.values():
        vertex_set = set(vertices)
        component_edges = [edge for edge in edges if edge[0].vertex in vertex_set]
        # Select a spanning tree among cross-vertex opposite pairs.
        local_index = {v: i for i, v in enumerate(vertices)}
        tree_uf = UnionFind(len(vertices))
        tree_edges: list[tuple[HalfEdge, HalfEdge]] = []
        for edge in component_edges:
            u, v = edge[0].vertex, edge[1].vertex
            if u != v and tree_uf.union(local_index[u], local_index[v]):
                tree_edges.append(edge)
        assert len(tree_edges) == len(vertices) - 1

        original_branches = sum(support_size(words[v]) for v in vertices)
        remaining_branches = original_branches - 2 * len(tree_edges)
        original_rank = sum(support_size(words[v]) - 2 for v in vertices)
        fused_rank = remaining_branches - 2
        assert original_rank == fused_rank
        assert fused_rank > 0 and fused_rank % 2 == 0

        removed = {half for edge in tree_edges for half in edge}
        remaining_residues = [
            half.residue
            for edge in component_edges
            for half in edge
            if half not in removed
        ]
        # Every non-tree pair survives in both orientations.
        remaining_counts = Counter(remaining_residues)
        assert all(remaining_counts[x] == remaining_counts[(-x) % p]
                   for x in range(1, p))
        assert len(remaining_residues) == remaining_branches

        total_rank += fused_rank
        component_rows.append({
            "vertices": vertices,
            "pair_edges": len(component_edges),
            "tree_edges_used_as_nodes": len(tree_edges),
            "original_branch_occurrences": original_branches,
            "remaining_smooth_branch_points": remaining_branches,
            "K_rank_before": original_rank,
            "K_rank_after": fused_rank,
            "remaining_opposite_counts": {
                str(x): remaining_counts[x] for x in range(1, p)
            },
        })

    expected_total = sum(support_size(word) - 2 for word in words)
    assert total_rank == expected_total
    return {"components": component_rows, "total_K_rank": total_rank}


def verify_code(name: str, p: int, generators: Sequence[Sequence[int]]) -> dict[str, object]:
    assert is_prime(p)
    code = span_code(generators, p)
    assert all(sum(word) % p == 0 for word in code)
    assert all(any(word[i] for word in code) for i in range(len(generators[0])))
    reps, matrix = signature_matrix(code, p)
    kernel, smith_invariants = smith_integer_kernel(matrix)
    assert matrix.rank() <= (p - 1) // 2
    assert len(kernel) == len(reps) - matrix.rank()
    relation_rows = []
    for relation in kernel:
        column = matrix * sp.Matrix(relation)
        assert all(value == 0 for value in column)
        words = effective_word(reps, relation, p)
        balance = verify_balanced(words, p)
        fusion = fusion_check(words, p)
        relation_rows.append({
            "relation": list(relation),
            "occurrence_count": sum(abs(x) for x in relation),
            "balance": balance,
            "fusion": fusion,
        })
    return {
        "name": name,
        "p": p,
        "length": len(generators[0]),
        "dimension": len(generators),
        "codewords": len(code),
        "oriented_sign_pairs": len(reps),
        "signature_rank": matrix.rank(),
        "integral_relation_rank": len(kernel),
        "smith_nonzero_invariants": smith_invariants,
        "representatives": [list(c) for c in reps],
        "signature_matrix": [list(map(int, matrix.row(i))) for i in range(matrix.rows)],
        "relations": relation_rows,
    }


def verify_mixed_p5() -> dict[str, object]:
    p = 5
    c = (1, 1, 3, 0, 0, 0, 0, 0)
    d = (0, 0, 0, 1, 2, 4, 4, 4)
    sig_c = signature_column(c, p)
    sig_d = signature_column(d, p)
    assert tuple(x + y for x, y in zip(sig_c, sig_d)) == (0, 0, 0, 0)
    words = [c, d]
    balance = verify_balanced(words, p)

    # Choose the cross pair 3 (first factor) with 2 (second factor) as the node.
    remaining = [1, 1, 1, 4, 4, 4]
    assert Counter(remaining)[1] == Counter(remaining)[4] == 3
    assert len(remaining) - 2 == (support_size(c) - 2) + (support_size(d) - 2) == 4
    return {
        "p": p,
        "first_word": list(c),
        "second_word": list(d),
        "signature_first": list(sig_c),
        "signature_second": list(sig_d),
        "balanced_concatenation": balance,
        "chosen_node_residues": [3, 2],
        "fused_smooth_branch_tuple": remaining,
        "fused_K_rank": 4,
        "Hodge_codimension": 2,
    }


def double_transpositions(indices: Sequence[int]) -> list[tuple[int, ...]]:
    assert len(indices) == 4
    a, b, c, d = indices
    # permutation arrays on the four local positions
    return [
        (1, 0, 3, 2),
        (2, 3, 0, 1),
        (3, 2, 1, 0),
    ]


def disk_saturation_check(max_p: int = 19) -> dict[str, object]:
    rows = []
    total_balanced = 0
    for p in [q for q in range(3, max_p + 1) if is_prime(q)]:
        checked = 0
        balanced = 0
        # Fix the first entry to 1 by scalar normalization.
        for x2, x3, x4 in product(range(1, p), repeat=3):
            c = (1, x2, x3, x4)
            if sum(c) % p:
                continue
            checked += 1
            if any(signature_column(c, p)):
                continue
            balanced += 1
            counts = Counter(c)
            assert all(counts[x] == counts[(-x) % p] for x in range(1, p))
            found = False
            nc = negative(c, p)
            for perm in double_transpositions(range(4)):
                moved = tuple(c[perm[i]] for i in range(4))
                if moved == nc:
                    found = True
                    break
            assert found
        total_balanced += balanced
        rows.append({"p": p, "normalized_disks_checked": checked,
                     "zero_signature_disks": balanced, "failures": 0})
    return {"primes_through": max_p, "rows": rows,
            "total_zero_signature_disks": total_balanced, "failures": 0}


def split_family_check(max_p: int = 31) -> list[dict[str, int]]:
    rows = []
    for p in [q for q in range(3, max_p + 1) if is_prime(q)]:
        generators = [
            (1, 0, p - 1, 0),
            (0, 1, 0, p - 1),
        ]
        code = span_code(generators, p)
        reps, matrix = signature_matrix(code, p)
        assert matrix.rank() == 0
        assert all(all(value == 0 for value in signature_column(c, p)) for c in reps)
        rows.append({
            "p": p,
            "sign_orbits_with_cohomology": len(reps),
            "signature_torus_rank": 0,
            "relation_rank": len(reps),
        })
    return rows


def main() -> None:
    sample_codes = [
        verify_code(
            "mixed_support_p5",
            5,
            [
                (1, 1, 3, 0, 0, 0, 0, 0),
                (0, 0, 0, 1, 2, 4, 4, 4),
            ],
        ),
        verify_code(
            "ternary_two_triangle_code",
            3,
            [
                (1, 1, 1, 0, 0, 0),
                (0, 0, 0, 1, 1, 1),
            ],
        ),
        verify_code(
            "quinary_overlap_code",
            5,
            [
                (1, 0, 1, 3, 0),
                (0, 1, 1, 0, 3),
            ],
        ),
        verify_code(
            "septenary_length_six",
            7,
            [
                (1, 1, 2, 3, 0, 0),
                (0, 1, 0, 2, 1, 3),
            ],
        ),
    ]

    result = {
        "scope": (
            "Exact regression for the elementary-prime signature-torus, "
            "determinant-relation, and compact-type fusion calculations"
        ),
        "sample_codes": sample_codes,
        "mixed_p5_relation": verify_mixed_p5(),
        "isolated_disk_saturation": disk_saturation_check(19),
        "split_elementary_p_family": split_family_check(31),
        "warnings": [
            "The displayed relation vectors are a certified Smith-normal-form Z-basis of the integral signature kernel for each sample code.",
            "Aoki's all-prime opposite-pair theorem is a written published input; the finite disk check is regression only.",
            "Admissible-cover smoothing, specialization of cycles, and Schoen's cycle theorem are mathematical arguments, not computational claims.",
            "The theorem concerns prime exponent p; composite-exponent non-simple balanced words are outside its scope.",
        ],
    }
    result["script_sha256"] = sha256(Path(__file__).read_bytes()).hexdigest()
    manuscript = HERE / "phase_II_complete.tex"
    phase_i = HERE / "phase_I_complete.tex"
    result["artifact_hashes"] = {}
    if manuscript.exists():
        result["artifact_hashes"]["phase_II_complete.tex"] = sha256(manuscript.read_bytes()).hexdigest()
    if phase_i.exists():
        result["artifact_hashes"]["phase_I_complete.tex"] = sha256(phase_i.read_bytes()).hexdigest()
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "script_sha256": result["script_sha256"],
        "sample_code_count": len(sample_codes),
        "mixed_p5_fused_K_rank": result["mixed_p5_relation"]["fused_K_rank"],
        "disk_failures": result["isolated_disk_saturation"]["failures"],
        "split_family_last_prime": result["split_elementary_p_family"][-1]["p"],
        "report": str(OUT),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
