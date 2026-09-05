#!/usr/bin/env python3
"""Bounded exact regressions for the general odd-prime argument, not a proof.

Standard-library only. Bounds are fixed: all odd primes <=31 for partitions
and labelled four-words, support 5 at primes <=7 and support 6 at primes <=5
for higher-rank words. No braid representation or geometric cycle is computed.
JSON is deterministic; --output writes the report to the supplied path.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from hashlib import sha256
from itertools import combinations, product
import json
from math import isqrt
from pathlib import Path


def require(condition: bool, message: str) -> None:
    """An explicit check that remains active under Python -O/-OO."""
    if not condition:
        raise AssertionError(message)


def primes_through(bound: int) -> list[int]:
    return [p for p in range(3, bound + 1, 2)
            if all(p % d for d in range(2, isqrt(p) + 1))]


def partitions(n: int, minimum: int = 1):
    if n == 0:
        yield ()
    for first in range(minimum, n + 1):
        for tail in partitions(n - first, first):
            yield (first,) + tail


def words(p: int, support: int):
    for prefix in product(range(1, p), repeat=support - 1):
        last = -sum(prefix) % p
        if last:
            yield prefix + (last,)


def ages(word: tuple[int, ...], p: int) -> list[int]:
    require(len(word) >= 2 and all(0 < a < p for a in word), "Invalid active word")
    sums = [sum(t * a % p for a in word) for t in range(1, p)]
    require(all(s % p == 0 for s in sums), "Branch word has nonintegral age")
    values = [s // p for s in sums]
    require(all(1 <= q < len(word) for q in values), "Age outside allowed range")
    require(all(a + b == len(word) for a, b in zip(values, reversed(values))),
            "Negation identity for ages")
    return values


def positive_embedding(word: tuple[int, ...], p: int) -> tuple[int, int, int]:
    """Return first mixed row, its age, and number of carry identities checked."""
    values = ages(word, p)
    require(len(word) >= 4, "Mixed-embedding claim requires support >=4")
    interior = [t for t, q in enumerate(values, 1) if 2 <= q <= len(word) - 2]
    require(bool(interior), f"No mixed embedding at p={p}, word={word}")
    carry_checks = 0
    if values[0] in (1, len(word) - 1):
        normalized = word if values[0] == 1 else tuple(-a % p for a in word)
        require(sum(normalized) == p, "Endpoint normalization")
        qs = ages(normalized, p)
        require(qs[0] == 1 and qs[-1] == len(word) - 1, "Normalized endpoints")
        for t in range(1, p - 1):
            carries = sum((t * a % p) + a >= p for a in normalized)
            require(qs[t] - qs[t - 1] == 1 - carries, "Exact carry identity")
            require(qs[t] - qs[t - 1] <= 1, "Upward increment exceeded one")
            carry_checks += 1
        require(next(q for q in qs if q >= 2) == 2, "First crossing skipped age two")
    first = interior[0]
    return first, values[first - 1], carry_checks


def pair_sums(word: tuple[int, ...], p: int) -> tuple[int, ...]:
    return tuple((a + b) % p for a, b in combinations(word, 2))


def signed_pair_fingerprint(word: tuple[int, ...], p: int) -> tuple[int, ...]:
    return tuple(min(a, -a % p) for a in pair_sums(word, p))


def signed_v4(word: tuple[int, ...], p: int) -> set[tuple[int, ...]]:
    require(len(word) == 4, "V4 requires four labelled coordinates")
    permutations = ((0, 1, 2, 3), (1, 0, 3, 2), (2, 3, 0, 1), (3, 2, 1, 0))
    return {tuple(sign * word[j] % p for j in perm)
            for perm in permutations for sign in (1, -1)}


def check_partitions() -> dict:
    rows = []
    for p in primes_through(31):
        count = carry_checks = 0
        first_rows = Counter()
        for word in partitions(p):
            if len(word) < 4:
                continue
            first, q, checks = positive_embedding(word, p)
            require(q == 2, "Normalized partition must first cross at age two")
            first_rows[first] += 1
            count += 1
            carry_checks += checks
        rows.append({"p": p, "partitions": count, "carry_identities": carry_checks,
                     "first_mixed_embedding_counts": dict(sorted(first_rows.items()))})
    return {"prime_bound": 31, "rows": rows,
            "total_partitions": sum(r["partitions"] for r in rows),
            "coverage": "Every all-definite candidate scales/sorts to a partition of p; "
                        "support >p is automatically mixed. This bounds the computation, "
                        "not the separately written universal proof."}


def check_four_labels() -> dict:
    rows = []
    for p in primes_through(31):
        buckets = defaultdict(set)
        count = carry_checks = 0
        for word in words(p, 4):
            _, _, checks = positive_embedding(word, p)
            carry_checks += checks
            x, y, z = ((word[0] + word[i]) % p for i in (1, 2, 3))
            inv_two = pow(2, -1, p)
            reconstructed = tuple(v * inv_two % p for v in
                                  (x + y + z, x - y - z, -x + y - z, -x - y + z))
            require(reconstructed == word, "Four-label linear reconstruction")
            buckets[signed_pair_fingerprint(word, p)].add(word)
            count += 1
        sizes = Counter()
        for bucket in buckets.values():
            require(bucket == signed_v4(min(bucket), p), "Extra or missing V4 collision")
            sizes[len(bucket)] += 1
        rows.append({"p": p, "words": count, "fibers": len(buckets),
                     "fiber_size_counts": dict(sorted(sizes.items())),
                     "carry_identities": carry_checks,
                     "all_fibers_exactly_signed_V4": True})
    return {"prime_bound": 31, "rows": rows,
            "total_words": sum(r["words"] for r in rows),
            "total_fibers": sum(r["fibers"] for r in rows),
            "scope": "All six fixed labelled pair sums, each compared up to its own sign"}


def projective_spectrum(exponent: int, dimension: int, p: int) -> tuple[int, ...]:
    values = [exponent] + [0] * (dimension - 1)
    return min(tuple(sorted((a + shift) % p for a in values)) for shift in range(p))


def check_higher_rank() -> dict:
    rows = []
    for support, bound in ((5, 7), (6, 5)):
        for p in primes_through(bound):
            buckets = defaultdict(set)
            count = 0
            for word in words(p, support):
                positive_embedding(word, p)
                values = pair_sums(word, p)
                fingerprint = min(values, tuple(-a % p for a in values))
                buckets[fingerprint].add(word)
                # Invert the first three labelled pair sums, using one fixed sign.
                a, b, c = word[:3]
                reconstructed_a = ((a + b) + (a + c) - (b + c)) * pow(2, -1, p) % p
                require(reconstructed_a == a, "Higher-rank triple reconstruction")
                count += 1
            for bucket in buckets.values():
                w = min(bucket)
                require(bucket == {w, tuple(-a % p for a in w)},
                        "Higher-rank common-sign fingerprint fiber")
            rows.append({"p": p, "support": support, "words": count,
                         "fibers": len(buckets), "all_fibers_exactly_global_sign": True})
    spectrum_rows = []
    for p in primes_through(31):
        for dimension in (2, 3, 4, 5):
            buckets = defaultdict(set)
            for exponent in range(1, p):
                buckets[projective_spectrum(exponent, dimension, p)].add(exponent)
            for bucket in buckets.values():
                e = min(bucket)
                expected = {e, -e % p} if dimension == 2 else {e}
                require(bucket == expected, "Projective reflection multiplicity distinction")
            spectrum_rows.append({"p": p, "dimension": dimension,
                                  "nonidentity_semisimple_spectra": len(buckets)})
    return {"rows": rows, "projective_reflection_spectra": spectrum_rows,
            "scope": "Higher-rank reconstruction assumes the single global inner/outer "
                     "sign justified in the written proof; no matrix monodromy is certified."}


def shift_cyclotomic(value: tuple[int, ...], exponent: int, p: int) -> tuple[int, ...]:
    """Multiply by z^exponent in Z[z]/(1+z+...+z^(p-1))."""
    require(len(value) == p - 1, "Cyclotomic coefficient dimension")
    coefficients = [0] * p
    for degree, coefficient in enumerate(value):
        coefficients[(degree + exponent) % p] += coefficient
    return tuple(a - coefficients[-1] for a in coefficients[:-1])


def mul_cyclotomic(left: tuple[int, ...], right: tuple[int, ...], p: int) -> tuple[int, ...]:
    out = [0] * (p - 1)
    for degree, coefficient in enumerate(right):
        if coefficient:
            shifted = shift_cyclotomic(left, degree, p)
            out = [a + coefficient * b for a, b in zip(out, shifted)]
    return tuple(out)


def check_empty_word_vandermonde() -> dict:
    rows = []
    for p in [2] + primes_through(31):
        one = (1,) + (0,) * (p - 2)
        require(shift_cyclotomic(one, p, p) == one, "z^p=1 in cyclotomic quotient")
        root_sum = [sum(shift_cyclotomic(one, a, p)[j] for a in range(p))
                    for j in range(p - 1)]
        require(not any(root_sum), "Phi_p(z)=0")
        # Exact Vandermonde determinant for rows b=1,...,p-1 and columns a=0,...,p-2.
        determinant = one
        for b, c in combinations(range(1, p), 2):
            right = shift_cyclotomic(determinant, c, p)
            left = shift_cyclotomic(determinant, b, p)
            determinant = tuple(x - y for x, y in zip(right, left))
        require(any(determinant), "Empty-word coefficient Vandermonde is singular")
        conjugate = [0] * (p - 1)
        for a, coefficient in enumerate(determinant):
            image = shift_cyclotomic(one, -a, p)
            conjugate = [x + coefficient * y for x, y in zip(conjugate, image)]
        norm = mul_cyclotomic(determinant, tuple(conjugate), p)
        expected = (p ** (p - 2),) + (0,) * (p - 2)
        require(norm == expected, "Exact cyclotomic Vandermonde squared absolute value")
        rows.append({"p": p, "matrix_dimension": p - 1,
                     "determinant_coefficients_mod_Phi_p": list(determinant),
                     "determinant_times_conjugate": p ** (p - 2),
                     "one_trace_column_rank": 1, "all_deck_columns_rank": p - 1})
    return {"rows": rows, "degree_zero_empty_word": {"source": "Q", "map": "identity"},
            "scope": "Exact polynomial quotient arithmetic, no floating-point roots. "
                     "Invertibility checks the coefficient algebra, not algebraicity of cycles."}


def check_negative_controls() -> dict:
    c = (1, 1, 1, 2)
    negative = tuple(-a % 5 for a in c)
    qs, opposite_qs = ages(c, 5), ages(negative, 5)
    require(qs == [1, 2, 2, 3] and opposite_qs == [3, 2, 2, 1], "Orientation fixture")
    require(signed_pair_fingerprint(c, 5) == signed_pair_fingerprint(negative, 5),
            "Rank-two negative fixture must share projective fingerprints")
    require(qs[0] - 1 != opposite_qs[0] - 1,
            "False SL2-module-isomorphism implies oriented Hodge-isomorphism shortcut")
    exclusive = (1, 2, 2, 2, 2)
    require(sum(exclusive) % 3 == 0, "Exclusive-label fixture is not zero-sum")
    incident = [(exclusive[0] + a) % 3 for a in exclusive[1:]]
    require(incident == [0, 0, 0, 0], "False semisimple pair at every active label shortcut")
    twelve = (1,) * 12
    twelve_ages = ages(twelve, 3)
    require(twelve_ages == [4, 8] and 2 not in twelve_ages, "False every-word age-two shortcut")
    positive_embedding(twelve, 3)
    binary = []
    for support in (4, 6, 8, 12):
        q = ages((1,) * support, 2)
        require(q == [support // 2] and 2 <= q[0] <= support - 2, "Binary mixed signature")
        binary.append({"support": support, "age": q[0],
                       "Hodge_multiplicities": [q[0] - 1, support - 1 - q[0]]})
    # Ensure the check helper rejects a bad input even under optimized Python.
    rejected = False
    try:
        ages((1, 1, 1, 1), 5)
    except AssertionError:
        rejected = True
    require(rejected, "Malformed branch-word check was disabled")
    return {
        "rank_two_orientation": {"p": 5, "word": list(c), "negative": list(negative),
                                 "ages": qs, "negative_ages": opposite_qs,
                                 "same_projective_fingerprint": True,
                                 "different_oriented_Hodge_multiplicities": True},
        "false_semisimple_pair_shortcut": {"p": 3, "word": list(exclusive),
                                           "pair_sums_incident_to_first_label": incident,
                                           "actual_unipotent_nontriviality":
                                               "Requires written spanning-vector proof; not checked here"},
        "false_every_word_has_age_two": {"p": 3, "word": list(twelve),
                                         "ages": twelve_ages, "mixed_embedding_exists": True},
        "binary_cases": binary,
        "malformed_nonzero_sum_word_rejected": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    script = Path(__file__).resolve()
    report = {
        "schema_version": 1,
        "status": "bounded_checks_passed",
        "scope": "Deterministic exact finite arithmetic regressions, NOT a universal proof",
        "proof_boundary": [
            "Finite primes and supports do not prove the universal classification.",
            "No braid representation, Hodge lifting, algebraic correspondence, or cycle construction is verified.",
            "No all-powers Hodge theorem or external theorem is certified by this script.",
        ],
        "script_sha256": sha256(script.read_bytes()).hexdigest(),
        "candidate_partitions": check_partitions(),
        "four_label_fingerprints": check_four_labels(),
        "higher_rank_regressions": check_higher_rank(),
        "empty_word_coefficient_algebra": check_empty_word_vandermonde(),
        "negative_controls": check_negative_controls(),
    }
    payload = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload)
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
