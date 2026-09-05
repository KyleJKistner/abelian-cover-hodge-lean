#!/usr/bin/env python3
"""Exact bounded checks for the new structural/transfer drafts, not geometry.

Checks subgroup signatures, first exceptional dimensions, Koszul signs,
evaluation-hyperplane general position, and odd-order primitive projectors.
No cycle, monodromy, or novelty claim is certified by these finite
computations. Standard library only.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, combinations_with_replacement, permutations, product
import json
from math import comb, factorial, gcd, isqrt, lcm
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def signature(word: list[int], b: int, p: int) -> int:
    value = sum(b * a % p for a in word)
    require(value % p == 0, "Nonintegral branch age")
    return len(word) - 1 - value // p


def determinant(matrix: list[list[int]]) -> Fraction:
    a = [[Fraction(x) for x in row] for row in matrix]
    result = Fraction(1)
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            result *= -1
        entry = a[j][j]
        result *= entry
        for i in range(j + 1, len(a)):
            ratio = a[i][j] / entry
            a[i] = [x - ratio * y for x, y in zip(a[i], a[j])]
    return result


def check_exceptional() -> dict:
    rows = []
    for p in range(3, 104, 2):
        if any(p % d == 0 for d in range(2, isqrt(p) + 1)):
            continue
        for m in range(3, p, 2):
            if (p - 1) % m:
                continue
            subgroup = [a for a in range(1, p) if pow(a, m, p) == 1]
            require(len(subgroup) == m and sum(subgroup) % p == 0, "Subgroup data")
            for k in range(4):
                word = subgroup + [a for _ in range(k) for a in (1, p - 1)]
                if len(word) < 5:
                    continue
                h = len(word) - 2
                d = {b: signature(word, b, p) for b in range(1, p)}
                stabilizer = [v for v in range(1, p)
                              if all(d[b] == d[b * v % p] for b in d)]
                require(stabilizer == subgroup, "Extra signature stabilizer")
                generated = Counter()
                for v in subgroup:
                    if v == 1:
                        continue
                    second = [-v * a % p for a in word]
                    generator = -pow(v, -1, p) % p
                    require(all(pow(generator, -1, p) * a % p == b
                                for a, b in zip(word, second)), "Generator inverse")
                    counts = Counter(word + second)
                    require(all(counts[a] == counts[-a % p] for a in counts),
                            "Mixed word is not opposite-paired")
                    current = set()
                    for b in range(1, p):
                        require(d[b] + signature(second, b, p) == h, "Hodge type")
                        pair = tuple(sorted((b, -v * b % p)))
                        require(pair[0] != pair[1] and sum(pair) % p != 0,
                                "Zero wedge or divisor weight")
                        current.add(pair)
                        generated[pair] += 1
                    require(len(current) == p - 1, "Diagonal loses injectivity")
                # Independently scan every nonopposite unordered volume pair,
                # and test its type at every Galois conjugate, not just b=1.
                all_hodge_pairs = {
                    (b, c) for b, c in combinations(range(1, p), 2)
                    if (b + c) % p and all(d[u * b % p] + d[u * c % p] == h
                                          for u in range(1, p))
                }
                require(all_hodge_pairs == set(generated), "Missed exceptional orbit")
                expected = (p - 1) * (m - 1) // 2
                require(len(generated) == expected, "Exceptional dimension")
                require(set(generated.values()) == {2}, "Inverse-v duplicate count")
                rows.append({"p": p, "subgroup_order": m, "added_pairs": k,
                             "word": word, "rank": h, "genus": (p - 1) * h // 2,
                             "first_exceptional_codimension": h,
                             "exceptional_dimension": expected,
                             "divisor_dimension": comb((p - 1) // 2 + h - 1, h)})
    first = next(row for row in rows if (row["p"], row["subgroup_order"],
                                         row["added_pairs"]) == (7, 3, 1))
    require(first["genus"] == 9 and first["exceptional_dimension"] == 6
            and first["divisor_dimension"] == 10, "Ninefold example")
    controls = []
    for p in (7, 13, 19, 31):
        pairs = {tuple(sorted((b, -b % p))) for b in range(1, p)}
        require(len(pairs) == (p - 1) // 2, "v=1 control should collapse")
        controls.append({"p": p, "v": 1, "diagonal_rank": len(pairs)})
    return {"prime_bound": 103, "case_count": len(rows), "rows": rows,
            "negative_controls": controls}


def check_volume_words() -> dict:
    count = 0
    for p in (7, 13, 19):
        subgroup = {a for a in range(1, p) if pow(a, 3, p) == 1}
        word = sorted(subgroup) + [1, p - 1]
        h = len(word) - 2
        cosets = {b: frozenset(b * a % p for a in subgroup) for b in range(1, p)}
        for length in (2, 4):
            for labels in combinations_with_replacement(range(1, p), length):
                balanced = all(sum(signature(word, b * t % p, p) for b in labels)
                               == length * h // 2 for t in range(1, p))
                charges = Counter(cosets[b] for b in labels)
                paired = all(charges[cosets[b]] == charges[cosets[-b % p]]
                             for b in range(1, p))
                require(balanced == paired, "Volume-word opposite-coset criterion")
                count += 1
    return {"primes": [7, 13, 19], "volume_lengths": [2, 4], "cases": count}


def check_koszul() -> list[dict]:
    rows = []
    for h in range(1, 7):
        alternating_trace = symmetric_trace = 0
        for perm in permutations(range(h)):
            unseen = set(range(h))
            cycles = 0
            while unseen:
                cycles += 1
                item = next(iter(unseen))
                while item in unseen:
                    unseen.remove(item)
                    item = perm[item]
            trace = h ** cycles
            symmetric_trace += trace
            alternating_trace += (-1) ** (h - cycles) * trace
        require(alternating_trace == factorial(h), "Exterior determinant not rank one")
        require(symmetric_trace == factorial(h) * comb(2 * h - 1, h),
                "Ordinary symmetric negative control")
        rows.append({"tensor_slots": h, "eigenspace_dimension": h,
                     "geometric_permutation_invariant_dimension": 1,
                     "incorrect_unsigned_dimension": symmetric_trace // factorial(h)})
    return rows


def check_hyperplanes() -> list[dict]:
    rows = []
    for h in range(1, 9):
        # Evaluation at h+2 distinct finite points gives the h+2 branch
        # hyperplanes in the coefficient projective space of degree-h forms.
        evaluations = [[t ** j for j in range(h + 1)] for t in range(h + 2)]
        minors = [determinant([row for i, row in enumerate(evaluations) if i != omit])
                  for omit in range(h + 2)]
        require(all(minors), "Evaluation hyperplanes not in general position")
        relation = [(-1) ** i * value for i, value in enumerate(minors)]
        require(all(sum(relation[i] * evaluations[i][j] for i in range(h + 2)) == 0
                    for j in range(h + 1)), "Wrong unique relation")
        rows.append({"dimension": h, "branch_hyperplanes": h + 2,
                     "all_maximal_minors_nonzero": True,
                     "unique_relation_has_no_zero_coefficient": True})
    return rows


def prime_divisors(value: int) -> list[int]:
    result = []
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            result.append(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor += 1
    if value > 1:
        result.append(value)
    return result


def cyclic_multiply(left: list[Fraction], right: list[Fraction]) -> list[Fraction]:
    """Exact multiplication in Q[T]/(T^d−1), in the regular group basis."""
    require(len(left) == len(right), "Incompatible cyclic group algebras")
    degree = len(left)
    result = [Fraction(0)] * degree
    for i, a in enumerate(left):
        if a:
            for j, b in enumerate(right):
                if b:
                    result[(i + j) % degree] += a * b
    return result


def check_primitive_projectors() -> dict:
    rows = []
    for degree in (3, 9, 15, 21, 25, 27, 35, 45, 63, 75, 105):
        identity = [Fraction(int(i == 0)) for i in range(degree)]
        projector = identity[:]
        averages = []
        for prime in prime_divisors(degree):
            average = [Fraction(0)] * degree
            for j in range(prime):
                average[j * degree // prime] = Fraction(1, prime)
            averages.append(average)
            projector = cyclic_multiply(
                projector, [a - b for a, b in zip(identity, average)]
            )
        require(cyclic_multiply(projector, projector) == projector,
                "Primitive projector is not idempotent")
        require(all(not any(cyclic_multiply(projector, average)) for average in averages),
                "Primitive projector retains a lower conductor")
        units = [b for b in range(degree) if gcd(b, degree) == 1]
        # The trace of multiplication by P in the regular representation is
        # degree times its identity coefficient. It independently counts rank.
        require(degree * projector[0] == len(units), "Primitive projector rank")
        slots = prime_divisors(degree)[0]
        simultaneous = {slots * b % degree for b in units}
        simultaneous_conductors = {degree // gcd(b, degree) for b in simultaneous}
        require(simultaneous_conductors == {degree // slots}
                and len(simultaneous) < len(units),
                "Simultaneous-slot negative control failed to lose conductor")
        rows.append({"degree": degree, "primitive_rank": len(units),
                     "idempotent": True, "lower_conductors_removed": True,
                     "one_slot_eigenlabel_count": len(units),
                     "simultaneous_slot_negative_control": {
                         "slots": slots, "conductor": degree // slots,
                         "distinct_eigenlabels": len(simultaneous)}})
    return {"algebra": "Exact rational cyclic group algebra, not algebraic geometry",
            "rows": rows}


def check_character_inventory() -> list[dict]:
    rows = []
    for factors in ((9,), (3, 9), (3, 15), (15, 15), (5, 9), (3, 5, 7)):
        exponent = lcm(*factors)
        units = [u for u in range(exponent) if gcd(u, exponent) == 1]
        characters = list(product(*(range(n) for n in factors)))
        zero = (0,) * len(factors)
        seen = {zero}
        orbit_count = 0
        whole_quotient_occurrences = Counter()
        for character in characters:
            if character in seen:
                continue
            conductor = lcm(*(n // gcd(b, n) for b, n in zip(character, factors)))
            orbit = {tuple(u * b % n for b, n in zip(character, factors)) for u in units}
            require(not orbit.intersection(seen), "Primitive character orbits overlap")
            expected_size = sum(gcd(u, conductor) == 1 for u in range(conductor))
            require(len(orbit) == expected_size, "Unit orbit has the wrong conductor size")
            seen.update(orbit)
            orbit_count += 1
            for multiplier in range(1, conductor):
                whole_quotient_occurrences[
                    tuple(multiplier * b % n for b, n in zip(character, factors))
                ] += 1
        require(seen == set(characters), "Primitive factors omit a character")
        require(set(whole_quotient_occurrences) == set(characters) - {zero},
                "Whole-quotient negative control misses a character")
        require(any(count > 1 for count in whole_quotient_occurrences.values()),
                "Whole-quotient negative control did not exhibit double counting")
        rows.append({"cyclic_group_factors": list(factors), "exponent": exponent,
                     "nonzero_characters": len(characters) - 1,
                     "primitive_orbits": orbit_count,
                     "incorrect_whole_quotient_occurrence_count":
                     sum(whole_quotient_occurrences.values())})
    return rows


def polynomial_multiply(left: list[int], right: list[int]) -> list[int]:
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return result


def polynomial_remainder(value: list[int], monic: list[int]) -> list[int]:
    require(monic[-1] == 1, "Polynomial divisor is not monic")
    result = value[:]
    while len(result) >= len(monic):
        lead = result[-1]
        offset = len(result) - len(monic)
        for j, coefficient in enumerate(monic):
            result[offset + j] -= lead * coefficient
        result.pop()
    while result and result[-1] == 0:
        result.pop()
    return result


def check_conductor_fifteen() -> dict:
    # Verify the modulus from its cyclotomic factorization, then work in
    # Z[x]/Phi_15 exactly; no approximate complex roots are used.
    phi15 = [1, -1, 0, 1, -1, 1, 0, -1, 1]
    factorization = phi15
    for factor in ([-1, 1], [1, 1, 1], [1, 1, 1, 1, 1]):
        factorization = polynomial_multiply(factorization, factor)
    require(factorization == [-1] + [0] * 14 + [1], "Wrong Phi_15 polynomial")
    subgroup = {1, 2, 4, 8}
    period = [int(i in subgroup) for i in range(15)]
    conjugate = [int(-i % 15 in subgroup) for i in range(15)]
    require(polynomial_remainder([a + b for a, b in zip(period, conjugate)], phi15) == [1],
            "Wrong conductor-15 Gaussian-period trace")
    require(polynomial_remainder(polynomial_multiply(period, conjugate), phi15) == [4],
            "Wrong conductor-15 Gaussian-period norm")
    units = [u for u in range(1, 15) if gcd(u, 15) == 1]
    four = {str(u): signature([1, 2, 4, 8], u, 15) for u in units}
    three = {str(u): signature([1, 2, 12], u, 15) for u in units}
    require(all(four[str(u)] == (2 if u in subgroup else 0)
                and three[str(u)] == (1 if u in subgroup else 0) for u in units),
            "The exceptional factor and elliptic source have different primitive CM types")
    # A primitive composite cover need not contain a unit branch residue.
    # This word has no deck-fixed branch point for Abel–Jacobi normalization.
    no_unit_word = [3, 5, 10, 12]
    require(sum(no_unit_word) % 15 == 0 and gcd(15, *no_unit_word) == 1
            and all(gcd(15, a) > 1 for a in no_unit_word),
            "No-unit branch-word negative control")
    count = 0
    exceptions = {}
    for degree in range(3, 46, 2):
        degree_units = [u for u in range(1, degree) if gcd(u, degree) == 1]
        # Sort the first three residues and force the fourth by sum zero.
        # Unlike normalization to a leading 1, this also checks no-unit words.
        for a, b, c in combinations_with_replacement(range(1, degree), 3):
            last = (-a - b - c) % degree
            if not last or last < c or gcd(degree, a, b, c, last) != 1:
                continue
            word = [a, b, c, last]
            count += 1
            if all(signature(word, u, degree) in (0, 2) for u in degree_units):
                exceptions.setdefault(str(degree), []).append(word)
    require(exceptions == {"15": [[1, 2, 4, 8], [7, 11, 13, 14]]},
            "Unexpected all-definite primitive support-four word")
    return {"period_polynomial": "z^2-z+4", "quadratic_discriminant": -15,
            "four_branch_hodge_multiplicities": four,
            "three_branch_hodge_multiplicities": three,
            "four_branch_primitive_rational_dimension": 16,
            "three_branch_primitive_rational_dimension": 8,
            "no_unit_branch_negative_control": no_unit_word,
            "support_four_enumeration": {"odd_degree_range": [3, 45],
                                         "sorted_primitive_words_checked": count,
                                         "all_definite_words": exceptions},
            "scope": "Numeric CM types and bounded enumeration, not constant-family geometry"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sources = ["manuscripts/structural_extensions.tex",
               "manuscripts/fermat_determinant_transfer.tex"]
    report = {
        "status": "PASS",
        "scope": "Bounded arithmetic, eigenlabel, primitive-projector, Koszul and hyperplane checks; no geometry certified",
        "source_sha256": {s: sha256((ROOT / s).read_bytes()).hexdigest() for s in sources},
        "exceptional_families": check_exceptional(),
        "volume_words": check_volume_words(),
        "koszul_sign": check_koszul(), "evaluation_hyperplanes": check_hyperplanes(),
        "odd_primitive_projectors": check_primitive_projectors(),
        "primitive_character_inventory": check_character_inventory(),
        "conductor_fifteen": check_conductor_fifteen(),
    }
    result = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(result)
    else:
        print(result, end="")


if __name__ == "__main__":
    main()
