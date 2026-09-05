#!/usr/bin/env python3
"""New bounded Phase I regression checks; does not recover the legacy core.

Requires SymPy (see requirements-audit.txt). No legacy module is imported.
The written argument, not these finite checks, proves the all-prime statement.
Run: python scripts/check_phase_i.py --prime-bound 101 --output report.json
"""
from __future__ import annotations

import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path
from typing import Any

import sympy as sp


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def primes_through(bound: int) -> list[int]:
    return [
        n for n in range(3, bound + 1, 2)
        if all(n % d for d in range(2, isqrt(n) + 1))
    ]


def check_maps() -> dict[str, Any]:
    x, u, v, t, s, z = sp.symbols("x u v t s z", nonzero=True)
    f1, f2 = x / (x - t), x - 1
    maps = {
        "Phi": (t * (x - 1) / (x - t), v / s, s * u),
        "Psi": ((t - x) / (1 - x), -1 / (s * u), -s / v),
        "Omega": (t / x, -1 / v, -1 / u),
    }
    phi, psi, omega = (maps[name][0] for name in ("Phi", "Psi", "Omega"))
    differences = {
        "Phi_f1": f1.subs(x, phi) - f2 / (t - 1),
        "Phi_f2": f2.subs(x, phi) - (t - 1) * f1,
        "Psi_f1": f1.subs(x, psi) * f1 + 1 / (t - 1),
        "Psi_f2": f2.subs(x, psi) * f2 - (1 - t),
        "Omega_f1": f1.subs(x, omega) * f2 + 1,
        "Omega_f2": f2.subs(x, omega) * f1 + 1,
    }
    for name, difference in differences.items():
        require(sp.cancel(difference) == 0, f"Defining-equation identity: {name}")

    def compose(F, G):
        substitution = {x: G[0], u: G[1], v: G[2]}
        return tuple(sp.cancel(e.subs(substitution, simultaneous=True)) for e in F)

    def equal(F, G):
        return all(sp.cancel(a - b) == 0 for a, b in zip(F, G))

    identity = (x, u, v)
    for name, F in maps.items():
        require(equal(compose(F, F), identity), f"{name} must square to identity")
    require(equal(compose(maps["Phi"], maps["Psi"]), maps["Omega"]), "Phi Psi")
    require(equal(compose(maps["Psi"], maps["Phi"]), maps["Omega"]), "Psi Phi")
    rho1, rho2 = (x, z * u, v), (x, u, z * v)
    inv1, inv2 = (x, u / z, v), (x, u, v / z)
    conjugations = [
        ("Phi", rho1, rho2), ("Phi", rho2, rho1),
        ("Psi", rho1, inv1), ("Psi", rho2, inv2),
        ("Omega", rho1, inv2), ("Omega", rho2, inv1),
    ]
    for name, rho, target in conjugations:
        require(equal(compose(maps[name], compose(rho, maps[name])), target),
                f"Deck conjugation for {name}")
    return {
        "rational_function_identities": list(differences),
        "involutions": list(maps),
        "composition_relations": 2,
        "deck_conjugation_relations": len(conjugations),
        "equation_preservation_premises": ["p odd", "s^p = t - 1"],
        "status": "PASS",
    }


def check_split_primes(bound: int) -> dict[str, Any]:
    rows = []
    for p in primes_through(bound):
        fibres: dict[tuple[int, int], set[tuple[int, int]]] = {}
        source_rows = 0
        for a in range(1, p):
            for b in range(1, p):
                # All nonzero Galois rows permute these pairs. Verify the
                # positive- and negative-root finite labels explicitly.
                for k in (1, p - 1):
                    labels = [(k * v) % p for v in (a, b, p - a)]
                    require(all(0 < v < p for v in labels), "Inactive source label")
                    require(p < sum(labels) < 2 * p, "MN good n=3 inequality")
                    require(sum(labels) % p != 0, "Infinity must remain active")
                    source_rows += 1
                # A completely independent collision grouping: two unordered
                # eigenratios represented as residues modulo sign.
                r1, r2 = (a + b) % p, (b - a) % p
                key = (min(r1, (-r1) % p), min(r2, (-r2) % p))
                fibres.setdefault(key, set()).add((a, b))
                word = (a, b, (-a) % p, (-b) % p)
                require(sum(word) == 2 * p, "Split age must be two")
                # Equation-level inverse of the two independent signs.
                orbit = {(a, b), ((-a) % p, (-b) % p),
                         (b, a), ((-b) % p, (-a) % p)}
                inv_two = pow(2, -1, p)
                for eps in (-1, 1):
                    for eta in (-1, 1):
                        ap = inv_two * (eps * (a + b) + eta * (a - b)) % p
                        bp = inv_two * (eps * (a + b) - eta * (a - b)) % p
                        require((ap, bp) in orbit, "Independent-sign reconstruction")
        for fibre in fibres.values():
            a, b = next(iter(fibre))
            orbit = {(a, b), ((-a) % p, (-b) % p),
                     (b, a), ((-b) % p, (-a) % p)}
            require(fibre == orbit, f"Extra or missing eigenratio collision at p={p}")

        size2 = sum(len(fibre) == 2 for fibre in fibres.values())
        size4 = sum(len(fibre) == 4 for fibre in fibres.values())
        require(size2 == p - 1, "Size-two orbit count")
        require(size4 == (p - 1) * (p - 3) // 4, "Size-four orbit count")
        require(len(fibres) == (p * p - 1) // 4, "Total monodromy-block count")
        slopes = {frozenset((r, pow(r, -1, p))) for r in range(1, p)}
        fixed = sum(len(o) == 1 for o in slopes)
        paired = sum(len(o) == 2 for o in slopes)
        require(fixed == 2 and paired == (p - 3) // 2, "Rational slope orbits")
        d, genus = (p - 1) // 2, (p - 1) ** 2
        require(2 * genus - 2 == -2 * p * p + 4 * p * (p - 1),
                "Riemann-Hurwitz")
        require((2 * fixed + 4 * paired) * d == genus, "Isogeny dimensions")
        end_dim = (4 * fixed + 16 * paired) * d
        require(end_dim == 4 * size2 + 16 * size4 == 4 * (p - 1) * (p - 2),
                "Rational algebra and complex commutant dimensions")
        ns_rank = (3 * fixed + 10 * paired) * d
        require(ns_rank == (p - 1) * (5 * p - 9) // 2, "NS formula")
        rows.append({
            "p": p, "words": (p - 1) ** 2, "source_orientation_rows": source_rows,
            "genus": genus, "complex_blocks": len(fibres),
            "size_two_blocks": size2, "size_four_blocks": size4,
            "rational_slope_blocks": len(slopes), "End0_Q_dimension": end_dim,
            "NS_rank": ns_rank,
        })
    return {
        "status": "PASS", "prime_bound": bound, "prime_count": len(rows),
        "total_words": sum(row["words"] for row in rows),
        "all_unit_rows_coverage":
            "Multiplication by every nonzero k permutes all enumerated (a,b); "
            "both source root orientations are also checked explicitly.",
        "rows": rows,
    }


def check_crossed_products(bound: int) -> dict[str, Any]:
    z = sp.symbols("z")
    rows = []
    for p in primes_through(min(bound, 13)):
        n = p - 1
        modulus = sp.Poly(sum(z**j for j in range(p)), z, domain=sp.QQ)

        def column(exponent: int):
            remainder = sp.rem(sp.Poly(z**exponent, z, domain=sp.QQ), modulus)
            return sp.Matrix([remainder.nth(i) for i in range(n)])

        Z = sp.Matrix.hstack(*(column(j + 1) for j in range(n)))
        S = sp.Matrix.hstack(*(column((-j) % p) for j in range(n)))
        require(S * S == sp.eye(n), "Cyclotomic conjugation involution")
        require(S * Z * S == Z.inv(), "Cyclotomic semilinear relation")
        basis = [Z**j for j in range(n)] + [Z**j * S for j in range(n)]
        rank = sp.Matrix.hstack(*(B.reshape(n * n, 1) for B in basis)).rank()
        require(rank == 2 * n, "Faithful Q-dimension of K semidirect C2")
        real_generator = Z + Z.inv()
        require(real_generator * S == S * real_generator, "Real centre")
        centre_rank = sp.Matrix.hstack(*(
            (real_generator**j).reshape(n * n, 1) for j in range(n // 2)
        )).rank()
        require(centre_rank == n // 2, "Real cyclotomic field degree")
        rows.append({"p": p, "algebra_Q_dimension": rank,
                     "real_centre_Q_dimension": centre_rank})
    return {"status": "PASS", "prime_bound": min(bound, 13), "rows": rows}


def check_inverse_matrix_units() -> dict[str, Any]:
    checks = 0
    for multiplicity in (2, 4):
        D = [sp.Matrix([[1, i], [0, 1]]) for i in range(multiplicity)]
        units = {}
        for i in range(multiplicity):
            for j in range(multiplicity):
                slot = sp.zeros(multiplicity)
                slot[i, j] = 1
                units[i, j] = sp.kronecker_product(slot, D[i] * D[j].inv())
        zero = sp.zeros(2 * multiplicity)
        for (i, j), E in units.items():
            for (k, ell), F in units.items():
                target = units[i, ell] if j == k else zero
                require(E * F == target, "Inverse-graph matrix-unit identity")
                checks += 1
    # Regression for the exact defect in the former adjoint shortcut.
    I, O = sp.eye(2), sp.zeros(2)
    J = O.row_join(I).col_join((-I).row_join(O))
    e_c = I.row_join(O).col_join(O.row_join(O))
    e_minus_c = sp.eye(4) - e_c
    adjoint = J.inv() * e_c.T * J
    require(adjoint == e_minus_c, "Rosati switches a nonreal character")
    require(adjoint * e_c == sp.zeros(4), "Old oriented-adjoint composite vanishes")
    return {"status": "PASS", "matrix_unit_products": checks,
            "Rosati_orientation_regression": "e_c^dagger = e_-c; e_-c e_c = 0"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prime-bound", type=int, default=101)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.prime_bound < 3:
        parser.error("--prime-bound must be at least 3")
    root = Path(__file__).resolve().parents[1]
    sources = [
        Path(__file__).resolve(),
        root / "manuscripts/phase_I_revised.tex",
    ]
    report = {
        "status": "PASS",
        "certificate": "New Phase I split-family regression; not recovered legacy core",
        "proof_boundary": [
            "Finite bounds do not prove the all-prime theorem.",
            "No computational verification of geometric monodromy or Hodge theory.",
            "No replay of missing Fox-Gassner or 7,077,120-vector legacy census.",
            "No general finite-abelian block or fusion theorem certified.",
        ],
        "maps": check_maps(),
        "split_primes": check_split_primes(args.prime_bound),
        "crossed_products": check_crossed_products(args.prime_bound),
        "inverse_matrix_units": check_inverse_matrix_units(),
        "compact_embedding_regression": [
            {"row": k, "residues": [(k * a) % 5 for a in (1, 1, 1, 2)],
             "signature": [3 - sum((k * a) % 5 for a in (1, 1, 1, 2)) // 5,
                           sum((k * a) % 5 for a in (1, 1, 1, 2)) // 5 - 1]}
            for k in range(1, 5)
        ],
        "sympy_version": sp.__version__,
        "source_sha256": {
            str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sources
        },
    }
    serialized = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(serialized)
    else:
        print(serialized, end="")


if __name__ == "__main__":
    main()
