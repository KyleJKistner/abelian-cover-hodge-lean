#!/usr/bin/env python3
"""Exact regression certificate for the completed finite-abelian Phase I theorem.

This script does not replace the written proofs of:
  * full simple projection and semisimple Goursat assembly;
  * high-rank character reconstruction;
  * algebraic descent and the double-centralizer theorem;
  * the Hodge-theoretic all-powers argument.

It independently checks every finite or symbolic identity used in the four-point
and split elementary-p calculations, and records reproducible file hashes.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
from math import isqrt
from pathlib import Path
from typing import Any

import sympy as sp

HERE = Path(__file__).resolve().parent
CORE_PATH = HERE / "phase1src" / "p_ary_mt_defect_certificate.py"
MANUSCRIPT = HERE / "phase_I_complete.tex"
OUT = HERE / "phase_I_certificate_report.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_core():
    spec = importlib.util.spec_from_file_location("p_ary_core", CORE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot load {CORE_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def primes_through(n: int) -> list[int]:
    out: list[int] = []
    for q in range(2, n + 1):
        if all(q % d for d in range(2, isqrt(q) + 1)):
            out.append(q)
    return out


def verify_kummer_action_and_split_formulas(max_prime: int = 101) -> dict[str, Any]:
    # Character-lattice actions induced by Phi, Psi, Omega.
    I = sp.eye(2)
    S = sp.Matrix([[0, 1], [1, 0]])
    actions = {"Phi": S, "Psi": -I, "Omega": -S}
    for matrix in actions.values():
        assert matrix * matrix == I
    assert actions["Phi"] * actions["Psi"] == actions["Omega"]
    assert actions["Psi"] * actions["Phi"] == actions["Omega"]

    rows: list[dict[str, int]] = []
    for p in [q for q in primes_through(max_prime) if q % 2 == 1]:
        pairs = [(a, b) for a in range(1, p) for b in range(1, p)]

        def orbit(pair: tuple[int, int]) -> frozenset[tuple[int, int]]:
            a, b = pair
            return frozenset({
                (a % p, b % p),
                ((-a) % p, (-b) % p),
                (b % p, a % p),
                ((-b) % p, (-a) % p),
            })

        orbits = {orbit(pair) for pair in pairs}
        expected_blocks = (p * p - 1) // 4
        assert len(orbits) == expected_blocks

        size2 = sum(len(o) == 2 for o in orbits)
        size4 = sum(len(o) == 4 for o in orbits)
        assert size2 == p - 1  # oriented embeddings on the two fixed slopes
        assert size4 == (p - 1) * (p - 3) // 4

        # Rational slope orbits under r -> r^{-1}.
        slopes = set(range(1, p))
        slope_orbits: set[frozenset[int]] = set()
        while slopes:
            r = slopes.pop()
            rinv = pow(r, -1, p)
            block = frozenset({r, rinv})
            slope_orbits.add(block)
            slopes.discard(rinv)
        assert len(slope_orbits) == (p + 1) // 2
        fixed = sum(len(o) == 1 for o in slope_orbits)
        nonfixed = sum(len(o) == 2 for o in slope_orbits)
        assert fixed == 2
        assert nonfixed == (p - 3) // 2

        d = (p - 1) // 2
        genus = (p - 1) ** 2
        decomposition_dimension = 2 * d + 2 * d + nonfixed * 4 * d
        assert decomposition_dimension == genus

        complex_coordinates = (p - 1) ** 2 // 2
        defect = complex_coordinates - expected_blocks
        assert defect == (p - 1) * (p - 3) // 4

        ns_from_blocks = d * (2 * 3 + nonfixed * 10)
        ns_closed = (p - 1) * (5 * p - 9) // 2
        assert ns_from_blocks == ns_closed

        end_dimension_q = 2 * (2**2) * d + nonfixed * (4**2) * d
        assert end_dimension_q == 4 * (p - 1) * (p - 2)

        rows.append({
            "p": p,
            "genus": genus,
            "complex_disk_coordinates": complex_coordinates,
            "complex_kummer_blocks": expected_blocks,
            "diagonal_defect": defect,
            "rational_Hodge_factors": len(slope_orbits),
            "fixed_slope_factors": fixed,
            "nonfixed_slope_factors": nonfixed,
            "simple_factor_dimension": d,
            "decomposition_dimension": decomposition_dimension,
            "End0_Q_dimension": end_dimension_q,
            "Neron_Severi_rank": ns_closed,
        })

    return {
        "character_lattice_actions": {
            name: [[int(x) for x in row] for row in matrix.tolist()]
            for name, matrix in actions.items()
        },
        "group_relations": "Phi^2=Psi^2=Omega^2=1 and Phi Psi=Psi Phi=Omega",
        "odd_primes_checked_through": max_prime,
        "rows": rows,
    }


def verify_mobius_involutions() -> dict[str, str]:
    x, t = sp.symbols("x t", nonzero=True)
    transformations = {
        "Phi": t * (x - 1) / (x - t),
        "Psi": (t - x) / (1 - x),
        "Omega": t / x,
    }
    for name, T in transformations.items():
        composed = sp.cancel(T.subs(x, T, simultaneous=True) - x)
        assert sp.factor(composed) == 0, name
    return {name: str(sp.factor(T)) for name, T in transformations.items()}



def verify_full_kummer_maps() -> dict[str, Any]:
    """Check the complete Phi/Psi/Omega formulas, not only their base maps."""
    x, u, v, t, s, z = sp.symbols("x u v t s z", nonzero=True)
    identity = (x, u, v)
    maps = {
        "Phi": (t * (x - 1) / (x - t), v / s, s * u),
        "Psi": ((t - x) / (1 - x), -1 / (s * u), -s / v),
        "Omega": (t / x, -1 / v, -1 / u),
    }
    rho1 = (x, z * u, v)
    rho2 = (x, u, z * v)
    rho1_inv = (x, u / z, v)
    rho2_inv = (x, u, v / z)

    def compose(F: tuple[sp.Expr, sp.Expr, sp.Expr],
                G: tuple[sp.Expr, sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr, sp.Expr]:
        sub = {x: G[0], u: G[1], v: G[2]}
        return tuple(sp.factor(sp.cancel(expr.subs(sub, simultaneous=True))) for expr in F)

    def equal(F: tuple[sp.Expr, sp.Expr, sp.Expr],
              G: tuple[sp.Expr, sp.Expr, sp.Expr]) -> bool:
        return all(sp.factor(sp.cancel(a - b)) == 0 for a, b in zip(F, G))

    for name, F in maps.items():
        assert equal(compose(F, F), identity), name
    assert equal(compose(maps["Phi"], maps["Psi"]), maps["Omega"])
    assert equal(compose(maps["Psi"], maps["Phi"]), maps["Omega"])

    # Conjugation relations; each Kummer map is its own inverse.
    assert equal(compose(maps["Phi"], compose(rho1, maps["Phi"])), rho2)
    assert equal(compose(maps["Phi"], compose(rho2, maps["Phi"])), rho1)
    assert equal(compose(maps["Psi"], compose(rho1, maps["Psi"])), rho1_inv)
    assert equal(compose(maps["Psi"], compose(rho2, maps["Psi"])), rho2_inv)
    assert equal(compose(maps["Omega"], compose(rho1, maps["Omega"])), rho2_inv)
    assert equal(compose(maps["Omega"], compose(rho2, maps["Omega"])), rho1_inv)

    return {
        "involutions": ["Phi", "Psi", "Omega"],
        "composition": "Phi Psi = Psi Phi = Omega",
        "deck_conjugation": {
            "Phi": "rho1 <-> rho2",
            "Psi": "rho_i -> rho_i^{-1}",
            "Omega": "rho1 -> rho2^{-1}, rho2 -> rho1^{-1}",
        },
    }

def main() -> None:
    core = load_core()
    core_results = {
        "gassner_fricke": core.derive_rank_two_gassner(),
        "half_shift_finite_regression": core.verify_half_shift_denominators(),
        "low_prime_code_census": core.verify_low_prime_census(),
        "split_rational_function_identities": core.split_family_checks(),
    }

    result: dict[str, Any] = {
        "scope": "exact symbolic and finite regression for Phase I completion",
        "proof_boundary": [
            "not a substitute for full simple projection",
            "not a substitute for semisimple Goursat and high-rank reconstruction",
            "not a substitute for algebraic descent and double centralizer",
            "not a substitute for the all-powers Hodge argument",
        ],
        "core": core_results,
        "mobius_involutions": verify_mobius_involutions(),
        "full_kummer_map_checks": verify_full_kummer_maps(),
        "split_family_rational_checks": verify_kummer_action_and_split_formulas(),
        "hashes": {
            str(CORE_PATH.relative_to(HERE)): sha256(CORE_PATH),
            MANUSCRIPT.name: sha256(MANUSCRIPT),
            Path(__file__).name: sha256(Path(__file__)),
        },
    }
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    summary = {
        "report": str(OUT),
        "disk_vectors_checked": core_results["half_shift_finite_regression"]["disk_vectors_checked"],
        "half_shift_failures": core_results["half_shift_finite_regression"]["failures"],
        "p3_defective_orbits": core_results["low_prime_code_census"]["p3"]["defective_orbits"],
        "p5_defective_orbits": core_results["low_prime_code_census"]["p5"]["defective_orbits"],
        "odd_primes_checked_through": 101,
        "manuscript_sha256": result["hashes"][MANUSCRIPT.name],
        "certificate_sha256": result["hashes"][Path(__file__).name],
    }
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
