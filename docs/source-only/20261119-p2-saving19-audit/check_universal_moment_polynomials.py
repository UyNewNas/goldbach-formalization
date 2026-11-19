#!/usr/bin/env python3
"""Exact coefficient audit of saving19's two universal degree-six guards.

This independently enumerates monomials in nine arbitrary variables. It does
not elaborate Lean or prove the analytic integral, the row guards or P2.6.
"""
import argparse
import hashlib
from fractions import Fraction as Q
from math import comb, factorial, prod
from pathlib import Path

SOURCE_SHA = "59ccbb110e9aceac63a5bb7030b49e0f1103993bc6b2f6fb2b49a80391b2d41e"
ZERO = (0,) * 9
DEGREE = 6


def require(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)


def compositions(total, width):
    if width == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for rest in compositions(total - first, width - 1):
                yield (first,) + rest


def shifted(exp, position, degree):
    result = list(exp)
    result[position] += degree
    return tuple(result)


def newton(duplicate):
    # H_k = (1/k) sum_{j=1}^k (sum y_r^j + y_i^j) H_{k-j}.
    hs = [{ZERO: Q(1)}]
    for k in range(1, DEGREE + 1):
        numer = {}
        for j in range(1, k + 1):
            for e, c in hs[k - j].items():
                for v in list(range(9)) + [duplicate]:
                    n = shifted(e, v, j)
                    numer[n] = numer.get(n, Q()) + c
        hs.append({e: c / k for e, c in numer.items()})
        require(all(c.denominator == 1 for c in hs[k].values()),
                f"duplicate={duplicate} k={k}: Newton divisibility")
    return hs


def author(duplicate):
    # Nine geometric-series factors, convolved with one extra copy of y_i.
    hs = [{ZERO: Q(1)}] + [{} for _ in range(DEGREE)]
    for v in list(range(9)) + [duplicate]:
        for k in range(1, DEGREE + 1):
            for e, c in list(hs[k - 1].items()):
                n = shifted(e, v, 1)
                hs[k][n] = hs[k].get(n, Q()) + c
    return hs


def integrated_coefficient(e, duplicate):
    # Source's Nat.multinomial times baryCoefficient(bumped e i):
    # k! / prod(e!) * prod((e + delta_i)!) / (k + 9)!.
    k = sum(e)
    numerator = factorial(k) * prod(factorial(x + (j == duplicate))
                                    for j, x in enumerate(e))
    denominator = prod(factorial(x) for x in e) * factorial(k + 9)
    return Q(numerator, denominator)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source", type=Path, required=True)
    a = p.parse_args()
    require(hashlib.sha256(a.source.read_bytes()).hexdigest() == SOURCE_SHA, "source SHA-256")
    total = 0
    for i in range(9):
        recurrence, geometric = newton(i), author(i)
        count = 0
        for k in range(DEGREE + 1):
            exponents = list(compositions(k, 9))
            require(len(exponents) == comb(k + 8, 8), f"i={i} k={k}: enumeration")
            require(set(recurrence[k]) == set(geometric[k]) == set(exponents),
                    f"i={i} k={k}: support")
            norm = factorial(9) * comb(9 + k, k)
            for e in exponents:
                require(recurrence[k][e] == geometric[k][e], f"i={i} k={k} {e}: Newton/author")
                require(integrated_coefficient(e, i) == recurrence[k][e] / norm,
                        f"i={i} k={k} {e}: integral coefficient")
                count += 1
        total += count
        print(f"PASS node={i} degrees=0..6 monomials={count} recurrence_and_integral={2 * count}")
    require(total == 9 * comb(15, 9), "total monomials")
    print(f"PASS total node_degree_cases=63 monomials={total} coefficient_equalities={2 * total}")
    print("SCOPE: universal exact polynomial coefficients only; no Lean, integration or kernel replay")


if __name__ == "__main__":
    main()
