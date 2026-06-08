"""
verify_sigma3_finite_window.py — exact finite-window check for the sigma_3
inclusion-exclusion identity over {2..N}.

The checked identity is
    sigma3 = e3 - a1*p1 + c + t
where
    p1 = sum_i u_i,
    e3 = sum_{i<j<k} u_i*u_j*u_k,
    a1 = sum_i u_i*u_{i+1},
    c  = sum_i u_i*u_{i+1}*(u_i + u_{i+1}),
    t  = sum_i u_i*u_{i+1}*u_{i+2},
with every sum restricted to the finite window {2..N}.  Arithmetic is exact
(Fraction), so residual 0 means the finite-window formula matches brute force.
"""

from fractions import Fraction
from itertools import combinations

CASES = [(1, 0, 1), (1, 1, 1), (2, 1, 3), (1, 2, 1)]
WINDOWS = [5, 6, 7, 8]


def make_u(A, B, C):
    def b(k):
        return A * k * k + B * k + C

    def u(n):
        return Fraction(1, b(n - 1) * b(n))

    return u


def prod(values):
    out = Fraction(1)
    for value in values:
        out *= value
    return out


def sigma3_brute(u, N):
    idx = range(2, N + 1)
    total = Fraction(0)
    for triple in combinations(idx, 3):
        if triple[1] - triple[0] >= 2 and triple[2] - triple[1] >= 2:
            total += prod(u(i) for i in triple)
    return total


def pieces(u, N):
    idx = range(2, N + 1)
    p1 = sum((u(i) for i in idx), Fraction(0))
    e3 = sum((prod(u(i) for i in triple) for triple in combinations(idx, 3)), Fraction(0))
    a1 = sum((u(i) * u(i + 1) for i in range(2, N)), Fraction(0))
    c = sum((u(i) * u(i + 1) * (u(i) + u(i + 1)) for i in range(2, N)), Fraction(0))
    t = sum((u(i) * u(i + 1) * u(i + 2) for i in range(2, N - 1)), Fraction(0))
    return p1, e3, a1, c, t


def sigma3_formula(u, N):
    p1, e3, a1, c, t = pieces(u, N)
    return e3 - a1 * p1 + c + t


def short(fr):
    if fr == 0:
        return "0"
    return f"{fr.numerator}/{fr.denominator}"


def main():
    print("triple,N,sigma3_brute,sigma3_formula,residual")
    all_ok = True
    for case in CASES:
        u = make_u(*case)
        for N in WINDOWS:
            brute = sigma3_brute(u, N)
            formula = sigma3_formula(u, N)
            residual = brute - formula
            all_ok = all_ok and residual == 0
            print(f"{case},{N},{short(brute)},{short(formula)},{short(residual)}")
    if not all_ok:
        raise SystemExit("*** SIGMA3 FINITE-WINDOW FORMULA MISMATCH ***")
    print("ALL SIGMA3 FINITE-WINDOW CHECKS EXACTLY ZERO")


if __name__ == "__main__":
    main()
