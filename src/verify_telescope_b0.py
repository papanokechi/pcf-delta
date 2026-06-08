"""
verify_telescope_b0.py — exact-rational gate for the B=0 weighted telescoping
identity formalized in Lean as PcfContinuant.Topic5.weighted_telescope_value.

Checked identity (b_m = A m^2 + C, weight A(2m+1) = b_{m+1} - b_m):

    sum_{m=1}^{N-1} A*(2m+1) / (b_m * b_{m+1}) = 1/(A+C) - 1/(A N^2 + C).

Arithmetic is exact (Fraction); residual 0 means the closed value matches the
brute-force partial sum termwise. This is the numeric companion to the Lean proof
(which is unconditional over any field); the unweighted-tail "no rational
telescoper" (Gosper) and the coth/digamma limit are out of scope here and were
checked separately in sympy/mpmath during development.
"""

from fractions import Fraction

# (A, C) with A != 0 and b_m = A m^2 + C nonzero on the windows used.
CASES = [(1, 1), (1, 4), (2, 3), (1, 2), (3, 1), (5, 7)]
WINDOWS = [1, 2, 3, 6, 9, 15]


def b(A, C, m):
    return Fraction(A) * m * m + C


def brute(A, C, N):
    total = Fraction(0)
    for m in range(1, N):  # Ico 1 N  ==  m = 1 .. N-1
        total += Fraction(A * (2 * m + 1)) / (b(A, C, m) * b(A, C, m + 1))
    return total


def closed(A, C, N):
    return 1 / (Fraction(A) + C) - 1 / (Fraction(A) * N * N + C)


def main():
    print("A,C,N,brute,closed,residual")
    all_ok = True
    for (A, C) in CASES:
        for N in WINDOWS:
            lhs = brute(A, C, N)
            rhs = closed(A, C, N)
            res = lhs - rhs
            all_ok = all_ok and res == 0
            print(f"{A},{C},{N},{lhs},{rhs},{res}")
    if not all_ok:
        raise SystemExit("*** TELESCOPE B=0 IDENTITY MISMATCH ***")
    print("ALL B=0 WEIGHTED-TELESCOPE CHECKS EXACTLY ZERO")


if __name__ == "__main__":
    main()
