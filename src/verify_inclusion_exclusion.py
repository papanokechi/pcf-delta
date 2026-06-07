"""
verify_inclusion_exclusion.py — VERIFY the *step-by-step* inclusion-exclusion
derivation of the cluster closed forms sigma_2, sigma_3 (the appendix derivation),
not merely the final formulas (which verify_clusters.py already checks).

Path-graph independent sets on {m,m+1,...}; weight u_n = 1/(b_{n-1} b_n).
sigma_k = sum over k-subsets with NO two adjacent of prod u.

Elementary symmetric polynomials via Newton's identities:
    e_2 = (p1^2 - p2)/2
    e_3 = (p1^3 - 3 p1 p2 + 2 p3)/6              (p_j = sum u_n^j)
Adjacency sums:
    a1 = sum u_n u_{n+1}
    c  = sum u_n u_{n+1}(u_n + u_{n+1})
    t  = sum u_n u_{n+1} u_{n+2}

Claims checked link-by-link against brute force over a finite window:
  (1) e2 formula == sum over ALL 2-subsets
  (2) e3 formula == sum over ALL 3-subsets
  (3) a1 == sum over ADJACENT 2-subsets
  (4) sigma2 == e2 - a1
  (5) a1*p1 == c + W,   W = sum over (adjacent pair, third DISTINCT vertex)
  (6) W == B1 + 2t,     B1 = 3-subsets with exactly one adjacent pair, runs=t
  (7) B  == B1 + t,     B  = 3-subsets with at least one adjacent pair
  (8) B  == a1*p1 - c - t
  (9) sigma3 == e3 - B  == e3 - a1*p1 + c + t
"""
import mpmath as mp
from itertools import combinations

mp.mp.dps = 50
TOL = mp.mpf(10) ** -40


def make_u(A, B, C):
    Af, Bf, Cf = mp.mpf(A), mp.mpf(B), mp.mpf(C)
    b = lambda k: Af * k * k + Bf * k + Cf
    return lambda n: 1 / (b(n - 1) * b(n))


def prod(u, comb):
    p = mp.mpf(1)
    for n in comb:
        p *= u(n)
    return p


def check(A, B, C, m=2, N=14):
    u = make_u(A, B, C)
    idx = list(range(m, m + N))
    hi = m + N - 1

    # ---- power sums and formula pieces (window-consistent boundaries) ----
    p1 = sum(u(n) for n in idx)
    p2 = sum(u(n) ** 2 for n in idx)
    p3 = sum(u(n) ** 3 for n in idx)
    a1 = sum(u(n) * u(n + 1) for n in range(m, hi))
    c = sum(u(n) * u(n + 1) * (u(n) + u(n + 1)) for n in range(m, hi))
    t = sum(u(n) * u(n + 1) * u(n + 2) for n in range(m, hi - 1))
    e2 = (p1 * p1 - p2) / 2
    e3 = (p1 ** 3 - 3 * p1 * p2 + 2 * p3) / 6

    # ---- brute-force pieces over the window ----
    all2 = [s for s in combinations(idx, 2)]
    all3 = [s for s in combinations(idx, 3)]
    adj2 = [s for s in all2 if s[1] - s[0] == 1]
    non2 = [s for s in all2 if s[1] - s[0] >= 2]
    non3 = [s for s in all3 if all(s[i + 1] - s[i] >= 2 for i in range(2))]

    def n_adj(s):  # number of adjacent pairs inside a sorted triple
        return sum(1 for i in range(len(s) - 1) if s[i + 1] - s[i] == 1)

    bad3 = [s for s in all3 if n_adj(s) >= 1]
    one3 = [s for s in all3 if n_adj(s) == 1]
    run3 = [s for s in all3 if n_adj(s) == 2]  # i,i+1,i+2

    e2_b = sum(prod(u, s) for s in all2)
    e3_b = sum(prod(u, s) for s in all3)
    a1_b = sum(prod(u, s) for s in adj2)
    s2_b = sum(prod(u, s) for s in non2)
    s3_b = sum(prod(u, s) for s in non3)
    B_b = sum(prod(u, s) for s in bad3)
    B1_b = sum(prod(u, s) for s in one3)
    run_b = sum(prod(u, s) for s in run3)

    # W = sum over (adjacent pair (n,n+1) in window, third vertex r in window, r!=n,n+1)
    W_b = mp.mpf(0)
    for n in range(m, hi):
        for r in idx:
            if r != n and r != n + 1:
                W_b += u(n) * u(n + 1) * u(r)

    checks = {
        "(1) e2 == all-2-subsets": abs(e2 - e2_b),
        "(2) e3 == all-3-subsets": abs(e3 - e3_b),
        "(3) a1 == adjacent pairs": abs(a1 - a1_b),
        "(4) sigma2 == e2 - a1": abs(s2_b - (e2 - a1)),
        "(5) a1*p1 == c + W": abs(a1 * p1 - (c + W_b)),
        "(6) W == B1 + 2t": abs(W_b - (B1_b + 2 * run_b)),
        "(7) B == B1 + t": abs(B_b - (B1_b + run_b)),
        "(8) B == a1*p1 - c - t": abs(B_b - (a1 * p1 - c - t)),
        "(9) sigma3 == e3 - a1*p1 + c + t": abs(s3_b - (e3 - a1 * p1 + c + t)),
    }
    return checks, run_b, t


if __name__ == "__main__":
    cases = [(1, 0, 1), (1, 1, 1), (2, 1, 3), (1, 2, 1)]
    allok = True
    for (A, B, C) in cases:
        checks, run_b, t = check(A, B, C)
        # also confirm t (formula) == runs (brute) as a sanity tie-in
        checks["    t == runs-of-3 (brute)"] = abs(t - run_b)
        print(f"(A,B,C)={(A,B,C)}")
        for name, d in checks.items():
            ok = d < TOL
            allok = allok and ok
            print(f"   {name:36s} |diff|={mp.nstr(d,3):>10s}  {'OK' if ok else 'FAIL'}")
        print()
    print("ALL INCLUSION-EXCLUSION STEPS VERIFIED" if allok else "*** MISMATCH ***")
