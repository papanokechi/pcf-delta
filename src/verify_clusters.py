"""
verify_clusters.py — VERIFY the exact cluster-sum closed forms sigma_2, sigma_3 for
the Euler-continuant tail  T(m) = sum_k sigma_k(m),  sigma_k = sum over k-subsets of
{m,m+1,...} with NO two adjacent of  prod u  ,  u_n = 1/(b_{n-1} b_n).

We check the analytic formulas
  sigma_2 = (p1^2 - p2)/2 - a1
  sigma_3 = (p1^3 - 3 p1 p2 + 2 p3)/6 - a1*p1 + c + t
with power sums  p_j = sum u_n^j , adjacency sums a1 = sum u_n u_{n+1},
c = sum u_n u_{n+1}(u_n+u_{n+1}),  t = sum u_n u_{n+1} u_{n+2}
against a BRUTE-FORCE enumeration over a finite window (truncation negligible because
u_n decays like n^-4 so the dropped tail is far below the comparison tolerance).

Discipline: never trust a derived combinatorial identity from memory — machine-check it.
"""
import mpmath as mp
from itertools import combinations

mp.mp.dps = 50


def make_u(A, B, C):
    Af, Bf, Cf = mp.mpf(A), mp.mpf(B), mp.mpf(C)
    b = lambda k: Af * k * k + Bf * k + Cf
    return lambda n: 1 / (b(n - 1) * b(n))


def brute(u, m, N, k):
    """sum over k-subsets of {m..m+N-1} with no two adjacent of prod u."""
    idx = list(range(m, m + N))
    tot = mp.mpf(0)
    for comb in combinations(idx, k):
        if all(comb[i + 1] - comb[i] >= 2 for i in range(len(comb) - 1)):
            p = mp.mpf(1)
            for n in comb:
                p *= u(n)
            tot += p
    return tot


def formulas(u, m, N):
    rng = range(m, m + N)
    hi = m + N - 1  # last index inside the window
    p1 = sum(u(n) for n in rng)
    p2 = sum(u(n) ** 2 for n in rng)
    p3 = sum(u(n) ** 3 for n in rng)
    # adjacency sums must stay strictly inside the window to match brute force
    a1 = sum(u(n) * u(n + 1) for n in range(m, hi))            # n+1 <= hi
    c = sum(u(n) * u(n + 1) * (u(n) + u(n + 1)) for n in range(m, hi))
    t = sum(u(n) * u(n + 1) * u(n + 2) for n in range(m, hi - 1))  # n+2 <= hi
    s2 = (p1 * p1 - p2) / 2 - a1
    s3 = (p1 ** 3 - 3 * p1 * p2 + 2 * p3) / 6 - a1 * p1 + c + t
    return s2, s3


if __name__ == "__main__":
    cases = [(1, 0, 1), (1, 1, 1), (2, 1, 3), (1, 2, 1)]
    m, N = 2, 14  # small window; brute force C(14,2/3) is tiny
    print(f"window {{m..m+N-1}} = {{{m}..{m+N-1}}}, comparing formula vs brute force\n")
    allok = True
    for (A, B, C) in cases:
        u = make_u(A, B, C)
        s2f, s3f = formulas(u, m, N)
        s2b = brute(u, m, N, 2)
        s3b = brute(u, m, N, 3)
        d2 = abs(s2f - s2b)
        d3 = abs(s3f - s3b)
        ok = d2 < mp.mpf(10) ** -40 and d3 < mp.mpf(10) ** -40
        allok = allok and ok
        print(f"(A,B,C)={(A,B,C)}")
        print(f"   sigma2: formula={mp.nstr(s2f,20)}  |diff|={mp.nstr(d2,3)}")
        print(f"   sigma3: formula={mp.nstr(s3f,20)}  |diff|={mp.nstr(d3,3)}  {'OK' if ok else 'FAIL'}")
    print("\nALL CLUSTER FORMULAS VERIFIED" if allok else "\n*** FORMULA MISMATCH ***")
