"""
Structural characterization of R_inf as an INFINITE EULER CONTINUANT.

The scaled denominators obey  R_n = R_{n-1} + u_n R_{n-2},  R_0=R_1=1,
with  u_n = 1/(b_{n-1} b_n) > 0.  This is the transfer recurrence of the Euler
continuant: R_n = K(u_2,...,u_n) = sum over subsets T of {2,...,n} containing
NO TWO CONSECUTIVE indices of  prod_{i in T} u_i.  Hence

    R_inf = 1 + sum_{k>=1} sigma_k,
    sigma_k = sum_{2<=i_1, i_{j+1}>=i_j+2} u_{i_1} u_{i_2} ... u_{i_k}   (gaps >= 2),

a convergent series of nested sums.  sigma_0=1, sigma_1=S=sum u_n.  Because
0 <= sigma_k <= S^k, this immediately gives the closed-form bracket
    1 + S <= R_inf <= 1/(1-S).
delta = log R_inf.  This script VERIFIES the continuant identity numerically:
  (1) R_n via recurrence == K(u_2,...,u_n) via the non-consecutive-subset sum;
  (2) partial sums sigma_0+...+sigma_k -> R_inf.
"""
import mpmath as mp
from functools import lru_cache

mp.mp.dps = 50


def b_of(A, B, C):
    Af, Bf, Cf = mp.mpf(A), mp.mpf(B), mp.mpf(C)
    return lambda k: Af * k * k + Bf * k + Cf


def u_of(A, B, C):
    b = b_of(A, B, C)
    return lambda n: 1 / (b(mp.mpf(n - 1)) * b(mp.mpf(n)))


def R_rec(A, B, C, N):
    u = u_of(A, B, C)
    Rm2, Rm1 = mp.mpf(1), mp.mpf(1)
    for n in range(2, N + 1):
        Rn = Rm1 + u(n) * Rm2
        Rm2, Rm1 = Rm1, Rn
    return Rm1


def continuant_subset(A, B, C, N):
    """K(u_2,...,u_N) as the non-consecutive-subset sum (DP, equals R_N)."""
    u = u_of(A, B, C)
    # DP: f[i] = continuant of u_2..u_i ; standard f[i]=f[i-1]+u_i f[i-2]
    # but here we recompute as explicit subset DP to be an INDEPENDENT check:
    #   g_in[i]  = sum of weights of subsets of {2..i} that INCLUDE i (no two consec)
    #   g_out[i] = sum of weights of subsets of {2..i} that EXCLUDE i
    g_in, g_out = mp.mpf(0), mp.mpf(1)   # i = 1 (no index 1): include none
    for i in range(2, N + 1):
        ui = u(i)
        new_in = ui * (g_out)            # i included -> i-1 must be excluded
        new_out = g_in + g_out           # i excluded -> anything before
        g_in, g_out = new_in, new_out
    return g_in + g_out


def sigma_k(A, B, C, k, N):
    """sigma_k via DP over k layers (sum over increasing gap>=2 k-tuples in 2..N)."""
    u = u_of(A, B, C)
    if k == 0:
        return mp.mpf(1)
    # prev[i] = sum of (k-1)-tuples ending at index i ; build up
    # layer 1:
    cur = {i: u(i) for i in range(2, N + 1)}
    for _ in range(2, k + 1):
        # prefix sums of cur for indices <= i-2
        nxt = {}
        pref = mp.mpf(0)
        # iterate i ascending; pref accumulates cur[j] for j <= i-2
        vals = sorted(cur)
        idx = 0
        for i in range(2, N + 1):
            while idx < len(vals) and vals[idx] <= i - 2:
                pref += cur[vals[idx]]
                idx += 1
            nxt[i] = u(i) * pref
        cur = nxt
    return sum(cur.values())


if __name__ == "__main__":
    print("=== (1) continuant identity:  R_n (recurrence) == K(u_2..u_n) (subset DP) ===")
    for (A, B, C) in [(1, 0, 1), (1, 1, 1), (3, 2, 5)]:
        ok = True
        for N in [2, 3, 5, 8, 12, 20]:
            a = R_rec(A, B, C, N)
            b = continuant_subset(A, B, C, N)
            ok = ok and abs(a - b) < mp.mpf(10) ** -40
        print(f"  (A,B,C)={(A,B,C)}: R_n == continuant for N in [2..20]: {ok}")

    print("\n=== (2) sigma_k partial sums -> R_inf ===")
    Ntrunc = 4000
    for (A, B, C) in [(1, 0, 1), (1, 0, 2), (1, 1, 1)]:
        Rinf = R_rec(A, B, C, 60000)   # high-N recurrence reference
        partial = mp.mpf(0)
        print(f"  (A,B,C)={(A,B,C)}  R_inf~{mp.nstr(Rinf,18)}")
        for k in range(0, 6):
            sk = sigma_k(A, B, C, k, Ntrunc)
            partial += sk
            print(f"     sigma_{k} = {mp.nstr(sk,14):>18}   sum_0^{k} = {mp.nstr(partial,16):>18}"
                  f"   R_inf-sum = 10^{float(mp.log10(abs(Rinf-partial)+mp.mpf(10)**-90)):.1f}")

    print("\n=== (3) bracket from continuant: 1+S <= R_inf <= 1/(1-S), S=sigma_1 ===")
    for (A, B, C) in [(1, 0, 1), (2, 0, 1), (1, 2, 1), (3, 2, 5)]:
        S = sigma_k(A, B, C, 1, 200000)
        Rinf = R_rec(A, B, C, 60000)
        lo, hi = 1 + S, 1 / (1 - S)
        print(f"  {(A,B,C)}: 1+S={mp.nstr(lo,14)}  R_inf={mp.nstr(Rinf,14)}  1/(1-S)={mp.nstr(hi,14)}"
              f"  bracket_width={mp.nstr(hi-lo,3)}")
