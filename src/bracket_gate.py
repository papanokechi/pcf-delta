"""
bracket_gate.py — numerics-first EXACT gate for the PROVEN-bracket (pcf-delta v1.1).

Before formalizing in Lean, machine-check the two load-bearing algebra facts that the
finitary induction proofs will rest on, plus the end-to-end numeric bracket.

Target finitary statements (u_k >= 0, with S_n = sum_{k=2}^n u_k < 1):
  LOWER  rseq u n >= rmin u n,  rmin: 1,1, rmin(n+2)=rmin(n+1)+u(n+2)  =>  rmin u n = 1 + S_n
  UPPER  rmaj u n <= 1/(1 - S_n),  rmaj: 1,1, rmaj(n+2)=rmaj(n+1)*(1+u(n+2))

The two induction-step identities to confirm EXACTLY (sympy, symbolic):
  (U) (1 - S) - (1 + u)*(1 - S - u) == u*S + u**2        [>= 0, so the upper step holds]
  (L) [1 + (S + u)] - [(1 + S) + u] == 0                 [sum-majorant recurrence is exact]

Then a numeric end-to-end check on real triples: 1 + S_n <= rseq_n <= rmaj_n <= 1/(1-S_n),
and rseq_n increasing to R_inf inside [1+S, 1/(1-S)].
"""
import sympy as sp
import mpmath as mp

# ---- EXACT symbolic step identities (the algebra the Lean induction will use) ----
u, S = sp.symbols('u S', nonnegative=True)

upper_gap = sp.expand((1 - S) - (1 + u) * (1 - S - u))      # should be u*S + u**2
lower_gap = sp.expand((1 + (S + u)) - ((1 + S) + u))         # should be 0

print("=== EXACT symbolic gate ===")
print(f"(U) (1-S) - (1+u)(1-S-u) = {upper_gap}   [need = u*S + u**2, and >=0 for u,S>=0]")
assert sp.simplify(upper_gap - (u * S + u**2)) == 0, "UPPER step identity FAILED"
# u*S + u**2 >= 0 for u,S >= 0 is immediate; assert sympy agrees it's nonneg-shaped
assert upper_gap == u * S + u**2
print(f"(L) sum-majorant recurrence residual = {lower_gap}   [need = 0]")
assert lower_gap == 0, "LOWER recurrence identity FAILED"
print("  -> both step identities EXACT.  Upper gap = u*S + u**2 >= 0.  Lower recurrence exact.\n")

# ---- Numeric end-to-end bracket on real triples ----
mp.mp.dps = 50


def make_u(A, B, C):
    Af, Bf, Cf = mp.mpf(A), mp.mpf(B), mp.mpf(C)
    b = lambda k: Af * k * k + Bf * k + Cf
    return lambda n: 1 / (b(n - 1) * b(n))


def rseq_seq(u_fn, nmax):
    r = [mp.mpf(1), mp.mpf(1)]
    for n in range(2, nmax + 1):
        r.append(r[n - 1] + u_fn(n) * r[n - 2])
    return r


def rmaj_seq(u_fn, nmax):
    r = [mp.mpf(1), mp.mpf(1)]
    for n in range(2, nmax + 1):
        r.append(r[n - 1] * (1 + u_fn(n)))
    return r


cases = [(1, 0, 1), (1, 1, 1), (2, 1, 3), (1, 2, 1), (3, 2, 5)]
nmax = 4000
print(f"=== numeric bracket (nmax={nmax}, dps={mp.mp.dps}) ===")
allok = True
for (A, B, C) in cases:
    u_fn = make_u(A, B, C)
    rs = rseq_seq(u_fn, nmax)
    rm = rmaj_seq(u_fn, nmax)
    Sn = sum(u_fn(k) for k in range(2, nmax + 1))
    assert Sn < 1, f"S_n >= 1 for {(A,B,C)} -- upper bound n/a"
    lo = 1 + Sn
    hi = 1 / (1 - Sn)
    Rinf = rs[-1]              # rseq has converged to many digits at nmax
    # monotone increasing
    mono = all(rs[i] <= rs[i + 1] + mp.mpf(10) ** -45 for i in range(len(rs) - 1))
    # finite-n bracket at the largest n
    chain = (lo <= Rinf + mp.mpf(10) ** -45 <= rm[-1] + mp.mpf(10) ** -45) and (rm[-1] <= hi + mp.mpf(10) ** -45)
    ok = mono and chain and (lo <= Rinf <= hi)
    allok = allok and ok
    print(f"(A,B,C)={(A,B,C)}: 1+S={mp.nstr(lo,14)}  R_inf~={mp.nstr(Rinf,14)}  "
          f"prod={mp.nstr(rm[-1],14)}  1/(1-S)={mp.nstr(hi,14)}  {'OK' if ok else 'FAIL'}")

print("\nBRACKET GATE PASSED" if allok else "\n*** BRACKET GATE FAILED ***")
