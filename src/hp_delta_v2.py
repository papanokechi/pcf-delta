"""
hp_delta_v2.py  (roadmap M2) — high-precision delta = log R_inf via an EXACT
cluster (Mayer / independence-polynomial) seed, plus an honest determination of the
reliable digit count.

Object:
  R_inf = T(2),  T(m) = T(m+1) + u_m T(m+2),  T(inf)=1,  u_n = 1/(b_{n-1} b_n),
  b(n) = A n^2 + B n + C.  delta = log R_inf.

T(m) is the infinite Euler continuant of the tail; its cluster expansion is
  T(m) = sum_{k>=0} sigma_k(m),   sigma_k = sum over k-subsets of {m,m+1,...} with
  NO two adjacent of prod u.  The downward recurrence is EXACT, so all error lives in
  the seed T(M+1), T(M+2).  Truncating the cluster series at order p gives seed error
  ~ sigma_{p+1} ~ O(M^{-3(p+1)}), i.e. ~3(p+1) reliable digits per decade of M:

    seed   leading neglected   digits / decade of M
    sigma1        sigma2              ~6      (old hp_delta.py exp-seed effectively ~7)
    sigma2        sigma3              ~9
    sigma3        sigma4              ~12   <-- used here

Closed forms used (sigma1 exact via digamma; sigma2, sigma3 VERIFIED in
verify_clusters.py against brute force to ~1e-54):
  p1 = sum_{n>=m} u_n            = -sum_rho Res_rho psi(m-rho)         [exact, digamma]
  p_j = sum_{n>=m} u_n^j ,  a1 = sum u_n u_{n+1},
  c = sum u_n u_{n+1}(u_n+u_{n+1}),  t = sum u_n u_{n+1} u_{n+2}        [fast tails, nsum]
  sigma2 = (p1^2 - p2)/2 - a1
  sigma3 = (p1^3 - 3 p1 p2 + 2 p3)/6 - a1 p1 + c + t

Reliable digits are CERTIFIED two independent ways: (i) self-convergence as M grows;
(ii) seed-order independence (sigma3 seed vs sigma2 seed and vs sigma3+sigma4_lead).
The deposited paper's "80-digit PSLQ null" is addressed honestly: with exact sigma3 and
M=1e7 we reach ~80 digits (see __main__); nothing is asserted beyond the certified count.
"""
import mpmath as mp


def roots(A, B, C):
    Af, Bf, Cf = mp.mpf(A), mp.mpf(B), mp.mpf(C)
    s = mp.sqrt(Bf * Bf - 4 * Af * Cf)
    return (-Bf + s) / (2 * Af), (-Bf - s) / (2 * Af)


def residues(A, B, C):
    r1, r2 = roots(A, B, C)
    Af = mp.mpf(A)
    poles = [r1, r2, 1 + r1, 1 + r2]
    res = []
    for i, rho in enumerate(poles):
        d = Af * Af
        for j, sig in enumerate(poles):
            if j != i:
                d *= (rho - sig)
        res.append((rho, 1 / d))
    return res


def _poles_distinct(A, B, C, tol=None):
    """True iff the four poles {r1, r2, 1+r1, 1+r2} are pairwise distinct, so the
    simple-pole digamma residue form for p1 is valid. Perfect-square b (e.g. (1,2,1):
    b=(n+1)^2) gives a repeated root -> coincident poles -> residue form divides by 0."""
    if tol is None:
        tol = mp.mpf(10) ** (-mp.mp.dps // 2)
    r1, r2 = roots(A, B, C)
    poles = [r1, r2, 1 + r1, 1 + r2]
    for i in range(len(poles)):
        for j in range(i + 1, len(poles)):
            if abs(poles[i] - poles[j]) < tol:
                return False
    return True


def _cluster_poles(poles, tol=mp.mpf(10) ** -25):
    reps = []
    for p in poles:
        placed = False
        for i, (q, mlt) in enumerate(reps):
            if abs(p - q) < tol:
                reps[i] = ((q * mlt + p) / (mlt + 1), mlt + 1)
                placed = True
                break
        if not placed:
            reps.append((p, 1))
    return reps


def _p1_confluent(A, B, C):
    """Return an EXACT p1(m) = sum_{n>=m} u_n closure valid for repeated poles, via the
    confluent digamma/polygamma partial-fraction form (generalizes S_confluent.py from a
    fixed start n=2 to an arbitrary start m, by using psi^{(k)}(m-rho)). Full-precision at
    any m, unlike nsum which degrades for tails starting at large m."""
    r1, r2 = roots(A, B, C)
    Af = mp.mpf(A)
    reps = _cluster_poles([r1, r2, 1 + r1, 1 + r2])

    def p1(m):
        total = mp.mpc(0)
        for i, (rho, mult) in enumerate(reps):
            def phi(n, i=i):
                val = Af * Af
                for k, (rk, mk) in enumerate(reps):
                    if k == i:
                        continue
                    val *= (n - rk) ** mk
                return 1 / val
            for t in range(mult):
                j = mult - t
                a = (mp.diff(phi, rho, t) if t > 0 else phi(rho)) / mp.factorial(t)
                if j == 1:
                    total += -a * mp.digamma(m - rho)
                else:
                    total += a * ((-1) ** j) * mp.polygamma(j - 1, m - rho) / mp.factorial(j - 1)
        return mp.re(total)
    return p1


def make_ctx(A, B, C):
    Af, Bf, Cf = mp.mpf(A), mp.mpf(B), mp.mpf(C)
    b = lambda k: Af * k * k + Bf * k + Cf
    u = lambda n: 1 / (b(n - 1) * b(n))
    if _poles_distinct(A, B, C):
        RES = residues(A, B, C)
        p1 = lambda m: -mp.fsum(r * mp.digamma(m - rho) for (rho, r) in RES)
    else:
        # repeated-pole (degenerate) case: simple-pole digamma residue form is singular.
        # Use the EXACT confluent (polygamma) closed form -- full precision at any m.
        p1 = _p1_confluent(A, B, C)
    return b, u, p1


def seed_value(u, p1, m, order):
    """1 + sigma1 + ... + sigma_order  for the tail starting at index m."""
    s1 = p1(m)
    val = 1 + s1
    if order >= 2 or order >= 3:
        p2 = mp.nsum(lambda n: u(n) ** 2, [m, mp.inf])
        a1 = mp.nsum(lambda n: u(n) * u(n + 1), [m, mp.inf])
        sigma2 = (s1 * s1 - p2) / 2 - a1
        val += sigma2
    if order >= 3:
        p3 = mp.nsum(lambda n: u(n) ** 3, [m, mp.inf])
        c = mp.nsum(lambda n: u(n) * u(n + 1) * (u(n) + u(n + 1)), [m, mp.inf])
        t = mp.nsum(lambda n: u(n) * u(n + 1) * u(n + 2), [m, mp.inf])
        sigma3 = (s1 ** 3 - 3 * s1 * p2 + 2 * p3) / 6 - a1 * s1 + c + t
        val += sigma3
    if order >= 4:  # leading sigma4 only (for a certification cross-check)
        val += s1 ** 4 / 24
    return val


def R_inf(A, B, C, M, order=3):
    """downward exact recurrence from seed at M; returns T(2) = R_inf."""
    b, u, p1 = make_ctx(A, B, C)
    Tp2 = seed_value(u, p1, M + 2, order)
    Tp1 = seed_value(u, p1, M + 1, order)
    Tm = Tp1
    for m in range(M, 1, -1):
        Tm = Tp1 + u(m) * Tp2
        Tp2, Tp1 = Tp1, Tm
    return Tm


def agree_digits(x, y):
    d = abs(x - y)
    if d == 0:
        return mp.inf
    return -mp.log10(d / max(abs(x), mp.mpf(1)))


def forward_neville(A, B, C, Ns):
    """independent algorithm: forward continuant R_N = K(u_2..u_N) + Neville in 1/N."""
    b, u, _ = make_ctx(A, B, C)

    def R_N(N):
        Rm2, Rm1 = mp.mpf(1), mp.mpf(1)  # R_0 = R_1 = 1
        Rn = Rm1
        for n in range(2, N + 1):  # start at n=2 so the u(2) term is included (matches T(2)=R_inf)
            Rn = Rm1 + u(n) * Rm2
            Rm2, Rm1 = Rm1, Rn
        return Rn

    xs = [mp.mpf(1) / N for N in Ns]
    ys = [R_N(N) for N in Ns]
    n = len(xs)
    P = ys[:]
    for k in range(1, n):
        for i in range(n - k):
            P[i] = ((0 - xs[i + k]) * P[i] - (0 - xs[i]) * P[i + 1]) / (xs[i] - xs[i + k])
    return P[0]


if __name__ == "__main__":
    import sys

    mp.mp.dps = 170
    print("=" * 80)
    print("M2: high-precision delta via exact sigma3 cluster seed (12 digits/decade)")
    print(f"working precision dps = {mp.mp.dps}")
    print("=" * 80)

    # ---- (1,0,1): the case carrying the deposited 80-digit PSLQ null ----
    A, B, C = 1, 0, 1
    print(f"\n[(A,B,C)={(A,B,C)}]  pushing precision + certifying")
    import time
    t0 = time.time()
    v6_s3 = R_inf(A, B, C, 10**6, order=3)
    v6_s2 = R_inf(A, B, C, 10**6, order=2)
    v6_s4 = R_inf(A, B, C, 10**6, order=4)
    print(f"  seed-order indep @M=1e6:  s2 vs s3 = {mp.nstr(agree_digits(v6_s2,v6_s3),5)} dig"
          f" ;  s3 vs s3+s4lead = {mp.nstr(agree_digits(v6_s3,v6_s4),5)} dig")
    v5_s3 = R_inf(A, B, C, 10**5, order=3)
    print(f"  self-convergence (s3):    M=1e5 vs 1e6 = {mp.nstr(agree_digits(v5_s3,v6_s3),5)} dig")
    # forward-Neville independent cross-check (limited, ~25-30 dig) on the same value
    fn = forward_neville(A, B, C, [2000, 4000, 8000, 16000, 32000, 64000])
    print(f"  indep. forward-Neville vs s3@1e6 = {mp.nstr(agree_digits(fn,v6_s3),5)} dig"
          f"  (Neville is the weak method; only certifies its own ~25-30)")
    print(f"  [elapsed {round(time.time()-t0,1)} s]")

    # the big reference at M=1e7 (~80 digits); guarded behind a flag for cost
    do_1e7 = ("--full" in sys.argv)
    if do_1e7:
        t1 = time.time()
        v7_s3 = R_inf(A, B, C, 10**7, order=3)
        ad = agree_digits(v6_s3, v7_s3)
        print(f"  M=1e6 vs 1e7 (s3) = {mp.nstr(ad,5)} dig  [elapsed {round(time.time()-t1,1)} s]")
        best = v7_s3
        reliable = int(float(agree_digits(v6_s3, v7_s3)) - 2)
    else:
        best = v6_s3
        reliable = int(float(agree_digits(v5_s3, v6_s3)) - 2)
    delta101 = mp.log(best)
    print(f"\n  RELIABLE digits of delta(1,0,1): >= {reliable}")
    mp.mp.dps = reliable + 10
    print(f"  delta(1,0,1) = {mp.nstr(delta101, reliable)}")
    mp.mp.dps = 170

    # ---- delta(A,B,C) map (moderate precision, M=2e5 s3 ~ 55 dig) ----
    print("\n" + "=" * 80)
    print("delta(A,B,C) map  [M=2e5, exact sigma3; each self-checked vs M=5e4]")
    print("=" * 80)
    grid = [(1, 0, 1), (1, 0, 2), (1, 0, 3), (2, 0, 1), (3, 0, 1),
            (1, 1, 1), (1, 2, 1), (2, 1, 3), (3, 2, 5)]
    print(f"{'(A,B,C)':>10} {'rel.dig':>7} {'S=sum u(n>=2)':>20} {'R_inf':>22} {'delta':>22}")
    rows = []
    for (A, B, C) in grid:
        _, _, p1 = make_ctx(A, B, C)
        S = p1(2)
        vbig = R_inf(A, B, C, 200000, order=3)
        vsm = R_inf(A, B, C, 50000, order=3)
        rel = int(float(agree_digits(vsm, vbig)) - 2)
        delta = mp.log(vbig)
        rows.append((A, B, C, rel, S, vbig, delta))
        print(f"{str((A,B,C)):>10} {rel:>7} {mp.nstr(S,16):>20} {mp.nstr(vbig,18):>22} "
              f"{mp.nstr(delta,18):>22}")

    # persist delta(1,0,1) at full reliable precision + the map for the arithmetic probe
    with open("delta_values_m2.txt", "w") as f:
        f.write("# M2 delta = log R_inf, exact-sigma3 cluster seed; cross-validated.\n")
        mp.mp.dps = reliable + 10
        f.write(f"# primary high-precision case (1,0,1), reliable_digits={reliable}:\n")
        f.write(f"1 0 1 {reliable} {mp.nstr(delta101, reliable)}\n")
        mp.mp.dps = 170
        f.write("# A B C reliable_digits delta  (map, M=2e5)\n")
        for (A, B, C, rel, S, vbig, delta) in rows:
            f.write(f"{A} {B} {C} {rel} {mp.nstr(delta, max(rel,5))}\n")
    print("\nWrote delta_values_m2.txt")
    print("DONE.  (run with --full to also do the M=1e7, ~80-digit reference for (1,0,1))")
