"""
R_inf research harness (EXPLORATORY: numerically computes, does NOT prove).

Object of study: the correction constant delta = log R_inf of the quadratic PCF
    V(A,B,C) = 1 + K_{n>=1} 1/(A n^2 + B n + C),   integers A,B,C with A>=1.

Setup.  b_k = A k^2 + B k + C.  Denominators q_n (q_0=1, q_1=b_1,
q_n = b_n q_{n-1} + q_{n-2}); numerators p_n (p_{-1}=1, p_0=1,
p_n = b_n p_{n-1} + p_{n-2}).  Scale by the naive product P_n^prod = prod_{k=1}^n b_k:
    Q_n = q_n / prod b_k ,   P_n = p_n / prod b_k .
Both Q_n and P_n solve the SAME first-order-correction recurrence
    S_n = S_{n-1} + S_{n-2}/(b_{n-1} b_n) ,
with Q_0=Q_1=1 and P_0=1, P_1=(b_1+1)/b_1.  Hence
    R_inf := Q_inf = lim q_n/prod b_k ,   delta = log R_inf ,
    P_inf := lim p_n/prod b_k ,           V = P_inf / Q_inf = lim p_n/q_n.
This is the two-solution / Casoratian structure: {P_n, Q_n} is a basis of the
2-dim solution space of the scaled linear recurrence; R_inf is the value-at-
infinity of the Q-solution.

Exact Casoratian (continuant determinant), unit numerators a_k=1:
    p_n q_{n-1} - p_{n-1} q_n = (-1)^{n-1}
  =>  P_n Q_{n-1} - P_{n-1} Q_n = (-1)^{n-1} / ( b_n * (prod_{k=1}^{n-1} b_k)^2 ).

Everything here is numerics. A relation that holds to the reported digits is
VERIFIED-numerically (for the tested triples only), NOT proven. A null PSLQ
result is an equally valid, informative outcome.
"""
import mpmath as mp

mp.mp.dps = 120


# ---------------------------------------------------------------------------
# core: scaled sequences via the exact recurrences
# ---------------------------------------------------------------------------
def b_of(A, B, C):
    Af, Bf, Cf = mp.mpf(A), mp.mpf(B), mp.mpf(C)
    def b(k):
        kk = mp.mpf(k)
        return Af * kk * kk + Bf * kk + Cf
    return b


def R_at(A, B, C, N):
    """Q_N = q_N / prod_{k<=N} b_k  via  R_n = R_{n-1} + R_{n-2}/(b_{n-1} b_n)."""
    b = b_of(A, B, C)
    Rm2, Rm1 = mp.mpf(1), mp.mpf(1)      # R_0, R_1
    for n in range(2, N + 1):
        Rn = Rm1 + Rm2 / (b(n - 1) * b(n))
        Rm2, Rm1 = Rm1, Rn
    return Rm1


def P_at(A, B, C, N):
    """P_N = p_N / prod_{k<=N} b_k  (numerator-scaled solution), same recurrence."""
    b = b_of(A, B, C)
    b1 = b(1)
    Pm2, Pm1 = mp.mpf(1), (b1 + 1) / b1   # P_0, P_1
    if N == 0:
        return Pm2
    for n in range(2, N + 1):
        Pn = Pm1 + Pm2 / (b(n - 1) * b(n))
        Pm2, Pm1 = Pm1, Pn
    return Pm1


def neville_zero(xs, ys):
    P = list(ys)
    m = len(xs)
    for k in range(1, m):
        for i in range(m - 1, k - 1, -1):
            P[i] = ((0 - xs[i - k]) * P[i] - (0 - xs[i]) * P[i - 1]) / (xs[i] - xs[i - k])
    return P[-1]


def extrap_limit(seq_fn, A, B, C, nodes):
    """Neville extrapolation in 1/N of a scaled sequence to its N->inf limit."""
    xs = [1 / mp.mpf(N) for N in nodes]
    ys = [seq_fn(A, B, C, N) for N in nodes]
    return neville_zero(xs, ys)


def R_inf(A, B, C, nodes):
    return extrap_limit(R_at, A, B, C, nodes)


def P_inf(A, B, C, nodes):
    return extrap_limit(P_at, A, B, C, nodes)


def cf_value(A, B, C, N=4000):
    """V = lim p_n/q_n directly (ratio converges fast; no scaling needed)."""
    b = b_of(A, B, C)
    pm1, p0 = mp.mpf(1), mp.mpf(1)        # p_{-1}, p_0
    qm1, q0 = mp.mpf(0), mp.mpf(1)        # q_{-1}, q_0
    for n in range(1, N + 1):
        bn = b(n)
        pn = bn * p0 + pm1
        qn = bn * q0 + qm1
        pm1, p0 = p0, pn
        qm1, q0 = q0, qn
        # periodic rescale to avoid overflow
        if n % 64 == 0:
            s = q0
            pm1, p0, qm1, q0 = pm1 / s, p0 / s, qm1 / s, q0 / s
    return p0 / q0


def stable_digits(x, y):
    """number of agreeing significant digits between x and y."""
    if x == 0 and y == 0:
        return mp.inf
    d = abs(x - y)
    if d == 0:
        return mp.mp.dps
    return float(-mp.log10(d / abs(x)))


# ---------------------------------------------------------------------------
# closed-form reference pieces (for orientation only)
# ---------------------------------------------------------------------------
def K_gamma(A, B, C):
    Af, Bf, Cf = mp.mpf(A), mp.mpf(B), mp.mpf(C)
    s = mp.sqrt(Bf * Bf - 4 * Af * Cf)
    r1, r2 = (-Bf + s) / (2 * Af), (-Bf - s) / (2 * Af)
    return -mp.log(mp.re(mp.gamma(1 - r1) * mp.gamma(1 - r2)))


if __name__ == "__main__":
    nodesA = [2000, 4000, 6000, 8000, 10000, 13000, 16000, 20000]
    nodesB = [3000, 5000, 7000, 9000, 12000, 15000, 18000, 24000]

    cases = [
        (1, 0, 1), (1, 0, 2), (1, 0, 3), (2, 0, 1), (1, 0, 5),
        (1, 1, 1), (1, 2, 1), (2, 1, 1), (1, 3, 1), (3, 2, 5),
    ]
    print(f"[mpmath dps={mp.mp.dps}]  R_inf = lim q_n/prod b_k,  delta = log R_inf")
    print("Two-solution frame: Q_inf=R_inf, P_inf=lim p_n/prod b_k, V=P_inf/Q_inf=lim p_n/q_n\n")
    hdr = (f"{'(A,B,C)':>10} {'R_inf(=Q_inf)':>22} {'delta=logR':>16} "
           f"{'stab':>5} {'P_inf':>14} {'V=P/Q':>14} {'cfV':>14} {'|V-cfV|':>9}")
    print(hdr); print("-" * len(hdr))
    results = {}
    for (A, B, C) in cases:
        Ra = R_inf(A, B, C, nodesA)
        Rb = R_inf(A, B, C, nodesB)
        sd = stable_digits(Ra, Rb)
        Pinf = P_inf(A, B, C, nodesA)
        Vpq = Pinf / Ra
        cfV = cf_value(A, B, C)
        results[(A, B, C)] = (Ra, mp.log(Ra), Pinf, Vpq, cfV, sd)
        print(f"{str((A,B,C)):>10} {mp.nstr(Ra,18):>22} {mp.nstr(mp.log(Ra),12):>16} "
              f"{sd:5.0f} {mp.nstr(Pinf,10):>14} {mp.nstr(Vpq,10):>14} "
              f"{mp.nstr(cfV,10):>14} {mp.nstr(abs(Vpq-cfV),2):>9}")

    # ---- Casoratian exact identity check (n small, exact) ----
    print("\n[CASORATIAN] P_n Q_{n-1} - P_{n-1} Q_n  vs  (-1)^{n-1}/(b_n (prod_{<n} b_k)^2)")
    A, B, C = 1, 0, 1
    b = b_of(A, B, C)
    for n in [2, 3, 4, 5, 6]:
        Qn, Qn1 = R_at(A, B, C, n), R_at(A, B, C, n - 1)
        Pn, Pn1 = P_at(A, B, C, n), P_at(A, B, C, n - 1)
        lhs = Pn * Qn1 - Pn1 * Qn
        prod_lt = mp.mpf(1)
        for k in range(1, n):
            prod_lt *= b(k)
        rhs = mp.mpf((-1) ** (n - 1)) / (b(n) * prod_lt ** 2)
        print(f"  n={n}: lhs={mp.nstr(lhs,12):>16}  rhs={mp.nstr(rhs,12):>16}  "
              f"match={abs(lhs-rhs) < mp.mpf(10)**(-80)}")

    # ---- orientation: relation of delta to K_gamma (already known nonzero) ----
    print("\n[ORIENT] delta vs K_Gamma (the naive-product constant) for B=0 cases:")
    for (A, B, C) in [(1, 0, 1), (1, 0, 2), (2, 0, 1)]:
        Ra = results[(A, B, C)][0]
        print(f"  (A,B,C)={ (A,B,C) }: delta={mp.nstr(mp.log(Ra),15)}  "
              f"K_Gamma={mp.nstr(K_gamma(A,B,C),15)}  V={mp.nstr(results[(A,B,C)][4],15)}")
