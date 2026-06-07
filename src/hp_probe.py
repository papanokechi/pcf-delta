"""
Closed-form probes at HONEST precision (rubber-duck point 5):
 - V = lim p_n/q_n is computable to ~117 digits cheaply (converges like (prod b)^-2);
   this is the strongest null (V is the natural 'answer').
 - delta = log R_inf is only reliably ~35 digits (Method B downward-T, closed-form seed),
   so we run its identify/PSLQ at a CONSERVATIVE 28 digits.  We do NOT claim an 80-digit null.
"""
import mpmath as mp

# ---- shared ----
def bfun(A, B, C):
    Af, Bf, Cf = mp.mpf(A), mp.mpf(B), mp.mpf(C)
    return lambda k: Af * k * k + Bf * k + Cf

def V_value(A, B, C, N):
    """direct convergent value lim p_n/q_n (fast)."""
    b = bfun(A, B, C)
    pm1, p0 = mp.mpf(1), mp.mpf(1)       # p_{-1}=1, p_0=1
    qm1, q0 = mp.mpf(0), mp.mpf(1)       # q_{-1}=0, q_0=1  (q_1=b_1)
    # build with p_n=b_n p_{n-1}+p_{n-2}, q_n=b_n q_{n-1}+q_{n-2}; start n=1
    p_prev2, p_prev1 = p0, p0            # using p_0 as both seeds is wrong; do explicit
    # explicit standard convergents of 1 + K 1/b_n:
    h_prev, h_cur = mp.mpf(1), mp.mpf(1) # h_0 = b_0-ish; we use the value recurrence
    # Use A_n/B_n with A_{-1}=1,A_0=a_0=1 ; B_{-1}=0,B_0=1 ; a_0=1,b_k=1(num),a_k=b(k)
    Am1, A0 = mp.mpf(1), mp.mpf(1)
    Bm1, B0 = mp.mpf(0), mp.mpf(1)
    Aprev2, Aprev1 = Am1, A0
    Bprev2, Bprev1 = Bm1, B0
    for n in range(1, N + 1):
        an = b(n)            # partial denominator a_n = b_n ; partial numerator = 1
        An = an * Aprev1 + 1 * Aprev2
        Bn = an * Bprev1 + 1 * Bprev2
        Aprev2, Aprev1 = Aprev1, An
        Bprev2, Bprev1 = Bprev1, Bn
    return Aprev1 / Bprev1

def residues(A, B, C):
    Af = mp.mpf(A)
    s = mp.sqrt(mp.mpf(B) ** 2 - 4 * Af * mp.mpf(C))
    r1, r2 = (-mp.mpf(B) + s) / (2 * Af), (-mp.mpf(B) - s) / (2 * Af)
    poles = [r1, r2, 1 + r1, 1 + r2]
    out = []
    for i, rho in enumerate(poles):
        d = Af * Af
        for j, sig in enumerate(poles):
            if j != i:
                d *= (rho - sig)
        out.append((rho, 1 / d))
    return out

def t1_tail(A, B, C, m):
    return -sum(r * mp.digamma(m - rho) for (rho, r) in residues(A, B, C))

def delta_methodB(A, B, C, M):
    b = bfun(A, B, C)
    u = lambda n: 1 / (b(n - 1) * b(n))
    seed = lambda m: (lambda t: 1 + t + t * t / 2)(t1_tail(A, B, C, m))
    Tp2, Tp1 = seed(M + 2), seed(M + 1)
    Tm = None
    for m in range(M, 1, -1):
        Tm = Tp1 + u(m) * Tp2
        Tp2, Tp1 = Tp1, Tm
    return mp.log(Tm)  # delta = log R_inf


if __name__ == "__main__":
    A, B, C = 1, 0, 1

    # ---- V to high precision ----
    mp.mp.dps = 130
    V = V_value(A, B, C, 4000)
    V2 = V_value(A, B, C, 6000)
    Vdig = -mp.log10(abs(V - V2) / abs(V)) if V != V2 else mp.inf
    print(f"V(1,0,1) stable to ~{mp.nstr(Vdig,4)} digits")
    print(f"  V = {mp.nstr(V, 110)}")

    print("\n--- identify(V) at 100 dps vs constants ---")
    mp.mp.dps = 100
    Vr = +V
    for name, val in [("V", Vr), ("V-1", Vr - 1), ("1/V", 1 / Vr), ("log V", mp.log(Vr)),
                      ("V^2", Vr ** 2)]:
        r = mp.identify(val, ['pi', 'log(2)', 'euler', 'catalan', 'zeta(3)', 'exp(1)'])
        print(f"  identify({name}) = {r}")

    # ---- delta at honest precision ----
    mp.mp.dps = 60
    d = mp.re(delta_methodB(A, B, C, 300000))
    d2 = mp.re(delta_methodB(A, B, C, 100000))
    ddig = -mp.log10(abs(d - d2) / abs(d))
    print(f"\ndelta(1,0,1) Method B self-stable to ~{mp.nstr(ddig,4)} digits")
    print(f"  delta = {mp.nstr(d, 40)}")

    print("\n--- identify(delta) at CONSERVATIVE 26 dps (delta good to ~35) ---")
    mp.mp.dps = 26
    dr = +d
    for name, val in [("delta", dr), ("exp(delta)=R_inf", mp.e ** dr),
                      ("delta/pi^2", dr / mp.pi ** 2), ("exp(delta)-1", mp.e ** dr - 1)]:
        r = mp.identify(val, ['pi', 'log(2)', 'euler', 'catalan', 'zeta(3)'])
        print(f"  identify({name}) = {r}")

    print("\n--- PSLQ: is delta a Q-combination of {1,pi,log2,euler,catalan,zeta3}? (26 dps) ---")
    basis = [dr, mp.mpf(1), mp.pi, mp.log(2), mp.euler, mp.catalan, mp.zeta(3)]
    rel = mp.pslq(basis, maxcoeff=10**8, maxsteps=10**5)
    print(f"  pslq -> {rel}  (None/large = no low-height relation)")

    print("\n--- PSLQ: is R_inf algebraic of degree<=4? (26 dps) ---")
    R = mp.e ** dr
    rel2 = mp.pslq([R ** k for k in range(5)], maxcoeff=10**6, maxsteps=10**5)
    print(f"  pslq[1,R,R^2,R^3,R^4] -> {rel2}")
