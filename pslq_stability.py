"""
Rigorous PSLQ-null test for delta = log R_inf (good to ~34 digits).
A genuine integer relation is precision-INDEPENDENT; a PSLQ artifact changes with dps.
We run the same basis at several dps and check whether the returned vector is stable
AND whether its residual keeps shrinking as dps grows (real) or floors out (spurious).
"""
import mpmath as mp


def bfun(A, B, C):
    Af, Bf, Cf = mp.mpf(A), mp.mpf(B), mp.mpf(C)
    return lambda k: Af * k * k + Bf * k + Cf

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

def delta_methodB(A, B, C, M):
    b = bfun(A, B, C)
    u = lambda n: 1 / (b(n - 1) * b(n))
    t1 = lambda m: -sum(r * mp.digamma(m - rho) for (rho, r) in residues(A, B, C))
    seed = lambda m: (lambda t: 1 + t + t * t / 2)(t1(m))
    Tp2, Tp1 = seed(M + 2), seed(M + 1)
    Tm = None
    for m in range(M, 1, -1):
        Tm = Tp1 + u(m) * Tp2
        Tp2, Tp1 = Tp1, Tm
    return mp.re(mp.log(Tm))


if __name__ == "__main__":
    mp.mp.dps = 60
    d_full = delta_methodB(1, 0, 1, 300000)   # ~34-digit-reliable delta
    print(f"delta(1,0,1) = {mp.nstr(d_full, 40)}  (reliable ~34 digits)")

    print("\n=== relation-stability test across dps (basis [delta,1,pi,log2,euler,catalan,zeta3]) ===")
    print("   real relation -> SAME vector at every dps; spurious -> vector wanders, residual floors\n")
    for dps in [18, 22, 26, 30, 34]:
        mp.mp.dps = dps
        d = +d_full
        basis = [d, mp.mpf(1), mp.pi, mp.log(2), mp.euler, mp.catalan, mp.zeta(3)]
        rel = mp.pslq(basis, maxcoeff=10**6, maxsteps=10**5)
        if rel is None:
            print(f"  dps={dps:>3}: pslq -> None (no relation)")
            continue
        # residual evaluated at HIGH precision using the reliable delta
        mp.mp.dps = 50
        bhi = [+d_full, mp.mpf(1), mp.pi, mp.log(2), mp.euler, mp.catalan, mp.zeta(3)]
        resid = mp.fdot([mp.mpf(int(c)) for c in rel], bhi)
        height = max(abs(int(c)) for c in rel)
        print(f"  dps={dps:>3}: height={height:>8}  |residual@50dps|={mp.nstr(abs(resid),3):>10}  rel={rel}")

    print("\n=== controlled low-height search: maxcoeff=200, dps=32 ===")
    mp.mp.dps = 32
    d = +d_full
    basis = [d, mp.mpf(1), mp.pi, mp.log(2), mp.euler, mp.catalan, mp.zeta(3)]
    rel = mp.pslq(basis, maxcoeff=200, maxsteps=10**5)
    print(f"  pslq(maxcoeff=200) -> {rel}   (None => no relation with |coeff|<=200)")

    print("\n=== algebraicity of R_inf=exp(delta), controlled height, stability ===")
    for dps in [22, 28, 34]:
        mp.mp.dps = dps
        R = mp.e ** (+d_full)
        rel = mp.pslq([R ** k for k in range(5)], maxcoeff=10**4, maxsteps=10**5)
        if rel is None:
            print(f"  dps={dps:>3}: None (not algebraic deg<=4, height<=1e4)")
        else:
            mp.mp.dps = 50
            Rh = mp.e ** (+d_full)
            resid = mp.fdot([mp.mpf(int(c)) for c in rel], [Rh ** k for k in range(5)])
            print(f"  dps={dps:>3}: height={max(abs(int(c)) for c in rel)}  |resid@50|={mp.nstr(abs(resid),3)}  rel={rel}")
