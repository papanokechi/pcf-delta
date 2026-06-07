"""
General (confluent) closed form for  S(A,B,C) = sum_{n>=2} 1/(b_{n-1} b_n).

D(n) := b_{n-1} b_n = A^2 (n - r1)(n - r2)(n - (1+r1))(n - (1+r2))   (degree 4 in n)
has poles rho in the MULTISET {r1, r2, 1+r1, 1+r2}.  Partial fractions:
   1/D(n) = sum_rho sum_{j=1}^{m_rho}  a_{rho,j} / (n - rho)^j ,
with m_rho the multiplicity of rho.  Termwise,
   sum_{n>=2} 1/(n-rho)^j = (-1)^j psi^{(j-1)}(2-rho) / (j-1)!     for j>=2  (convergent),
and for j=1 the pieces are individually divergent but combine because
   sum_rho a_{rho,1} = 0   (1/D decays like 1/n^4),
leaving  sum_{n>=2} sum_rho a_{rho,1}/(n-rho) = - sum_rho a_{rho,1} psi(2-rho).
Hence:
   S = - sum_rho a_{rho,1} psi(2-rho)
       + sum_rho sum_{j>=2} a_{rho,j} (-1)^j psi^{(j-1)}(2-rho)/(j-1)!.

The simple-pole case (all m_rho=1) reduces to S = -sum_rho Res_rho psi(2-rho),
Res_rho = a_{rho,1} = 1/(A^2 prod_{sigma!=rho}(rho-sigma)).  This file handles BOTH
by clustering poles to detect multiplicity and taking Laurent coefficients via mpmath.diff.
Verified against nsum, and against the exact rational+pi^2 value for the (1,2,1) double case.
"""
import mpmath as mp

mp.mp.dps = 60


def roots(A, B, C):
    Af, Bf, Cf = mp.mpf(A), mp.mpf(B), mp.mpf(C)
    s = mp.sqrt(Bf * Bf - 4 * Af * Cf)
    return (-Bf + s) / (2 * Af), (-Bf - s) / (2 * Af)


def cluster_poles(poles, tol=mp.mpf(10) ** -25):
    """Group near-equal poles into (representative, multiplicity)."""
    reps = []
    for p in poles:
        placed = False
        for i, (q, m) in enumerate(reps):
            if abs(p - q) < tol:
                reps[i] = ((q * m + p) / (m + 1), m + 1)  # running mean keeps it centered
                placed = True
                break
        if not placed:
            reps.append((p, 1))
    return reps


def S_confluent(A, B, C):
    """Unified digamma/polygamma closed form, valid for simple AND repeated poles."""
    r1, r2 = roots(A, B, C)
    Af = mp.mpf(A)
    reps = cluster_poles([r1, r2, 1 + r1, 1 + r2])  # [(rho, mult), ...]

    total = mp.mpc(0)
    a1_sum = mp.mpc(0)  # to check sum of simple-part residues = 0
    for i, (rho, m) in enumerate(reps):
        # phi(n) = (n-rho)^m / D(n) with the cluster's own factor removed EXACTLY,
        # i.e. phi(n) = 1 / (A^2 * prod_{k != i} (n - rho_k)^{m_k}) -- analytic & nonzero at rho.
        def phi(n, i=i, rho=rho):
            val = Af * Af
            for k, (rk, mk) in enumerate(reps):
                if k == i:
                    continue
                val *= (n - rk) ** mk
            return 1 / val
        # a_{rho, m-t} = phi^{(t)}(rho)/t!,  t=0..m-1
        for t in range(m):
            j = m - t
            a = (mp.diff(phi, rho, t) if t > 0 else phi(rho)) / mp.factorial(t)
            if j == 1:
                a1_sum += a
                total += -a * mp.digamma(2 - rho)
            else:
                total += a * ((-1) ** j) * mp.polygamma(j - 1, 2 - rho) / mp.factorial(j - 1)
    return mp.re(total), mp.re(a1_sum)


def S_num(A, B, C):
    Af, Bf, Cf = mp.mpf(A), mp.mpf(B), mp.mpf(C)
    b = lambda k: Af * k * k + Bf * k + Cf
    return mp.nsum(lambda n: 1 / (b(n - 1) * b(n)), [2, mp.inf])


if __name__ == "__main__":
    print("=== general confluent S vs nsum (simple AND repeated poles) ===")
    hdr = f"{'(A,B,C)':>10} {'disc':>6} {'S_confluent':>22} {'|S-nsum|':>12} {'sum a1':>12}"
    print(hdr); print("-" * len(hdr))
    cases = [(1,0,1),(1,0,2),(2,0,1),(1,1,1),(3,2,5),     # generic / distinct poles
             (1,2,1),                                      # double-double: r=-1,-1 -> poles {-1,-1,0,0}
             (4,4,1),                                      # (2n+1)^2-type: 4n^2+4n+1, root -1/2 double
             (1,-2,1),                                     # roots 1,1 -> poles {1,1,2,2}; b_n=(n-1)^2>0 only n>=2! skip n where 0
             (9,6,1)]                                      # 9n^2+6n+1=(3n+1)^2, root -1/3 double
    for (A,B,C) in cases:
        # guard: need b_n>0 for n>=1 used in the tail (n>=1). (1,-2,1): b_1=0 -> skip
        Af=mp.mpf(A); b1=Af+B+C
        disc = B*B-4*A*C
        if b1==0:
            print(f"{str((A,B,C)):>10} {disc:>6}  b_1=0 (skipped: tail starts at n=2 but b_1=0 breaks frame)")
            continue
        Sc, a1 = S_confluent(A,B,C)
        Sn = S_num(A,B,C)
        print(f"{str((A,B,C)):>10} {disc:>6} {mp.nstr(Sc,18):>22} {mp.nstr(abs(Sc-Sn),3):>12} {mp.nstr(a1,3):>12}")

    print("\n=== exact check: (1,2,1) double-double, S should equal pi^2/3 - 13/4 ===")
    Sc,_ = S_confluent(1,2,1)
    exact = mp.pi**2/3 - mp.mpf(13)/4
    print(f"  S_confluent = {mp.nstr(Sc,30)}")
    print(f"  pi^2/3-13/4 = {mp.nstr(exact,30)}")
    print(f"  match to 1e-40: {abs(Sc-exact) < mp.mpf(10)**-40}")

    print("\n=== exact check: (4,4,1), b_n=(2n+1)^2, double pole at -1/2 ===")
    # b_{n-1}b_n = (2n-1)^2 (2n+1)^2 = (4n^2-1)^2.  1/(4n^2-1)^2 partial fractions ->
    # closed form sum_{n>=2} 1/(4n^2-1)^2.  Compare confluent vs nsum only (exact messy).
    Sc,_ = S_confluent(4,4,1)
    Sn = S_num(4,4,1)
    print(f"  S_confluent={mp.nstr(Sc,30)}  nsum={mp.nstr(Sn,30)}  match={abs(Sc-Sn)<mp.mpf(10)**-40}")
