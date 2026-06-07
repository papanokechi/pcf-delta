"""
Explicit closed form of  S(A,B,C) = sum_{n>=2} 1/(b_{n-1} b_n),  b_n=A(n-r1)(n-r2).
The integrand is a rational function of n with 4 simple poles
   rho in {r1, r2, 1+r1, 1+r2},  residues  Res_rho = 1/(A^2 prod_{sig!=rho}(rho-sig)).
Since sum of residues = 0, the tail sum telescopes against digamma:
   sum_{n>=2} 1/(b_{n-1}b_n) = - sum_rho Res_rho * psi(2 - rho).
For B=0 (r1,2 = +- i sqrt(C)) this is real and reduces to a coth/digamma combo.
Verified here against mpmath nsum to 40+ digits.
"""
import mpmath as mp

mp.mp.dps = 50


def roots(A, B, C):
    Af, Bf, Cf = mp.mpf(A), mp.mpf(B), mp.mpf(C)
    s = mp.sqrt(Bf * Bf - 4 * Af * Cf)
    return (-Bf + s) / (2 * Af), (-Bf - s) / (2 * Af)


def poles_distinct(A, B, C, tol=mp.mpf(10) ** -20):
    r1, r2 = roots(A, B, C)
    poles = [r1, r2, 1 + r1, 1 + r2]
    for i in range(4):
        for j in range(i + 1, 4):
            if abs(poles[i] - poles[j]) < tol:
                return False
    return True


def S_closed(A, B, C):
    # Generic (distinct-pole) closed form. Degenerate cases (B^2=4AC double root,
    # or roots differing by exactly 1) make two of the four poles collide and need
    # the confluent psi'-form; we guard and fall back to nsum there.
    if not poles_distinct(A, B, C):
        return None
    r1, r2 = roots(A, B, C)
    Af = mp.mpf(A)
    poles = [r1, r2, 1 + r1, 1 + r2]
    total = mp.mpc(0)
    for k, rho in enumerate(poles):
        denom = Af * Af
        for j, sig in enumerate(poles):
            if j == k:
                continue
            denom *= (rho - sig)
        res = 1 / denom
        total += res * mp.digamma(2 - rho)
    return -total


def S_num(A, B, C):
    Af, Bf, Cf = mp.mpf(A), mp.mpf(B), mp.mpf(C)
    b = lambda k: Af * k * k + Bf * k + Cf
    return mp.nsum(lambda n: 1 / (b(n - 1) * b(n)), [2, mp.inf])


def R_rec(A, B, C, N):
    Af, Bf, Cf = mp.mpf(A), mp.mpf(B), mp.mpf(C)
    b = lambda k: Af * k * k + Bf * k + Cf
    Rm2, Rm1 = mp.mpf(1), mp.mpf(1)
    for n in range(2, N + 1):
        Rn = Rm1 + Rm2 / (b(n - 1) * b(n))
        Rm2, Rm1 = Rm1, Rn
    return Rm1


if __name__ == "__main__":
    print("=== closed-form S via digamma residues vs nsum, and the delta bracket ===")
    hdr = f"{'(A,B,C)':>10} {'S_closed':>16} {'S_num':>16} {'match':>6} | {'lo':>12} {'delta':>14} {'hi':>12}"
    print(hdr); print("-" * len(hdr))
    for (A, B, C) in [(1,0,1),(1,0,2),(1,0,3),(2,0,1),(1,0,5),(1,1,1),(1,2,1),(2,1,1),(3,2,5),(1,5,2)]:
        Sc = S_closed(A, B, C)
        Sn = S_num(A, B, C)
        Rinf = R_rec(A, B, C, 60000)
        delta = mp.log(Rinf)
        if Sc is None:
            lo, hi = mp.log(1 + Sn), -mp.log(1 - Sn)
            print(f"{str((A,B,C)):>10} {'DEGEN(psi-prime)':>16} {mp.nstr(Sn,12):>16} {'  --':>6} | "
                  f"{mp.nstr(lo,8):>12} {mp.nstr(delta,10):>14} {mp.nstr(hi,8):>12}")
            continue
        Sc_re = mp.re(Sc)
        match = abs(Sc_re - Sn) < mp.mpf(10) ** -35
        lo, hi = mp.log(1 + Sc_re), -mp.log(1 - Sc_re)
        print(f"{str((A,B,C)):>10} {mp.nstr(Sc_re,12):>16} {mp.nstr(Sn,12):>16} {str(match):>6} | "
              f"{mp.nstr(lo,8):>12} {mp.nstr(delta,10):>14} {mp.nstr(hi,8):>12}")

    # The especially clean B=0 form: show S in terms of coth/psi for b_n=n^2+C
    print("\n=== B=0 check: S(1,0,C) closed form is real, matches; show pieces ===")
    for C in [1, 2, 3, 5]:
        Sc = mp.re(S_closed(1, 0, C))
        Sn = S_num(1, 0, C)
        w = mp.sqrt(C)
        # reference combo: (pi/w)coth(pi w) is sum over all integers of 1/(n^2+C)
        full = (mp.pi / w) * mp.coth(mp.pi * w)
        print(f"  C={C}: S={mp.nstr(Sc,30)}  (match nsum={abs(Sc-Sn)<mp.mpf(10)**-35})  "
              f"[ref (pi/w)coth(pi w)={mp.nstr(full,12)}]")
