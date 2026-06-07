"""
verify_forward_crosscheck.py — confirm the INDEPENDENT forward+Neville method agrees
with the exact-sigma3 cluster method for R_inf, after fixing the forward_neville
off-by-one (it had started the continuant at n=3, silently dropping the u(2) term, so it
converged to a different limit; the older trusted hp_delta.py used range(2,N+1)).

Cheap certification: cluster R_inf at M=1e5 (>= ~36 reliable digits) vs forward+Neville
(its own ~25-30). Agreement to the Neville method's own resolution certifies the value
with a genuinely independent algorithm (no shared seed, no shared recurrence direction).
"""
import mpmath as mp
from hp_delta_v2 import R_inf, forward_neville, agree_digits

mp.mp.dps = 120

cases = [(1, 0, 1), (1, 0, 2), (1, 1, 1), (2, 1, 3)]
Ns = [2000, 4000, 8000, 16000, 32000, 64000]

print("independent forward+Neville  vs  exact-sigma3 cluster (M=1e5)")
print(f"{'(A,B,C)':>10} {'agree (dig)':>12}   note")
allok = True
for (A, B, C) in cases:
    vc = R_inf(A, B, C, 10**5, order=3)          # cluster, ~36+ reliable digits
    fn = forward_neville(A, B, C, Ns)            # independent method (fixed)
    ad = float(agree_digits(fn, vc).real)
    ok = ad >= 20.0
    allok = allok and ok
    print(f"{str((A,B,C)):>10} {ad:>12.2f}   {'OK' if ok else 'FAIL (independent method disagrees)'}")

print("\nINDEPENDENT CROSS-CHECK PASSES" if allok
      else "\n*** INDEPENDENT CROSS-CHECK FAILS ***")
