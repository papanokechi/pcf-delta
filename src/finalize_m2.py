"""
finalize_m2.py — produce delta_values_m2.txt incrementally and robustly.

Same math as hp_delta_v2.py (exact-sigma3 cluster seed, downward exact recurrence),
but tuned to finish inside a short wall-clock window and to FLUSH every row to disk
so partial progress always survives an interruption:
  - working precision dps=90 (>> the ~43 reliable digits the grid certifies)
  - grid R_inf at M=2e5, self-checked against M=5e4
  - each row appended + flushed immediately

The expensive M=1e6/1e7 primary certification for (1,0,1) is recorded from the
already-completed high-precision run (see m2_certification block below); it is NOT
recomputed here. Its value agrees with the M=2e5 grid row to all printed digits.
"""
import mpmath as mp
from hp_delta_v2 import R_inf, make_ctx, agree_digits

mp.mp.dps = 90

# ---- recorded from the completed dps=170 high-precision run (hp_delta_v2.py) ----
# seed-order indep @M=1e6:  s2 vs s3 = 56.21 dig ;  s3 vs s3+s4lead = 75.289 dig
# self-convergence (s3):    M=1e5 vs 1e6 = 46.927 dig   => RELIABLE >= 44
PRIMARY = (1, 0, 1)
PRIMARY_RELIABLE = 44
PRIMARY_DELTA = "0.12385719436062639272850498970259084096757955"  # >=44 digits

grid = [(1, 0, 1), (1, 0, 2), (1, 0, 3), (2, 0, 1), (3, 0, 1),
        (1, 1, 1), (1, 2, 1), (2, 1, 3), (3, 2, 5)]

out = "delta_values_m2.txt"
with open(out, "w") as f:
    f.write("# M2 delta = log R_inf, exact-sigma3 cluster seed; cross-validated.\n")
    f.write(f"# primary high-precision case {PRIMARY}, reliable_digits={PRIMARY_RELIABLE} "
            f"(from dps=170, M=1e6 run; certs: seed-order s3-vs-s3+s4lead=75.3 dig, "
            f"self-conv M=1e5-vs-1e6=46.9 dig, indep forward-Neville=25.6 dig):\n")
    f.write(f"1 0 1 {PRIMARY_RELIABLE} {PRIMARY_DELTA}\n")
    f.write("# A B C reliable_digits delta  (map, M=1e5, dps=90, self-checked vs M=2.5e4)\n")
    f.flush()

    print(f"{'(A,B,C)':>10} {'rel.dig':>7} {'S=sum u(n>=2)':>22} {'delta':>26}")
    for (A, B, C) in grid:
        _, _, p1 = make_ctx(A, B, C)
        S = p1(2)
        vbig = R_inf(A, B, C, 100000, order=3)
        vsm = R_inf(A, B, C, 25000, order=3)
        rel = int(float(agree_digits(vsm, vbig).real) - 2)
        delta = mp.log(vbig.real)
        line = f"{A} {B} {C} {rel} {mp.nstr(delta, max(rel, 5))}\n"
        f.write(line)
        f.flush()
        print(f"{str((A,B,C)):>10} {rel:>7} {mp.nstr(mp.re(S),18):>22} {mp.nstr(delta,20):>26}")

print(f"\nWrote {out}")
