# pcf-delta

The growth-law correction constant **δ = log R∞ > 0** of the quadratic polynomial
continued fraction *V(A,B,C) = 1 + K\_{n≥1} 1/(An² + Bn + C)* (integers A,B,C ≥ 1):
its structure, an elementary two-sided bracket, certified high-precision values, a
rigorous integer-relation null, and a machine-checked finitary core in Lean 4.

This is the **deposit unit** for the δ-characterization note. It characterizes the
constant δ that the companion quadratic growth-law note introduces and leaves
undetermined.

## Contents

- **Paper:** `delta_characterization.pdf` (source `delta_characterization.tex`).
- **Reproducibility scripts** (`mpmath`):
  - `harness_rinf.py` — two-solution frame, R∞, value V.
  - `continuant_verify.py` — exact independence-polynomial check.
  - `S_closed_form.py`, `S_confluent.py` — closed forms for S (incl. degenerate
    repeated-pole triples).
  - `verify_clusters.py` — the σ₂, σ₃ cluster-identity gate (vs brute force).
  - `hp_delta_v2.py`, `finalize_m2.py` — the high-precision δ values (Table 2),
    output `delta_values_m2.txt`.
  - `verify_forward_crosscheck.py` — independent forward + Neville cross-check.
  - `hp_probe.py`, `pslq_stability.py` — the integer-relation nulls.
- **Data:** `delta_values_m2.txt` — the M2 output Table 2 is read from.
- **Lean core:** `lean/pcf_continuant/` — `Check.lean` prints the axiom cones for the
  twelve declarations (`casoratian_step`, `casoratian_eq`, `pq_casoratian`,
  `rseq_ge_one`, `rseq_mono`, `rseq_monotone`, `rmaj_ge_one`, `rmaj_mono`,
  `rseq_le_rmaj`, `rseq_bddAbove_of_rmaj`, `rseq_tendsto_ciSup`,
  `rseq_tendsto_of_rmaj_bddAbove`), each a subset of
  `{propext, Classical.choice, Quot.sound}` with no `sorryAx`.

## Licensing (dual)

- **Paper, text, and prose** — the manuscript (`.tex`/`.pdf`) and this README — are
  licensed under **Creative Commons Attribution 4.0 International (CC BY 4.0)**; see
  the top-level `LICENSE`.
- **Code** — the ten Python scripts and the Lean project under
  `lean/pcf_continuant/` — is licensed under the **Apache License 2.0**; see the
  top-level `LICENSE-CODE` (and the Lean package's own `lean/pcf_continuant/LICENSE`).

## Reproducing

- **Numerics:** install `mpmath` (e.g. `pip install mpmath`) and run any of the
  scripts above with Python 3, e.g. `python finalize_m2.py`. The δ map is certified
  ≥39 digits per triple, ≥44 for (1,0,1).
- **Lean core:** install the pinned toolchain (`leanprover/lean4:v4.30.0`, Mathlib
  `rev=v4.30.0`) via `elan`, then from `lean/pcf_continuant/` run
  `lake exe cache get` (to fetch Mathlib oleans) and verify the axiom cones with
  `lake env lean Check.lean`. PROVEN means a clean axiom cone with no `sorryAx`, not
  merely a green build.

## Companion deposit

This note characterizes the additive correction constant δ = log R∞ that the
quadratic growth-law note introduces and leaves undetermined. The Zenodo metadata
records this as `isSupplementTo` the growth-law note (concept DOI
`10.5281/zenodo.20564681`).

## Status

The public repository and the Zenodo deposit are **forthcoming and operator-gated**.
No DOI for this work is minted here; it is assigned by Zenodo at publish time. This
unit is staged for review only.
