# pcf_continuant — finitary core for the quadratic-PCF growth law

A small, machine-checked Lean 4 / Mathlib formalization of the **finitary algebraic
and order core** underlying the growth law of the quadratic polynomial continued
fraction

```
V(A,B,C) = 1 + K_{n≥1} 1/(A n² + B n + C),   A,B,C ≥ 1.
```

Its convergent numerators `p` and denominators `q` satisfy the same second-order
recurrence `s (n+2) = b (n+2) · s (n+1) + s n`, with `b n = A n² + B n + C`. This
repo formalizes the two structural facts that the analytic growth-constant analysis
(`delta_characterization.md`, the deposited growth-law note) rests on — the parts
that are *finitary* and so admit a clean, sorry-free proof.

## What is PROVEN here (clean axiom cone, machine-checked)

All results below were checked with `#print axioms` (see `Check.lean`). Every cone is a
subset of the Mathlib defaults `{propext, Classical.choice, Quot.sound}` with **no
`sorryAx`** — and the source contains **no `sorry`/`admit`** and builds with **zero
warnings/errors**.

| Declaration       | Statement                                                                                   | Axiom cone |
|-------------------|----------------------------------------------------------------------------------------------|------------|
| `casoratian_step` | Casoratian (discrete Wronskian) of two solutions of the same recurrence flips sign each step | `[propext]` |
| `casoratian_eq`   | hence it equals `(-1)^n` times its value at `0`                                              | `[propext, Quot.sound]` |
| `pq_casoratian`   | for convergents (`p 0=1, p 1=b 1+1, q 0=1, q 1=b 1`): `p (n+1)·q n − p n·q (n+1) = (-1)^n`    | `[propext, Quot.sound]` |
| `rseq_ge_one`     | the scaled sequence `r (n+2)=r (n+1)+u (n+2)·r n` (`r 0=r 1=1`, `u ≥ 0`) satisfies `r n ≥ 1`  | `[propext, Classical.choice, Quot.sound]` |
| `rseq_mono`       | …and is monotone nondecreasing                                                                | `[propext, Classical.choice, Quot.sound]` |
| `rseq_monotone`   | the full `Monotone (rseq u)` (via `monotone_nat_of_le_succ`)                                  | `[propext, Classical.choice, Quot.sound]` |
| `rmaj_ge_one`     | the product majorant `rmaj u n = ∏_{k=2}^n (1+uₖ)` satisfies `rmaj n ≥ 1`                     | `[propext, Classical.choice, Quot.sound]` |
| `rmaj_mono`       | …and is monotone nondecreasing                                                                | `[propext, Classical.choice, Quot.sound]` |
| `rseq_le_rmaj`    | **the finitary bound** `Rₙ ≤ ∏_{k=2}^n (1+uₖ)`                                               | `[propext, Classical.choice, Quot.sound]` |
| `rseq_bddAbove_of_rmaj` | if the partial products are bounded above, so is `rseq`                                 | `[propext, Classical.choice, Quot.sound]` |
| `rseq_tendsto_ciSup` | **monotone convergence**: `rseq` bounded above `⟹ Rₙ → ⨆ₙ Rₙ`                            | `[propext, Classical.choice, Quot.sound]` |
| `rseq_tendsto_of_rmaj_bddAbove` | **`Rₙ → R∞` exists** when `∏(1+uₖ)` (i.e. `Σ uₙ`) is bounded above             | `[propext, Classical.choice, Quot.sound]` |

`casoratian_step`, `casoratian_eq`, `pq_casoratian` are stated over an arbitrary
`CommRing`. The `rseq_*`/`rmaj_*` results are specialized to `ℝ` (the application
domain). Together these are the exact **Casoratian identity** (item 2 of
`delta_characterization.md`), the **monotone, bounded-below** structure, and now the
**limit existence** `Rₙ → R∞` (item 3) via Mathlib's `tendsto_atTop_ciSup`, reduced to
the single finitary hypothesis that the partial products `∏(1+uₖ)` are bounded above
(equivalently `Σ uₙ < ∞`).

## What is OUT OF SCOPE (deliberately not formalized — labelled hypotheses)

These are analytic and remain hand-proved / numerically verified elsewhere; they are
**not** claimed here:

* the boundedness hypothesis itself — that `Σ uₙ < ∞` (equivalently the partial products
  `∏(1+uₖ)` are bounded above); the *value* of the limit and the upper bound `R∞ ≤ 1/(1−S)`
  (needs the analytic tail estimate / a convergent dominating series);
* the closed-form digamma residue for `S` and the bracket `log(1+S) ≤ δ ≤ −log(1−S)`;
* the Γ-product constant `K_Γ = −log(Γ(1−r₁)Γ(1−r₂))` and Stirling/Gamma-ratio
  asymptotics;
* the conjecture that `δ = log R∞` is non-elementary.

This is the **conditional-core pattern**: formalize the finitary structural core
cleanly, take the heavy analysis as explicit labelled hypotheses.

## Reproduce

Toolchain is pinned: `lean-toolchain` = `leanprover/lean4:v4.30.0`, Mathlib `rev =
v4.30.0` (`lakefile.toml`, `lake-manifest.json`).

```sh
lake exe cache get      # fetch prebuilt Mathlib oleans
lake build              # builds PcfContinuant (zero warnings/errors)
lake env lean Check.lean   # prints the twelve axiom cones above
```

## License

Apache-2.0 (Lean/Mathlib-adjacent code). See `LICENSE`.
