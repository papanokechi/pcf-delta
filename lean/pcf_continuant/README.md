# pcf_continuant — finitary core for the quadratic-PCF growth law

A small, machine-checked Lean 4 / Mathlib formalization of the **finitary algebraic
and order core** underlying the growth law of the quadratic polynomial continued
fraction

```
V(A,B,C) = 1 + K_{n≥1} 1/(A n² + B n + C),   A,B,C ≥ 1.
```

Its convergent numerators `p` and denominators `q` satisfy the same second-order
recurrence `s (n+2) = b (n+2) · s (n+1) + s n`, with `b n = A n² + B n + C`. This
repo formalizes the finitary structural facts that the analytic growth-constant analysis
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
| `psum`            | partial sum `S_n = Σ_{k=2}^n uₖ` (mirrors the `rseq`/`rmaj` indexing)                          | `[propext, Classical.choice, Quot.sound]` |
| `psum_nonneg`     | `S_n ≥ 0` for `u ≥ 0`                                                                          | `[propext, Classical.choice, Quot.sound]` |
| `rseq_ge_one_add_psum` | **the finitary lower bound** `1 + S_n ≤ Rₙ`                                              | `[propext, Classical.choice, Quot.sound]` |
| `rmaj_mul_one_sub_psum_le_one` | **the finitary upper bound** `(∏_{k=2}^n(1+uₖ))·(1 − S_n) ≤ 1` (exact identity `(1−S_n)−(1+u)(1−S_n−u)=u·S_n+u²≥0`) | `[propext, Classical.choice, Quot.sound]` |
| `rinf_bracket`    | **the closed-form bracket** `1 + S ≤ R∞ ≤ 1/(1 − S)` (conditional on `Σ uₙ` bounded above and `S = ⨆ₙ S_n < 1`) | `[propext, Classical.choice, Quot.sound]` |
| `rseq_tendsto_under_psum_bdd` | `Rₙ → R∞` under the same `psum`-boundedness/`S<1` hypotheses                     | `[propext, Classical.choice, Quot.sound]` |
| `indepPoly_eq_rseq` | **the independence-polynomial identity** `Rₙ = ∑_{T ⊆ {2,…,n}, no two consecutive} ∏_{i∈T} uᵢ` (weighted independence polynomial of the path graph), unconditional | `[propext, Classical.choice, Quot.sound]` |
| `indepPoly_succ_succ` | the deletion–contraction recurrence `indepPoly (n+2) = indepPoly (n+1) + u(n+2)·indepPoly n` | `[propext, Classical.choice, Quot.sound]` |
| `sum_filter_mem_top` | subsets containing the top vertex `n+2` sum to `u(n+2)·indepPoly n` (the contraction half, via `sum_bij'`) | `[propext, Classical.choice, Quot.sound]` |
| `filter_not_mem_top` | subsets avoiding `n+2` are exactly the no-two-consecutive subsets of `{2,…,n+1}` (the deletion half) | `[propext, Classical.choice, Quot.sound]` |
| `indepPoly_zero`, `indepPoly_one`, `NoTwoConsec.erase` | base cases and the erase-stability of `NoTwoConsec`  | `[propext, Classical.choice, Quot.sound]` |
| `sigma2win_eq`    | **finite-window σ₂ closed-form core** `σ₂ = e₂ − a₁` over any window `[m,M]` (no-two-consecutive pair sum = all pairs − consecutive pairs), unconditional | `[propext, Classical.choice, Quot.sound]` |

`casoratian_step`, `casoratian_eq`, `pq_casoratian` are stated over an arbitrary
`CommRing`. The `rseq_*`/`rmaj_*` results are specialized to `ℝ` (the application
domain). Together these are the exact **Casoratian identity** (item 2 of
`delta_characterization.md`), the **monotone, bounded-below** structure, the
**limit existence** `Rₙ → R∞` (item 3) via Mathlib's `tendsto_atTop_ciSup`, and now the
**closed-form two-sided bracket** `1 + S ≤ R∞ ≤ 1/(1 − S)` (item 4), all reduced to
the single finitary hypothesis that the partial sums `S_n = Σ uₖ` are bounded above
(equivalently `Σ uₙ < ∞`) together with `S = ⨆ₙ S_n < 1`.

`Indep.lean` and `Sigma.lean` add two **unconditional, fully finitary** results
(no analytic hypotheses at all), promoting parts of the note's STRUCTURAL list to
PROVEN. `indepPoly_eq_rseq` is the **independence-polynomial identity** (item: `Rₙ`
as a weighted independence polynomial of the path graph): `Rₙ` equals the sum over
no-two-consecutive subsets `T ⊆ {2,…,n}` of `∏_{i∈T} uᵢ`, proved by the
deletion–contraction split at the top vertex `n+2`. `sigma2win_eq` is the
**finite-window inclusion–exclusion core of the σ₂ cluster closed form**,
`σ₂ = e₂ − a₁`: over any window `[m,M]` the no-two-consecutive pair sum equals the
unrestricted pair sum minus the adjacent-pair sum. The Newton reduction
`e₂ = ½(p₁² − p₂)` and the σ₃ closed form `σ₃ = e₃ − a₁p₁ + c + t` remain STRUCTURAL
/ numerically VERIFIED for now (the σ₃ formalization — the runs-counted-twice
reindexing of Appendix A — is the next increment).

## What is OUT OF SCOPE (deliberately not formalized — labelled hypotheses)

These are analytic and remain hand-proved / numerically verified elsewhere; they are
**not** claimed here:

* the boundedness hypothesis itself — that `Σ uₙ < ∞` (equivalently the partial sums
  `S_n = Σ uₖ` are bounded above) and the inequality `S < 1`; the *value* of the limit;
* the closed-form digamma residue for `S` (the bracket `log(1+S) ≤ δ ≤ −log(1−S)` for
  `δ = log R∞` then follows from `rinf_bracket` by monotonicity of `log`);
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
lake env lean Check.lean   # prints the twenty-six axiom cones above
```

## License

Apache-2.0 (Lean/Mathlib-adjacent code). See `LICENSE`.
