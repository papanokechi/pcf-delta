/-
Copyright (c) 2026 papanokechi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: papanokechi
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Topic 3 — Two-sided cluster-partial-sum enclosure of `R_inf` (PROVEN)

A rigorously PROVEN finitary two-sided enclosure of `R_inf` from the cluster
partial sums, conditional on exactly two clearly-labelled analytic hypotheses:

* `(H1)`  `HasSum σ R_inf`        — the cluster expansion converges to `R_inf`.
* `(H2)`  `∀ k, 0 ≤ σ k ∧ σ k ≤ S ^ k`  — nonnegativity and the per-cluster tail bound.

Everything else (the finite-sum / geometric-tail inequality algebra) is PROVEN here.

`(H1)` and `(H2)` are taken as HYPOTHESES of every theorem below; they are NOT
proved here (that is the separate, harder convergence theory). The results are
therefore **enclosures PROVEN conditional on `(H1)`, `(H2)`** — the conditions are
spelled out in each statement and are never silently dropped.

Main result (`Rinf_enclosure`): for `0 ≤ S < 1`,
`L_m ≤ R_inf ≤ L_m + S ^ (m+1) / (1 - S)`,
where `L_m = ∑_{k=0}^m σ_k` is the `m`-th cluster partial sum.

The lower bound is monotonicity of partial sums of a nonnegative summable series;
the upper bound is the closed-form geometric tail `∑_{k≥m+1} S^k = S^{m+1}/(1-S)`.
-/

namespace PcfContinuant.Topic3

open scoped BigOperators

/-- The `m`-th cluster partial sum `L_m = ∑_{k=0}^m σ_k`. -/
noncomputable def clusterPartial (sigma : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), sigma k

/-- The closed-form geometric tail bound `S^{m+1} / (1 - S)`. -/
noncomputable def geomTail (S : ℝ) (m : ℕ) : ℝ :=
  S ^ (m + 1) / (1 - S)

/-- The geometric tail `∑_{i} S^{i+m+1}` evaluates to `geomTail S m = S^{m+1}/(1-S)`.
This is pure geometric-series algebra; it uses no hypothesis on `σ`. -/
theorem tsum_geomTail (S : ℝ) (hS0 : 0 ≤ S) (hS1 : S < 1) (m : ℕ) :
    ∑' i : ℕ, S ^ (i + (m + 1)) = geomTail S m := by
  have hfun : (fun i : ℕ => S ^ (i + (m + 1))) = (fun i : ℕ => S ^ (m + 1) * S ^ i) := by
    funext i; rw [pow_add]; ring
  rw [hfun, tsum_mul_left, tsum_geometric_of_lt_one hS0 hS1, geomTail, div_eq_mul_inv]

/-- **Two-sided enclosure of `R_inf`, PROVEN conditional on `(H1)`, `(H2)`.**

Given `0 ≤ S < 1`, the cluster expansion `(H1) HasSum σ R_inf`, and the per-cluster
bounds `(H2) 0 ≤ σ k ≤ S^k`, the `m`-th cluster partial sum brackets `R_inf`:

  `L_m ≤ R_inf ≤ L_m + S^{m+1}/(1-S)`. -/
theorem Rinf_enclosure {sigma : ℕ → ℝ} {S R_inf : ℝ}
    (hS0 : 0 ≤ S) (hS1 : S < 1)
    (H1 : HasSum sigma R_inf)
    (H2 : ∀ k, 0 ≤ sigma k ∧ sigma k ≤ S ^ k)
    (m : ℕ) :
    clusterPartial sigma m ≤ R_inf ∧
      R_inf ≤ clusterPartial sigma m + geomTail S m := by
  have hsummable : Summable sigma := H1.summable
  -- Lower bound: partial sum of a nonnegative summable series is ≤ its total.
  have hlow : clusterPartial sigma m ≤ R_inf := by
    have := sum_le_hasSum (Finset.range (m + 1)) (fun i _ => (H2 i).1) H1
    simpa [clusterPartial] using this
  -- Split `R_inf` into partial sum plus tail.
  have hsplit := hsummable.sum_add_tsum_nat_add (m + 1)
  rw [H1.tsum_eq] at hsplit
  have hR : R_inf = clusterPartial sigma m + ∑' i : ℕ, sigma (i + (m + 1)) := by
    simpa [clusterPartial] using hsplit.symm
  -- Bound the tail term-by-term by the geometric tail, then evaluate it.
  have hf_sum : Summable (fun i : ℕ => sigma (i + (m + 1))) :=
    (summable_nat_add_iff (m + 1)).mpr hsummable
  have hg_sum : Summable (fun i : ℕ => S ^ (i + (m + 1))) :=
    (summable_nat_add_iff (m + 1)).mpr (summable_geometric_of_lt_one hS0 hS1)
  have hcmp : ∑' i : ℕ, sigma (i + (m + 1)) ≤ ∑' i : ℕ, S ^ (i + (m + 1)) :=
    hf_sum.tsum_le_tsum (fun i => (H2 (i + (m + 1))).2) hg_sum
  have htail : ∑' i : ℕ, sigma (i + (m + 1)) ≤ geomTail S m := by
    rw [tsum_geomTail S hS0 hS1 m] at hcmp; exact hcmp
  have hhigh : R_inf ≤ clusterPartial sigma m + geomTail S m := by
    rw [hR]; linarith [htail]
  exact ⟨hlow, hhigh⟩

/-- **Two-sided enclosure of `δ = log R_inf`, PROVEN conditional on `(H1)`, `(H2)`.**

Taking logarithms of `Rinf_enclosure` (valid since `log` is monotone on `(0, ∞)`),
under the same hypotheses plus the structural positivity `0 < L_m` of the partial
sum, the cluster partial sum brackets `δ = log R_inf`:

  `log L_m ≤ δ ≤ log (L_m + S^{m+1}/(1-S))`.

This is the bracket that tightens the paper's certified numerics. The positivity
`hLpos : 0 < L_m` is a clearly-labelled structural side condition (it holds e.g.
when `σ_0 > 0`); it is NOT one of the two analytic facts `(H1)`, `(H2)`. -/
theorem delta_enclosure {sigma : ℕ → ℝ} {S R_inf : ℝ}
    (hS0 : 0 ≤ S) (hS1 : S < 1)
    (H1 : HasSum sigma R_inf)
    (H2 : ∀ k, 0 ≤ sigma k ∧ sigma k ≤ S ^ k)
    (m : ℕ) (hLpos : 0 < clusterPartial sigma m) :
    Real.log (clusterPartial sigma m) ≤ Real.log R_inf ∧
      Real.log R_inf ≤ Real.log (clusterPartial sigma m + geomTail S m) := by
  obtain ⟨hlo, hhi⟩ := Rinf_enclosure hS0 hS1 H1 H2 m
  refine ⟨Real.log_le_log hLpos hlo, Real.log_le_log (lt_of_lt_of_le hLpos hlo) hhi⟩

/-! ### Sanity check

A lightweight check that the enclosure is non-vacuous: the upper end is at least the
lower end whenever `0 ≤ S < 1` (the geometric tail is nonnegative). Independent of `σ`. -/
theorem enclosure_nonvacuous {sigma : ℕ → ℝ} {S : ℝ}
    (hS0 : 0 ≤ S) (hS1 : S < 1) (m : ℕ) :
    clusterPartial sigma m ≤ clusterPartial sigma m + geomTail S m := by
  have h1S : 0 < 1 - S := by linarith
  have : 0 ≤ geomTail S m := by
    rw [geomTail]; positivity
  linarith

/-! ### `m = 1` reproduces the paper's S-only bracket (structural, not coincidental)

The reviewer asks that the `m = 1` non-improvement be a *proved structural identity*
rather than an observed numerical coincidence.  With the cluster normalisation
`σ₀ = 1` and `σ₁ = S` (both structural facts of the cluster expansion, not analytic
hypotheses), the `m = 1` enclosure of `δ = log R_inf` collapses *exactly* to the
paper's S-only bracket `[log (1 + S), log (1 - S)⁻¹] = [log (1 + S), -log (1 - S)]`.
So the paper's bracket *is* the `m = 1` instance of `delta_enclosure`; genuine
tightening only begins at `m ≥ 2`. -/

/-- `L₁ = σ₀ + σ₁`; with the cluster normalisation `σ₀ = 1` this is `1 + σ₁`. -/
theorem clusterPartial_one_eq {sigma : ℕ → ℝ} (h0 : sigma 0 = 1) :
    clusterPartial sigma 1 = 1 + sigma 1 := by
  rw [clusterPartial, Finset.sum_range_succ, Finset.sum_range_one, h0]

/-- **`m = 1` reproduces the paper's S-only endpoints, exactly.**
With `σ₀ = 1` and `σ₁ = S`, the lower end is `L₁ = 1 + S` and the upper end
`L₁ + S²/(1-S)` collapses to `(1 - S)⁻¹`.  This is an algebraic identity, not a
numerical coincidence. -/
theorem m1_recovers_S_bracket {sigma : ℕ → ℝ} {S : ℝ}
    (hS1 : S < 1) (h0 : sigma 0 = 1) (h1 : sigma 1 = S) :
    clusterPartial sigma 1 = 1 + S ∧
      clusterPartial sigma 1 + geomTail S 1 = (1 - S)⁻¹ := by
  have hne : (1 - S) ≠ 0 := ne_of_gt (by linarith)
  refine ⟨?_, ?_⟩
  · rw [clusterPartial_one_eq h0, h1]
  · rw [clusterPartial_one_eq h0, h1, geomTail]
    field_simp
    ring

/-- **The `m = 1` enclosure of `δ` is exactly the paper's S-only bracket.**
Combining `delta_enclosure` at `m = 1` with `m1_recovers_S_bracket` gives
`log (1 + S) ≤ δ ≤ log (1 - S)⁻¹`, machine-checked end-to-end (positivity of `L₁`
is derived from `σ₀ = 1` and `0 ≤ S`, not assumed). -/
theorem m1_delta_eq_S_bracket {sigma : ℕ → ℝ} {S R_inf : ℝ}
    (hS0 : 0 ≤ S) (hS1 : S < 1)
    (H1 : HasSum sigma R_inf)
    (H2 : ∀ k, 0 ≤ sigma k ∧ sigma k ≤ S ^ k)
    (h0 : sigma 0 = 1) (h1 : sigma 1 = S) :
    Real.log (1 + S) ≤ Real.log R_inf ∧
      Real.log R_inf ≤ Real.log ((1 - S)⁻¹) := by
  obtain ⟨hb1, hb2⟩ := m1_recovers_S_bracket hS1 h0 h1
  have hLpos : 0 < clusterPartial sigma 1 := by rw [hb1]; linarith
  obtain ⟨hlo, hhi⟩ := delta_enclosure hS0 hS1 H1 H2 1 hLpos
  rw [hb1] at hlo
  rw [hb2] at hhi
  exact ⟨hlo, hhi⟩

/-! ### The `(H2)` boundary at `k = 0`

Hypothesis `(H2)` at `k = 0` reads `0 ≤ σ₀ ≤ S⁰ = 1`, i.e. it *forces* `σ₀ ≤ 1`.
The certified triple sits on this boundary with `σ₀ = 1` exactly, so `(H2)` does no
work at `k = 0` — its real content is the tail `k ≥ 1`.  Any discharge of `(H2)` for
a concrete `bₖ`-family must therefore verify the `k = 0` case (`σ₀ ≤ 1`), not only
the tail; were the cluster expansion ever to yield `σ₀ > 1`, `(H2)` would fail and
the entire enclosure would be vacuous. -/

/-- `(H2)` at `k = 0` forces `σ₀ ≤ 1`, since `S⁰ = 1`. -/
theorem H2_zero_forces_sigma0_le_one {sigma : ℕ → ℝ} {S : ℝ}
    (H2 : ∀ k, 0 ≤ sigma k ∧ sigma k ≤ S ^ k) :
    sigma 0 ≤ 1 := by
  have h := (H2 0).2
  simpa using h

end PcfContinuant.Topic3
