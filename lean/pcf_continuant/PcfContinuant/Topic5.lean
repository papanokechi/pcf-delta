/-
Copyright (c) 2026 papanokechi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: papanokechi
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp

/-!
# Topic 5 — Exact weighted partial-fraction telescoping for the `B = 0` family (PROVEN)

For the quadratic-PCF `B = 0` family the relevant denominator sequence is
`b_m = A m² + C`, and the *weighted* increment `A (2m+1) = b_{m+1} - b_m`.  The key
finitary fact is a **partial-fraction / telescoping identity**, proven here
unconditionally over an arbitrary field:

  `∑_{m=1}^{N-1} A(2m+1) / (b_m b_{m+1}) = 1/(A+C) − 1/(A N² + C)`.

This is the honest, fully PROVEN core.  The *unweighted* truncation
`∑ 1/(b_{m-1} b_m)` has **no** closed form rational in `N` (Gosper's algorithm
returns no rational telescoper — a verified negative), and the unweighted limit is a
`coth`/digamma expression that needs `Real` special functions; that closed form is
therefore left out of scope (numerically verified only), exactly as the
conditional-core discipline requires.

We additionally record, over `ℝ`, that the weighted infinite sum equals the rational
`1/(A+C)` **conditional on** the single labelled analytic hypothesis `1/b_N → 0`
(`weighted_sum_tendsto`).

* `partialFraction`        — `A(2m+1)/(b_m b_{m+1}) = 1/b_m − 1/b_{m+1}` (field, `b_m,b_{m+1} ≠ 0`).
* `sum_Ico_telescope`      — generic telescoping `∑_{Ico 1 N} (g m − g (m+1)) = g 1 − g N`.
* `weighted_telescope`     — termwise rewrite of the weighted sum to a telescoping sum.
* `weighted_telescope_value` — the closed finite value `1/(A+C) − 1/(A N² + C)` (PROVEN).
* `weighted_sum_tendsto`   — the `ℝ` limit `→ 1/(A+C)`, conditional on `1/b_N → 0`.
-/

namespace PcfContinuant.Topic5

open Finset Filter Topology

variable {K : Type*} [Field K]

/-- The `B = 0` denominator sequence `b_m = A m² + C`.  Note `b_1 = A + C`. -/
def b (A C : K) (m : ℕ) : K := A * (m : K) ^ 2 + C

/-- The unweighted term `1 / (b_m b_{m+1})`. -/
noncomputable def term (A C : K) (m : ℕ) : K := (b A C m * b A C (m + 1))⁻¹

/-- **Partial fraction.** The weighted term collapses to a difference of reciprocals,
because the weight `A (2m+1)` is exactly the increment `b_{m+1} − b_m`. -/
theorem partialFraction (A C : K) (m : ℕ)
    (h1 : b A C m ≠ 0) (h2 : b A C (m + 1) ≠ 0) :
    (A * (2 * (m : K) + 1)) * term A C m = (b A C m)⁻¹ - (b A C (m + 1))⁻¹ := by
  have hdiff : b A C (m + 1) - b A C m = A * (2 * (m : K) + 1) := by
    simp only [b]; push_cast; ring
  rw [term, inv_sub_inv h1 h2, hdiff, div_eq_mul_inv]

/-- **Generic telescoping** over `Ico 1 N`: `∑ (g m − g (m+1)) = g 1 − g N`. -/
theorem sum_Ico_telescope (g : ℕ → K) :
    ∀ N, 1 ≤ N → ∑ m ∈ Ico 1 N, (g m - g (m + 1)) = g 1 - g N := by
  intro N
  induction N with
  | zero => intro h; exact absurd h (by norm_num)
  | succ n ih =>
      intro _
      rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · subst hn0; simp
      · rw [Finset.sum_Ico_succ_top hn0, ih hn0]; ring

/-- The weighted sum equals a telescoping sum of reciprocal differences. -/
theorem weighted_telescope (A C : K) (N : ℕ)
    (hb : ∀ m, 1 ≤ m → m ≤ N → b A C m ≠ 0) :
    ∑ m ∈ Ico 1 N, (A * (2 * (m : K) + 1)) * term A C m
      = ∑ m ∈ Ico 1 N, ((b A C m)⁻¹ - (b A C (m + 1))⁻¹) := by
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [mem_Ico] at hm
  exact partialFraction A C m (hb m hm.1 (by omega)) (hb (m + 1) (by omega) (by omega))

/-- **The exact finite weighted-telescoping value (PROVEN, any field).**
`∑_{m=1}^{N-1} A(2m+1) / (b_m b_{m+1}) = 1/(A+C) − 1/(A N² + C)`. -/
theorem weighted_telescope_value (A C : K) (N : ℕ) (hN : 1 ≤ N)
    (hb : ∀ m, 1 ≤ m → m ≤ N → b A C m ≠ 0) :
    ∑ m ∈ Ico 1 N, (A * (2 * (m : K) + 1)) * term A C m
      = (A + C)⁻¹ - (A * (N : K) ^ 2 + C)⁻¹ := by
  rw [weighted_telescope A C N hb, sum_Ico_telescope (fun m => (b A C m)⁻¹) N hN]
  simp only [b, Nat.cast_one, one_pow, mul_one]

/-- **Conditional weighted-sum limit (over `ℝ`).**  Conditional on the single
labelled analytic hypothesis `Hw : 1/b_N → 0`, the weighted infinite sum converges
to the rational value `1/(A+C)`.  (`Hw` is exactly the elementary fact that
`A N² + C → ∞`; it is the only non-finitary input and is taken as a hypothesis.) -/
theorem weighted_sum_tendsto (A C : ℝ) (hb : ∀ m, 1 ≤ m → b A C m ≠ 0)
    (Hw : Tendsto (fun N : ℕ => (A * (N : ℝ) ^ 2 + C)⁻¹) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ m ∈ Ico 1 N, (A * (2 * (m : ℝ) + 1)) * term A C m)
      atTop (𝓝 ((A + C)⁻¹)) := by
  have hcongr : (fun N : ℕ => ∑ m ∈ Ico 1 N, (A * (2 * (m : ℝ) + 1)) * term A C m)
      =ᶠ[atTop] (fun N : ℕ => (A + C)⁻¹ - (A * (N : ℝ) ^ 2 + C)⁻¹) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact weighted_telescope_value A C N hN (fun m h1 _ => hb m h1)
  refine Tendsto.congr' hcongr.symm ?_
  have h2 : Tendsto (fun N : ℕ => (A + C)⁻¹ - (A * (N : ℝ) ^ 2 + C)⁻¹)
      atTop (𝓝 ((A + C)⁻¹ - 0)) := Tendsto.const_sub _ Hw
  simpa using h2

end PcfContinuant.Topic5
