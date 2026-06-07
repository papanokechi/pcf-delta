/-
Copyright (c) 2026 papanokechi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: papanokechi
-/
import PcfContinuant.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite-window cluster closed form `σ₂` (PROVEN)

This upgrades the `σ₂` cluster closed form of `delta_characterization` Appendix A
(`Proposition prop:sigma`, the inclusion–exclusion derivation) from STRUCTURAL to a
machine-checked, **fully finitary** identity.

Over a finite window `[m, M]` with weights `u : ℕ → ℝ`, the *cluster sum* `σ₂`
runs over pairs with **no two consecutive** indices, while the *elementary* sum
`e₂` runs over all pairs.  We use the equivalent ordered-pair encodings (the same
combinations the verification scripts brute-force):

* `e₂ = ∑_{i<j} u_i u_j`,  `σ₂ = ∑_{i+2≤j} u_i u_j`,
  and the adjacency sum `a₁ = ∑_{j=i+1} u_i u_j`.

`sigma2win_eq` proves `σ₂ = e₂ − a₁` by finite `Finset` algebra with no analytic
input (so the axiom cone is clean): every ordered pair `i<j` is either
non-consecutive (`j ≥ i+2`, counted by `σ₂`) or consecutive (`j = i+1`, counted by
`a₁`).

The companion `σ₃` closed form (`σ₃ = e₃ − a₁p₁ + c + t`, Appendix A) needs the
full inclusion–exclusion reindexing (runs counted twice) and remains STRUCTURAL /
numerically VERIFIED for now; its Lean formalization is the next increment.  The
Newton identities `e₂ = ½(p₁²−p₂)`, `e₃ = ⅙(p₁³−3p₁p₂+2p₃)` are the standard
*unrestricted* symmetric-function step and are likewise left STRUCTURAL.
-/

namespace PcfContinuant

open Finset

variable (u : ℕ → ℝ) (m M : ℕ)

/-- `e₂` over the window `[m,M]`: sum of `u_i u_j` over ordered pairs `i < j`. -/
def e2win : ℝ := ∑ i ∈ Icc m M, ∑ j ∈ Icc m M, if i < j then u i * u j else 0

/-- `σ₂` over the window `[m,M]`: sum over **non-consecutive** ordered pairs
(`j ≥ i+2`). -/
def sigma2win : ℝ := ∑ i ∈ Icc m M, ∑ j ∈ Icc m M, if i + 2 ≤ j then u i * u j else 0

/-- `a₁`, the adjacency sum over the window: consecutive pairs `j = i+1`. -/
def a1win : ℝ := ∑ i ∈ Icc m M, ∑ j ∈ Icc m M, if j = i + 1 then u i * u j else 0

/-- **`σ₂ = e₂ − a₁` (finite window).**  Every unordered pair is either
non-consecutive (counted by `σ₂`) or consecutive (counted by `a₁`). -/
theorem sigma2win_eq : sigma2win u m M = e2win u m M - a1win u m M := by
  rw [eq_sub_iff_add_eq, sigma2win, a1win, e2win, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hc : i < j
  · rcases Nat.lt_or_ge (i + 1) j with h2 | h2
    · rw [if_pos (show i + 2 ≤ j by omega), if_neg (show j ≠ i + 1 by omega),
        if_pos hc]; ring
    · rw [if_neg (show ¬ i + 2 ≤ j by omega), if_pos (show j = i + 1 by omega),
        if_pos hc]; ring
  · rw [if_neg (show ¬ i + 2 ≤ j by omega), if_neg (show j ≠ i + 1 by omega),
      if_neg hc]; ring

end PcfContinuant
