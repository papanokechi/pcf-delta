/-
Copyright (c) 2026 papanokechi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: papanokechi
-/
import PcfContinuant.Basic
import Mathlib.Algebra.Order.Field.Basic

/-!
# The closed-form bracket `1 + S ≤ R∞ ≤ 1/(1 - S)` (conditional core, PROVEN)

This upgrades the bracket of `delta_characterization.md` (item 4) from STRUCTURAL/VERIFIED
to a machine-checked result, in the project's *conditional-core* style: the finitary
algebra/order is proved unconditionally, and the single analytic input — convergence of
`Σ uₙ` — enters only as the hypotheses `BddAbove (Set.range (psum u))` and `S < 1`, where
`S := ⨆ n, psum u n`.

`psum u n = Σ_{k=2}^n u k` is the partial sum `S_n` (mirroring the `rseq`/`rmaj` indexing
of `Basic.lean`).  The two load-bearing finitary facts, both checked numerically/exactly in
`bracket_gate.py` before formalizing, are:

* `rseq_ge_one_add_psum` — `1 + S_n ≤ Rₙ` (lower sum-majorant), and
* `rmaj_mul_one_sub_psum_le_one` — `(∏_{k=2}^n (1+uₖ))·(1 - S_n) ≤ 1`, i.e. the product
  majorant is `≤ 1/(1 - S_n)`; the step rests on the exact identity
  `(1 - S_n) - (1 + u)(1 - S_n - u) = u·S_n + u² ≥ 0`.

These are combined with the existing `rseq ≤ rmaj` and monotone-bounded convergence
(`rseq_tendsto_of_rmaj_bddAbove`) to bracket the limit `R∞ = ⨆ n, rseq u n`.
-/

namespace PcfContinuant

open Filter Topology

/-- Partial sum `S_n = Σ_{k=2}^n u k`, mirroring the `rseq`/`rmaj` indexing. -/
def psum (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | (n + 2) => psum u (n + 1) + u (n + 2)

/-- The partial sums are nonnegative when `u ≥ 0`. -/
theorem psum_nonneg (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (n : ℕ) : 0 ≤ psum u n := by
  induction n with
  | zero => simp [psum]
  | succ k ih =>
      match k with
      | 0 => simp [psum]
      | (j + 1) =>
          simp only [psum]
          have := hu (j + 1 + 1)
          linarith [ih]

/-! ## Lower finitary bound: `1 + S_n ≤ Rₙ` -/

/-- The lower sum-majorant: `Rₙ ≥ 1 + S_n` (carrying two consecutive values). -/
theorem rseq_ge_one_add_psum (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) :
    ∀ n, 1 + psum u n ≤ rseq u n ∧ 1 + psum u (n + 1) ≤ rseq u (n + 1) := by
  intro n
  induction n with
  | zero => exact ⟨by simp [psum, rseq], by simp [psum, rseq]⟩
  | succ k ih =>
      obtain ⟨_, hk1⟩ := ih
      refine ⟨hk1, ?_⟩
      change 1 + psum u (k + 2) ≤ rseq u (k + 2)
      have hr0 : (1 : ℝ) ≤ rseq u k := (rseq_ge_one u hu k).1
      have huk : 0 ≤ u (k + 2) := hu (k + 2)
      have hmul : u (k + 2) ≤ u (k + 2) * rseq u k := by nlinarith [hr0, huk]
      simp only [psum, rseq]
      linarith [hk1, hmul]

/-! ## Upper finitary bound: `(∏(1+uₖ))·(1 - S_n) ≤ 1` -/

/-- The product majorant satisfies `rmaj u n · (1 - S_n) ≤ 1`, i.e. `rmaj u n ≤ 1/(1 - S_n)`
when `S_n < 1`.  The induction step uses the exact identity
`(1 + v)(1 - a - v) = (1 - a) - (a·v + v²)` with `a = S_n`, `v = u (n+1)`. -/
theorem rmaj_mul_one_sub_psum_le_one (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) :
    ∀ n, rmaj u n * (1 - psum u n) ≤ 1 ∧ rmaj u (n + 1) * (1 - psum u (n + 1)) ≤ 1 := by
  intro n
  induction n with
  | zero => exact ⟨by simp [rmaj, psum], by simp [rmaj, psum]⟩
  | succ k ih =>
      obtain ⟨_, hk1⟩ := ih
      refine ⟨hk1, ?_⟩
      change rmaj u (k + 2) * (1 - psum u (k + 2)) ≤ 1
      have hrm : (1 : ℝ) ≤ rmaj u (k + 1) := (rmaj_ge_one u hu k).2
      have hrm0 : (0 : ℝ) ≤ rmaj u (k + 1) := le_trans zero_le_one hrm
      have hps : 0 ≤ psum u (k + 1) := psum_nonneg u hu (k + 1)
      have huk : 0 ≤ u (k + 2) := hu (k + 2)
      simp only [rmaj, psum]
      nlinarith [hk1, mul_nonneg hrm0 (mul_nonneg hps huk),
                 mul_nonneg hrm0 (mul_nonneg huk huk)]

/-! ## The bracket on the limit `R∞ = ⨆ n, rseq u n` -/

/-- **The closed-form bracket (conditional core).** With `u ≥ 0`, the partial sums bounded
above (convergence of `Σ uₙ`) and `S := ⨆ n, psum u n < 1`, the scaled limit
`R∞ = ⨆ n, rseq u n` satisfies `1 + S ≤ R∞ ≤ 1/(1 - S)`. -/
theorem rinf_bracket (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hpb : BddAbove (Set.range (psum u))) (hS1 : (⨆ n, psum u n) < 1) :
    1 + (⨆ n, psum u n) ≤ (⨆ n, rseq u n) ∧
      (⨆ n, rseq u n) ≤ 1 / (1 - (⨆ n, psum u n)) := by
  set S := ⨆ n, psum u n with hSdef
  have hps_le : ∀ n, psum u n ≤ S := fun n => le_ciSup hpb n
  have hSpos : 0 < 1 - S := by linarith
  -- each product majorant is ≤ 1/(1 - S)
  have hrmaj_le : ∀ n, rmaj u n ≤ 1 / (1 - S) := by
    intro n
    have hprod : rmaj u n * (1 - psum u n) ≤ 1 := (rmaj_mul_one_sub_psum_le_one u hu n).1
    have hrm0 : 0 ≤ rmaj u n := le_trans zero_le_one (rmaj_ge_one u hu n).1
    have hpsS : psum u n ≤ S := hps_le n
    have hmul : rmaj u n * (1 - S) ≤ 1 := by nlinarith [hprod, hrm0, hpsS]
    rw [le_div_iff₀ hSpos]
    linarith [hmul]
  have hrmaj_bdd : BddAbove (Set.range (rmaj u)) :=
    ⟨1 / (1 - S), by rintro _ ⟨n, rfl⟩; exact hrmaj_le n⟩
  have hrseq_bdd : BddAbove (Set.range (rseq u)) := rseq_bddAbove_of_rmaj u hu hrmaj_bdd
  refine ⟨?_, ?_⟩
  · -- lower:  1 + S ≤ ⨆ rseq
    have hlow : ∀ n, psum u n ≤ (⨆ k, rseq u k) - 1 := by
      intro n
      have h1 : 1 + psum u n ≤ rseq u n := (rseq_ge_one_add_psum u hu n).1
      have h2 : rseq u n ≤ ⨆ k, rseq u k := le_ciSup hrseq_bdd n
      linarith
    have hSle : S ≤ (⨆ k, rseq u k) - 1 := ciSup_le hlow
    linarith
  · -- upper:  ⨆ rseq ≤ 1/(1 - S)
    apply ciSup_le
    intro n
    exact le_trans (rseq_le_rmaj u hu n).1 (hrmaj_le n)

/-- The limit `R∞ = ⨆ n, rseq u n` exists (as the monotone-bounded limit) under the same
hypotheses, so the bracket of `rinf_bracket` is a bracket on the genuine limit. -/
theorem rseq_tendsto_under_psum_bdd (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hpb : BddAbove (Set.range (psum u))) (hS1 : (⨆ n, psum u n) < 1) :
    Tendsto (rseq u) atTop (𝓝 (⨆ n, rseq u n)) := by
  set S := ⨆ n, psum u n with hSdef
  have hSpos : 0 < 1 - S := by linarith
  have hrmaj_bdd : BddAbove (Set.range (rmaj u)) := by
    refine ⟨1 / (1 - S), ?_⟩
    rintro _ ⟨n, rfl⟩
    have hprod : rmaj u n * (1 - psum u n) ≤ 1 := (rmaj_mul_one_sub_psum_le_one u hu n).1
    have hrm0 : 0 ≤ rmaj u n := le_trans zero_le_one (rmaj_ge_one u hu n).1
    have hpsS : psum u n ≤ S := le_ciSup hpb n
    have hmul : rmaj u n * (1 - S) ≤ 1 := by nlinarith [hprod, hrm0, hpsS]
    rw [le_div_iff₀ hSpos]
    linarith [hmul]
  exact rseq_tendsto_of_rmaj_bddAbove u hu hrmaj_bdd

end PcfContinuant
