/-
Copyright (c) 2026 papanokechi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: papanokechi
-/
import PcfContinuant.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite-window cluster closed form `σ₃` (PROVEN)

This upgrades the `σ₃` inclusion–exclusion closed form of `delta_characterization`
Appendix A from STRUCTURAL / numerically VERIFIED to a machine-checked, fully
finitary identity.

Over a finite window `[m, M]` with weights `u : ℕ → ℝ`, the *cluster sum* `σ₃`
runs over ordered triples with **no two consecutive** indices (`j ≥ i+2`,
`k ≥ j+2`), while `e₃` runs over all ordered triples `i<j<k`.  With

* `p₁ = ∑ u_i`,  `a₁ = ∑_{j=i+1} u_i u_j`,
* `c  = ∑_{j=i+1} u_i u_j (u_i + u_j)`  (the adjacency diagonal),
* `t  = ∑_{j=i+1, k=j+1} u_i u_j u_k`  (consecutive triples),

`sigma3win_eq` proves the Appendix-A identity

  `σ₃ = e₃ − a₁·p₁ + c + t`

by finite `Finset` algebra with **no analytic input** (clean axiom cone).  Unlike
`σ₂`, this is **not** a termwise identity: the cross term `a₁·p₁` expands into a
sum over an index *cube* whose monomials only match after the inclusion–exclusion
reindexing.  The bridge is the "bad triple" sum `B` (ordered triples carrying at
least one adjacency):

* `e₃ = σ₃ + B`                     (every ordered triple is non-adjacent or bad),
* `a₁·p₁ = B + t + c`               (the cube counts each bad triple once per
  adjacency it contains; consecutive triples carry two adjacencies, hence the
  extra `t`; the diagonal `l ∈ {i,i+1}` is `c`).

Subtracting gives the closed form.  The unrestricted Newton step
`e₃ = ⅙(p₁³ − 3p₁p₂ + 2p₃)` is the standard symmetric-function identity and is
left STRUCTURAL (it is not needed here: `e₃` is kept as the all-triples sum).

The companion finite-window check is `src/verify_sigma3_finite_window.py`
(exact rational arithmetic, residual `0` over four `bₖ`-families × windows
`{5,6,7,8}`).
-/

namespace PcfContinuant

open Finset

variable (u : ℕ → ℝ) (m M : ℕ)

/-- `p₁` over the window `[m,M]`: the degree-1 power sum. -/
def p1win : ℝ := ∑ i ∈ Icc m M, u i

/-- `e₃` over the window `[m,M]`: `∑ u_i u_j u_k` over ordered triples `i<j<k`. -/
def e3win : ℝ :=
  ∑ i ∈ Icc m M, ∑ j ∈ Icc m M, ∑ k ∈ Icc m M,
    if i < j ∧ j < k then u i * u j * u k else 0

/-- `σ₃` over the window `[m,M]`: ordered **non-consecutive** triples
(`j ≥ i+2`, `k ≥ j+2`). -/
def sigma3win : ℝ :=
  ∑ i ∈ Icc m M, ∑ j ∈ Icc m M, ∑ k ∈ Icc m M,
    if i + 2 ≤ j ∧ j + 2 ≤ k then u i * u j * u k else 0

/-- `c`, the adjacency diagonal: `∑_{j=i+1} u_i u_j (u_i + u_j)`. -/
def cwin : ℝ :=
  ∑ i ∈ Icc m M, ∑ j ∈ Icc m M, if j = i + 1 then u i * u j * (u i + u j) else 0

/-- `t`, the consecutive triples `∑_{j=i+1, k=j+1} u_i u_j u_k`. -/
def twin : ℝ :=
  ∑ i ∈ Icc m M, ∑ j ∈ Icc m M, ∑ k ∈ Icc m M,
    if j = i + 1 ∧ k = j + 1 then u i * u j * u k else 0

/-- `B`, the ordered "bad" triples: `i<j<k` carrying at least one adjacency. -/
def Bwin : ℝ :=
  ∑ i ∈ Icc m M, ∑ j ∈ Icc m M, ∑ k ∈ Icc m M,
    if i < j ∧ j < k ∧ (j = i + 1 ∨ k = j + 1) then u i * u j * u k else 0

/-- `B₁`, ordered triples with a *first-pair* adjacency (`j = i+1`, `j < k`). -/
def B1win : ℝ :=
  ∑ i ∈ Icc m M, ∑ j ∈ Icc m M, ∑ k ∈ Icc m M,
    if j = i + 1 ∧ j < k then u i * u j * u k else 0

/-- `B₂`, ordered triples with a *second-pair* adjacency (`i < j`, `k = j+1`). -/
def B2win : ℝ :=
  ∑ i ∈ Icc m M, ∑ j ∈ Icc m M, ∑ k ∈ Icc m M,
    if i < j ∧ k = j + 1 then u i * u j * u k else 0

/-- `P`, the cube expansion of `a₁·p₁`: `∑_{i,j,l} [j=i+1] u_i u_j u_l`. -/
def Pwin : ℝ :=
  ∑ i ∈ Icc m M, ∑ j ∈ Icc m M, ∑ l ∈ Icc m M,
    if j = i + 1 then u i * u j * u l else 0

/-- The per-index `l`-partition: over the window, splitting the free factor `u_l`
according to `l > i+1`, `l < i`, `l = i`, `l = i+1`. -/
theorem partition_l (i : ℕ) (hi : i ∈ Icc m M) (hi1 : i + 1 ∈ Icc m M) :
    (∑ l ∈ Icc m M, u i * u (i + 1) * u l)
      = (∑ l ∈ Icc m M, if i + 1 < l then u i * u (i + 1) * u l else 0)
        + (∑ l ∈ Icc m M, if l < i then u i * u (i + 1) * u l else 0)
        + u i * u (i + 1) * (u i + u (i + 1)) := by
  have hsplit : ∀ l, u i * u (i + 1) * u l
      = (if i + 1 < l then u i * u (i + 1) * u l else 0)
        + (if l < i then u i * u (i + 1) * u l else 0)
        + (if l = i then u i * u (i + 1) * u l else 0)
        + (if l = i + 1 then u i * u (i + 1) * u l else 0) := by
    intro l
    rcases lt_trichotomy l i with h | h | h
    · rw [if_neg (by omega), if_pos h, if_neg (by omega), if_neg (by omega)]; ring
    · rw [if_neg (by omega), if_neg (by omega), if_pos h, if_neg (by omega)]; ring
    · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h2 | h2
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]; ring
      · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring
  rw [Finset.sum_congr rfl (fun l _ => hsplit l)]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [hi, hi1, if_true]
  ring

/-- **`σ₃ = e₃ − a₁·p₁ + c + t` (finite window).**  The inclusion–exclusion closed
form of Appendix A, PROVEN by finite `Finset` algebra with a clean axiom cone. -/
theorem sigma3win_eq :
    sigma3win u m M
      = e3win u m M - a1win u m M * p1win u m M + cwin u m M + twin u m M := by
  -- (L1) every ordered triple is either non-adjacent (`σ₃`) or bad (`B`).
  have hL1 : e3win u m M = sigma3win u m M + Bwin u m M := by
    simp only [e3win, sigma3win, Bwin, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : i < j ∧ j < k
    · obtain ⟨hij, hjk⟩ := h1
      by_cases h2 : i + 2 ≤ j ∧ j + 2 ≤ k
      · rw [if_pos ⟨hij, hjk⟩, if_pos h2, if_neg (by rintro ⟨_, _, h | h⟩ <;> omega)]; ring
      · rw [if_pos ⟨hij, hjk⟩, if_neg h2, if_pos ⟨hij, hjk, by omega⟩]; ring
    · rw [if_neg h1, if_neg (by rintro ⟨h, h'⟩; exact h1 ⟨by omega, by omega⟩),
        if_neg (by rintro ⟨h, h', _⟩; exact h1 ⟨h, h'⟩)]; ring
  -- (L2a) the cube expansion of `a₁·p₁`.
  have hP : a1win u m M * p1win u m M = Pwin u m M := by
    simp only [a1win, p1win, Pwin]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs with h <;> ring
  -- (L2b) collapse `P`, `B₁`, `c`, `B₂` to a common `i`-indexed form, then apply
  -- the per-index partition.
  have hPe : Pwin u m M = cwin u m M + B1win u m M + B2win u m M := by
    have e1 : Pwin u m M
        = ∑ i ∈ Icc m M, (if i + 1 ∈ Icc m M then
            ∑ l ∈ Icc m M, u i * u (i + 1) * u l else 0) := by
      simp only [Pwin, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq']
    have eB1 : B1win u m M
        = ∑ i ∈ Icc m M, (if i + 1 ∈ Icc m M then
            ∑ l ∈ Icc m M, (if i + 1 < l then u i * u (i + 1) * u l else 0) else 0) := by
      simp only [B1win, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
        Finset.sum_ite_eq']
    have ec : cwin u m M
        = ∑ i ∈ Icc m M, (if i + 1 ∈ Icc m M then
            u i * u (i + 1) * (u i + u (i + 1)) else 0) := by
      simp only [cwin, Finset.sum_ite_eq']
    have eB2 : B2win u m M
        = ∑ i ∈ Icc m M, (if i + 1 ∈ Icc m M then
            ∑ l ∈ Icc m M, (if l < i then u i * u (i + 1) * u l else 0) else 0) := by
      have h0 : B2win u m M
          = ∑ a ∈ Icc m M, ∑ b ∈ Icc m M,
              (if a < b ∧ b + 1 ∈ Icc m M then u a * u b * u (b + 1) else 0) := by
        simp only [B2win, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
          Finset.sum_ite_eq']
      rw [h0, Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb1 : b + 1 ∈ Icc m M
      · simp only [hb1, and_true, if_true]
        refine Finset.sum_congr rfl fun a _ => ?_
        split_ifs with h <;> ring
      · simp only [hb1, and_false, if_false, Finset.sum_const_zero]
    rw [e1, ec, eB1, eB2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases hi1 : i + 1 ∈ Icc m M
    · simp only [hi1, if_true]
      rw [partition_l u m M i hi hi1]; ring
    · simp only [hi1, if_false]; ring
  -- (L2c) reassemble the bad triples: `B₁ + B₂ = B + t`.
  have hBe : B1win u m M + B2win u m M = Bwin u m M + twin u m M := by
    simp only [B1win, B2win, Bwin, twin, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hb1 : j = i + 1 ∧ j < k
    · by_cases hb2 : i < j ∧ k = j + 1
      · rw [if_pos hb1, if_pos hb2, if_pos ⟨by omega, by omega, by omega⟩,
          if_pos ⟨by omega, by omega⟩]
      · rw [if_pos hb1, if_neg hb2, if_pos ⟨by omega, by omega, by omega⟩,
          if_neg (by rintro ⟨h, h'⟩; exact hb2 ⟨by omega, h'⟩)]
    · by_cases hb2 : i < j ∧ k = j + 1
      · rw [if_neg hb1, if_pos hb2, if_pos ⟨by omega, by omega, by omega⟩,
          if_neg (by rintro ⟨h, h'⟩; exact hb1 ⟨h, by omega⟩)]; ring
      · rw [if_neg hb1, if_neg hb2,
          if_neg (by rintro ⟨h, h', h'' | h''⟩; exacts [hb1 ⟨h'', h'⟩, hb2 ⟨h, h''⟩]),
          if_neg (by rintro ⟨h, h'⟩; exact hb1 ⟨h, by omega⟩)]
  -- combine: `e₃ = σ₃ + B`, `a₁p₁ = P = c + B₁ + B₂`, `B₁ + B₂ = B + t`.
  linarith [hL1, hP, hPe, hBe]

end PcfContinuant
