/-
Copyright (c) 2026 papanokechi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: papanokechi
-/
import PcfContinuant.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# `Rₙ` as a weighted independence polynomial of the path graph (PROVEN)

This upgrades the independence-polynomial identity of `delta_characterization`
(the proposition "`Rₙ` as an independence polynomial") from STRUCTURAL/VERIFIED to a
machine-checked, **fully finitary** result: no analysis, no extra axioms beyond the
Mathlib defaults.

For weights `u : ℕ → ℝ`, the scaled sequence `rseq` of `Basic.lean`
(`r 0 = r 1 = 1`, `r (n+2) = r (n+1) + u (n+2) · r n`) equals the **weighted
independence polynomial** of the path graph on the vertices `{2, …, n}` (edges between
consecutive integers):

`indepPoly u n = ∑_{T ⊆ {2,…,n}, no two consecutive} ∏_{i ∈ T} u i`.

`indepPoly_eq_rseq` proves `indepPoly u n = rseq u n` for all `n`, by the
deletion–contraction split at the top vertex `n+2`:

* subsets **not** containing `n+2` are exactly the no-two-consecutive subsets of
  `{2,…,n+1}` — they give `indepPoly u (n+1)`;
* subsets **containing** `n+2` cannot contain `n+1`, so they are `{n+2} ∪ S` with `S`
  a no-two-consecutive subset of `{2,…,n}` — they give `u (n+2) · indepPoly u n`.

Every step is a finite identity over `ℝ` proved with `Finset` algebra; the recurrence
matches `rseq`, so the two agree.  The corollaries `σ_k ≥ 0`, `R∞ = ∑_k σ_k` are the
cluster expansion discussed in the note.
-/

namespace PcfContinuant

open Finset

/-- A finset of naturals has **no two consecutive** elements:
whenever `i ∈ T`, its successor `i+1` is not in `T`. -/
def NoTwoConsec (T : Finset ℕ) : Prop := ∀ i ∈ T, i + 1 ∉ T

instance (T : Finset ℕ) : Decidable (NoTwoConsec T) := by
  unfold NoTwoConsec; infer_instance

/-- Removing an element preserves the no-two-consecutive property. -/
theorem NoTwoConsec.erase {T : Finset ℕ} (h : NoTwoConsec T) (a : ℕ) :
    NoTwoConsec (T.erase a) := by
  intro i hi hsucc
  exact h i (mem_of_mem_erase hi) (mem_of_mem_erase hsucc)

/-- The weighted independence polynomial of the path on `{2,…,n}`:
the sum over no-two-consecutive subsets `T ⊆ {2,…,n}` of `∏_{i ∈ T} u i`. -/
def indepPoly (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ T ∈ (Icc 2 n).powerset.filter NoTwoConsec, ∏ i ∈ T, u i

@[simp] theorem indepPoly_zero (u : ℕ → ℝ) : indepPoly u 0 = 1 := by
  simp [indepPoly, Finset.filter_singleton, NoTwoConsec]

@[simp] theorem indepPoly_one (u : ℕ → ℝ) : indepPoly u 1 = 1 := by
  simp [indepPoly, Finset.filter_singleton, NoTwoConsec]

/-- The index family of `indepPoly u (n+1)` is exactly the no-two-consecutive subsets
of `{2,…,n+2}` that avoid the top vertex `n+2`. -/
theorem filter_not_mem_top (n : ℕ) :
    ((Icc 2 (n + 2)).powerset.filter NoTwoConsec).filter (fun T => n + 2 ∉ T)
      = (Icc 2 (n + 1)).powerset.filter NoTwoConsec := by
  ext T
  simp only [mem_filter, mem_powerset]
  constructor
  · rintro ⟨⟨hsub, hntc⟩, hnot⟩
    refine ⟨?_, hntc⟩
    intro x hx
    have hx2 : x ∈ Icc 2 (n + 2) := hsub hx
    rw [mem_Icc] at hx2 ⊢
    refine ⟨hx2.1, ?_⟩
    rcases Nat.lt_or_ge x (n + 2) with hlt | hge
    · omega
    · have hxeq : x = n + 2 := le_antisymm hx2.2 hge
      exact absurd (hxeq ▸ hx) hnot
  · rintro ⟨hsub, hntc⟩
    refine ⟨⟨?_, hntc⟩, ?_⟩
    · intro x hx
      have hx2 := hsub hx
      rw [mem_Icc] at hx2 ⊢; omega
    · intro hmem
      have hx2 := hsub hmem
      rw [mem_Icc] at hx2; omega

/-- The subsets containing the top vertex `n+2`, summed, give `u (n+2) · indepPoly u n`,
via the bijection `S ↦ insert (n+2) S` with inverse `T ↦ T.erase (n+2)`. -/
theorem sum_filter_mem_top (u : ℕ → ℝ) (n : ℕ) :
    ∑ T ∈ ((Icc 2 (n + 2)).powerset.filter NoTwoConsec).filter (fun T => n + 2 ∈ T),
        ∏ i ∈ T, u i
      = u (n + 2) * indepPoly u n := by
  rw [indepPoly, Finset.mul_sum]
  refine Finset.sum_bij'
    (fun T _ => T.erase (n + 2))
    (fun S _ => insert (n + 2) S)
    ?_ ?_ ?_ ?_ ?_
  · -- erase lands in the n-window family
    intro T hT
    simp only [mem_filter, mem_powerset] at hT ⊢
    obtain ⟨⟨hsub, hntc⟩, hmem⟩ := hT
    refine ⟨?_, hntc.erase _⟩
    intro x hx
    have hxT : x ∈ T := mem_of_mem_erase hx
    have hxne : x ≠ n + 2 := ne_of_mem_erase hx
    have hx2 : x ∈ Icc 2 (n + 2) := hsub hxT
    rw [mem_Icc] at hx2 ⊢
    refine ⟨hx2.1, ?_⟩
    have hne1 : x ≠ n + 1 := by
      intro hx1
      have hx2mem : x + 1 ∈ T := by rw [hx1]; exact hmem
      exact hntc x hxT hx2mem
    omega
  · -- insert lands in the (n+2)-window family, containing n+2
    intro S hS
    simp only [mem_filter, mem_powerset] at hS ⊢
    obtain ⟨hsub, hntc⟩ := hS
    refine ⟨⟨?_, ?_⟩, mem_insert_self _ _⟩
    · intro x hx
      rcases mem_insert.1 hx with rfl | hxS
      · rw [mem_Icc]; omega
      · have hx2 := hsub hxS
        rw [mem_Icc] at hx2 ⊢; omega
    · intro i hi hsucc
      rcases mem_insert.1 hi with rfl | hiS
      · rcases mem_insert.1 hsucc with h | h
        · omega
        · have hx2 := hsub h
          rw [mem_Icc] at hx2; omega
      · rcases mem_insert.1 hsucc with h | h
        · have hx2 := hsub hiS
          rw [mem_Icc] at hx2; omega
        · exact hntc i hiS h
  · -- left inverse: erase then insert is identity (n+2 ∈ T)
    intro T hT
    simp only [mem_filter] at hT
    exact insert_erase hT.2
  · -- right inverse: insert then erase is identity (n+2 ∉ S)
    intro S hS
    simp only [mem_filter, mem_powerset] at hS
    have hnotin : n + 2 ∉ S := by
      intro hmem
      have hx2 := hS.1 hmem
      rw [mem_Icc] at hx2; omega
    exact erase_insert hnotin
  · -- the weights match: ∏ over T = u(n+2) * ∏ over T.erase (n+2)
    intro T hT
    simp only [mem_filter] at hT
    have hmem : n + 2 ∈ T := hT.2
    rw [← Finset.prod_erase_mul _ _ hmem, mul_comm]

/-- **The independence-polynomial recurrence.**  `indepPoly` satisfies the same
second-order recurrence as `rseq`:
`indepPoly u (n+2) = indepPoly u (n+1) + u (n+2) · indepPoly u n`. -/
theorem indepPoly_succ_succ (u : ℕ → ℝ) (n : ℕ) :
    indepPoly u (n + 2) = indepPoly u (n + 1) + u (n + 2) * indepPoly u n := by
  have hsplit :
      indepPoly u (n + 2)
        = (∑ T ∈ ((Icc 2 (n + 2)).powerset.filter NoTwoConsec).filter
              (fun T => n + 2 ∈ T), ∏ i ∈ T, u i)
          + (∑ T ∈ ((Icc 2 (n + 2)).powerset.filter NoTwoConsec).filter
              (fun T => n + 2 ∉ T), ∏ i ∈ T, u i) := by
    rw [indepPoly]
    exact (Finset.sum_filter_add_sum_filter_not _ (fun T => n + 2 ∈ T) _).symm
  rw [hsplit, sum_filter_mem_top u n, filter_not_mem_top n]
  change u (n + 2) * indepPoly u n + indepPoly u (n + 1)
      = indepPoly u (n + 1) + u (n + 2) * indepPoly u n
  ring

/-- **`Rₙ` is the weighted independence polynomial of the path graph.**
For all `n`, `indepPoly u n = rseq u n`. -/
theorem indepPoly_eq_rseq (u : ℕ → ℝ) : ∀ n, indepPoly u n = rseq u n
  | 0 => by simp [rseq]
  | 1 => by simp [rseq]
  | (n + 2) => by
      rw [indepPoly_succ_succ, indepPoly_eq_rseq u (n + 1), indepPoly_eq_rseq u n]
      simp only [rseq]

end PcfContinuant
