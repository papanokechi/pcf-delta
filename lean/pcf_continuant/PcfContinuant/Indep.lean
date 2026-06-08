/-
Copyright (c) 2026 papanokechi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: papanokechi
-/
import PcfContinuant.Basic
import PcfContinuant.Bracket
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

The finite-window version `indepPolyWin u a b` proves the general deletion-contraction
recurrence on `[a,b]`, and `indepKWin` proves its degree-graded refinement.  The
existing `indepPoly_succ_succ` is the `a = 2` corollary, so `indepPoly_eq_rseq`
continues to follow by matching the recurrence defining `rseq`.
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

section CommRing

variable {R : Type*} [CommRing R]

/-- The weighted independence polynomial of the path on the finite window `[a,b]`:
the sum over no-two-consecutive subsets `T ⊆ {a,…,b}` of `∏_{i ∈ T} u i`.
If `b < a`, then `Icc a b = ∅`, so the value is the empty product `1`. -/
def indepPolyWin (u : ℕ → R) (a b : ℕ) : R :=
  ∑ T ∈ (Icc a b).powerset.filter NoTwoConsec, ∏ i ∈ T, u i

/-- The degree-`k` part of `indepPolyWin`: independent `k`-subsets of `[a,b]`. -/
def indepKWin (u : ℕ → R) (k a b : ℕ) : R :=
  ∑ T ∈ (powersetCard k (Icc a b)).filter NoTwoConsec, ∏ i ∈ T, u i

@[simp] theorem indepKWin_zero (u : ℕ → R) (a b : ℕ) :
    indepKWin u 0 a b = 1 := by
  rw [indepKWin, powersetCard_zero]
  simp [Finset.filter_singleton, NoTwoConsec]

/-- The degree-one part is the ordinary sum of the weights in the window. -/
theorem indepKWin_one (u : ℕ → R) (a b : ℕ) :
    indepKWin u 1 a b = ∑ i ∈ Icc a b, u i := by
  rw [indepKWin]
  have hfilter : ((powersetCard 1 (Icc a b)).filter NoTwoConsec)
      = powersetCard 1 (Icc a b) := by
    apply Finset.filter_true_of_mem
    intro T hT
    rw [mem_powersetCard] at hT
    obtain ⟨_, hcard⟩ := hT
    rw [Finset.card_eq_one] at hcard
    obtain ⟨x, rfl⟩ := hcard
    intro i hi hsucc
    rw [mem_singleton] at hi hsucc
    omega
  rw [hfilter, powersetCard_one, Finset.sum_map]
  simp

/-- Subsets of `[a,b+2]` avoiding the top vertex are exactly subsets of `[a,b+1]`. -/
theorem filter_not_mem_top_win (a b : ℕ) :
    ((Icc a (b + 2)).powerset.filter NoTwoConsec).filter (fun T => b + 2 ∉ T)
      = (Icc a (b + 1)).powerset.filter NoTwoConsec := by
  ext T
  simp only [mem_filter, mem_powerset]
  constructor
  · rintro ⟨⟨hsub, hntc⟩, hnot⟩
    refine ⟨?_, hntc⟩
    intro x hx
    have hx2 : x ∈ Icc a (b + 2) := hsub hx
    rw [mem_Icc] at hx2 ⊢
    refine ⟨hx2.1, ?_⟩
    rcases Nat.lt_or_ge x (b + 2) with hlt | hge
    · omega
    · have hxeq : x = b + 2 := le_antisymm hx2.2 hge
      exact absurd (hxeq ▸ hx) hnot
  · rintro ⟨hsub, hntc⟩
    refine ⟨⟨?_, hntc⟩, ?_⟩
    · intro x hx
      have hx2 := hsub hx
      rw [mem_Icc] at hx2 ⊢
      omega
    · intro hmem
      have hx2 := hsub hmem
      rw [mem_Icc] at hx2
      omega

/-- Degree-`k` version of `filter_not_mem_top_win`. -/
theorem filter_not_mem_top_win_card (k a b : ℕ) :
    ((powersetCard k (Icc a (b + 2))).filter NoTwoConsec).filter (fun T => b + 2 ∉ T)
      = (powersetCard k (Icc a (b + 1))).filter NoTwoConsec := by
  ext T
  simp only [mem_filter, mem_powersetCard]
  constructor
  · rintro ⟨⟨⟨hsub, hcard⟩, hntc⟩, hnot⟩
    refine ⟨⟨?_, hcard⟩, hntc⟩
    intro x hx
    have hx2 : x ∈ Icc a (b + 2) := hsub hx
    rw [mem_Icc] at hx2 ⊢
    refine ⟨hx2.1, ?_⟩
    rcases Nat.lt_or_ge x (b + 2) with hlt | hge
    · omega
    · have hxeq : x = b + 2 := le_antisymm hx2.2 hge
      exact absurd (hxeq ▸ hx) hnot
  · rintro ⟨⟨hsub, hcard⟩, hntc⟩
    refine ⟨⟨⟨?_, hcard⟩, hntc⟩, ?_⟩
    · intro x hx
      have hx2 := hsub hx
      rw [mem_Icc] at hx2 ⊢
      omega
    · intro hmem
      have hx2 := hsub hmem
      rw [mem_Icc] at hx2
      omega

/-- The top-containing part of the window sum is `u (b+2)` times the shorter window. -/
theorem sum_filter_mem_top_win (u : ℕ → R) {a b : ℕ} (h : a ≤ b + 2) :
    ∑ T ∈ ((Icc a (b + 2)).powerset.filter NoTwoConsec).filter (fun T => b + 2 ∈ T),
        ∏ i ∈ T, u i
      = u (b + 2) * indepPolyWin u a b := by
  rw [indepPolyWin, Finset.mul_sum]
  refine Finset.sum_bij'
    (fun T _ => T.erase (b + 2))
    (fun S _ => insert (b + 2) S)
    ?_ ?_ ?_ ?_ ?_
  · intro T hT
    simp only [mem_filter, mem_powerset] at hT ⊢
    obtain ⟨⟨hsub, hntc⟩, hmem⟩ := hT
    refine ⟨?_, hntc.erase _⟩
    intro x hx
    have hxT : x ∈ T := mem_of_mem_erase hx
    have hxne : x ≠ b + 2 := ne_of_mem_erase hx
    have hx2 : x ∈ Icc a (b + 2) := hsub hxT
    rw [mem_Icc] at hx2 ⊢
    refine ⟨hx2.1, ?_⟩
    have hne1 : x ≠ b + 1 := by
      intro hx1
      have hx2mem : x + 1 ∈ T := by rw [hx1]; exact hmem
      exact hntc x hxT hx2mem
    omega
  · intro S hS
    simp only [mem_filter, mem_powerset] at hS ⊢
    obtain ⟨hsub, hntc⟩ := hS
    refine ⟨⟨?_, ?_⟩, mem_insert_self _ _⟩
    · intro x hx
      rcases mem_insert.1 hx with rfl | hxS
      · rw [mem_Icc]
        exact ⟨h, le_rfl⟩
      · have hx2 := hsub hxS
        rw [mem_Icc] at hx2 ⊢
        omega
    · intro i hi hsucc
      rcases mem_insert.1 hi with rfl | hiS
      · rcases mem_insert.1 hsucc with hsuccTop | hsuccS
        · omega
        · have hx2 := hsub hsuccS
          rw [mem_Icc] at hx2
          omega
      · rcases mem_insert.1 hsucc with hsuccTop | hsuccS
        · have hx2 := hsub hiS
          rw [mem_Icc] at hx2
          omega
        · exact hntc i hiS hsuccS
  · intro T hT
    simp only [mem_filter] at hT
    exact insert_erase hT.2
  · intro S hS
    simp only [mem_filter, mem_powerset] at hS
    have hnotin : b + 2 ∉ S := by
      intro hmem
      have hx2 := hS.1 hmem
      rw [mem_Icc] at hx2
      omega
    exact erase_insert hnotin
  · intro T hT
    simp only [mem_filter] at hT
    have hmem : b + 2 ∈ T := hT.2
    rw [← Finset.prod_erase_mul _ _ hmem, mul_comm]

/-- Degree-graded top-containing sum. -/
theorem sum_filter_mem_top_win_card (u : ℕ → R) (k : ℕ) {a b : ℕ} (h : a ≤ b + 2) :
    ∑ T ∈ ((powersetCard (k + 1) (Icc a (b + 2))).filter NoTwoConsec).filter
          (fun T => b + 2 ∈ T),
        ∏ i ∈ T, u i
      = u (b + 2) * indepKWin u k a b := by
  rw [indepKWin, Finset.mul_sum]
  refine Finset.sum_bij'
    (fun T _ => T.erase (b + 2))
    (fun S _ => insert (b + 2) S)
    ?_ ?_ ?_ ?_ ?_
  · intro T hT
    simp only [mem_filter, mem_powersetCard] at hT ⊢
    obtain ⟨⟨⟨hsub, hcard⟩, hntc⟩, hmem⟩ := hT
    refine ⟨⟨?_, ?_⟩, hntc.erase _⟩
    · intro x hx
      have hxT : x ∈ T := mem_of_mem_erase hx
      have hxne : x ≠ b + 2 := ne_of_mem_erase hx
      have hx2 : x ∈ Icc a (b + 2) := hsub hxT
      rw [mem_Icc] at hx2 ⊢
      refine ⟨hx2.1, ?_⟩
      have hne1 : x ≠ b + 1 := by
        intro hx1
        have hx2mem : x + 1 ∈ T := by rw [hx1]; exact hmem
        exact hntc x hxT hx2mem
      omega
    · have hc := card_erase_of_mem hmem
      omega
  · intro S hS
    simp only [mem_filter, mem_powersetCard] at hS ⊢
    obtain ⟨⟨hsub, hcard⟩, hntc⟩ := hS
    have hnotin : b + 2 ∉ S := by
      intro hmem
      have hx2 := hsub hmem
      rw [mem_Icc] at hx2
      omega
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, mem_insert_self _ _⟩
    · intro x hx
      rcases mem_insert.1 hx with rfl | hxS
      · rw [mem_Icc]
        exact ⟨h, le_rfl⟩
      · have hx2 := hsub hxS
        rw [mem_Icc] at hx2 ⊢
        omega
    · rw [card_insert_of_notMem hnotin, hcard]
    · intro i hi hsucc
      rcases mem_insert.1 hi with rfl | hiS
      · rcases mem_insert.1 hsucc with hsuccTop | hsuccS
        · omega
        · have hx2 := hsub hsuccS
          rw [mem_Icc] at hx2
          omega
      · rcases mem_insert.1 hsucc with hsuccTop | hsuccS
        · have hx2 := hsub hiS
          rw [mem_Icc] at hx2
          omega
        · exact hntc i hiS hsuccS
  · intro T hT
    simp only [mem_filter] at hT
    exact insert_erase hT.2
  · intro S hS
    simp only [mem_filter, mem_powersetCard] at hS
    have hnotin : b + 2 ∉ S := by
      intro hmem
      have hx2 := hS.1.1 hmem
      rw [mem_Icc] at hx2
      omega
    exact erase_insert hnotin
  · intro T hT
    simp only [mem_filter] at hT
    have hmem : b + 2 ∈ T := hT.2
    rw [← Finset.prod_erase_mul _ _ hmem, mul_comm]

/-- **Window deletion-contraction.** -/
theorem indepPolyWin_succ_succ (u : ℕ → R) (a b : ℕ) (h : a ≤ b + 2) :
    indepPolyWin u a (b + 2)
      = indepPolyWin u a (b + 1) + u (b + 2) * indepPolyWin u a b := by
  have hsplit :
      indepPolyWin u a (b + 2)
        = (∑ T ∈ ((Icc a (b + 2)).powerset.filter NoTwoConsec).filter
              (fun T => b + 2 ∈ T), ∏ i ∈ T, u i)
          + (∑ T ∈ ((Icc a (b + 2)).powerset.filter NoTwoConsec).filter
              (fun T => b + 2 ∉ T), ∏ i ∈ T, u i) := by
    rw [indepPolyWin]
    exact (Finset.sum_filter_add_sum_filter_not _ (fun T => b + 2 ∈ T) _).symm
  rw [hsplit, sum_filter_mem_top_win u h, filter_not_mem_top_win a b]
  change u (b + 2) * indepPolyWin u a b + indepPolyWin u a (b + 1)
      = indepPolyWin u a (b + 1) + u (b + 2) * indepPolyWin u a b
  ring

/-- **Degree-graded window deletion-contraction.** -/
theorem indepKWin_succ_succ (u : ℕ → R) (k a b : ℕ) (h : a ≤ b + 2) :
    indepKWin u (k + 1) a (b + 2)
      = indepKWin u (k + 1) a (b + 1) + u (b + 2) * indepKWin u k a b := by
  have hsplit :
      indepKWin u (k + 1) a (b + 2)
        = (∑ T ∈ ((powersetCard (k + 1) (Icc a (b + 2))).filter NoTwoConsec).filter
              (fun T => b + 2 ∈ T), ∏ i ∈ T, u i)
          + (∑ T ∈ ((powersetCard (k + 1) (Icc a (b + 2))).filter NoTwoConsec).filter
              (fun T => b + 2 ∉ T), ∏ i ∈ T, u i) := by
    rw [indepKWin]
    exact (Finset.sum_filter_add_sum_filter_not _ (fun T => b + 2 ∈ T) _).symm
  rw [hsplit, sum_filter_mem_top_win_card u k h, filter_not_mem_top_win_card (k + 1) a b]
  change u (b + 2) * indepKWin u k a b + indepKWin u (k + 1) a (b + 1)
      = indepKWin u (k + 1) a (b + 1) + u (b + 2) * indepKWin u k a b
  ring

/-- Reassemble the independence polynomial from its degree-graded cluster sums. -/
theorem indepPolyWin_eq_sum_indepKWin (u : ℕ → R) (a b : ℕ) :
    indepPolyWin u a b
      = ∑ k ∈ range ((Icc a b).card + 1), indepKWin u k a b := by
  rw [indepPolyWin]
  symm
  let s := (Icc a b).powerset.filter NoTwoConsec
  let top := range ((Icc a b).card + 1)
  trans ∑ k ∈ top,
      ∑ T ∈ s.filter (fun T => T.card = k), ∏ i ∈ T, u i
  · refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [indepKWin]
    congr 1
    ext T
    simp only [s, mem_filter, mem_powerset, mem_powersetCard]
    tauto
  · have hmaps : ∀ T ∈ s, T.card ∈ top := by
      intro T hT
      simp only [top, mem_range]
      simp only [s, mem_filter, mem_powerset] at hT
      exact Nat.lt_succ_of_le (card_le_card hT.1)
    exact Finset.sum_fiberwise_of_maps_to (s := s) (t := top) (g := fun T => T.card)
      hmaps (fun T => ∏ i ∈ T, u i)

/-! ### The `σ₃` cluster sum (PROVEN via the graded engine)

The degree-3 no-two-consecutive cluster sum `σ₃` of `delta_characterization`
Appendix A is exactly `indepKWin u 3`.  Its deletion–contraction recurrence is the
`k = 2` instance of the proven graded recurrence `indepKWin_succ_succ`, and it is the
degree-3 summand of the proven reassembly `indepPolyWin_eq_sum_indepKWin`.  This
promotes `σ₃` from STRUCTURAL to machine-checked **PROVEN** as a graded cluster sum.

The alternative *inclusion–exclusion closed form* `σ₃ = e₃ − a₁·p₁ + c + t` is
numerically VERIFIED (exact rational checks over many windows), but it is a genuine
inclusion–exclusion identity: the cross term `a₁·p₁` permutes monomials across the
index cube, so it is **not** a termwise `Finset.sum_congr` identity (it holds only
after grouping equal monomials).  Its full formalization is deferred and it is **not**
claimed PROVEN here. -/

/-- The weighted **`σ₃` cluster sum** over the window `[a,b]`: the degree-3 part of the
independence polynomial — the sum over 3-element no-two-consecutive subsets. -/
def sigma3Win (u : ℕ → R) (a b : ℕ) : R := indepKWin u 3 a b

/-- `σ₃` is, by definition, the sum over no-two-consecutive 3-subsets of the window. -/
theorem sigma3Win_eq (u : ℕ → R) (a b : ℕ) :
    sigma3Win u a b
      = ∑ T ∈ (powersetCard 3 (Icc a b)).filter NoTwoConsec, ∏ i ∈ T, u i := rfl

/-- **`σ₃` deletion–contraction recurrence (PROVEN).**  On `[a, b+2]`, `σ₃` equals `σ₃`
on `[a, b+1]` plus `u (b+2)` times the degree-2 cluster sum `σ₂ = indepKWin u 2` on
`[a, b]`.  This is the `k = 2` instance of the graded recurrence `indepKWin_succ_succ`. -/
theorem sigma3Win_succ_succ (u : ℕ → R) (a b : ℕ) (h : a ≤ b + 2) :
    sigma3Win u a (b + 2)
      = sigma3Win u a (b + 1) + u (b + 2) * indepKWin u 2 a b :=
  indepKWin_succ_succ u 2 a b h

end CommRing

/-- The weighted independence polynomial of the path on `{2,…,n}`:
the sum over no-two-consecutive subsets `T ⊆ {2,…,n}` of `∏_{i ∈ T} u i`. -/
def indepPoly (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ T ∈ (Icc 2 n).powerset.filter NoTwoConsec, ∏ i ∈ T, u i

/-- The original `indepPoly` is the `a = 2` finite-window polynomial. -/
theorem indepPoly_eq_indepPolyWin (u : ℕ → ℝ) (n : ℕ) :
    indepPoly u n = indepPolyWin u 2 n := rfl

@[simp] theorem indepPoly_zero (u : ℕ → ℝ) : indepPoly u 0 = 1 := by
  simp [indepPoly, Finset.filter_singleton, NoTwoConsec]

@[simp] theorem indepPoly_one (u : ℕ → ℝ) : indepPoly u 1 = 1 := by
  simp [indepPoly, Finset.filter_singleton, NoTwoConsec]

/-- The index family of `indepPoly u (n+1)` is exactly the no-two-consecutive subsets
of `{2,…,n+2}` that avoid the top vertex `n+2`. -/
theorem filter_not_mem_top (n : ℕ) :
    ((Icc 2 (n + 2)).powerset.filter NoTwoConsec).filter (fun T => n + 2 ∉ T)
      = (Icc 2 (n + 1)).powerset.filter NoTwoConsec := by
  simpa using filter_not_mem_top_win (a := 2) (b := n)

/-- The subsets containing the top vertex `n+2`, summed, give `u (n+2) · indepPoly u n`,
via the bijection `S ↦ insert (n+2) S` with inverse `T ↦ T.erase (n+2)`. -/
theorem sum_filter_mem_top (u : ℕ → ℝ) (n : ℕ) :
    ∑ T ∈ ((Icc 2 (n + 2)).powerset.filter NoTwoConsec).filter (fun T => n + 2 ∈ T),
        ∏ i ∈ T, u i
      = u (n + 2) * indepPoly u n := by
  simpa [indepPoly_eq_indepPolyWin] using
    (sum_filter_mem_top_win (u := u) (a := 2) (b := n) (by omega))

/-- **The independence-polynomial recurrence.**  `indepPoly` satisfies the same
second-order recurrence as `rseq`:
`indepPoly u (n+2) = indepPoly u (n+1) + u (n+2) · indepPoly u n`. -/
theorem indepPoly_succ_succ (u : ℕ → ℝ) (n : ℕ) :
    indepPoly u (n + 2) = indepPoly u (n + 1) + u (n + 2) * indepPoly u n := by
  simpa [indepPoly_eq_indepPolyWin] using
    (indepPolyWin_succ_succ (u := u) (a := 2) (b := n) (by omega))

/-- **`Rₙ` is the weighted independence polynomial of the path graph.**
For all `n`, `indepPoly u n = rseq u n`. -/
theorem indepPoly_eq_rseq (u : ℕ → ℝ) : ∀ n, indepPoly u n = rseq u n
  | 0 => by simp [rseq]
  | 1 => by simp [rseq]
  | (n + 2) => by
      rw [indepPoly_succ_succ, indepPoly_eq_rseq u (n + 1), indepPoly_eq_rseq u n]
      simp only [rseq]

end PcfContinuant
