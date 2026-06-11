/-
Copyright (c) 2026 papanokechi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: papanokechi
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Finitary core for the quadratic-PCF growth law

Pure-algebra / order core underlying the two-solution (connection-constant) structure of the
quadratic polynomial continued fraction `V(A,B,C) = 1 + K_{n≥1} 1/(A n² + B n + C)`, whose
convergent numerators `p` and denominators `q` satisfy the same second-order recurrence
`s (n+2) = b (n+2) * s (n+1) + s n`.

Main results (all finitary; no analysis, no extra axioms beyond Mathlib defaults):

* `casoratian_step` — the Casoratian (discrete Wronskian) of two solutions of the SAME
  recurrence flips sign at each step.
* `casoratian_eq`   — hence it equals `(-1)^n` times its initial value.
* `pq_casoratian`   — for convergents (`p 0 = 1, p 1 = b 1 + 1, q 0 = 1, q 1 = b 1`),
  `p (n+1) * q n - p n * q (n+1) = (-1)^n`.  This is the exact Casoratian identity from
  `delta_characterization.md` (item 2), the source of the `(∏ b)⁻²` Wronskian decay.
* `rseq_ge_one`, `rseq_mono` — the scaled sequence `r (n+2) = r (n+1) + u (n+2) * r n`
  (with `u ≥ 0`) is `≥ 1` and monotone — the "monotone, bounded-below" half of the
  monotone-bounded convergence of `Rₙ → R∞` (item 3).
* `rseq_monotone` — the full `Monotone (rseq u)` packaging (via `monotone_nat_of_le_succ`).
* `rmaj`, `rmaj_ge_one`, `rmaj_mono`, `rseq_le_rmaj` — the finitary product majorant
  `Rₙ ≤ ∏_{k=2}^n (1 + uₖ)` (pure algebra/order), which bounds `rseq` above whenever the
  partial products converge.
* `rseq_tendsto_ciSup`, `rseq_tendsto_of_rmaj_bddAbove` — **limit existence**: `Rₙ → ⨆ₙ Rₙ`
  via Mathlib's monotone-convergence theorem `tendsto_atTop_ciSup`, conditional on the one
  labelled analytic hypothesis that `rseq` (equivalently the partial products `∏(1+uₖ)`, i.e.
  `Σ uₙ`) is bounded above.  The *value* `R∞ ≤ 1/(1-S)` and the closed form for `S` remain
  OUT OF SCOPE (labelled hypotheses).
-/

namespace PcfContinuant

/-! ## The algebraic Casoratian identity (over any commutative ring) -/

variable {R : Type*} [CommRing R]

/-- A second-order linear recurrence `s (n+2) = c (n+2) * s (n+1) + s n`. -/
def IsSol (c s : ℕ → R) : Prop := ∀ n, s (n + 2) = c (n + 2) * s (n + 1) + s n

/-- The **general** second-order linear recurrence
`s (n+2) = c (n+2) * s (n+1) + d n * s n`, with an arbitrary lower coefficient `d`.
The classical `IsSol` is the special case `d ≡ 1` (see `IsSol.isSolG`). -/
def IsSolG (c d s : ℕ → R) : Prop := ∀ n, s (n + 2) = c (n + 2) * s (n + 1) + d n * s n

/-- The Casoratian (discrete Wronskian) of two sequences. -/
def casoratian (y z : ℕ → R) (n : ℕ) : R := y (n + 1) * z n - y n * z (n + 1)

/-- The Casoratian of two solutions of the same recurrence flips sign at each step. -/
theorem casoratian_step {c y z : ℕ → R} (hy : IsSol c y) (hz : IsSol c z) (n : ℕ) :
    casoratian y z (n + 1) = -casoratian y z n := by
  have hyn : y (n + 1 + 1) = c (n + 1 + 1) * y (n + 1) + y n := hy n
  have hzn : z (n + 1 + 1) = c (n + 1 + 1) * z (n + 1) + z n := hz n
  simp only [casoratian, hyn, hzn]
  ring

/-- Hence the Casoratian equals `(-1)^n` times its value at `0`. -/
theorem casoratian_eq {c y z : ℕ → R} (hy : IsSol c y) (hz : IsSol c z) (n : ℕ) :
    casoratian y z n = (-1) ^ n * casoratian y z 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [casoratian_step hy hz k, ih, pow_succ]
      ring

/-- The exact Casoratian identity for PCF convergents: with `p 0 = 1, p 1 = b 1 + 1`,
`q 0 = 1, q 1 = b 1`, both solving `s (n+2) = b (n+2) s (n+1) + s n`,
`p (n+1) * q n - p n * q (n+1) = (-1)^n`. -/
theorem pq_casoratian {b p q : ℕ → R}
    (hp : IsSol b p) (hq : IsSol b q)
    (hp0 : p 0 = 1) (hp1 : p 1 = b 1 + 1) (hq0 : q 0 = 1) (hq1 : q 1 = b 1) (n : ℕ) :
    p (n + 1) * q n - p n * q (n + 1) = (-1) ^ n := by
  have h := casoratian_eq hp hq n
  have h0 : casoratian p q 0 = 1 := by
    simp only [casoratian, hp0, hp1, hq0, hq1]; ring
  rw [h0, mul_one] at h
  simpa [casoratian] using h

/-! ### General Casoratian over an arbitrary lower coefficient `d`

For the general recurrence `s (n+2) = c (n+2) · s (n+1) + d n · s n`, the Casoratian
no longer merely flips sign — it is scaled by `-(d n)` at each step, hence equals
`(∏_{k<n} -(d k))` times its initial value.  The classical sign-flip results above
are the `d ≡ 1` specialization (`IsSol.isSolG`, `Finset.prod_const`).  The identity is
independent of the upper coefficient `c`. -/

/-- The classical recurrence is the `d ≡ 1` case of the general one. -/
theorem IsSol.isSolG {c s : ℕ → R} (h : IsSol c s) : IsSolG c (fun _ => 1) s := by
  intro n; simpa using h n

/-- **General Casoratian step.** For two solutions of the same general recurrence,
the Casoratian is scaled by `-(d n)` at each step. -/
theorem casoratian_stepG {c d y z : ℕ → R} (hy : IsSolG c d y) (hz : IsSolG c d z)
    (n : ℕ) : casoratian y z (n + 1) = -(d n) * casoratian y z n := by
  have hyn : y (n + 1 + 1) = c (n + 1 + 1) * y (n + 1) + d n * y n := hy n
  have hzn : z (n + 1 + 1) = c (n + 1 + 1) * z (n + 1) + d n * z n := hz n
  simp only [casoratian, hyn, hzn]
  ring

/-- **General Casoratian closed form.** Hence the Casoratian equals
`(∏_{k<n} -(d k))` times its value at `0`. -/
theorem casoratian_eqG {c d y z : ℕ → R} (hy : IsSolG c d y) (hz : IsSolG c d z)
    (n : ℕ) :
    casoratian y z n = (∏ k ∈ Finset.range n, -(d k)) * casoratian y z 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [casoratian_stepG hy hz k, ih, Finset.prod_range_succ]
      ring

/-- **General convergent Casoratian.** For two solutions `p`, `q` of the same general
recurrence, `p (n+1) q n - p n q (n+1) = (∏_{k<n} -(d k)) · (p 1 q 0 - p 0 q 1)`.
The classical `pq_casoratian` is the `d ≡ 1`, normalized-initial-data specialization. -/
theorem pq_casoratianG {c d p q : ℕ → R} (hp : IsSolG c d p) (hq : IsSolG c d q)
    (n : ℕ) :
    p (n + 1) * q n - p n * q (n + 1)
      = (∏ k ∈ Finset.range n, -(d k)) * (p 1 * q 0 - p 0 * q 1) := by
  have h := casoratian_eqG hp hq n
  have h0 : casoratian p q 0 = p 1 * q 0 - p 0 * q 1 := by simp [casoratian]
  rw [h0] at h
  simpa [casoratian] using h

/-- **Faithfulness of the generalization.**  Instantiating the general closed form
`casoratian_eqG` at `d ≡ 1` (via `IsSol.isSolG`) recovers the classical `(-1)^n`
sign-flip law `casoratian_eq` verbatim: `∏_{k<n} -(1) = (-1)^n`.  This is the cheapest
possible witness that the general lemma genuinely specializes to the original. -/
theorem casoratian_eqG_recovers_classical {c y z : ℕ → R}
    (hy : IsSol c y) (hz : IsSol c z) (n : ℕ) :
    casoratian y z n = (-1) ^ n * casoratian y z 0 := by
  have h := casoratian_eqG hy.isSolG hz.isSolG n
  simpa [Finset.prod_const, Finset.card_range] using h

/-! ## The convergence core: the scaled sequence is `≥ 1` and monotone

Specialized to `ℝ` (the application domain) to use its order instances directly. -/

section Order

/-- The scaled denominator-type sequence `r (n+2) = r (n+1) + u (n+2) * r n`,
`r 0 = r 1 = 1`. With `u = 1/(b_{n-1} b_n) ≥ 0` this is `Rₙ` of the note. -/
def rseq (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | (n + 2) => rseq u (n + 1) + u (n + 2) * rseq u n

/-- `rseq` is bounded below by `1` (carrying two consecutive values through the induction). -/
theorem rseq_ge_one (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) :
    ∀ n, 1 ≤ rseq u n ∧ 1 ≤ rseq u (n + 1) := by
  intro n
  induction n with
  | zero => exact ⟨by simp [rseq], by simp [rseq]⟩
  | succ k ih =>
      obtain ⟨hk, hk1⟩ := ih
      refine ⟨hk1, ?_⟩
      change 1 ≤ rseq u (k + 2)
      have hpos : 0 ≤ u (k + 2) * rseq u k :=
        mul_nonneg (hu _) (le_trans zero_le_one hk)
      simp only [rseq]
      linarith

/-- `rseq` is monotone (nondecreasing) when all `u n ≥ 0`. -/
theorem rseq_mono (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (n : ℕ) :
    rseq u n ≤ rseq u (n + 1) := by
  match n with
  | 0 => change rseq u 0 ≤ rseq u 1; simp [rseq]
  | (k + 1) =>
      change rseq u (k + 1) ≤ rseq u (k + 2)
      have hpos : 0 ≤ u (k + 2) * rseq u k :=
        mul_nonneg (hu _) (le_trans zero_le_one (rseq_ge_one u hu k).1)
      simp only [rseq]
      linarith

/-- `rseq` is *strictly* increasing on indices `≥ 1`: `rseq u (n+1) < rseq u (n+2)`
when all `u n > 0` (the genuine situation, since `u n = 1/(b_{n-1} b_n) > 0`).
The consecutive-step `rseq_mono` only gives `≤` (it needs merely `u ≥ 0`); strictness
is what the manuscript's "strictly increasing" actually asserts.  Note `rseq` is flat at
the very start (`rseq u 0 = rseq u 1 = 1`), so strictness begins at index `1`. -/
theorem rseq_strictMono_succ (u : ℕ → ℝ) (hu : ∀ n, 0 < u n) (n : ℕ) :
    rseq u (n + 1) < rseq u (n + 2) := by
  have hrn : (1 : ℝ) ≤ rseq u n := (rseq_ge_one u (fun k => (hu k).le) n).1
  have hpos : 0 < u (n + 2) * rseq u n :=
    mul_pos (hu (n + 2)) (lt_of_lt_of_le zero_lt_one hrn)
  simp only [rseq]
  linarith

end Order

/-! ## Limit existence (conditional core): `Rₙ → R∞`

`rseq` is monotone (`rseq_mono`/`rseq_monotone`) and, *provided it is bounded above*,
converges to its supremum by Mathlib's monotone-convergence theorem
`tendsto_atTop_ciSup`.  Boundedness is the analytic content (convergence of `Σ uₙ`); we
keep it as an explicit hypothesis and, to make it concrete, majorize `rseq` by the partial
products `∏_{k=2}^n (1 + uₖ)` (`rmaj`).  This reduces "`rseq` bounded above" to "the partial
products are bounded above" — a purely finitary step — which is exactly the
convergence-of-`Σ uₙ` condition stated in `delta_characterization.md` (item 3/4).  The
*value* of the limit (`R∞ ≤ 1/(1-S)`, the closed-form `S`) remains OUT OF SCOPE. -/

section Convergence

open Filter Topology

/-- `Monotone` (full `≤`-monotonicity) form of the consecutive-step `rseq_mono`. -/
theorem rseq_monotone (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) : Monotone (rseq u) :=
  monotone_nat_of_le_succ (rseq_mono u hu)

/-- Monotone convergence: if `rseq u` is bounded above it converges to its supremum. -/
theorem rseq_tendsto_ciSup (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hbdd : BddAbove (Set.range (rseq u))) :
    Tendsto (rseq u) atTop (𝓝 (⨆ n, rseq u n)) :=
  tendsto_atTop_ciSup (rseq_monotone u hu) hbdd

/-- The product majorant `∏_{k=2}^n (1 + uₖ)`, defined recursively to mirror `rseq`. -/
def rmaj (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | (n + 2) => rmaj u (n + 1) * (1 + u (n + 2))

/-- `rmaj` is bounded below by `1` (carrying two consecutive values through the induction). -/
theorem rmaj_ge_one (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) :
    ∀ n, 1 ≤ rmaj u n ∧ 1 ≤ rmaj u (n + 1) := by
  intro n
  induction n with
  | zero => exact ⟨by simp [rmaj], by simp [rmaj]⟩
  | succ k ih =>
      obtain ⟨_, hk1⟩ := ih
      refine ⟨hk1, ?_⟩
      change 1 ≤ rmaj u (k + 2)
      have hfac : (1 : ℝ) ≤ 1 + u (k + 2) := by linarith [hu (k + 2)]
      simp only [rmaj]
      nlinarith [hk1, hfac]

/-- `rmaj` is monotone (nondecreasing) when all `u n ≥ 0`. -/
theorem rmaj_mono (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (n : ℕ) :
    rmaj u n ≤ rmaj u (n + 1) := by
  match n with
  | 0 => simp [rmaj]
  | (k + 1) =>
      change rmaj u (k + 1) ≤ rmaj u (k + 2)
      have h1 : (1 : ℝ) ≤ rmaj u (k + 1) := (rmaj_ge_one u hu k).2
      have hfac : (1 : ℝ) ≤ 1 + u (k + 2) := by linarith [hu (k + 2)]
      simp only [rmaj]
      nlinarith [h1, hfac]

/-- The key finitary bound: `Rₙ ≤ ∏_{k=2}^n (1 + uₖ)`.  Pure algebra/order — no analysis. -/
theorem rseq_le_rmaj (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) :
    ∀ n, rseq u n ≤ rmaj u n ∧ rseq u (n + 1) ≤ rmaj u (n + 1) := by
  intro n
  induction n with
  | zero => exact ⟨by simp [rseq, rmaj], by simp [rseq, rmaj]⟩
  | succ k ih =>
      obtain ⟨hk, hk1⟩ := ih
      refine ⟨hk1, ?_⟩
      change rseq u (k + 2) ≤ rmaj u (k + 2)
      have hboundk : rseq u k ≤ rmaj u (k + 1) := le_trans hk (rmaj_mono u hu k)
      have hu2 : 0 ≤ u (k + 2) := hu (k + 2)
      have hstep : rseq u (k + 1) + u (k + 2) * rseq u k
              ≤ rmaj u (k + 1) + u (k + 2) * rmaj u (k + 1) :=
        add_le_add hk1 (mul_le_mul_of_nonneg_left hboundk hu2)
      simp only [rseq, rmaj]
      calc rseq u (k + 1) + u (k + 2) * rseq u k
          ≤ rmaj u (k + 1) + u (k + 2) * rmaj u (k + 1) := hstep
        _ = rmaj u (k + 1) * (1 + u (k + 2)) := by ring

/-- If the product majorant is bounded above, so is `rseq` (since `rseq ≤ rmaj`). -/
theorem rseq_bddAbove_of_rmaj (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hbdd : BddAbove (Set.range (rmaj u))) : BddAbove (Set.range (rseq u)) := by
  obtain ⟨M, hM⟩ := hbdd
  refine ⟨M, ?_⟩
  rintro y ⟨n, rfl⟩
  exact le_trans (rseq_le_rmaj u hu n).1 (hM (Set.mem_range_self n))

/-- **`Rₙ → R∞` exists** when the partial products `∏(1+uₖ)` are bounded above; the limit
is `⨆ n, rseq u n`.  This is the monotone-bounded convergence of `Rₙ → R∞` with the single
labelled analytic hypothesis "the partial products converge" (i.e. `Σ uₙ < ∞`). -/
theorem rseq_tendsto_of_rmaj_bddAbove (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hbdd : BddAbove (Set.range (rmaj u))) :
    Tendsto (rseq u) atTop (𝓝 (⨆ n, rseq u n)) :=
  rseq_tendsto_ciSup u hu (rseq_bddAbove_of_rmaj u hu hbdd)

end Convergence

end PcfContinuant
