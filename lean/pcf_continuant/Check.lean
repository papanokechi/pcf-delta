import PcfContinuant.Basic
import PcfContinuant.Bracket
import PcfContinuant.Indep
import PcfContinuant.Sigma
import PcfContinuant.Sigma3
import PcfContinuant.Topic3
import PcfContinuant.Topic5
import PcfContinuant.HigherCaso
import PcfContinuant.GeneralCaso

open PcfContinuant

#print axioms casoratian_step
#print axioms casoratian_eq
#print axioms pq_casoratian
#print axioms rseq_ge_one
#print axioms rseq_mono
#print axioms rseq_strictMono_succ
#print axioms rseq_monotone
#print axioms rmaj_ge_one
#print axioms rmaj_mono
#print axioms rseq_le_rmaj
#print axioms rseq_bddAbove_of_rmaj
#print axioms rseq_tendsto_ciSup
#print axioms rseq_tendsto_of_rmaj_bddAbove
#print axioms psum
#print axioms psum_nonneg
#print axioms rseq_ge_one_add_psum
#print axioms rmaj_mul_one_sub_psum_le_one
#print axioms rinf_bracket
#print axioms rseq_tendsto_under_psum_bdd

-- Independence-polynomial identity (Indep.lean): Rₙ = weighted independence
-- polynomial of the path graph.  STRUCTURAL → PROVEN.
#print axioms NoTwoConsec.erase
#print axioms indepPoly_zero
#print axioms indepPoly_one
#print axioms filter_not_mem_top
#print axioms sum_filter_mem_top
#print axioms indepPoly_succ_succ
#print axioms indepPoly_eq_rseq

-- Finite-window cluster closed form σ₂ (Sigma.lean): σ₂ = e₂ − a₁.
-- STRUCTURAL → PROVEN.
#print axioms sigma2win_eq

-- Finite-window cluster closed form σ₃ (Sigma3.lean): the Appendix-A inclusion–
-- exclusion identity σ₃ = e₃ − a₁·p₁ + c + t over an ordered-triple encoding.
-- VERIFIED → PROVEN (clean axiom cone, fully finitary; the cross term a₁·p₁ is
-- reconciled with σ₃ via the bad-triple decomposition, no analytic input).
#print axioms partition_l
#print axioms sigma3win_eq

-- Topic 2 (Indep.lean): general weighted independence-polynomial engine —
-- arbitrary-window deletion-contraction and its degree-graded (σ_k) refinement.
-- PROVEN (clean axiom cone, finitary).
#print axioms indepPolyWin
#print axioms indepKWin
#print axioms indepKWin_zero
#print axioms indepKWin_one
#print axioms filter_not_mem_top_win
#print axioms filter_not_mem_top_win_card
#print axioms sum_filter_mem_top_win
#print axioms sum_filter_mem_top_win_card
#print axioms indepPolyWin_succ_succ
#print axioms indepKWin_succ_succ
#print axioms indepPolyWin_eq_sum_indepKWin
#print axioms indepPoly_eq_indepPolyWin

-- Two-sided cluster-partial-sum enclosure of R_inf (Topic3.lean), PROVEN
-- conditional on the two labelled analytic hypotheses (H1) HasSum and
-- (H2) 0 ≤ σ_k ≤ S^k.
#print axioms PcfContinuant.Topic3.tsum_geomTail
#print axioms PcfContinuant.Topic3.Rinf_enclosure
#print axioms PcfContinuant.Topic3.delta_enclosure
#print axioms PcfContinuant.Topic3.enclosure_nonvacuous

-- Topic 3 referee items: m=1 provably reproduces the paper's S-only bracket,
-- and (H2) at k=0 forces σ₀ ≤ 1.  PROVEN.
#print axioms PcfContinuant.Topic3.clusterPartial_one_eq
#print axioms PcfContinuant.Topic3.m1_recovers_S_bracket
#print axioms PcfContinuant.Topic3.m1_delta_eq_S_bracket
#print axioms PcfContinuant.Topic3.H2_zero_forces_sigma0_le_one

-- Topic 4 (Basic.lean): general Casoratian for `s(n+2)=c(n+2)s(n+1)+d n·s n`
-- over any CommRing.  The classical (-1)^n results are the d≡1 specialization.
-- PROVEN.
#print axioms IsSol.isSolG
#print axioms casoratian_stepG
#print axioms casoratian_eqG
#print axioms pq_casoratianG
#print axioms casoratian_eqG_recovers_classical

-- Topic 1 (Indep.lean): σ₃ cluster sum promoted to PROVEN via the graded engine
-- (σ₃ = indepKWin u 3; recurrence is the k=2 instance of indepKWin_succ_succ).
#print axioms sigma3Win_eq
#print axioms sigma3Win_succ_succ

-- Topic 5 (Topic5.lean): exact weighted partial-fraction telescoping for the B=0
-- family.  Finite identity PROVEN over any field; the ℝ limit is conditional on the
-- labelled hypothesis 1/b_N → 0.
#print axioms PcfContinuant.Topic5.partialFraction
#print axioms PcfContinuant.Topic5.sum_Ico_telescope
#print axioms PcfContinuant.Topic5.weighted_telescope
#print axioms PcfContinuant.Topic5.weighted_telescope_value
#print axioms PcfContinuant.Topic5.weighted_sum_tendsto

-- Topic 6 (HigherCaso.lean): HIGHER-ORDER Casoratians — the new order≥3 research
-- space.  Abel–Jacobi–Liouville first-order law for the order-3 discrete Wronskian
-- of a PCF / simultaneous-Hermite–Padé recurrence: C(n+1) = c₀(n)·C(n), hence the
-- closed product form C(n) = (∏_{m<n} c₀ m)·C(0).  Order-2 (corpus sign −c₀) is the
-- faithfulness witness.  All finitary; clean cones, no analytic input.  PROVEN.
#print axioms PcfHigherCaso.caso2_step
#print axioms PcfHigherCaso.caso3_step
#print axioms PcfHigherCaso.caso3_eq
#print axioms PcfHigherCaso.caso3_eq_const
#print axioms PcfHigherCaso.caso3_ne_zero_of_init

-- Topic 6 (GeneralCaso.lean): GENERAL-ORDER (arbitrary k) Casoratian law — the
-- uniform-in-k Abel–Jacobi–Liouville theorem for the order-(k+1) discrete
-- Wronskian.  The last row of C(n+1), rewritten by the (k+1)-term recurrence, is a
-- linear combination of the cyclically rotated rows of C(n); det_updateRow_sum
-- collapses it to the c₀ coefficient and sign_finRotate contributes the cyclic
-- sign (-1)^k, giving C(n+1) = (-1)^k·c₀(n)·C(n) and the closed product form.
-- k=1 recovers the order-2 sign −c₀, k=2 the order-3 sign +c₀.  Includes the
-- constant-coefficient power form and the integral-domain non-vanishing
-- (linear-independence) certificate.  All finitary; clean cones.  PROVEN.
#print axioms PcfGeneralCaso.casoMat_det_step
#print axioms PcfGeneralCaso.casoMat_det_eq
#print axioms PcfGeneralCaso.casoMat_det_eq_const
#print axioms PcfGeneralCaso.casoMat_det_ne_zero_of_init
