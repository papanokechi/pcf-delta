import PcfContinuant.Basic
import PcfContinuant.Bracket
import PcfContinuant.Indep
import PcfContinuant.Sigma

open PcfContinuant

#print axioms casoratian_step
#print axioms casoratian_eq
#print axioms pq_casoratian
#print axioms rseq_ge_one
#print axioms rseq_mono
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
