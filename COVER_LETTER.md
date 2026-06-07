# Cover letter — *pcf-delta* manuscript submission

**Author:** Papanokechi — ORCID [0009-0000-6192-8273](https://orcid.org/0009-0000-6192-8273)
**Manuscript:** *The growth-law correction constant δ = log R∞ of the quadratic
polynomial continued fraction: structure, a closed-form bracket, and certified
high-precision values*
**Date:** June 2026

> Operator note: addressee/venue left generic on purpose — fill in once the venue is
> chosen (see the venue discussion accompanying this draft). Nothing below names a
> journal.

---

To the Editors,

I am submitting the manuscript named above for consideration as a research article.

**The problem and the result.** A companion note establishes the exact two-sided
growth law for the convergent denominators `q_n` of the quadratic polynomial continued
fraction `V(A,B,C) = 1 + K_{n≥1} 1/(An² + Bn + C)` (integers `A,B,C ≥ 1`), but its
additive constant splits as `K_Γ + δ` where only the Gamma-product part `K_Γ` is
closed-form; the correction `δ = log R∞`, `R∞ = lim q_n / ∏ b_k`, is left as a black
box. This manuscript characterizes `δ`. The key structural observation is that the
scaled limit `R∞` is exactly the **independence polynomial of a path graph** evaluated
at the weights `u_n = 1/(b_{n-1} b_n)`. From this we derive (i) a closed-form two-sided
bracket `log(1+S) ≤ δ ≤ −log(1−S)` with `S` in closed digamma / confluent-polygamma
form (one degenerate value is exactly `S(1,2,1) = π²/3 − 13/4`); (ii) certified
high-precision values of `δ` (≥44 digits for the reference triple, a nine-triple table)
via an exact downward cluster recurrence, each value cross-checked by an independent
extrapolation; and (iii) rigorous evidence — with a precision-stability control that
distinguishes genuine integer relations from numerical artifacts — that `δ` has no
low-height elementary closed form, i.e. that it is conjecturally a new transcendental
constant of the family.

**Positioning.** The recurrence `q_n = b_n q_{n-1} + q_{n-2}` with `b_n → ∞` is a
Poincaré-type difference equation; the classical theory of recessive/minimal solutions
(Pincherle's theorem, modern treatment in Gautschi 1967) and the growing-coefficient
asymptotics of Perron, Birkhoff–Trjitzinsky and Wong–Li supply the *leading* growth but
leave precisely the amplitude constant `δ` undetermined. This note isolates that
constant; to my knowledge neither the path-independence-polynomial identity for the
amplitude nor the digamma closed form for its bracketing series appears in that
literature. The manuscript's §"Relation to prior work" makes the connection explicit.

**Methodological strengths a referee may wish to weigh.** The paper adopts an explicit
four-grade epistemic convention (PROVEN / STRUCTURAL / VERIFIED / CONJECTURED) and tags
every numbered result. In particular, the finitary structural core — the Casoratian
identity, the monotone–bounded convergence `R_n → R∞`, and the closed-form bracket
`1 + S ≤ R∞ ≤ 1/(1−S)` — is **machine-checked in Lean 4 / Mathlib** (pinned toolchain),
with `#print axioms` confirming every axiom cone is a subset of the Mathlib defaults
`{propext, Classical.choice, Quot.sound}` with no `sorryAx` and the source free of
`sorry`/`admit`. The heavy analysis is taken as explicitly labelled hypotheses rather
than silently assumed (the "conditional-core" pattern). Every numerical claim is
reproduced by named, archived scripts (mpmath/sympy), and the Lean package builds from
a pinned `lake-manifest.json`.

**Limitations, stated up front.** I deliberately do not overclaim: `δ` is certified to
≥44 digits (not the larger figure an earlier internal record mentioned, which is not
certified at feasible cost); non-elementarity is a conjecture supported by a controlled
null, not a theorem; irrationality of `δ` is open; and the analytic inputs (existence
of `R∞`, the closed form of `S`) are labelled hypotheses in the formalization, not
machine-checked. These caveats are in the abstract and the "Epistemic status" section.

**Originality and ethics.** This work is not under consideration at any other journal
and has not been published elsewhere. Version 1.0 of the note is archived as a preprint
on Zenodo (version DOI 10.5281/zenodo.20578401, concept DOI 10.5281/zenodo.20578400);
the submitted version additionally carries the machine-checked closed-form bracket. The
manuscript includes an AI-assistance disclosure (drafting and computer-algebra/Lean
verification; all values produced by the named scripts, all cones by `#print axioms`,
with author responsibility for content and grading). Code, data, and the Lean sources
are available in the deposit's public repository.

**Suggested classification.** 2020 MSC: 11J70 (primary), 11A55, 33B15, 05C31.
Keywords: polynomial continued fraction; convergent denominators; independence
polynomial; cluster expansion; digamma function; high-precision computation;
integer-relation detection; formal verification (Lean).

Thank you for your consideration.

Sincerely,
Papanokechi
ORCID 0009-0000-6192-8273
