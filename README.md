# pcf-delta

The growth-law correction constant **δ = log R∞** of the quadratic polynomial
continued fraction *V(A,B,C) = 1 + K_{n≥1} 1/(An²+Bn+C)*, integers *A,B,C ≥ 1*:
structure, a closed-form bracket, and certified high-precision values.

- **Slug ↔ repo ↔ Zenodo concept:** `pcf-delta` ↔ `papanokechi/pcf-delta` ↔
  `10.5281/zenodo.20578400` (concept, cite-all).
- **Companion** growth-law note (parent, `isSupplementTo`): `10.5281/zenodo.20564681`.

## Layout (durable convention)

```
pcf-delta/
  delta_characterization.pdf   LIVE canonical manuscript (root only; bare name)
  delta_characterization.tex   LIVE source
  COVER_LETTER.md              editor cover letter (live)
  METADATA.yml                 single source of truth for deposit fields
  claims.jsonl                 SIARC ledger (one claim per line)
  src/                         reproducibility scripts (Apache-2.0)
  lean/pcf_continuant/         machine-checked finitary core (Apache-2.0)
  archive/                     FROZEN, read-only (delta_characterization_v1.0.*)
  deposit/                     DISPOSABLE; assembled fresh at deposit, then deleted
  tools/                       validate_metadata.py + hooks/pre-push
  README.md                    this file
```

### Versioning

- **One live file at root, bare-named.** The live `delta_characterization.{tex,pdf}`
  always holds the *current* version; the version itself is recorded in
  `METADATA.yml` (`version:`), on the PDF title page (`pcf-delta vX.Y draft`), and in
  `claims.jsonl`. There is never a second bare-named copy at root, so size/timestamp
  are never needed to disambiguate.
- **Frozen versions are versioned in `archive/`.** Finalizing a version copies it to
  `archive/delta_characterization_vX.Y.pdf` (read-only, never re-opened to "refresh").
  The live root file then advances to the next version.
- **Deposit artifacts carry the version in the filename.** At deposit time the
  candidate is assembled into `deposit/` as `delta_characterization_vX.Y.pdf`, whose
  filename version must equal `METADATA.version` and the PDF title-page version.

The current live version is **v1.3** (enlarges the machine-checked core to 58 clean
axiom cones: a general Casoratian over any commutative ring with the classical
(&minus;1)<sup>n</sup> case recovered as a faithfulness witness; a degree-graded
independence refinement with the order-3 cluster window object — the σ₃ closed form
stays structural, not promoted; an *m*-term geometric-tail enclosure refining the
bracket; and an exact weighted partial-fraction telescoping identity for the *B=0*
family. v1.2 promoted the independence-polynomial identity and the σ₂ cluster core
to PROVEN; v1.1 added the closed-form bracket `rinf_bracket` and the σ₂,σ₃
inclusion–exclusion appendix over the deposited v1.0).

## Epistemic convention (SIARC four-class)

- **PROVEN** = machine-checked in Lean 4 with a clean axiom cone (a subset of
  `{propext, Classical.choice, Quot.sound}`, no `sorryAx`, no `sorry`/`admit`,
  build exit 0). "PROVEN" means the **axiom cone**, not merely a green build.
- **STRUCTURAL** = complete elementary hand proof, not yet formalized.
- **VERIFIED** = confirmed numerically for the stated finite cases.
- **CONJECTURED** = supported by evidence, not established.

See `claims.jsonl` for the per-claim grading.

## Reproduce

Numerics (mpmath):

```
python src/bracket_gate.py                 # the bracket gate
python src/verify_clusters.py              # σ2,σ3 final-form gate
python src/verify_inclusion_exclusion.py   # step-by-step appendix derivation gate
python src/continuant_verify.py            # exact independence-polynomial check
python src/S_closed_form.py src/S_confluent.py
python src/hp_delta_v2.py src/finalize_m2.py   # certified δ values -> delta_values_m2.txt
python src/pslq_stability.py               # integer-relation null
```

Lean core (toolchain pinned `leanprover/lean4:v4.30.0`, Mathlib `rev=v4.30.0`):

```
cd lean/pcf_continuant
lake build
lake env lean Check.lean    # prints every axiom cone; the PROVEN gate
```

## Before any deposit or submission

Run the metadata validator (must exit 0):

```
python tools/validate_metadata.py
```

It checks: ORCID exact `0009-0000-6192-8273`; version agreement
(METADATA ↔ PDF title page ↔ deposit filename); AI-disclosure byte-identical to the
frozen org boilerplate (`../_boilerplate/disclosures.md`, after LaTeX/Markdown
normalization); repo URL present in both manuscript and metadata; companion DOI and
GitHub linked in `related_identifiers`; license = `CC-BY-4.0`.

## Publish boundary (operator-gated)

Agents **commit** freely; only the operator **pushes** or **mints**. The tracked
`tools/hooks/pre-push` hard-blocks pushes unless `SIARC_OPERATOR=1` is set in an
interactive operator shell. Activate the hook in any fresh clone with:

```
git config core.hooksPath tools/hooks
```

License: paper unit (`delta_characterization.*`) is **CC-BY-4.0**; bundled code
(`src/`, `lean/`) is **Apache-2.0**.
