> **BigO-Hunter fork notice.** The org's reference copy of [JoshuaQFEX/apsp-bound](https://github.com/JoshuaQFEX/apsp-bound) — the APSP word-RAM bounds and Lean proofs referenced by the org's SSSP/APSP lane. The org stamps this copy's LICENSE with the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE) ([github.com/darkhipo/cfsf](https://github.com/darkhipo/cfsf)); upstream's content remains as published (upstream carries no license file) — see [NOTICE](NOTICE.md). Upstream's README below is unchanged.

# APSP bounds and Lean proofs

**Joshua Wharton · QFEX · [joshua@qfex.com](mailto:joshua@qfex.com)**

## Complete word-RAM theorem

The [complete Lean project](verified/README.md) proves

$$O\!\left(n^{2.995560766}\right)$$

for the challenge's exact deterministic integer APSP problem. Its closed theorem [Race.bound](verified/Submission.lean) provides a correct finite word-RAM program and a proof of its actual execution time, including the required input, output, memory, and word-width conditions. It has no unproved numerical, oracle, correctness, or execution-cost hypotheses.

This refines the **2.99556085** exponent listed as Lean Verified on [Big O Speedrun](https://bigospeedrun.com/apsp) on 20 October 2026. The decrease is exactly **0.000000084**. It retunes the executable parameters of Li Xuanji's complete proof, following Hrishik Sai Bojnal's earlier numerical refinement. Original algorithm, compiler, and proof attribution is preserved.

Run the complete verification with:

```bash
cd verified
lake exe cache get
python3 verify.py
```

The verification builds the sources, checks that the challenge statement is unchanged, checks the exact rational theorem type, and audits all transitive axioms of that theorem. The [successful verification transcript](verified/verification.txt) and [checked source hashes](verified/verification.json) record the local result. The [independent candidate CI run](https://github.com/JoshuaQFEX/apsp-bound/actions/runs/39424373480) also passed both proof jobs. See [provenance and changed files](verified/MODIFICATIONS.md) and the [full build instructions](verified/README.md).

**This complete theorem is for 2.995560766.** The faster exponent **2.9929479187094**, described below, remains conditional on unformalized machine implementation obligations. The complete proof above does not establish that faster exponent. Local proof checking does not mean the challenge has reviewed or accepted this new result.

The [`machine/` directory](machine/README.md) contains two newly checked components toward the faster construction: a selected-row controller and all twelve local row encoders. Their execution, memory, and resource proofs are complete at the component level. The [encoder refinement](machine/refinement/README.md) also proves equality to the imported upstream row definition and an execution-time comparison with its scalar counter. The [remaining full-program obligations](machine/MACHINE_OBLIGATIONS.md) are stated explicitly.

## Faster conditional numerical refinement

An exact numerical certificate for the conditional deterministic integer APSP bound

$$O\!\left(n^{2.9929479187094}\right).$$

This refines the exponent **2.99294792** displayed as **Claimed** on the [Big O Speedrun APSP challenge](https://bigospeedrun.com/apsp) when examined on 20 October 2026. The decrease in the exponent is exactly **0.0000000012906**.

Read the [research note (PDF)](apsp_refinement.pdf), its [LaTeX source](apsp_refinement.tex), the [complete word-RAM proof](verified/README.md), or the [faster bound’s numerical Lean proof](lean/README.md).

## What the conditional certificate establishes

The accompanying Lean development proves **47 strict numerical inequalities and all exact stage identities**, with the entropy expressions defined using Mathlib's actual `Real.log`. It also proves a common reserve of **2 × 10⁻¹⁴** in the inequalities, controls all stages of both phases, and derives the stated exponent for the explicit mathematical cost ledger, including fixed logarithmic factors and upward rounding. The independent Python checker verifies the same numerical conditions using rational interval arithmetic. These conditions come from the aligned Walsh embedding, polynomial query cache, and composite-incidence construction in the [pinned upstream note](https://github.com/shreshth-s/thin-matrix-results/blob/8a21eaae81599913dba562727e03a9b48c36a5b9/outputs/exponent-improvement.tex).

The APSP bound is **conditional on that construction's written algorithmic proof and word-RAM cost interpretation**. The theorems in `lean/` establish the numerical certificate and the mathematical cost ledger. A complete challenge `EndStatement.APSP` theorem at **2.9929479187094**, including a correct machine program and a proof of its execution cost, remains unproved. The fixed stage count is enormous and the certified slack is very small; no global optimality or practical speedup is claimed.

The contribution here is a refined rational parameter witness, its Lean formalization, an independently implemented exact checker, a reproducible numerical search, and an explanatory note. The underlying algorithm and adapted proof architecture are attributed to the sources below and in the Lean file headers. The materials were prepared with AI assistance; the separate reviews mentioned in the note were AI-agent reviews. This repository records the refinement and is not a submission to, or verification by, the challenge.

## Check the numerical Lean proof

The project pins **Lean 4.33.1** and an exact Mathlib commit. Follow the [setup instructions](lean/README.md), then run:

```bash
cd lean
lake build
lake env lean Audit.lean
```

The main results are `ApspBound.Analytic.analyticNumericalCertificate` and `ApspBound.Ledger.refinedExponentBigO`. The audit rejects any transitive axiom beyond `propext`, `Classical.choice`, and `Quot.sound`; the development uses no admitted proofs or native decision axioms. The [Lean README](lean/README.md) states the exact theorem and the remaining machine-program obligations. [Citation metadata](CITATION.cff) records the author, affiliation, and contact.

## Reproduce the certificate

Use **Python 3.10 or later**. No third-party Python packages are required. From this directory, run:

```bash
python3 verify_certificate.py --json certificate.json
```

The final output should include:

```text
PASS: 47 strict rational inequalities and all exact stage identities.
Certified exponent: 2.9929479187094
Smallest certified runtime gap: 0.0000000000000224020591996589
This certifies numerical feasibility, not the full word-RAM theorem.
```

The script reads the exact decimal strings in [parameters.json](parameters.json). All verification arithmetic uses Python's `Fraction`. Logarithms are enclosed by a 40-term positive series with an explicit rational remainder bound; decimal output is rounded outward and does not decide whether a condition passes. Explicit exceptions keep the checks active under `python3 -O` as well.

[certificate.json](certificate.json) contains the machine-readable results, including all lower and upper bounds. [verification.txt](verification.txt) records the successful console output.

## Exact parameters

Treat each decimal below as an exact rational number.

| Parameter | Exact value |
| --- | ---: |
| `c` | `10.665500244065729` |
| `theta` | `0.06529782369872631` |
| `b` | `0.046046352103722105` |
| `R` | `1000000000000` |
| `S` | `768979037380` |
| Target saving `delta` | `0.0070520812906` |
| Exponent `3 - delta` | `2.9929479187094` |

The stage variables are defined exactly by `eta = b/R`, `u = S*eta`, `v = (R-S)*eta`, and `e = b+u`. The note derives the cost expressions and explains why checking the endpoints covers both phases of the construction.

## Reproduce the numerical search

```bash
python3 optimize_parameters.py
```

This optional search uses Python `Decimal` with 80-digit working precision. It locates a stationary point of the balanced limiting objective, guiding the choice of the rational witness. It does **not** prove a global optimum, and the exact checker does not depend on its output. The recorded search output is in [optimization.txt](optimization.txt).

## Build the note

With pdfLaTeX and the packages listed in the LaTeX source installed:

```bash
pdflatex -interaction=nonstopmode -halt-on-error apsp_refinement.tex
pdflatex -interaction=nonstopmode -halt-on-error apsp_refinement.tex
```

The second pass resolves internal references. The resulting PDF is [apsp_refinement.pdf](apsp_refinement.pdf).

## Upstream finite checks

Three upstream finite checkers were also rerun during preparation. These provide finite corroboration of parts of the inherited construction; they do not prove its asymptotic correctness and are separate from the exact parameter certificate in this repository.

| Upstream checker | Observed result |
| --- | --- |
| [Aligned embedding](https://github.com/shreshth-s/thin-matrix-results/blob/8a21eaae81599913dba562727e03a9b48c36a5b9/outputs/check_five_term_aligned_embedding.py) | 352 original matrix outputs checked |
| [Aligned cache](https://github.com/shreshth-s/thin-matrix-results/blob/8a21eaae81599913dba562727e03a9b48c36a5b9/outputs/check_five_term_aligned_cache.py) | 34 arbitrary signed-array queries and 20 encoders checked |
| [Aligned integration](https://github.com/shreshth-s/thin-matrix-results/blob/8a21eaae81599913dba562727e03a9b48c36a5b9/outputs/check_five_term_aligned_integration.py) | 530 normalized scalar and cyclic coefficients checked |

To reproduce those checks, use the full upstream checkout so its supporting modules are available:

```bash
git clone https://github.com/shreshth-s/thin-matrix-results.git
cd thin-matrix-results
git checkout --detach 8a21eaae81599913dba562727e03a9b48c36a5b9
python3 outputs/check_five_term_aligned_embedding.py
python3 outputs/check_five_term_aligned_cache.py
python3 outputs/check_five_term_aligned_integration.py
```

## Attribution and references

The direct algorithmic source is GitHub author **shreshth-s**, *Improving the displayed exponents in arXiv:2610.06783v1*, in [`thin-matrix-results/outputs/exponent-improvement.tex`](https://github.com/shreshth-s/thin-matrix-results/blob/8a21eaae81599913dba562727e03a9b48c36a5b9/outputs/exponent-improvement.tex), pinned to commit `8a21eaae81599913dba562727e03a9b48c36a5b9`. Relevant dependencies include the aligned Walsh embedding and polynomial-cache lemmas and equations (A1)–(A13).

The construction builds on:

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783), 2026.
- Ruhollah Majdoddin, [*Thin matrix products up to D ≤ N^0.172 and lossless reductions for 3SUM, Exact Triangle and APSP, with 3SUM over abelian groups and a dichotomy for coordinatewise problems*](https://arxiv.org/abs/2610.17420v1), 2026.

The [research note](apsp_refinement.pdf) identifies the inherited proof dependencies and the limits of the refinement in more detail.
