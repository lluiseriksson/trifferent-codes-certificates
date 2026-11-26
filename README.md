# Formal Algebraic, Combinatorial, and Rational-Enclosure Certification for Trifferent Codes (`TRIFF-CERT-1.0`)

**Author:** Lluis Eriksson  
**Target Preprint:** Siddharth Bhandari and Abhishek Khetan, *"Constructions and Upper Bounds for Trifferent Codes"* (`arXiv:2611.33212v1`, November 2026)  
**Licenses:** Manuscript & figures `CC-BY-4.0`; Lean 4 kernel, verifier, tests, and certificates `MIT`

## Artifact Overview

This repository provides an independent, machine-checked Lean 4.35.0 kernel and zero-float exact rational certificate suite (`TRIFF-CERT-1.0`) auditing core algebraic, coding-theoretic, binary-box, and rational-enclosure components of `arXiv:2611.33212v1`:

1. **Constructive Lean 4.35.0 Kernel (`lean/TrifferentCodesCert.lean`):** 18 constructive theorems (`0 sorry`, `0` custom axioms, `0 Classical.choice`, `0` warnings), including direct proofs over `Fin 3` of the 9-word tetracode's constant Hamming distance 3 and rainbow-iff-distinct equivalence, `AGL(1,9)` invertibility and bijectivity over $\mathbb{F}_3[i]/(i^2+1)$, exact $|Q|=43{,}589{,}145{,}600$, integer proof of $1.162579^4 > 9/5$, wiring/port-cut rational identities, Section 3.6 binomial $\binom{t}{3} \ge 3t - 8$, ternary Turán inequality, $D \le 96Z/n$ density bound, and Appendix A.4 uniform logarithm-enclosure denominator bound $1 - \chi^2 \ge 8/9$.
2. **AST-Audited Zero-Float Rational Verifier (`src/trifferent_verifier.py`):** Four verification modes (`tetracode_and_agl19`, `local_rule_counts`, `section3_upper_bound` including exhaustive Lemma 3.2 central-hole contradiction check & $3^n$ binary-box enumeration, and `log_enclosures_and_port_cuts` implementing Appendix A.4 exact rational $\ln \xi$ enclosures proving $\bar{N} > g^n$).
3. **16 Canonical Certificates (`certificates/C01.json`–`C16.json`)** and **37 Unit & Adversarial Forgery Tests (`tests/test_verifier.py`)**.

## Quick Reproduction

```bash
cd lean && lake build && cd ..
python scripts/generate_certificates.py
python -m src.trifferent_verifier certificates/
pytest -q
python scripts/generate_figures.py
```
