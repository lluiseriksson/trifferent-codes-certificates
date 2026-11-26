"""Generate 3 publication-quality PNG figures for TRIFF-CERT-1.0."""

from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from src.trifferent_verifier import compute_local_rule_pair_counts, exact_log_enclosure


def main() -> None:
    out = Path(__file__).resolve().parent.parent / "paper" / "figures"
    out.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({
        "font.size": 10,
        "axes.titlesize": 11,
        "axes.labelsize": 10,
        "legend.fontsize": 8.5,
        "figure.dpi": 300,
    })

    # Figure 1: Exact Pair-Agreement Distribution H_j / |Q| for Local Rule Q (mult (4,3,1^7))
    nq, H = compute_local_rule_pair_counts()
    js = list(range(15))
    probs = [H[j] / nq for j in js]

    fig, ax = plt.subplots(figsize=(6.4, 3.7))
    ax.bar(js, probs, color="#2563eb", alpha=0.88, edgecolor="#1e3a8a")
    ax.axvline(14 / 9, color="#b91c1c", linestyle="--", linewidth=1.8, label=r"Exact mean $\mathbb{E}[J] = 14/9 \approx 1.556$")
    ax.set_xlabel(r"Number of agreeing coordinates $j \in \{0,\dots,14\}$")
    ax.set_ylabel(r"Exact probability $H_j / |Q|$")
    ax.set_title(r"Pair-Agreement Distribution of Local Rule $Q$ ($|Q| \approx 4.36 \times 10^{10}$)")
    ax.set_xticks(js)
    ax.grid(True, axis="y", linestyle=":", alpha=0.5)
    ax.legend(loc="upper right", frameon=True)
    fig.tight_layout()
    fig.savefig(out / "fig1_local_rule_pair_distribution.png", dpi=300)
    plt.close(fig)

    # Figure 2: Exponential Base Comparison & Exact Rational Log-Enclosure Convergence
    bases = [
        ("Körner–Marton\n$(9/5)^{1/4}$", (9 / 5) ** 0.25, "#64748b"),
        ("Yuan–Zhu\n(2026)", 1.158344, "#0284c7"),
        ("Disjoint $Q$\n(no overlap)", 1.16007, "#059669"),
        ("Bhandari–Khetan\n(certified $g$)", 1.162579, "#b91c1c"),
    ]
    fig, ax = plt.subplots(figsize=(6.4, 3.6))
    xs = list(range(len(bases)))
    vals = [b[1] for b in bases]
    cols = [b[2] for b in bases]
    bars = ax.bar(xs, [v - 1.155 for v in vals], bottom=1.155, color=cols, alpha=0.88, width=0.55)
    for bar, v in zip(bars, vals):
        ax.text(bar.get_x() + bar.get_width() / 2, v + 0.00025, f"{v:.6f}", ha="center", va="bottom", fontsize=8.5, fontweight="bold")
    ax.set_xticks(xs)
    ax.set_xticklabels([b[0] for b in bases], fontsize=8.5)
    ax.set_ylim(1.155, 1.1642)
    ax.set_ylabel(r"Exponential base $g$ in $T(n) = \Omega(g^n)$")
    ax.set_title(r"Trifferent Code Exponential Base Progression ($g^4 > 9/5$ Certified)")
    ax.grid(True, axis="y", linestyle=":", alpha=0.5)
    fig.tight_layout()
    fig.savefig(out / "fig2_exponential_base_progression.png", dpi=300)
    plt.close(fig)

    # Figure 3: Appendix A.4 Exact Rational Log-Enclosure Width vs Series Order q
    qs = [5, 10, 15, 20, 30, 40]
    widths_g = []
    widths_q = []
    for q in qs:
        lo_g, hi_g = exact_log_enclosure(Fraction(1162579, 1000000), q)
        lo_nq, hi_nq = exact_log_enclosure(Fraction(nq, 1), q)
        widths_g.append(float(hi_g - lo_g))
        widths_q.append(float(hi_nq - lo_nq))

    fig, ax = plt.subplots(figsize=(6.4, 3.6))
    ax.semilogy(qs, widths_q, "o-", color="#7c3aed", linewidth=2.0, markersize=6, label=r"Interval width for $\ln |Q|$")
    ax.semilogy(qs, widths_g, "s--", color="#0284c7", linewidth=2.0, markersize=5.5, label=r"Interval width for $\ln(1.162579)$")
    ax.set_xlabel(r"Rational Taylor series order $q$ (Appendix A.4)")
    ax.set_ylabel(r"Exact interval width $\mathrm{hi} - \mathrm{lo}$ (log scale)")
    ax.set_title(r"Zero-Float Exact Rational Logarithm Enclosure Precision")
    ax.grid(True, which="both", linestyle=":", alpha=0.45)
    ax.legend(loc="upper right", frameon=True)
    fig.tight_layout()
    fig.savefig(out / "fig3_log_enclosure_precision.png", dpi=300)
    plt.close(fig)

    print("Generated 3 figures in", out)


if __name__ == "__main__":
    main()
