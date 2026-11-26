"""Generate 16 canonical exact-rational certificates (C01-C16) for TRIFF-CERT-1.0."""

from __future__ import annotations

import json
import sys
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
from typing import Any, Dict, List, Tuple

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from src.trifferent_verifier import (
    SCHEMA,
    compute_local_rule_pair_counts,
    verify_certificate,
)


def _box_stats(n: int, words: List[List[int]]) -> Tuple[int, int, int]:
    wt = [tuple(w) for w in words]
    box_counts = {}
    D = Z = 0
    for q in product((0, 1, 2), repeat=n):
        cnt = sum(1 for w in wt if all(w[i] != q[i] for i in range(n)))
        box_counts[q] = cnt
        if cnt == 2:
            D += 1
        elif cnt == 0:
            Z += 1
    A = 0
    for q, cnt in box_counts.items():
        if cnt != 0:
            continue
        for i in range(n):
            if any(box_counts[q[:i] + (alt,) + q[i + 1:]] == 2 for alt in (0, 1, 2) if alt != q[i]):
                A += 1
    return D, Z, A


def _make_mode3(cid: str, desc: str, n: int, words: List[List[int]], check_l32: bool) -> Dict[str, Any]:
    D, Z, A = _box_stats(n, words)
    return {
        "schema": SCHEMA,
        "id": cid,
        "mode": "section3_upper_bound",
        "description": desc,
        "verify_lemma32_table": check_l32,
        "blocklength_n": n,
        "codewords": words,
        "claimed_M": len(words),
        "claimed_D": D,
        "claimed_Z": Z,
        "claimed_A": A,
    }


def generate_all(out_dir: Path) -> List[Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    nq, H = compute_local_rule_pair_counts()

    # Explicit finite trifferent codes (all verified by exhaustive triple check):
    # n=2, M=4 (optimal T(2)=4):
    c_n2_m4 = [[0, 0], [0, 1], [1, 2], [2, 2]]
    # n=3, M=6 (optimal T(3)=6):
    c_n3_m6 = [[0, 0, 0], [0, 1, 2], [1, 1, 1], [1, 2, 0], [2, 2, 2], [2, 0, 1]]
    # n=4, M=9 (Tetracode! Optimal T(4)=9)
    tetra = [[a, b, (a + b) % 3, (a - b) % 3] for a in range(3) for b in range(3)]
    # n=4, M=6 (subcode of tetracode)
    tetra6 = tetra[:6]
    # n=5, M=9 (lifted tetracode)
    c_n5_m9 = [w + [0] for w in tetra]
    # n=3, M=4 (4-word trifferent code, boundary M=4 for Eq. 37)
    c_n3_m4 = [[0, 0, 0], [0, 1, 2], [1, 2, 1], [2, 2, 0]]

    cuts_obj = {
        "pair_state_min": [69, 224],
        "all_equal_max": [31, 64],
        "linear_comb_max": [31, 56],
        "close_pair_max": [93, 224],
    }

    def _make_mode4(cid: str, desc: str, g_pair: List[int], q: int) -> Dict[str, Any]:
        return {
            "schema": SCHEMA,
            "id": cid,
            "mode": "log_enclosures_and_port_cuts",
            "description": desc,
            "claimed_g": g_pair,
            "log_series_terms_q": q,
            "blocklength_per_k": 124,
            "verify_Nbar_ge_gn": True,
            "claimed_port_cuts": dict(cuts_obj),
        }

    certs: List[Dict[str, Any]] = [
        # Mode 1: Tetracode & AGL(1,9) sharp 2-transitivity
        {
            "schema": SCHEMA,
            "id": "C01",
            "mode": "tetracode_and_agl19",
            "description": "9-word tetracode over F_3^4 (d=3, 84 rainbow triples) and 72-element AGL(1,9) sharp 2-transitivity",
            "claimed_code_size": 9,
            "claimed_constant_distance": 3,
            "claimed_rainbow_triples": 84,
            "claimed_agl19_order": 72,
            "claimed_ordered_distinct_pairs": 72,
        },
        # Mode 2: Exact Appendix A.1 local rule |Q| and pair-count polynomial H_0..H_14
        {
            "schema": SCHEMA,
            "id": "C02",
            "mode": "local_rule_counts",
            "description": "Appendix A.1 exact local rule |Q|=43589145600 and pair counts H_0..H_14 via binomial inversion",
            "claimed_NQ": nq,
            "claimed_H": H,
            "claimed_expected_agreements": [14, 9],
        },
        # Mode 3: Section 3 binary-box audit + Lemma 3.2 central-hole contradiction table
        _make_mode3("C03", "Optimal n=2, M=4 trifferent code + first-principles Lemma 3.2 central-hole contradiction (r=0,1,2)", 2, c_n2_m4, True),
        _make_mode3("C04", "Optimal n=3, M=6 trifferent code + first-principles Lemma 3.2 central-hole contradiction", 3, c_n3_m6, True),
        _make_mode3("C05", "Tetracode n=4, M=9 (optimal T(4)=9): exact D, Z, A, Eqs. (35)-(36), and D <= 96Z/n", 4, tetra, True),
        _make_mode3("C06", "Tetracode 6-word subcode (n=4, M=6): exact binary-box counts and 3A <= 16Z", 4, tetra6, False),
        _make_mode3("C07", "4-word n=3 trifferent code (boundary M=4 for Eq. 37): exact binary-box audit", 3, c_n3_m4, False),
        _make_mode3("C08", "9-word n=5 lifted tetracode: exact 3^5=243 binary-box audit and D <= 96Z/5", 5, c_n5_m9, False),
        # Mode 4: Appendix A.4 exact rational log enclosures & Appendix A.2 safe port cuts
        _make_mode4("C09", "Certified g = 1162579/1000000 with q=10 exact rational log terms: N_bar > g^n and Eq. (41)-(42) cuts", [1162579, 1000000], 10),
        _make_mode4("C10", "Certified g = 1162579/1000000 with q=20 exact rational log terms", [1162579, 1000000], 20),
        _make_mode4("C11", "Certified g = 1162579/1000000 with q=40 high-precision exact rational log terms (width < 10^-38)", [1162579, 1000000], 40),
        _make_mode4("C12", "Intermediate base g = 29/25 = 1.16 beating Korner-Marton with q=12 terms", [29, 25], 12),
        _make_mode4("C13", "Yuan-Zhu benchmark base g = 144793/125000 = 1.158344 with q=15 terms", [144793, 125000], 15),
        _make_mode4("C14", "Disjoint-block Q base g = 116007/100000 with q=15 terms showing N_bar > g^n", [116007, 100000], 15),
        _make_mode4("C15", "Exact Appendix A.2 safe port-profile cuts (69/224, 31/64, 31/56, 93/224) with q=8 terms", [1162579, 1000000], 8),
        _make_mode4("C16", "Tight certified base g = 1162579/1000000 with q=60 ultra-tight rational log enclosure", [1162579, 1000000], 60),
    ]

    written: List[Path] = []
    for cert in certs:
        verify_certificate(cert)
        p = out_dir / f"{cert['id']}.json"
        p.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
        written.append(p)
    return written


if __name__ == "__main__":
    root = Path(__file__).resolve().parent.parent
    files = generate_all(root / "certificates")
    print(f"Generated and verified {len(files)} certificates in {root / 'certificates'}.")
