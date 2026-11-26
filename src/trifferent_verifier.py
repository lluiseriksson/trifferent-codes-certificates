r"""Zero-float exact rational verifier for Trifferent Codes Constructions & Upper Bounds.

Certifies the 9-word tetracode over F_3^4, AGL(1,9) sharp 2-transitivity,
exact local-rule Q cardinality (|Q|=43589145600) and pair counts H_0..H_14 via
binomial inversion, Section 3 Lemma 3.2 central-hole contradiction table &
double-box/hole density bounds D <= (96/n)Z on finite trifferent codes, and
Appendix A.4 exact rational logarithm enclosures proving \bar{N} >= g^n for
g = 1162579/1000000 and safe port-profile cuts (Eqs. 41-42) from Siddharth
Bhandari and Abhishek Khetan (arXiv:2611.33212v1, Nov 2026).

Schema: TRIFF-CERT-1.0
Zero floats: uses strictly `int` and `fractions.Fraction` (no `float`, no `math`).
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction
from itertools import combinations, permutations, product
from pathlib import Path
from typing import Any, Dict, List, Sequence, Tuple

SCHEMA = "TRIFF-CERT-1.0"


def _gcd(a: int, b: int) -> int:
    a, b = abs(a), abs(b)
    while b:
        a, b = b, a % b
    return a


def _factorial(n: int) -> int:
    r = 1
    for i in range(2, n + 1):
        r *= i
    return r


def _comb(n: int, k: int) -> int:
    if k < 0 or k > n:
        return 0
    return _factorial(n) // (_factorial(k) * _factorial(n - k))


def _req_int(obj: Dict[str, Any], key: str) -> int:
    if key not in obj:
        raise ValueError(f"missing integer field '{key}'")
    v = obj[key]
    if isinstance(v, bool) or not isinstance(v, int):
        raise ValueError(f"field '{key}' must be exact int")
    return v


def _req_bool(obj: Dict[str, Any], key: str) -> bool:
    if key not in obj:
        raise ValueError(f"missing boolean field '{key}'")
    v = obj[key]
    if not isinstance(v, bool):
        raise ValueError(f"field '{key}' must be bool")
    return v


def _req_list(obj: Dict[str, Any], key: str) -> List[Any]:
    if key not in obj:
        raise ValueError(f"missing list field '{key}'")
    v = obj[key]
    if not isinstance(v, list):
        raise ValueError(f"field '{key}' must be list")
    return v


def _req_frac(obj: Dict[str, Any], key: str) -> Fraction:
    if key not in obj:
        raise ValueError(f"missing rational field '{key}'")
    v = obj[key]
    if not (isinstance(v, list) and len(v) == 2):
        raise ValueError(f"field '{key}' must be [num, den]")
    p, q = v
    if isinstance(p, bool) or not isinstance(p, int) or isinstance(q, bool) or not isinstance(q, int):
        raise ValueError(f"field '{key}' entries must be exact ints")
    if q <= 0 or _gcd(p, q) != 1:
        raise ValueError(f"field '{key}' must have q > 0 and lowest terms")
    return Fraction(p, q)


def exact_log_enclosure(xi: Fraction, terms_q: int = 20) -> Tuple[Fraction, Fraction]:
    """Appendix A.4 exact rational interval [lo, hi] enclosing ln(xi) for xi > 0."""
    if not isinstance(xi, Fraction):
        raise TypeError("exact_log_enclosure requires exact fractions.Fraction input")
    if xi <= 0:
        raise ValueError("log requires strictly positive rational")
    if terms_q < 1:
        raise ValueError("terms_q must be >= 1")
    # Write xi = 2^p * y with 1 <= y < 2
    p = 0
    y = xi
    while y >= 2:
        y /= 2
        p += 1
    while y < 1:
        y *= 2
        p -= 1

    def _enclose_y(val: Fraction, q: int) -> Tuple[Fraction, Fraction]:
        chi = (val - 1) / (val + 1)
        chi2 = chi * chi
        acc = Fraction(0)
        pow_c = chi
        for i in range(q):
            acc += pow_c / (2 * i + 1)
            pow_c *= chi2
        lo = 2 * acc
        rem = (2 * pow_c) / ((2 * q + 1) * (1 - chi2))
        return lo, lo + rem

    lo_y, hi_y = _enclose_y(y, terms_q)
    lo_2, hi_2 = _enclose_y(Fraction(2, 1), terms_q)
    if p >= 0:
        return p * lo_2 + lo_y, p * hi_2 + hi_y
    return p * hi_2 + lo_y, p * lo_2 + hi_y


def compute_local_rule_pair_counts() -> Tuple[int, List[int]]:
    """Appendix A.1 exact pair counts H_0..H_14 for Q = {x in F_9^14 : mult (4,3,1^7)} via binomial inversion."""
    a = (4, 3, 1, 1, 1, 1, 1, 1, 1)
    # Distinct rearrangements of a: choose which index gets 4 (9 ways) and which gets 3 (8 ways) -> 72 vectors
    rearrs = []
    for i4 in range(9):
        for i3 in range(9):
            if i3 == i4:
                continue
            b = [1] * 9
            b[i4] = 4
            b[i3] = 3
            rearrs.append(tuple(b))
    # Accumulate polynomial sum_{b in Rearr(a)} prod_{i=1}^9 (sum_{k=0}^{min(a_i,b_i)} C(a_i,k)/(b_i-k)! u^k)
    poly = [Fraction(0)] * 15
    for b in rearrs:
        cur = [Fraction(1)]
        for ai, bi in zip(a, b):
            m = min(ai, bi)
            fac_poly = [Fraction(_comb(ai, k), _factorial(bi - k)) for k in range(m + 1)]
            nxt = [Fraction(0)] * (len(cur) + len(fac_poly) - 1)
            for idx1, c1 in enumerate(cur):
                if c1 == 0:
                    continue
                for idx2, c2 in enumerate(fac_poly):
                    nxt[idx1 + idx2] += c1 * c2
            cur = nxt
        for j in range(15):
            if j < len(cur):
                poly[j] += cur[j]
    deltas = []
    for j in range(15):
        val = _factorial(14 - j) * poly[j]
        if val.denominator != 1:
            raise ValueError("non-integer Delta_j in binomial inversion")
        deltas.append(val.numerator)
    H = []
    for i in range(15):
        s = 0
        for j in range(i, 15):
            term = _comb(j, i) * deltas[j]
            s += term if (j - i) % 2 == 0 else -term
        H.append(s)
    nq = 9 * 8 * (_factorial(14) // (_factorial(4) * _factorial(3)))
    return nq, H


def verify_tetracode_and_agl19(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 1: Exact tetracode F_3^4 trifference/distance & AGL(1,9) sharp 2-transitivity."""
    claimed_code_size = _req_int(cert, "claimed_code_size")
    claimed_dist = _req_int(cert, "claimed_constant_distance")
    claimed_triples = _req_int(cert, "claimed_rainbow_triples")
    claimed_agl_order = _req_int(cert, "claimed_agl19_order")
    claimed_pairs = _req_int(cert, "claimed_ordered_distinct_pairs")

    f9 = [(a, b) for a in range(3) for b in range(3)]
    code = [(a, b, (a + b) % 3, (a - b) % 3) for (a, b) in f9]
    if len(code) != claimed_code_size:
        raise ValueError(f"tetracode size mismatch: {len(code)} vs {claimed_code_size}")
    for i in range(len(code)):
        for j in range(i + 1, len(code)):
            d = sum(1 for x, y in zip(code[i], code[j]) if x != y)
            if d != claimed_dist:
                raise ValueError(f"tetracode distance mismatch: got {d}, expected {claimed_dist}")
    triples_ok = 0
    for c1, c2, c3 in combinations(code, 3):
        if not any(len({c1[k], c2[k], c3[k]}) == 3 for k in range(4)):
            raise ValueError("tetracode triple failed rainbow test")
        triples_ok += 1
    if triples_ok != claimed_triples:
        raise ValueError(f"rainbow triple count mismatch: {triples_ok} vs {claimed_triples}")

    # Build AGL(1, 9) over F_3[i]/(i^2+1): (a,b) -> (a'*a + 2*a''*b + b', a''*a + a'*b + b'')
    maps = []
    for ap, app, bp, bpp in product(range(3), repeat=4):
        if (ap, app) == (0, 0):
            continue
        det = (ap * ap + app * app) % 3
        if det == 0:
            raise ValueError("unexpected zero determinant in F_9*")
        img = {
            (a, b): ((ap * a + 2 * app * b + bp) % 3, (app * a + ap * b + bpp) % 3)
            for (a, b) in f9
        }
        if len(set(img.values())) != 9:
            raise ValueError("non-bijective affine map in AGL(1,9)")
        maps.append(img)
    if len(maps) != claimed_agl_order:
        raise ValueError(f"AGL(1,9) order mismatch: {len(maps)} vs {claimed_agl_order}")
    # Sharp 2-transitivity: for fixed (0,0) != (1,0), images (f(0,0), f(1,0)) hit every ordered distinct pair once
    hit = [(m[(0, 0)], m[(1, 0)]) for m in maps]
    if len(set(hit)) != claimed_pairs or any(u == v for u, v in hit):
        raise ValueError("AGL(1,9) failed sharp 2-transitivity check")
    return {
        "mode": "tetracode_and_agl19",
        "code_size": len(code),
        "agl19_order": len(maps),
        "rainbow_triples": triples_ok,
    }


def verify_local_rule_counts(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 2: Exact Appendix A.1 local rule |Q| and pair-count polynomial H_0..H_14."""
    claimed_nq = _req_int(cert, "claimed_NQ")
    claimed_h = [_req_int({"x": v}, "x") for v in _req_list(cert, "claimed_H")]
    claimed_expected_agreements = _req_frac(cert, "claimed_expected_agreements")
    if len(claimed_h) != 15:
        raise ValueError("claimed_H must have length 15 (j=0..14)")
    nq, H = compute_local_rule_pair_counts()
    if nq != claimed_nq:
        raise ValueError(f"NQ mismatch: exact {nq}, claimed {claimed_nq}")
    if H != claimed_h:
        raise ValueError(f"H_j table mismatch: exact {H}")
    if sum(H) != nq or H[14] != 1 or any(v < 0 for v in H):
        raise ValueError("H_j consistency checks failed")
    # Independent theoretical expectation of agreements of two uniform words in Q:
    # By symmetry of positions, E[#agreements] = 14 * sum_label P(X_1=label)^2 = 14 * (4^2 + 3^2 + 7*1^2)/14^2 = 32/14 = 16/7?
    # Wait: labels are NOT fixed! Each position of X in Q is uniform on F_9, so E[#agreements] = 14 * (1/9) = 14/9!
    exp_agree = Fraction(sum(j * H[j] for j in range(15)), nq)
    if exp_agree != Fraction(14, 9) or exp_agree != claimed_expected_agreements:
        raise ValueError(f"expected agreements mismatch: got {exp_agree}, claimed {claimed_expected_agreements}")
    return {
        "mode": "local_rule_counts",
        "NQ": nq,
        "H0": H[0],
        "H14": H[14],
        "expected_agreements": [exp_agree.numerator, exp_agree.denominator],
    }


def verify_section3_upper_bound(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 3: Section 3 binary-box audit on finite trifferent codes + Lemma 3.2 central-hole check."""
    check_lemma32 = _req_bool(cert, "verify_lemma32_table")
    n = _req_int(cert, "blocklength_n")
    raw_words = _req_list(cert, "codewords")
    claimed_m = _req_int(cert, "claimed_M")
    claimed_d = _req_int(cert, "claimed_D")
    claimed_z = _req_int(cert, "claimed_Z")
    claimed_a = _req_int(cert, "claimed_A")

    if n < 2 or n > 6:
        raise ValueError("blocklength_n must be in 2..6 for exact 3^n binary-box enumeration")
    words: List[Tuple[int, ...]] = []
    seen = set()
    for w in raw_words:
        if not isinstance(w, list) or len(w) != n:
            raise ValueError("each codeword must be list of length n")
        wt = tuple(_req_int({"x": c}, "x") for c in w)
        if any(c not in (0, 1, 2) for c in wt):
            raise ValueError("codeword symbols must be in {0, 1, 2}")
        if wt in seen:
            raise ValueError("duplicate codeword")
        seen.add(wt)
        words.append(wt)
    M = len(words)
    if M != claimed_m:
        raise ValueError(f"code size M mismatch: {M} vs {claimed_m}")
    # Exhaustive trifference verification
    for w1, w2, w3 in combinations(words, 3):
        if not any(len({w1[i], w2[i], w3[i]}) == 3 for i in range(n)):
            raise ValueError("code is NOT trifferent")

    # Exhaustive binary-box enumeration over all 3^n masks q in F_3^n
    # Box(q) = {x in C : x_i != q_i for all i}; f(q) = |Box(q)| in {0, 1, 2}
    box_counts: Dict[Tuple[int, ...], int] = {}
    D_count = 0
    Z_count = 0
    for q in product((0, 1, 2), repeat=n):
        cnt = sum(1 for w in words if all(w[i] != q[i] for i in range(n)))
        if cnt > 2:
            raise ValueError("binary box contains > 2 codewords (contradicts trifference)")
        box_counts[q] = cnt
        if cnt == 2:
            D_count += 1
        elif cnt == 0:
            Z_count += 1

    # Compute A = sum_{f(q)=0} d_q where d_q = |{i : q has a double-box neighbor in direction i}|
    # and independently check exact pair identities Eqs. (35)-(36)!
    A_boxes = 0
    for q, cnt in box_counts.items():
        if cnt != 0:
            continue
        dq = 0
        for i in range(n):
            has_double = False
            for alt in (0, 1, 2):
                if alt == q[i]:
                    continue
                q2 = q[:i] + (alt,) + q[i + 1:]
                if box_counts[q2] == 2:
                    has_double = True
                    break
            if has_double:
                dq += 1
        A_boxes += dq

    D_pair = 0
    A_pair_twice = 0
    for w1, w2 in combinations(words, 2):
        dist = sum(1 for a, b in zip(w1, w2) if a != b)
        D_pair += 1 << (n - dist)
        A_pair_twice += (n - dist) * (1 << (n - dist))
    if D_count != D_pair or 2 * A_boxes != A_pair_twice:
        raise ValueError("exact pair-count identities Eqs. (35)-(36) violated")
    if D_count != claimed_d or Z_count != claimed_z or A_boxes != claimed_a:
        raise ValueError(f"box counts mismatch: exact (D={D_count}, Z={Z_count}, A={A_boxes})")
    if M >= 4:
        # Check Theorem 3.1 core inequalities: 3*A <= 16*Z and n*D <= 96*Z
        if 3 * A_boxes > 16 * Z_count or n * D_count > 96 * Z_count:
            raise ValueError("Section 3.6 density inequality violated")

    if check_lemma32:
        # First-principles verification of Section 3.4 Lemma 3.2 (Coherence of the Central Hole):
        # Eq. (25) normalized core object O: constant words A0,A1,A2 and even-permutation words B0,B1,B2
        core_words = {
            "A0": (0, 0, 0), "A1": (1, 1, 1), "A2": (2, 2, 2),
            "B0": (0, 1, 2), "B1": (1, 2, 0), "B2": (2, 0, 1),
        }
        # Precondition 1: verify Eq. (25) core is trifferent
        for w1, w2, w3 in combinations(core_words.values(), 3):
            if not any(len({w1[c], w2[c], w3[c]}) == 3 for c in range(3)):
                raise ValueError("Lemma 3.2 Eq. (25) core failed trifference")

        # Precondition 2: verify h = (0, 2, 1) and h' = (1, 0, 2) are valid holes of core_words
        # (every core word agrees with h and h' in at least one coordinate, in fact exactly one!)
        h1, h2 = (0, 2, 1), (1, 0, 2)
        for hm in (h1, h2):
            for wname, w in core_words.items():
                agrees = [c for c in range(3) if w[c] == hm[c]]
                if len(agrees) != 1:
                    raise ValueError(f"Lemma 3.2 hole precondition failed for {hm} on {wname}")

        def _derive_contacts(hm: Tuple[int, int, int]) -> List[Tuple[str, str]]:
            pairs = []
            for c in range(3):
                hitting = sorted(k for k, w in core_words.items() if w[c] == hm[c])
                if len(hitting) != 2:
                    raise ValueError(f"expected 2 contacts in coord {c} for hole {hm}")
                pairs.append((hitting[0], hitting[1]))
            return pairs

        def _derive_new_prefixes(hm: Tuple[int, int, int], sign_map: Dict[str, int]) -> List[Tuple[int, int, int]]:
            # Prefixes in F_3^3 avoiding hm that form a rainbow core triple with every same-sign pair (w, w')
            same_sign_pairs = [
                (w1, w2) for (n1, w1), (n2, w2) in combinations(core_words.items(), 2)
                if sign_map[n1] == sign_map[n2]
            ]
            out = []
            for pref in product((0, 1, 2), repeat=3):
                if any(pref[c] == hm[c] for c in range(3)):
                    continue
                if all(any(len({pref[c], w1[c], w2[c]}) == 3 for c in range(3)) for w1, w2 in same_sign_pairs):
                    out.append(pref)
            return sorted(out)

        # Derive f on B from contact pairs at h = (0, 2, 1) and f(A) = (-1, +1, +1)
        contacts_h1 = _derive_contacts(h1)
        f_val: Dict[str, int] = {"A0": -1, "A1": 1, "A2": 1}
        for a_name, b_name in contacts_h1:
            f_val[b_name] = -f_val[a_name]
        if (f_val["B0"], f_val["B1"], f_val["B2"]) != (1, -1, -1):
            raise ValueError("Lemma 3.2 Eq. (31) f(B) contact sign derivation mismatch")

        # Derive X, Y from first principles (must yield exactly {(1, 1, 0), (2, 0, 2)} per Eq. 31)
        XY = _derive_new_prefixes(h1, f_val)
        if XY != [(1, 1, 0), (2, 0, 2)]:
            raise ValueError(f"Lemma 3.2 Eq. (31) X, Y derivation mismatch: got {XY}")

        # Derive Z, T and verify Eq. (32) contradiction across all 3 minus-sign positions r in {0, 1, 2}
        contacts_h2 = _derive_contacts(h2)
        expected_ZT = {
            0: [(0, 1, 1), (2, 2, 0)],
            1: [(0, 1, 0), (2, 2, 1)],
            2: [(0, 2, 0), (2, 1, 1)],
        }
        for r in (0, 1, 2):
            g_val: Dict[str, int] = {"A0": 1, "A1": 1, "A2": 1}
            g_val[f"A{r}"] = -1
            for a_name, b_name in contacts_h2:
                g_val[b_name] = -g_val[a_name]
            ZT = _derive_new_prefixes(h2, g_val)
            if ZT != expected_ZT[r]:
                raise ValueError(f"Lemma 3.2 Z, T derivation mismatch at r={r}: got {ZT}")
            # Exhaustively check ALL 16 sign assignments (x, y, z, t) in {-1, +1}^4 violate Eq. (32)
            for x, y, z, t in product((-1, 1), repeat=4):
                ok = True
                for (P, Pk) in ((XY[0], x), (XY[1], y)):
                    for (Q, Qj) in ((ZT[0], z), (ZT[1], t)):
                        for wname, w in core_words.items():
                            rainbow_core = any(len({P[c], Q[c], w[c]}) == 3 for c in range(3))
                            if not rainbow_core and (Qj, Pk) == (f_val[wname], g_val[wname]):
                                ok = False
                                break
                        if not ok:
                            break
                    if not ok:
                        break
                if ok:
                    raise ValueError(f"Lemma 3.2 failed: consistent sign assignment found at r={r}")
    return {
        "mode": "section3_upper_bound",
        "n": n,
        "M": M,
        "D": D_count,
        "Z": Z_count,
        "A": A_boxes,
    }


def verify_log_enclosures_and_port_cuts(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 4: Appendix A.4 exact rational log enclosures for N_bar > g^n & Eq. (41)-(42) cuts."""
    g = _req_frac(cert, "claimed_g")
    terms_q = _req_int(cert, "log_series_terms_q")
    n_per_k = _req_int(cert, "blocklength_per_k")
    verify_nbar = _req_bool(cert, "verify_Nbar_ge_gn")
    if not verify_nbar:
        raise ValueError("verify_Nbar_ge_gn must be true to certify Mode 4")
    if terms_q < 5 or terms_q > 80:
        raise ValueError("log_series_terms_q must be in 5..80")
    if n_per_k != 124:
        raise ValueError("certified construction requires n = 124*k")
    # Verify g beats Korner-Marton (9/5)^{1/4}
    if g ** 4 <= Fraction(9, 5):
        raise ValueError(f"g={g} does not beat Korner-Marton base (9/5)^(1/4)")

    # Validate Appendix A.2 safe port-profile cuts (Eqs. 41-42) against certificate fields
    cuts_raw = cert.get("claimed_port_cuts")
    if not isinstance(cuts_raw, dict):
        raise ValueError("missing claimed_port_cuts object")
    c_pair = _req_frac(cuts_raw, "pair_state_min")
    c_hA = _req_frac(cuts_raw, "all_equal_max")
    c_lin = _req_frac(cuts_raw, "linear_comb_max")
    c_close = _req_frac(cuts_raw, "close_pair_max")

    m2, m3, m, D = 9, 22, 31, 84
    delta = Fraction(3, 8)
    cut_pair = (3 * delta * m - m2) / D
    cut_hA = 1 - (Fraction(9, 2) * delta * m - m2) / D
    cut_lin = (6 * m * (1 - 2 * delta)) / D
    cut_close = (3 * delta * m) / D
    if (c_pair, c_hA, c_lin, c_close) != (cut_pair, cut_hA, cut_lin, cut_close):
        raise ValueError("Appendix A.2 safe port-profile cuts mismatch")

    # Unconditionally check Eq. (9): N_bar^(1/k) = 9^31 * (|Q| / 9^14)^6 > g^124 via exact log enclosure
    nq = 9 * 8 * (_factorial(14) // (_factorial(4) * _factorial(3)))
    lo_q, _ = exact_log_enclosure(Fraction(nq, 1), terms_q)
    _, hi_9 = exact_log_enclosure(Fraction(9, 1), terms_q)
    _, hi_g = exact_log_enclosure(g, terms_q)
    lhs_lo = 6 * lo_q - 53 * hi_9
    rhs_hi = 124 * hi_g
    if lhs_lo <= rhs_hi:
        raise ValueError("exact rational log enclosure failed to certify N_bar > g^n")
    return {
        "mode": "log_enclosures_and_port_cuts",
        "g": [g.numerator, g.denominator],
        "terms_q": terms_q,
        "certified_Nbar_gt_gn": True,
        "positive_log_margin": True,
    }


def verify_certificate(cert: Dict[str, Any]) -> Dict[str, Any]:
    if not isinstance(cert, dict):
        raise ValueError("certificate must be JSON object")
    if cert.get("schema") != SCHEMA:
        raise ValueError(f"expected schema '{SCHEMA}', got '{cert.get('schema')}'")
    mode = cert.get("mode")
    if mode == "tetracode_and_agl19":
        return verify_tetracode_and_agl19(cert)
    if mode == "local_rule_counts":
        return verify_local_rule_counts(cert)
    if mode == "section3_upper_bound":
        return verify_section3_upper_bound(cert)
    if mode == "log_enclosures_and_port_cuts":
        return verify_log_enclosures_and_port_cuts(cert)
    raise ValueError(f"unknown mode '{mode}'")


def verify_file(path: Path) -> Dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    res = verify_certificate(data)
    res["file"] = path.name
    return res


def main(argv: Sequence[str] | None = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    if not args:
        print("Usage: python -m src.trifferent_verifier <cert_or_dir> [...]")
        return 2
    files: List[Path] = []
    for a in args:
        p = Path(a)
        if p.is_dir():
            files.extend(sorted(p.glob("*.json")))
        else:
            files.append(p)
    if not files:
        print("No certificate files found.")
        return 1
    for f in files:
        res = verify_file(f)
        print(f"PASS  {f.name}  ({res['mode']})")
    print(f"VERIFIED {len(files)}/{len(files)} certificates under {SCHEMA}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
