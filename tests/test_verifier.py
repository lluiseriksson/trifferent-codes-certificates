"""Unit, AST zero-float, and adversarial forgery tests for TRIFF-CERT-1.0."""

from __future__ import annotations

import ast
import copy
import json
from pathlib import Path

import pytest

from src.trifferent_verifier import SCHEMA, exact_log_enclosure, verify_certificate, verify_file

ROOT = Path(__file__).resolve().parent.parent
CERT_DIR = ROOT / "certificates"
VERIFIER_PATH = ROOT / "src" / "trifferent_verifier.py"


def _load(cid: str) -> dict:
    return json.loads((CERT_DIR / f"{cid}.json").read_text(encoding="utf-8"))


@pytest.mark.parametrize("cid", [f"C{i:02d}" for i in range(1, 17)])
def test_canonical_certificate_passes(cid: str) -> None:
    res = verify_file(CERT_DIR / f"{cid}.json")
    assert res["file"] == f"{cid}.json"


def test_verifier_is_ast_zero_float() -> None:
    tree = ast.parse(VERIFIER_PATH.read_text(encoding="utf-8"))
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, float):
            pytest.fail(f"float literal found: {node.value}")
        if isinstance(node, ast.Name) and node.id == "float":
            pytest.fail("float builtin referenced")
        if isinstance(node, ast.Import):
            for alias in node.names:
                assert alias.name not in {"math", "numpy", "scipy", "decimal"}
        if isinstance(node, ast.ImportFrom):
            assert node.module not in {"math", "numpy", "scipy", "decimal"}


def test_reject_wrong_schema() -> None:
    c = _load("C01")
    c["schema"] = "WRONG-1.0"
    with pytest.raises(ValueError, match="schema"):
        verify_certificate(c)


def test_reject_unknown_mode() -> None:
    c = _load("C01")
    c["mode"] = "bogus"
    with pytest.raises(ValueError, match="unknown mode"):
        verify_certificate(c)


def test_reject_forged_tetracode_distance() -> None:
    c = _load("C01")
    c["claimed_constant_distance"] = 2
    with pytest.raises(ValueError, match="distance mismatch"):
        verify_certificate(c)


def test_reject_forged_agl19_order() -> None:
    c = _load("C01")
    c["claimed_agl19_order"] = 70
    with pytest.raises(ValueError, match="AGL\\(1,9\\) order mismatch"):
        verify_certificate(c)


def test_reject_forged_NQ() -> None:
    c = _load("C02")
    c["claimed_NQ"] -= 1
    with pytest.raises(ValueError, match="NQ mismatch"):
        verify_certificate(c)


def test_reject_forged_H_table() -> None:
    c = _load("C02")
    c["claimed_H"][0] += 1
    with pytest.raises(ValueError, match="H_j table mismatch"):
        verify_certificate(c)


def test_reject_non_trifferent_code() -> None:
    c = copy.deepcopy(_load("C03"))
    c["codewords"] = [[0, 0], [0, 1], [1, 0], [1, 1]]  # no 2 anywhere -> not trifferent!
    with pytest.raises(ValueError, match="NOT trifferent"):
        verify_certificate(c)


def test_reject_duplicate_codeword() -> None:
    c = copy.deepcopy(_load("C03"))
    c["codewords"].append([0, 0])
    c["claimed_M"] = 5
    with pytest.raises(ValueError, match="duplicate codeword"):
        verify_certificate(c)


def test_reject_invalid_symbol() -> None:
    c = copy.deepcopy(_load("C03"))
    c["codewords"][0][0] = 3
    with pytest.raises(ValueError, match="symbols must be in"):
        verify_certificate(c)


def test_reject_forged_double_box_count_D() -> None:
    c = _load("C05")
    c["claimed_D"] += 1
    with pytest.raises(ValueError, match="box counts mismatch"):
        verify_certificate(c)


def test_reject_forged_hole_count_Z() -> None:
    c = _load("C05")
    c["claimed_Z"] -= 1
    with pytest.raises(ValueError, match="box counts mismatch"):
        verify_certificate(c)


def test_reject_g_below_korner_marton() -> None:
    c = _load("C09")
    c["claimed_g"] = [23, 20]
    with pytest.raises(ValueError, match="Korner-Marton"):
        verify_certificate(c)


def test_reject_g_exceeding_Nbar() -> None:
    c = _load("C10")
    c["claimed_g"] = [2, 1]  # way above N_bar^(1/n)
    with pytest.raises(ValueError, match="failed to certify N_bar"):
        verify_certificate(c)


def test_reject_false_verify_nbar_flag() -> None:
    c = _load("C09")
    c["verify_Nbar_ge_gn"] = False
    c["claimed_g"] = [100, 1]
    with pytest.raises(ValueError, match="verify_Nbar_ge_gn must be true"):
        verify_certificate(c)


def test_reject_forged_port_cut() -> None:
    c = copy.deepcopy(_load("C09"))
    c["claimed_port_cuts"]["pair_state_min"] = [70, 223]
    with pytest.raises(ValueError, match="port-profile cuts mismatch"):
        verify_certificate(c)


def test_exact_log_enclosure_rejects_int() -> None:
    with pytest.raises(TypeError, match="Fraction"):
        exact_log_enclosure(10)  # type: ignore[arg-type]


def test_reject_non_reduced_fraction() -> None:
    c = _load("C12")
    c["claimed_g"] = [58, 50]
    with pytest.raises(ValueError, match="lowest terms"):
        verify_certificate(c)


def test_reject_float_in_fraction() -> None:
    c = _load("C09")
    c["claimed_g"] = [1162579.0, 1000000]
    with pytest.raises(ValueError, match="exact ints"):
        verify_certificate(c)


def test_reject_bool_as_int() -> None:
    c = _load("C09")
    c["log_series_terms_q"] = True
    with pytest.raises(ValueError, match="exact int"):
        verify_certificate(c)


def test_reject_wrong_blocklength_per_k() -> None:
    c = _load("C09")
    c["blocklength_per_k"] = 120
    with pytest.raises(ValueError, match="n = 124\\*k"):
        verify_certificate(c)
