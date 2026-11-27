"""Tests for the Lean bridge (riemann_lab.lean_bridge). The parser and numerics tests always run;
the build/audit test runs only where `lake` is installed and lean/ has been built."""
import pytest

from riemann_lab import lean_bridge as B

SAMPLE = """'RiemannLab.mellin_g' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannLab.blowup_limit' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'RiemannLab.scale_identity' does not depend on any axioms
"""


def test_parse_axioms():
    ax = B.parse_axioms(SAMPLE)
    assert ax["RiemannLab.mellin_g"] == {"propext", "Classical.choice", "Quot.sound"}
    assert "sorryAx" in ax["RiemannLab.blowup_limit"]
    assert ax["RiemannLab.scale_identity"] == set()


def _full(sorry_in=()):
    ax = {n: set(B.STANDARD_AXIOMS) for n in B.PROVED}
    ax.update({n: set(B.STANDARD_AXIOMS) | {"sorryAx"} for n in B.OPEN})
    for n in sorry_in:
        ax[n] = ax[n] | {"sorryAx"}
    return ax


def test_classify_accepts_expected_split():
    r = B.classify(_full())
    assert r["ok"] and set(r["proved"]) == set(B.PROVED) and set(r["open"]) == set(B.OPEN)


def test_classify_rejects_sorry_in_proved():
    r = B.classify(_full(["RiemannLab.mellin_Mt"]))
    assert not r["ok"] and any("mellin_Mt" in p for p in r["problems"])


def test_classify_rejects_stale_open_list_and_extra_axioms():
    ax = _full()
    ax["RiemannLab.blowup_limit"] = set(B.STANDARD_AXIOMS)
    ax["RiemannLab.mellin_g"] = ax["RiemannLab.mellin_g"] | {"RiemannLab.myAxiom"}
    r = B.classify(ax)
    assert not r["ok"] and len(r["problems"]) == 2


def test_numerics_shifted_euler_integral():
    for s in (-0.5, -0.9 + 1j, -0.1 - 2j):
        assert B.mellin_g_numeric(s)["rel_err"] < 1e-20
    assert B.K_numeric(-0.5)["rel_err"] < 1e-15


def test_numerics_scale_identity():
    assert B.scale_identity_numeric(3.0, -0.4 + 2j) < 1e-13


def test_lean_Mt_is_M_minus_inverse_L1():
    from riemann_lab import hecke, hlr
    chi = hecke.primitive_characters(5)[1]
    ser = hlr.Series(chi, 0, xmax=10)
    x = 2.0
    assert abs(B.Mt_direct(chi, x) - (complex(ser(x)) - complex(hlr.inv_L1(chi)))) < 1e-9


@pytest.mark.skipif(B.find_lake() is None or not (B.LEAN_DIR / ".lake" / "build").exists(),
                    reason="lake not installed or lean/ not built")
def test_lean_audit():
    r = B.audit()
    assert r["ok"], r["problems"]


def test_parse_axioms_primed_name():
    ax = B.parse_axioms("'RiemannLab.grh_of_finiteNorms'' depends on axioms: [propext, Quot.sound]\n")
    assert ax["RiemannLab.grh_of_finiteNorms'"] == {"propext", "Quot.sound"}
