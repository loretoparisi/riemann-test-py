"""Fast tests for the Hardy-Littlewood-Ramanujan module (riemann_lab.hlr)."""
import math

import numpy as np
import pytest

from riemann_lab import hecke, hlr, zeros


@pytest.fixture(scope="module")
def zz():
    return zeros.first_zeros(12)


def test_series_matches_zero_expansion_zeta(zz):
    ze = hlr.ZeroExpansion(None, zz, zz)
    ser = hlr.Series(None, 0, xmax=60)
    for x in (5.0, 30.0, 60.0):
        assert abs(complex(ser(x)) - ze(x)[0]) * x**0.25 < 1e-12


def test_series_range_guard():
    ser = hlr.Series(None, 0, xmax=10)
    with pytest.raises(ValueError):
        ser(11.0)


def test_mellin_strip_zeta(zz):
    ze = hlr.ZeroExpansion(None, zz, zz)
    ser = hlr.Series(None, 0, xmax=30)
    for s in (-0.4, complex(-0.6, 2.0)):
        assert hlr.mellin_strip(None, s, ser, ze, 30.0)["rel_err"] < 1e-10


def test_moebius_sum_large_x_zeta(zz):
    ze = hlr.ZeroExpansion(None, zz, zz)
    mob = hlr.MobiusSum(10**5, None, K=2000, K_hi=20000)
    for x in (1e2, 1e5, 1e7):
        v, b = mob(x)
        assert (abs(v - ze(x)[0]) + b) * x**0.25 < 1e-8


def test_moebius_bound_is_honest():
    """With J = 0 the bound must cover the true truncation error."""
    zp = zeros.first_zeros(12)
    ze = hlr.ZeroExpansion(None, zp, zp)
    mob = hlr.MobiusSum(2000, None, J=0, K=500, K_hi=1000)
    for x in (1e4, 1e5):
        v, b = mob(x)
        assert abs(v - ze(x)[0]) <= b


@pytest.mark.parametrize("q,idx", [(4, 0), (5, 1), (5, 0)])
def test_reciprocity_characters(q, idx):
    chi = hecke.primitive_characters(q)[idx]
    zp = hecke.line_zeros(chi, 40.0)
    zn = hecke.line_zeros(chi.conj(), 40.0)
    r = hlr.reciprocity(chi, 1.0, zp, zn, zn, zp)
    assert r["diff"] < 1e-12


def test_reciprocity_zeta_is_hardy_littlewood(zz):
    r = hlr.reciprocity(None, 1.3, zz, zz, zz, zz)
    assert r["diff"] < 1e-12 and abs(r["beta"] - math.pi / 1.3) < 1e-15


def test_reciprocity_detects_wrong_root_number():
    chi = hecke.primitive_characters(5)[0]   # complex odd character: eps != 1
    zp, zn = hecke.line_zeros(chi, 40.0), hecke.line_zeros(chi.conj(), 40.0)
    good = hlr.reciprocity(chi, 1.0, zp, zn, zn, zp)
    fake = hecke.Character(chi.q, chi.label, tuple(np.conj(chi.values)))  # chibar with chi's label
    bad = hlr.reciprocity(fake, 1.0, zp, zn, zn, zp)                       # zeros of the wrong function
    assert good["diff"] < 1e-12 and bad["diff"] > 1e-6


def test_amplitude_dominated_by_first_zero(zz):
    ze = hlr.ZeroExpansion(None, zz, zz, trivial=False)
    top = np.sort(np.abs(ze.c))[::-1]
    assert top[:2].sum() / ze.amplitude > 0.99
    assert 0.99 * ze.amplitude < hlr.amplitude_sup(ze, umax=2000.0) <= ze.amplitude * (1 + 1e-12)


def test_hardy_edge_blows_up(zz):
    e = hlr.hardy_edge(None, zz[:5], deltas=(0.24, 0.249))
    a, b = e["rows"]
    assert b["max_phi"] / a["max_phi"] > 9.0
    assert abs(hlr.hardy_A(None) - math.pi / 2) < 0.05


def test_sensitivity_scaling():
    # log x needed grows linearly in gamma and like 1/delta
    a = hlr.log10_x_to_see(1000.0, 0.1, 1e-5)
    b = hlr.log10_x_to_see(2000.0, 0.1, 1e-5)
    c = hlr.log10_x_to_see(1000.0, 0.2, 1e-5)
    assert 1.9 < b / a < 2.1 and 0.45 < c / a < 0.55
    assert hlr.log10_x_to_see(hlr.PLATT_TRUDGIAN_HEIGHT, 0.5, 3e-5) > 1e12
    h = hlr.detection_height(0.2, 1e-11, 11)
    assert 25 < h < 45
