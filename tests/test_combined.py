"""Fast tests for the combined Ramanujan + Majorana + Masullo norm (riemann_lab.combined)."""
import math

import mpmath as mp
import pytest

from riemann_lab import combined as C, hecke, hlr, zeros


@pytest.fixture(scope="module")
def zeta_data():
    zz = zeros.first_zeros(12)
    return hlr.ZeroExpansion(None, zz, zz), hlr.Series(None, 0, xmax=30)


def test_line_norm_x_equals_mellin_zeta(zeta_data):
    ze, ser = zeta_data
    for c in (0.1, -0.5):
        x = C.line_norm_x(c, ser, ze, 30.0)
        m = C.line_norm_mellin(None, c, t_max=30.0)
        assert abs(x - m) / m < 1e-10


def test_unconditional_range_character():
    chi = hecke.primitive_characters(4)[0]
    ze = hlr.ZeroExpansion(chi, hecke.line_zeros(chi, 30.0), hecke.line_zeros(chi.conj(), 30.0))
    ser = hlr.Series(chi, 0, xmax=30)
    c = -0.6
    x = C.line_norm_x(c, ser, ze, 30.0, hlr.inv_L1(chi))
    m = C.line_norm_mellin(chi, c, t_max=30.0)
    assert abs(x - m) / m < 1e-10


def test_paley_wiener_zeta(zeta_data):
    ze, ser = zeta_data
    F = C.Holo(None, 800)
    v = 0.5
    lhs = C.hline_integral(F, v)
    rhs = 2 * math.pi * C.laplace_weighted(v, ser, ze, 30.0)
    assert abs(lhs - rhs) / rhs < 1e-8


def test_holo_tail_consistency():
    F1, F2 = C.Holo(None, 300), C.Holo(None, 1200)
    for w in (0.3 + 0.2j, -2 + 0.05j, 5 + 1j):
        assert abs(F1(w)[0] - F2(w)[0]) < 1e-12


def test_moved_zero_model_vanishes_off_line():
    with mp.workdps(30):
        g1 = mp.zetazero(1).imag
        L = C.moved_zero_L(None, g1, 0.6)
        assert abs(L(mp.mpc(0.6, g1))) < 1e-20
        assert abs(L(mp.mpc(0.5 + 1e-8, g1))) > 1e-3   # the old on-line zero is gone (removable point)


def test_coarse_space_blind_to_off_line_zero():
    g1 = float(mp.zetazero(1).imag)
    L = C.moved_zero_L(None, g1, 0.6)
    a = C.line_norm_mellin(None, 0.1, t_max=24.0, L_override=L)
    b = C.line_norm_mellin(None, 0.1, t_max=24.0)
    assert math.isfinite(a) and abs(a - b) / b < 1e-3   # finite: the coarse space keeps the off-line model


def test_visible_height():
    assert 15 < C.visible_height(0.1) < 40
