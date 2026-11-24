import math

import mpmath as mp
import numpy as np
import pytest

from riemann_lab import dbn, li_rigorous, nyman_beurling as nb, riesz_redheffer as rr, turing, weil, zeros, zeta


# ------------------------------------------------------------------ Turing
def test_theta_integral_matches_quadrature():
    a, b = 1000.0, 1010.0
    ref = float(mp.quad(lambda t: mp.siegeltheta(t) / mp.pi + 1, [a, b]))
    assert turing.theta_integral(a, b) == pytest.approx(ref, abs=1e-9)


@pytest.mark.parametrize("T1,T2", [(1000, 1150), (1e5, 1.003e5)])
def test_turing_window(T1, T2):
    w = turing.turing_verify(T1, T2)
    assert w.left.certified and w.right.certified
    assert w.all_on_line
    assert w.N_backlund == (w.left.N, w.right.N)          # agrees with the argument principle


def test_turing_rejects_a_wrong_count():
    good = turing.turing_anchor(700)
    bad = turing.turing_anchor(700, guess=702)              # claim one zero too many
    assert good.certified and good.N == 701
    assert not bad.certified and -1.5 < bad.E_lower and bad.E_upper < -0.5   # E = -1 forced


# ------------------------------------------------------------------ de Bruijn-Newman
@pytest.mark.parametrize("t,z", [(0.2, 10), (-0.3, 25 + 0.3j), (0.0, 30)])
def test_heat_flow_matches_definition(t, z):
    assert complex(dbn.H(t, z)) == pytest.approx(complex(dbn.H_direct(t, z)), rel=1e-10)


def test_rectangle_counts_zeros():
    assert dbn.rectangle_zero_free(0.0, -0.1, 60.3).winding == pytest.approx(3, abs=1e-6)
    r = dbn.rectangle_zero_free(0.0, 0.1, 60.3)
    assert r.zero_free and r.bound == pytest.approx(0.005)


def test_pair_collisions_negative():
    p = dbn.pair_collision_estimates(zeros.first_zeros(40))
    assert np.all(p["t_c"] < 0)


# ------------------------------------------------------------------ Nyman-Beurling
def test_vasyunin_matches_integral():
    with mp.workdps(30):
        cot = nb._cot_tables(6)
        for h, k in [(1, 1), (2, 3), (4, 6)]:
            assert float(nb.gram_entry(h, k, cot)) == pytest.approx(nb.gram_entry_numeric(h, k, 100), rel=1e-4)


def test_baez_duarte_distances():
    d2 = nb.distances(30, 40)
    assert d2[0] == pytest.approx(1 - (1 - np.euler_gamma) ** 2 / (math.log(2 * math.pi) - np.euler_gamma))
    assert np.all(np.diff(d2) <= 1e-25) and d2[-1] > 0
    assert d2[-1] * math.log(30) > nb.C0                      # Burnol's lower bound


# ------------------------------------------------------------------ Weil
def test_weil_matrix_sides_agree_and_positive():
    z = zeros.first_zeros(60)
    r = weil.check_family(0.1, 10, 0.35, z)
    assert r["max_entry_diff"] < 1e-12
    assert r["positive_within_error"] and r["lambda_min_primes"] > 0


# ------------------------------------------------------------------ Li (interval)
def test_li_rigorous_matches_and_certifies():
    r = li_rigorous.li_coefficients_rigorous(300)
    assert r.certified and r.all_positive
    assert r.mid[0] == pytest.approx(0.0230957089661210338, rel=1e-15)
    assert r.mid[1] == pytest.approx(0.0923457352280611, rel=1e-13)
    assert np.all(r.rad < 1e-30 * np.abs(r.mid))


def test_li_backends_agree():
    a = li_rigorous.li_coefficients_rigorous(25, backend="arb")
    b = li_rigorous.li_coefficients_rigorous(25, backend="mpmath")
    assert np.allclose(a.mid, b.mid, rtol=1e-12)


# ------------------------------------------------------------------ Riesz / Redheffer
@pytest.mark.parametrize("x", [10.0, 50.0, 200.0])
def test_riesz_fast_form_matches_series(x):
    R, err = rr.riesz(np.array([x]))
    assert R[0] == pytest.approx(rr.riesz_series_mp(x), abs=1e-7)


def test_riesz_matches_zero_expansion():
    x = np.array([1e4, 1e6, 1e8])
    R, _ = rr.riesz(x)
    assert np.allclose(R / x**0.25, rr.riesz_from_zeros(x, 10) / x**0.25, atol=1e-8)


def test_redheffer_det_is_mertens():
    assert rr.redheffer_check(40, (100, 300))["all_match"]
