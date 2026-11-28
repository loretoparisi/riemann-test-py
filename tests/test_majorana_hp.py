"""Fast tests for the Majorana-tower Hilbert-Polya frame (riemann_lab.majorana_hp)."""
import math

import mpmath as mp
import numpy as np

from riemann_lab import combined as C, majorana_hp as H, zeros


def test_oscillator_is_d_quarter_plus_three_quarters():
    r = H.oscillator_check(120)
    assert max(r["alg"], r["cas_even"], r["cas_odd"], r["plyushchay"], r["D_vs_K2"]) < 1e-12


def test_squeezed_vacuum_and_dilation_overlap():
    assert abs(H.squeezed_coeffs_closed(3, 20) - H.squeezed_coeffs_quad(3, 20)).max() < 1e-12
    D = H.oscillator(400)["D"]
    assert abs(H.dilation_overlap_matrix(D, 1.0) - math.cosh(1.0) ** -0.5) < 1e-10


def test_tower_is_gauss_rule_of_gamma_weight():
    k = 0.15
    E, W = H.tower_rule(k, 200)
    assert abs(W.sum() / (2 * math.pi * math.gamma(2 * k) / 4 ** k) - 1) < 1e-12
    assert abs(H.tower_moment(k, 3) / H.gamma_moment(k, 3) - 1) < 1e-10
    assert abs(np.sum(W * np.cos(E)) / H.gamma_charfun(k, 1.0) - 1) < 1e-8


def test_tower_norm_matches_line_norm_zeta():
    k = 0.1
    ref = C.line_norm_mellin(None, k)
    assert abs(H.tower_norm(None, k, 200) - ref) / ref < 1e-4


def test_first_zeta_zero_is_point_spectrum():
    g = zeros.first_zeros(6)
    peaks = [-x / 2 for x in g] + [x / 2 for x in g]
    h = 1e-3
    with mp.workdps(30):
        k = mp.mpf(1) / 4 - h
    E, W = H.arithmetic_measure(None, k, 20.0, peaks, h)
    ev, wt = H.lanczos_rule(E, W, 30)
    e, w = H.locate(ev, wt, -g[0] / 2)
    assert abs(e + g[0] / 2) < 1e-3
    assert abs(h * w / H.point_mass_pred(None, mp.mpc(0.5, g[0])) - 1) < 2e-2
