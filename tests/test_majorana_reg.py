"""Fast tests for the Majorana regularisation (riemann_lab.majorana_reg)."""
import math

import mpmath as mp
import numpy as np

from riemann_lab import combined as C, hecke, majorana_reg as R


def test_tower_coefficients_reproduce_zeta_norm():
    c = R.tower_coeffs_true(None, 0.9, 1024, 2 ** 13, N=1500)
    N = C.line_norm_mellin(None, 0.1)
    assert abs(np.sum(abs(c) ** 2) - N) / N < 1e-6


def test_model_fft_matches_binomial():
    chi = hecke.primitive_characters(4)[0]
    terms = R.model_terms(0.8, 6.0209489, chi=chi)
    a = R.tower_coeffs_model(terms, 0.8, 512, 2 ** 13)
    b = R.tower_coeffs_model_exact(terms, 0.8, 512)
    assert abs(a - b).max() / abs(b).max() < 1e-9


def test_tikhonov_finite_and_monotone():
    zt = [-14.134725141734695 / 2, 14.134725141734695 / 2]
    v1 = R.tikhonov_critical(None, 1e-4, zt, t_max=12.0)
    v2 = R.tikhonov_critical(None, 1e-6, zt, t_max=12.0)
    assert math.isfinite(v1) and v1 <= v2
