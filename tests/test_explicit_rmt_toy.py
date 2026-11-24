import numpy as np
import pytest

from riemann_lab import explicit_formula as ef, rmt, toy_trace, zeros


@pytest.fixture(scope="module")
def z60():
    return zeros.first_zeros(60)


@pytest.mark.parametrize("r0,sigma", [(20, 1.0), (30, 0.5), (0, 0.3)])
def test_explicit_formula_holds(z60, r0, sigma):
    assert abs(ef.check(z60, r0, sigma).residual) < 1e-10


def test_off_line_zero_is_detected(z60):
    assert abs(ef.check(z60, 20, 1.0, extra_zeros=[(0.6, 22.0)]).residual) > 0.1


def test_missing_zero_is_detected(z60):
    assert abs(ef.check(np.delete(z60, 1), 20, 1.0).residual) > 0.1


def test_toy_trace():
    inside = toy_trace.demo(7.0, 1.0, 0.8)
    assert inside["inside_(1,gamma)"] and abs(inside["spectral"]) < 1e-10 and inside["geometric"] == 0
    out = toy_trace.demo(3.0, 1.0, 0.8)
    assert out["spectral"] == pytest.approx(out["geometric"], abs=1e-10)
    assert out["matrix"] == pytest.approx(out["geometric"], abs=1e-10)


def test_gue_beats_goe_and_poisson():
    _, z = zeros.verify_window(1e4, 1.1e4)
    ks = rmt.ks_distances(rmt.spacings(z))
    assert ks["GUE"] < ks["GOE"] < ks["Poisson"]
