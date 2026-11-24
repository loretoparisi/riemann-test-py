import mpmath as mp
import numpy as np
import pytest

from riemann_lab import zeta, zeros


def test_first_zero():
    assert zeros.zetazero(1) == pytest.approx(14.134725141734693, abs=1e-12)


@pytest.mark.parametrize("t", [50.0, 1000.5, 12345.6, 100000.3])
def test_numpy_Z_matches_mpmath(t):
    assert zeta.Z(np.array([t, t]))[0] == pytest.approx(float(mp.siegelz(t)), abs=5e-3)


def test_gram_points():
    assert zeta.gram_point(0) == pytest.approx(17.8455995404, abs=1e-8)
    assert float(zeta.theta_mp(zeta.gram_point(500))) == pytest.approx(500 * np.pi, abs=1e-8)


@pytest.mark.parametrize("T,N", [(100, 29), (1000, 649)])
def test_N_exact(T, N):
    assert zeta.N_exact(T) == N == int(mp.nzeros(T))


def test_find_zeros_matches_mpmath():
    roots = zeros.find_zeros(100, 130)
    ref = [float(mp.zetazero(n).imag) for n in range(30, 30 + len(roots))]
    assert np.allclose(roots, ref, atol=1e-3)


def test_verify_window():
    rep, roots = zeros.verify_window(1000, 1200)
    assert rep.all_on_line and len(roots) == rep.expected > 0
