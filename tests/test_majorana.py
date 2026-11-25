"""Fast unit tests for the Majorana x Masullo module (the full checks are `python -m riemann_lab majorana`)."""
import math

import mpmath as mp
import numpy as np
import pytest

from riemann_lab import majorana as M


@pytest.mark.parametrize("j0", [0.0, 0.5])
def test_tower_algebra_and_spectrum(j0):
    r = M.tower_check(j0, 8 + j0, 60 + j0)
    assert r["algebra_err"] < 1e-12 and r["hermitian_err"] < 1e-12 and r["vector_err"] < 1e-11
    assert np.allclose(r["rest_masses"], r["rest_expected"], atol=1e-14)
    assert np.allclose(r["top_energies"][:3], r["expected_energies"][:3], atol=1e-8)
    assert (abs(r["negative"]) < r["p"]).all()


def test_tower_spectral_zeta():
    for half in (False, True):
        assert abs(M.tower_spectral_zeta(4, half) - M.tower_spectral_zeta_closed(4, half)) < 1e-12


@pytest.mark.parametrize("alpha", [0.6, 1.5])
def test_sl2(alpha):
    r = M.sl2_check(alpha, 20)
    assert r["comm_err"] < 1e-12 and r["casimir_err"] < 1e-12
    assert np.allclose(r["masses"], r["masses_expected"])
    assert M.plyushchay_orthonormal(alpha, 4) < 1e-12


def test_hardy_sobolev_chain_small():
    r = M.hardy_sobolev_chain(1.0, [1.0, -0.5, 0.25], dps=20)
    v = list(r.values())
    assert max(abs(x - v[0]) / v[0] for x in v) < 1e-12


def test_local_rh_and_control():
    assert M.local_rh(0.75, 12)["max_dev"] < 1e-25
    assert M.line_sign_changes(0.75, 8, 600)["sign_changes"] == 8
    assert M.mixed_control(0.75, 6, 5) > 1e-2


def test_meixner_pollaczek_orthogonality():
    lam = mp.mpf(0.75)
    for n, m in ((2, 2), (2, 4), (3, 5)):
        v = mp.quad(lambda x: M.mp_poly_values(lam, max(n, m), x)[n] * M.mp_poly_values(lam, max(n, m), x)[m]
                    * abs(mp.gamma(lam + 1j * x)) ** 2, [-mp.inf, 0, mp.inf])
        target = M.mp_poly_norm(lam, n) if n == m else 0
        assert abs(v - target) < 1e-12


def test_jensen_and_stars():
    beta = M.xi_taylor_beta(12, dps=40)
    with mp.workdps(40):
        tay = mp.taylor(lambda z: M.xi(mp.mpf(0.5) + z), 0, 4)
        assert abs(tay[2] - beta[1]) / beta[1] < 1e-20
        gam = M.gorz_gamma(beta)
        cf = M.jensen_coeffs(gam, 5, 3)
        assert M.sturm_real_roots(cf) == 5
        assert abs(M.majorana_stars(cf)[:, 1]).max() < 1e-12
        pg = M.gorz_gamma(M.perturbed_beta(beta, 0.5, 0.3))
        assert M.sturm_real_roots(M.jensen_coeffs(pg, 2, 0)) < 2


def test_sturm_counts():
    # (x - 1)(x - 2)(x^2 + 1): two real roots
    assert M.sturm_real_roots([M.Fr(2), M.Fr(-3), M.Fr(3), M.Fr(-3), M.Fr(1)]) == 2


def test_kronecker_and_quadratic_L():
    assert [M.kronecker(-4, n) for n in range(1, 8)] == [1, 0, -1, 0, 1, 0, -1]
    assert [M.kronecker(8, n) for n in range(1, 8)] == [1, 0, -1, 0, -1, 0, 1]
    assert M.is_fundamental(-4) and M.is_fundamental(5) and not M.is_fundamental(9) and not M.is_fundamental(-12 * 4)
    z = M.QuadraticL(-4).zeros(7.0)
    assert abs(z[0] - 6.020948904697597) < 1e-8          # first zero of L(s, chi_-4)


def test_bdg_symmetry():
    assert M.bdg_particle_hole_err("D") < 1e-12 and M.bdg_particle_hole_err("C") < 1e-12


def test_thomas_fermi_series():
    a = M.tf_series(120, dps=40)
    with mp.workdps(40):
        assert abs(a[1] - (9 - mp.sqrt(73))) < 1e-30
        assert abs(-mp.cbrt(mp.mpf(3) / 16) * mp.fsum(a) - M.TF_SLOPE) < 1e-8


@pytest.mark.parametrize("kind", ["2A", "3A", "4B", "5A", "6A"])
def test_norton_sakuma(kind):
    r = M.norton_sakuma_check(kind, pairs=100)
    assert r["commutative"] and r["form_associative"] and r["semisimple"] and r["dim_V1"] == 1
    assert r["fusion"] and r["tau_automorphism"] and r["norton_min"] >= 0
    assert r["identity_length"] == r["length_expected"]


def test_j_and_rademacher():
    c = M.j_coefficients(4)
    assert c[:5] == [1, 0, 196884, 21493760, 864299970]
    assert abs(M.rademacher_j(1, 300) - 196884) < 0.5
    assert M.weil_bound_check(60)["max_ratio"] <= 1 + 1e-9
    assert math.isclose(sum(m * d for m, d in zip(M.MCKAY_THOMPSON[3], M.MONSTER_DIMS)), c[4])
