import numpy as np
import pytest

from riemann_lab import criteria, primes, zeros


def test_prime_pi():
    assert primes.prime_pi(10**6) == 78498


def test_explicit_formula_for_pi():
    z = zeros.first_zeros(50)
    approx = primes.pi_explicit([100.5], z)[0]
    assert abs(approx - 25) < 0.6


def test_schoenfeld():
    assert primes.check_schoenfeld(10**5)["holds"]


def test_robin_bruteforce():
    r = criteria.robin_bruteforce(10**5)
    assert r["holds"]
    assert r["violations_n_le_5040"][-1] == 5040     # 5040 is the last violation (Robin)


def test_robin_ca():
    assert criteria.robin_at_ca(3000)["holds"]


def test_lagarias():
    assert criteria.lagarias_bruteforce(10**5)["holds"]


def test_mertens_known_values():
    M = criteria.mertens(10**4)
    assert M[10] == -1 and M[100] == 1 and M[1000] == 2 and M[10000] == -23


def test_li_coefficients():
    lam = criteria.li_coefficients(10)
    assert lam[0] == pytest.approx(0.0230957089661210338, rel=1e-12)
    assert lam[1] == pytest.approx(0.0923457352280611, rel=1e-10)
    assert (lam > 0).all()
