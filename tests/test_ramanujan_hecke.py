import math

import mpmath as mp
import numpy as np
import pytest

from riemann_lab import hecke, ramanujan as R, ramanujan_checks as RC, zeros


# ------------------------------------------------------------------ characters / Dirichlet L
@pytest.mark.parametrize("q", [3, 4, 5, 7, 8, 11])
def test_characters_are_primitive_unitary(q):
    for chi in hecke.primitive_characters(q):
        assert abs(sum(chi.values)) < 1e-12                           # non-principal
        assert abs(abs(chi.root_number()) - 1) < 1e-12                 # |eps| = 1 <=> primitive
        assert all(abs(chi(m * n) - chi(m) * chi(n)) < 1e-12 for m in range(1, 2 * q) for n in range(1, 2 * q))


def test_L1_digamma_formula():
    chi = hecke.primitive_characters(4)[0]
    assert float(mp.re(hecke.L(1, chi))) == pytest.approx(math.pi / 4, rel=1e-14)


def test_first_zero_chi4_and_count():
    chi = hecke.primitive_characters(4)[0]
    z = hecke.line_zeros(chi, 15)
    assert z[0] == pytest.approx(6.020948904697, abs=1e-9)
    assert hecke.winding_count(chi, 15) == pytest.approx(len(z), abs=1e-6)


def test_explicit_formula_chi5():
    chi = hecke.primitive_characters(5)[0]
    cb = hecke.primitive_characters(5)[2]
    zp, zb = hecke.line_zeros(chi, 25), hecke.line_zeros(cb, 25)
    r = hecke.explicit_formula(chi, zp, zb, 3.0)
    assert abs(r["residual"]) < 1e-10
    bad = hecke.explicit_formula(chi, zp, zb, 3.0, extra_zeros=[(0.6, 9.0)])
    assert abs(bad["residual"]) > 1e-4


def test_euler_product_converges_to_L1():
    chi = hecke.primitive_characters(3)[0]
    e = hecke.euler_product_1line(chi, [1e3, 1e5])
    assert e["rel_error"][-1] < 1e-3


def test_nicolas_primorials():
    assert hecke.nicolas_primorials(10**5)["holds"]


# ------------------------------------------------------------------ Master Theorem
def test_rmt_mellin_zeta_and_L():
    chi = hecke.primitive_characters(4)[0]
    for row in R.rmt_check(chi, points=[mp.mpc(0.4, 1.5), mp.mpc(0.6, -4)])["rows"]:
        assert row["max_rel_err"] < 1e-12 and row["taylor_err"] < 1e-12


def test_bernoulli_values_of_L():
    chi = hecke.primitive_characters(5)[1]
    lam = R.rmt_examples(chi)[2][2]
    for k in range(4):
        assert complex(lam(k)) == pytest.approx(complex(mp.dirichlet(-k, list(chi.values))), abs=1e-12)


def test_hardy_sobolev_plancherel():
    hs = R.hardy_sobolev_check()
    assert max(r["rel_diff"] for r in hs["rows"]) < 1e-10 and hs["sandwich"]


def test_hardy_growth_exponent_is_pi_over_2():
    assert R.hardy_growth_exponent_L(hecke.primitive_characters(4)[0], w1=40, w2=80) == pytest.approx(math.pi / 2, abs=0.05)


# ------------------------------------------------------------------ Hardy-Littlewood-Ramanujan
def test_hl_series_vs_zero_expansion_zeta():
    z = zeros.first_zeros(40)
    for x in (2.0, 30.0):
        assert R.hl_series(x) == pytest.approx(R.hl_zero_expansion(x, None, z, z), abs=1e-12)


def test_hl_mobius_vs_series():
    mob = R.MobiusTable(10**5)
    v, bound = mob(40.0)
    assert v.real == pytest.approx(R.hl_series(40.0).real, abs=1e-12) and bound < 1e-15


def test_ramanujan_alpha_beta_identity():
    r = R.ramanujan_alpha_beta(1.0, zeros.first_zeros(30))
    assert r["diff"] < 1e-13


# ------------------------------------------------------------------ Ramanujan sums / Robin / tau
def test_ramanujan_sums():
    assert all(R.ramanujan_sum(q, n) == round(R.ramanujan_sum_direct(q, n)) for q in range(1, 30) for n in range(1, 30))
    assert R.ramanujan_sum(12, 1) == 0 and R.ramanujan_sum(7, 7) == 6
    assert R.ramanujan_sigma_expansion(12, 1000) == pytest.approx(28 / 12, abs=1e-2)


def test_robin_ramanujan_constant_positive():
    r = R.robin_ramanujan_constant(3000, 10**5)
    assert (r["scaled"] > 0).all() and r["limit"] == pytest.approx(1.3932, abs=1e-4)


def test_tau_values_and_relations():
    c = R.tau_checks(500)
    assert c["tau_small"] == [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920]
    assert c["multiplicative"] and c["hecke_p2"] and c["congruence_691"]
    assert c["max_|tau(p)|/(2p^5.5)"] <= 1


def test_delta_first_zero():
    D = R.DeltaL()
    z = D.zeros(10.0)
    assert z[0] == pytest.approx(RC.FIRST_DELTA_ZERO, abs=1e-9)


def test_common_local_poles_only_at_zero():
    assert RC._common_local_poles(hecke.primitive_characters(5)[0], 70, 50.0) == [0.0]   # 11, 31, 41, 61 = 1 mod 5
