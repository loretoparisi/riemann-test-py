"""riemann-lab: numerical experiments around the Riemann Hypothesis.

Nothing here proves RH. Every module checks a known equivalent or consequence
of RH numerically, so you can test ideas against data before trying to prove them.
"""
from . import zeta, zeros, primes, criteria, explicit_formula, rmt, toy_trace
from . import turing, dbn, nyman_beurling, weil, li_rigorous, riesz_redheffer

__all__ = ["zeta", "zeros", "primes", "criteria", "explicit_formula", "rmt", "toy_trace",
           "turing", "dbn", "nyman_beurling", "weil", "li_rigorous", "riesz_redheffer"]
__version__ = "0.3.0"
