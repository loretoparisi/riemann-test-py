"""riemann-lab: numerical experiments around the Riemann Hypothesis.

Nothing here proves RH. Every module checks a known equivalent or consequence
of RH numerically, so you can test ideas against data before trying to prove them.
"""
from . import zeta, zeros, primes, criteria, explicit_formula, rmt, toy_trace

__all__ = ["zeta", "zeros", "primes", "criteria", "explicit_formula", "rmt", "toy_trace"]
__version__ = "0.1.0"
