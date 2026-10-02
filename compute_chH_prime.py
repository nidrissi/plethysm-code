r"""
Code for "Plethysm for characters of relative operads and PROPs"

Najib Idrissi and Erik Lindell

Computes the character of H'_d for 1 <= d <= dmax (default: 10) and writes it
to chH_prime.txt. Usage::

    sage -python compute_chH_prime.py [dmax]
"""

import sys

from relative_plethysm import save_chH_prime

if __name__ == "__main__":
    dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    save_chH_prime("chH_prime.txt", dmax, verbose=True)
