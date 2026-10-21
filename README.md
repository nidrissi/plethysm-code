# Code for the paper "Plethysm for characters of relative operads and PROPs"

This repository contains the code (in SageMath) for the article "Plethysm for characters of relative operads and PROPs" by Najib Idrissi[^1] and Erik Lindell[^2].

Files:

* `relative_plethysm.py`: The main file.
* `lambda-appl.ipynb`: Notebook (SageMath kernel) showcasing how to use `relative_plethysm.py`.
* `lambda-appl.pdf`: The same notebook, exported as a PDF.
* `compute_chH_prime.py`: The script producing `chH_prime.txt`.
* `chH_prime.txt`: The character of $\mathcal{H}'_n$, computed for $n \leq 10$.
* [Mathematica documentation](mathematica/README.md): The original Mathematica code and its correspondence with the SageMath implementation.

## Usage

The code was tested with SageMath 10.10.

```
sage: from relative_plethysm import *
sage: character_latex(chH_prime(2), 'V')
V_{2,21^{2}} \oplus V_{1^{2},2^{2}} \oplus V_{1^{2},1^{4}} \oplus V_{1,21} \oplus V_{1,1^{3}}^{\oplus 2} \oplus V_{\varnothing,1^{2}}^{\oplus 2}
```

* Tests: `sage -t relative_plethysm.py` (or `python3 -m sage.doctest relative_plethysm.py` if SageMath is installed as a Python package).
* Recomputing `chH_prime.txt`: `sage -python compute_chH_prime.py [dmax]` (or `python3 compute_chH_prime.py [dmax]`), which takes about 4 minutes for `dmax = 10`.

## API conventions

The helpers `omega`, `skew_by`, `expand`, and `plethysm` support tensor products whose factors are symmetric-function bases over a common coefficient ring. They also delegate to Sage's existing operations for single-alphabet inputs. Other tensor products are not treated as symmetric functions; in particular, `expand` falls back to Sage's global `expand` on those inputs.

For a tensor, `expand(f, n, alphabet='xy')` uses $n$ variables in each alphabet: `x0, ..., x(n-1)` and `y0, ..., y(n-1)`. The `alphabet` argument supplies one distinct prefix per factor and can also be a list such as `['out', 'in']`. For a single symmetric function, its meaning follows Sage's `.expand()` method.

The grading helpers `degree_part` and `restrict_arity` apply to two alphabets, ordered as outputs $x$ then inputs $y$, and preserve the input basis and coefficient ring. Here degree means $|\mu|-|\lambda|$, the paper's homological grading, rather than total arity $|\lambda|+|\mu|$.

The character computations return elements of the fixed Schur tensor parent `S2` over `QQ`. In `chP_upto_input_arity(d, n)` and `chH_upto_input_arity(d, n)`, the degree is exactly $d$ and the input arity is at most $n$. In `chP(d, m, n)` and `chH(d, m, n)`, both arities are exact.

`character_latex(f, sym='S')` converts to `S2` and returns a `LatexExpr` describing the irreducible decomposition. Direct-sum notation assumes nonnegative integer multiplicities; the function itself does not print. This replaces `print_poly`; the arity-bounded functions replace `chP_upto` and `chH_upto`.

## Lazy series

The characters are also lazy power series in a variable $t$ recording the degree $d$. Their coefficients are computed only when needed, then cached. The character functions (`chP`, `chH`, `chP_upto_input_arity`, `chP_prime`, ...) read their values off these series.

* `chQ_series`, `chQ_prime_series`, `chP_prime_series`, `chH_prime_series`: the coefficient of $t^d$ is a finite element of `S2`, e.g. `chQ_series[d] == chQ(d)` and `chH_prime_series[d] == chH_prime(d)`. Use `restrict_arity` to select arities: `restrict_arity(chQ_series[1], m=1, n=2)` returns `s[1] # s[2]`.
* `chP_series`, `chH_series`: the coefficient of $t^d$ has infinitely many terms. It is a lazy symmetric function (`LazySymmetricFunctions(S2)`) graded by total arity $m+n$; in degree $d$, its component of total arity $m+n$ has output arity $m$ and input arity $n$. For example, `chH_series[d][m + n] == chH(d, m, n)` when $n - m = d$.

`omega` also applies to lazy series, coefficientwise. Equality of lazy series is not decidable, so compare coefficients rather than series. Printing a series computes its first seven coefficients, for example degrees 1 to 7 for `chH_prime_series`, which takes a few seconds.

Since $\mathcal{Q}$ is $\mathcal{Q}'$ plus $h_1(x)h_1(y)$ in degree $0$, we have $\mathrm{ch}(\mathcal{H}) = \Omega \cdot (1 + \mathrm{ch}(\mathcal{H}'))$, where $\Omega = \sum_{n} h_n(xy)$ is the Cauchy kernel; it is `chH_series[0]`.

## Stored character tables

`save_chH_prime(path, dmax)` computes the characters and replaces the destination file. New tables record the SageMath version, coefficient field, basis, degree range, source-file SHA-256, Git HEAD, and whether `relative_plethysm.py` differs from HEAD. If Git or a tracked checkout is unavailable, the Git fields say `unavailable` and the source hash still identifies the file. The Git status describes the source module; notebook or documentation edits do not change it.

`load_chH_prime(path)` reads the coefficients as exact rationals and returns a dictionary of characters in `S2`. It ignores comment headers and therefore also accepts older tables. The checked-in degree-10 table retains its original header; its exact producing source revision was not recorded at generation time.

[^1]: Université Paris Cité and Sorbonne Université, CNRS, IMJ-PRG, F-75013 Paris, France.
[^2]: Institut for Matematiske Fag, Københavns Universitet, Universitetsparken 5, 2100 København Ø, Denmark
