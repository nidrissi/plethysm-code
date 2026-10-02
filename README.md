# Code for the paper "Plethysm for characters of relative operads and PROPs"

This repository contains the code (in SageMath) for the article "Plethysm for characters of relative operads and PROPs" by Najib Idrissi[^1] and Erik Lindell[^2]. The original Wolfram Mathematica code is in `mathematica/`.

Files:

* `relative_plethysm.py`: The main file.
* `lambda-appl.ipynb`: Notebook (SageMath kernel) showcasing how to use `relative_plethysm.py`.
* `lambda-appl.pdf`: The same notebook, exported as a PDF.
* `compute_chH_prime.py`: The script producing `chH_prime.txt`.
* `chH_prime.txt`: The character of $\mathcal{H}'_n$, computed for $n \leq 10$.
* `mathematica/`: The original Mathematica code.
  * `mathematica/Lambda/init.wl`: The main file.
  * `mathematica/Lambda/symCharTable.gap`: The GAP code to produce character tables for symmetric groups.
  * `mathematica/Lambda/charTable_*.wl`: The produced character tables.
  * `mathematica/lambda-appl.nb`: Notebook showcasing how to use the Lambda package.
  * `mathematica/lambda-appl.pdf`: The same notebook, exported as a PDF.
  * `mathematica/chH_prime.mx`: The character of $\mathcal{H}'_n$, computed for $n \leq 10$.

## Usage

The code was tested with SageMath 10.10.

```
sage: from relative_plethysm import *
sage: print_poly(chH_prime(2), 'V')
V_{2,21^{2}} \oplus V_{1^{2},2^{2}} \oplus V_{1^{2},1^{4}} \oplus V_{1,21} \oplus V_{1,1^{3}}^{\oplus 2} \oplus V_{\varnothing,1^{2}}^{\oplus 2}
```

* Tests: `sage -t relative_plethysm.py` (or `python3 -m sage.doctest relative_plethysm.py` if SageMath is installed as a Python package).
* Recomputing `chH_prime.txt`: `sage -python compute_chH_prime.py [dmax]` (or `python3 compute_chH_prime.py [dmax]`), which takes about 4 minutes for `dmax = 10`.

## Correspondence with the Mathematica code

Most of the Mathematica package is built into SageMath, which is used directly. Symmetric functions in the alphabets $x$ (outputs) and $y$ (inputs) are elements of `S2 = tensor([s, s])`, and $f(x)$, $f(y)$ are the plethysms `f(X)`, `f(Y)` with `X = tensor([s[1], s[[]]])` and `Y = tensor([s[[]], s[1]])`, as in SageMath's documentation. `relative_plethysm.py` only adds:

* the functions `omega`, `skew_by`, `expand` and `plethysm`, which extend the methods of the same name to tensor products of symmetric functions, i.e. to symmetric functions in several alphabets (on symmetric functions in one alphabet, they call these methods);
* the computations of the paper.

| Mathematica | SageMath |
|---|---|
| `tr[λ]`, `hook[λ]`, `𝓏[λ]` | `Partition(λ).conjugate()`, `.dimension()`, `.centralizer_size()` |
| `χ[λ, μ]` | `s[λ].scalar(p[μ])` |
| `charTable_*.wl`, `symCharTable.gap` | not needed |
| `m[λ, x]`, `e[n, x]`, `h[n, x]`, `p[n, x]`, `s[λ, x]` | `m[λ]`, `e[n]`, `h[n]`, `p[n]`, `s[λ]` |
| `f[…, y]` | `f(Y)` |
| `view[n][f]` | `f.expand(n)`, or `expand(f, n)` in several alphabets |
| `alt[α, x]` | a determinant (see the notebook) |
| `conv[t][f]` | `t(f)`, or `tensor([t, t])(f)` in two alphabets |
| `pl[f, g, x]` | `f(g)`, also when `g` is in several alphabets |
| `pl[f, {g, h}, x, y]` | `plethysm(f, g, h)` |
| `ℏ` | a variable of the base ring, which plethysm treats as an element of degree one (see `include`/`exclude` in SageMath's `plethysm`) |
| `adj[f, g]` | `g.skew_by(f)`, or `skew_by(g, f)` in several alphabets |
| `reg[n, x, y]`, `reg2[n, x, y]` | `h[n](X * Y)`, `tensor([p, p])(h[n](X * Y))` |
| `ω[f]` | `f.omega()`, or `omega(f)` in several alphabets |
| `coeff[d][𝓕[f, x, y]]` | `degree_part(f, d)` |
| `printPoly[S, x, y][f]` | `print_poly(f, 'S')` (LaTeX) |
| `chQ[d, x, y]`, `chP\[LetterSpace]upto[d, n, x, y]`, `chP[d, m, n, x, y]`, ... | `chQ(d)`, `chP_upto(d, n)`, `chP(d, m, n)`, ... |
| `Get["chH_prime.mx"]` | `load_chH_prime("chH_prime.txt")` |

Differences with the Mathematica version:

* In `chP[d, m, n, x, y]` (hence `chH`), the truncation to output arity $m$ did not remove the terms of output arity $0$, because `s[{}, x]` evaluates to `1`. For example, `Out[48]` in `mathematica/lambda-appl.nb` wrongly contains $S_{\varnothing,1^2}^{\oplus 2}$ for $d = 2$, $n = 2$ and every $m \geq 1$. `chP(d, m, n)` and `chH(d, m, n)` are correct. The other functions agree with the outputs stored in the Mathematica notebook.
* The characters are computed directly in degree $d$ instead of up to degree $d$, which is faster.
* `print_poly` returns LaTeX and may order the terms differently.

[^1]: Université Paris Cité and Sorbonne Université, CNRS, IMJ-PRG, F-75013 Paris, France.
[^2]: Institut for Matematiske Fag, Københavns Universitet, Universitetsparken 5, 2100 København Ø, Denmark
