r"""
Code for "Plethysm for characters of relative operads and PROPs"

Najib Idrissi\* and Erik Lindell\*\*

\* Université Paris Cité and Sorbonne Université, CNRS, IMJ-PRG, F-75013 Paris, France.

\*\* Institut for Matematiske Fag, Københavns Universitet, Universitetsparken 5, 2100 København Ø, Denmark.

SageMath port of ``mathematica/Lambda/init.wl``.

Everything that SageMath already provides (partitions, characters of symmetric
groups, the classical bases of symmetric functions and the conversions between
them, plethysm, ...) is used directly; the README lists the correspondence with
the Mathematica code. This module only adds:

- the extensions of the methods ``omega``, ``skew_by``, ``expand`` and
  ``plethysm`` of symmetric functions to tensor products of symmetric
  functions, i.e. to symmetric functions in several alphabets;
- the computations of the paper.

The tensor helpers work with tensor products of symmetric-function bases
over a common coefficient ring. The grading helpers are specific to two
alphabets, ordered as outputs then inputs; their degree is input arity minus
output arity, not total arity. The character computations, LaTeX formatting,
and storage use the fixed Schur tensor parent ``S2`` over ``QQ``.

Symmetric functions in the alphabets `x` (outputs) and `y` (inputs) are the
elements of ``S2 = tensor([s, s])``. As in Sage's documentation of
``plethysm``, `f(x)` and `f(y)` are the plethysms ``f(X)`` and ``f(Y)``::

    sage: h[2](X) * e[3](Y)
    s[2] # s[1, 1, 1]
    sage: tensor([p, p])(h[2](X * Y))
    1/2*p[1, 1] # p[1, 1] + 1/2*p[2] # p[2]
"""

from itertools import groupby

from sage.all import QQ, SymmetricFunctions, Partition, Partitions, PolynomialRing, cached_function, prod, tensor
from sage.calculus.functional import expand as sage_expand
from sage.combinat.free_module import CombinatorialFreeModule_Tensor
from sage.combinat.sf.sfa import SymmetricFunctionAlgebra_generic
from sage.misc.latex import LatexExpr

__all__ = ["Sym", "s", "h", "e", "p", "m", "S2", "X", "Y",
           "omega", "skew_by", "expand", "plethysm",
           "degree_part", "restrict_arity",
           "chQ", "chP_upto_input_arity", "chH_upto_input_arity", "chP", "chH", "chQ_prime", "chP_prime", "chH_prime",
           "character_latex", "save_chH_prime", "load_chH_prime"]

Sym = SymmetricFunctions(QQ)
s, h, e, p, m = Sym.s(), Sym.h(), Sym.e(), Sym.p(), Sym.m()

S2 = tensor([s, s])
X = tensor([s[1], s[[]]])
Y = tensor([s[[]], s[1]])


# Symmetric functions in several alphabets

def _tensor_factors(f):
    r"""
    Return the symmetric-function tensor factors of ``f``, or ``None`` for
    all other objects, including tensors with nonsymmetric-function factors.

    TESTS::

        sage: _tensor_factors(tensor([s[1], h[2]])) == (s, h)
        True
        sage: _tensor_factors(int(0)) is None
        True
        sage: F = CombinatorialFreeModule(QQ, [0, 1])
        sage: _tensor_factors(tensor([F.monomial(0), F.monomial(1)])) is None
        True
        sage: _tensor_factors(tensor([s[1], F.monomial(0)])) is None
        True
    """
    if not hasattr(f, 'parent'):
        return None
    P = f.parent()
    if isinstance(P, CombinatorialFreeModule_Tensor):
        factors = P.tensor_factors()
        if all(isinstance(B, SymmetricFunctionAlgebra_generic) for B in factors):
            return factors
    return None


def omega(f):
    r"""
    Return the image of ``f`` under the involution `\omega`, applied in every
    alphabet.

    This extends ``f.omega()`` to tensor products. If ``f`` is the character
    of `M`, then ``omega(f)`` is the character of `\omega(M)`, where
    `\omega(M)(p, q) = M(p, q) \otimes \mathrm{sgn}_p \otimes \mathrm{sgn}_q`.

    EXAMPLES::

        sage: omega(s[2, 1, 1])
        s[3, 1]
        sage: omega(h[2](X) * e[3](Y))
        s[1, 1] # s[3]
        sage: omega(tensor([p[2], p[3]]))
        -p[2] # p[3]
    """
    factors = _tensor_factors(f)
    if factors is None:
        return f.omega()
    return f.parent().sum(c * tensor([B.monomial(k).omega() for B, k in zip(factors, key)])
                          for key, c in f)


def skew_by(f, x):
    r"""
    Return the result of skewing ``f`` by ``x``, i.e. `x^\perp f`, where
    `x^\perp` is the adjoint of multiplication by `x` for the Hall scalar
    product.

    This extends ``f.skew_by(x)`` to tensor products. It is ``adj[x, f]`` in
    the Mathematica code.

    EXAMPLES::

        sage: skew_by(h[3], h[1])
        h[2]
        sage: skew_by(h[2](X * Y), X * Y)
        2*s[1] # s[1]

    In three alphabets `x, y, z`, with `f = (h_2 \circ (h_1(x)^3 h_1(y))) h_2(z)`
    and `g = h_2(yz)`, the function `g^\perp f` only depends on `x` and equals
    `h_2 \circ h_1^3` (``In[37]``--``In[41]`` in the Mathematica notebook)::

        sage: T3 = tensor([s, s, s])
        sage: X3, Y3, Z3 = [tensor([s[1] if i == j else s[[]] for i in range(3)]) for j in range(3)]
        sage: tensor([p, p, p])(skew_by(h[2](X3^3 * Y3) * h[2](Z3), h[2](Y3 * Z3)))
        1/2*p[1, 1, 1, 1, 1, 1] # p[] # p[] + 1/2*p[2, 2, 2] # p[] # p[]
        sage: _ == tensor([p, p, p])(h[2](p[1]^3)(X3))
        True
    """
    factors = _tensor_factors(f)
    if factors is None:
        return f.skew_by(x)
    P = f.parent()
    return P.sum(c * a * tensor([B.monomial(kf).skew_by(B.monomial(kx))
                                 for B, kf, kx in zip(factors, key_f, key_x)])
                 for key_x, a in P(x) for key_f, c in f)


def expand(f, *args, **kwds):
    r"""
    Return ``f`` as a polynomial in `n` variables in each alphabet.

    This extends ``f.expand(n, alphabet)`` to tensor products: the `i`-th
    tensor factor is expanded in the variables ``a0, ..., a(n-1)`` where ``a``
    is ``alphabet[i]`` (by default, the alphabets are ``'xyz'``). It is
    ``view[n][f]`` in the Mathematica code. On anything else, this is Sage's
    function ``expand``, which calls ``f.expand(*args, **kwds)`` when available
    and otherwise returns ``f`` unchanged.

    For a tensor, ``n`` is the number of variables in each alphabet, and
    ``alphabet`` is a sequence of distinct prefixes, one per factor. For
    example, ``alphabet=['out', 'in']`` uses ``out0, ..., out(n-1)`` and
    ``in0, ..., in(n-1)``. For a single symmetric function, the meaning of
    ``alphabet`` follows Sage's method instead.

    EXAMPLES::

        sage: expand(s[2, 1], 2)
        x0^2*x1 + x0*x1^2
        sage: expand(e[1](X) * e[2](Y), 3)
        x0*y0*y1 + x1*y0*y1 + x2*y0*y1 + x0*y0*y2 + x1*y0*y2 + x2*y0*y2 + x0*y1*y2 + x1*y1*y2 + x2*y1*y2
        sage: var('t')
        t
        sage: expand((t + 1)^2)
        t^2 + 2*t + 1
        sage: [expand(f) for f in (int(0), int(1), float(1.5))]
        [0, 1, 1.5]
        sage: F = CombinatorialFreeModule(QQ, [0, 1])
        sage: f = tensor([F.monomial(0), F.monomial(1)])
        sage: expand(f, 2) is f
        True
    """
    if _tensor_factors(f) is None:
        return sage_expand(f, *args, **kwds)
    return _expand_tensor(f, *args, **kwds)


def _expand_tensor(f, n, alphabet='xyz'):
    factors = _tensor_factors(f)
    if len(alphabet) < len(factors):
        raise ValueError(f"need {len(factors)} alphabets, got {len(alphabet)}")
    names = [[f"{a}{i}" for i in range(n)] for a in alphabet[:len(factors)]]
    R = PolynomialRing(f.parent().base_ring(), sum(names, []))
    variables = [R.gens()[j * n:(j + 1) * n] for j in range(len(factors))]
    return R.sum(c * prod(B.monomial(k).expand(n, alphabet=nm)(*v)
                          for B, k, nm, v in zip(factors, key, names, variables))
                 for key, c in f)


def plethysm(f, *args, include=None, exclude=None):
    r"""
    Return the plethysm `f \circ (g_1, \dots, g_k)`, where `f` is a symmetric
    function in `k` alphabets: the `i`-th alphabet of `f` is replaced by `g_i`.

    For a symmetric function `f` in one alphabet, this is ``f.plethysm(g)``.
    The signature follows the composition ``f(g_1, ..., g_k)`` of lazy
    symmetric functions of arity `k`, which Sage only implements for `k = 1`.
    It is ``pl[f, {g, h}, x, y]`` in the Mathematica code. As in Sage, the
    variables of the base ring are of degree one unless specified otherwise
    using ``include`` or ``exclude``.

    EXAMPLES::

        sage: P2 = tensor([p, p])
        sage: P2(plethysm(p[2](X) * p[3](Y), p[4](X), h[2](Y)))
        1/2*p[8] # p[3, 3] + 1/2*p[8] # p[6]

    Zero retains the parent of the substituted alphabets::

        sage: z = plethysm(S2.zero(), X, Y)
        sage: z.parent() is S2
        True
        sage: omega(z), degree_part(z, 0)
        (0, 0)
        sage: plethysm(S2.zero(), p[1], p[2]).parent() is p
        True
        sage: plethysm(P2.zero(), X, Y).parent() is S2
        True

    The grading variable `\hbar` of the Mathematica code is a variable of the
    base ring::

        sage: R.<hbar> = QQ[]
        sage: SymR = SymmetricFunctions(R)
        sage: sR, hR, eR = SymR.s(), SymR.h(), SymR.e()
        sage: XR, YR = tensor([sR[1], sR[[]]]), tensor([sR[[]], sR[1]])
        sage: f = plethysm(hR[2](XR) * eR[3](YR), hbar^2 * eR[2](XR) * eR[1](YR), hbar * hR[2](YR))
        sage: f == hbar^7 * plethysm(hR[2](XR) * eR[3](YR), eR[2](XR) * eR[1](YR), hR[2](YR))
        True
    """
    factors = _tensor_factors(f)
    if factors is None:
        return f.plethysm(*args, include=include, exclude=exclude)
    if len(args) != len(factors):
        raise ValueError("arity must be equal to the number of arguments provided")
    if not f:
        unit = prod(B.one().plethysm(g, include=include, exclude=exclude)
                    for B, g in zip(factors, args))
        return f.parent().base_ring().zero() * unit
    return sum(c * prod(B.monomial(k).plethysm(g, include=include, exclude=exclude)
                        for B, k, g in zip(factors, key, args))
               for key, c in f)


# Gradings

def degree_part(f, d):
    r"""
    Return the part of ``f`` in degree `d`, i.e. the terms
    `s_\lambda(x) s_\mu(y)` with `|\mu| - |\lambda| = d`.

    The input is a tensor of symmetric functions in two alphabets, ordered
    as outputs then inputs. This is the paper's homological grading, not
    total arity. The input basis and coefficient ring are preserved.

    This is ``coeff[d][𝓕[f, x, y]]`` in the Mathematica code: the regrading
    `\mathcal{F}` multiplies `s_\lambda(x) s_\mu(y)` by
    `(-\hbar)^{|\mu| - |\lambda|}`.

    EXAMPLES::

        sage: degree_part(chQ(2) + chQ(3), 2)
        s[] # s[2] + s[1] # s[3]
    """
    return f.map_support_skip_none(lambda key: key if key[1].size() - key[0].size() == d else None)


def restrict_arity(f, m=None, n=None, exact=True):
    r"""
    Return the terms `s_\lambda(x) s_\mu(y)` of ``f`` with output arity
    `|\lambda| = m` and input arity `|\mu| = n`.

    The input is a tensor of symmetric functions in two alphabets, ordered
    as outputs then inputs; its basis and coefficient ring are preserved.
    If ``exact`` is ``False`` then the terms with
    `|\lambda| \leq m` and `|\mu| \leq n` are kept. If `m` or `n` is ``None``,
    the corresponding arity is not restricted.

    EXAMPLES::

        sage: f = chQ(1) + chQ(2)
        sage: restrict_arity(f, m=1)
        s[1] # s[2] + s[1] # s[3]
        sage: restrict_arity(f, n=2, exact=False)
        s[] # s[1] + s[] # s[2] + s[1] # s[2]
    """
    def ok(size, bound):
        return bound is None or (size == bound if exact else size <= bound)
    return f.map_support_skip_none(lambda key: key if ok(key[0].size(), m) and ok(key[1].size(), n) else None)


# Computations

def _saturation(Q, d, n=None):
    r"""
    Return the degree `d` part of `\sum_{k \geq 0} h_k \circ (\sum_{l \geq 0} Q(l), 0)`.

    Here ``Q(l)`` is homogeneous of degree `l` and all its terms have input
    arity at least `1`. If ``Q(0)`` is nonzero, then the sum is infinite in
    each degree and only the terms of input arity at most `n` are computed.

    Since `h_k \circ (A_0 + A_1 + \dots) = \sum_{k_0 + k_1 + \dots = k}
    \prod_i h_{k_i} \circ A_i`, and since `h_{k_i} \circ A_i` has degree
    `i k_i` and input arity at least `k_i`, the degree `d` part is the sum,
    over partitions `\lambda` of `d` with `k_i` parts equal to `i` and over
    `0 \leq k_0 \leq n - \ell(\lambda)`, of
    `(h_{k_0} \circ A_0) \prod_{i \geq 1} h_{k_i} \circ A_i`.

    The computation is done in the basis of power sums, where products and
    plethysms are cheap, and the result is converted to the Schur basis.
    """
    P2 = tensor([p, p])
    Q0 = P2(Q(0))
    if Q0 and n is None:
        raise ValueError("the input arity must be bounded when Q(0) is nonzero")
    if Q0:
        H0 = [h[k](Q0) for k in range(n + 1)]
    total = P2.zero()
    for la in Partitions(d):
        if n is not None and len(la) > n:
            continue
        term = prod((h[k](P2(Q(i))) for i, k in la.to_exp_dict().items()), P2.one())
        if Q0:
            total += sum(H0[:n - len(la) + 1]) * term
        else:
            total += term
    return S2(total)


def chQ(d):
    r"""
    Return the character of `\mathcal{Q}` in degree `d`.

    EXAMPLES::

        sage: EH = tensor([e, h])
        sage: for d in range(4): print(d, EH(chQ(d)))
        0 e[1] # h[1]
        1 e[] # h[1] + e[1] # h[2]
        2 e[] # h[2] + e[1] # h[3]
        3 e[] # h[3] + e[1] # h[4]
    """
    f = S2.zero()
    if d >= 1:
        f += h[d](Y)
    if d >= 0:
        f += e[1](X) * h[d + 1](Y)
    return f


@cached_function
def chP_upto_input_arity(d, n):
    r"""
    Return the character of `\mathcal{P}` in degree `d`, up to input arity `n`.

    The degree is exactly ``d``; only the input arity is bounded by ``n``.
    The result belongs to ``S2`` over ``QQ``.

    TESTS:

    This agrees with the definition used in the Mathematica code::

        sage: all(chP_upto_input_arity(d, n) == restrict_arity(degree_part(sum(h[k](sum(chQ(l) for l in range(d + 1)))
        ....:                                                     for k in range(n + 1)), d), n=n, exact=False)
        ....:     for d in range(3) for n in range(4))
        True
    """
    return restrict_arity(_saturation(chQ, d, n), n=n, exact=False)


@cached_function
def chH_upto_input_arity(d, n):
    r"""
    Return the character of `\mathcal{H}` in degree `d`, up to input arity `n`.

    The degree is exactly ``d``; only the input arity is bounded by ``n``.
    The result belongs to ``S2`` over ``QQ``.

    EXAMPLES:

    Compare ``Out[47]`` in the Mathematica notebook::

        sage: character_latex(chH_upto_input_arity(2, 5))
        S_{3,41}^{\oplus 3} \oplus S_{3,32} \oplus S_{3,31^{2}}^{\oplus 6} \oplus S_{3,2^{2}1}^{\oplus 2} \oplus S_{3,21^{3}}^{\oplus 3} \oplus S_{21,41} \oplus S_{21,32}^{\oplus 5} \oplus S_{21,31^{2}}^{\oplus 7} \oplus S_{21,2^{2}1}^{\oplus 8} \oplus S_{21,21^{3}}^{\oplus 9} \oplus S_{21,1^{5}}^{\oplus 3} \oplus S_{1^{3},32}^{\oplus 2} \oplus S_{1^{3},31^{2}} \oplus S_{1^{3},2^{2}1}^{\oplus 6} \oplus S_{1^{3},21^{3}}^{\oplus 6} \oplus S_{1^{3},1^{5}}^{\oplus 5} \oplus S_{2,31}^{\oplus 3} \oplus S_{2,2^{2}} \oplus S_{2,21^{2}}^{\oplus 6} \oplus S_{2,1^{4}}^{\oplus 2} \oplus S_{1^{2},31} \oplus S_{1^{2},2^{2}}^{\oplus 4} \oplus S_{1^{2},21^{2}}^{\oplus 5} \oplus S_{1^{2},1^{4}}^{\oplus 5} \oplus S_{1,21}^{\oplus 3} \oplus S_{1,1^{3}}^{\oplus 4} \oplus S_{\varnothing,1^{2}}^{\oplus 2}
    """
    return omega(chP_upto_input_arity(d, n))


@cached_function
def chP(d, m, n):
    r"""
    Return the character of `\mathcal{P}` in degree `d`, output arity `m`
    and input arity `n`.

    EXAMPLES:

    Unlike in the Mathematica code, the terms of output arity `0` only
    appear for `m = 0`::

        sage: chP(2, 0, 2), chP(2, 1, 2)
        (2*s[] # s[2], 0)
    """
    return restrict_arity(chP_upto_input_arity(d, n), m, n)


@cached_function
def chH(d, m, n):
    r"""
    Return the character of `\mathcal{H}` in degree `d`, output arity `m`
    and input arity `n`.

    EXAMPLES:

    Compare ``Out[48]`` in the Mathematica notebook (where the term
    `S_{\varnothing,1^2}^{\oplus 2}` wrongly appears for every `m`)::

        sage: for m in range(6):
        ....:     for n in range(6):
        ....:         if chH(2, m, n):
        ....:             print(m, n, character_latex(chH(2, m, n)))
        0 2 S_{\varnothing,1^{2}}^{\oplus 2}
        1 3 S_{1,21}^{\oplus 3} \oplus S_{1,1^{3}}^{\oplus 4}
        2 4 S_{2,31}^{\oplus 3} \oplus S_{2,2^{2}} \oplus S_{2,21^{2}}^{\oplus 6} \oplus S_{2,1^{4}}^{\oplus 2} \oplus S_{1^{2},31} \oplus S_{1^{2},2^{2}}^{\oplus 4} \oplus S_{1^{2},21^{2}}^{\oplus 5} \oplus S_{1^{2},1^{4}}^{\oplus 5}
        3 5 S_{3,41}^{\oplus 3} \oplus S_{3,32} \oplus S_{3,31^{2}}^{\oplus 6} \oplus S_{3,2^{2}1}^{\oplus 2} \oplus S_{3,21^{3}}^{\oplus 3} \oplus S_{21,41} \oplus S_{21,32}^{\oplus 5} \oplus S_{21,31^{2}}^{\oplus 7} \oplus S_{21,2^{2}1}^{\oplus 8} \oplus S_{21,21^{3}}^{\oplus 9} \oplus S_{21,1^{5}}^{\oplus 3} \oplus S_{1^{3},32}^{\oplus 2} \oplus S_{1^{3},31^{2}} \oplus S_{1^{3},2^{2}1}^{\oplus 6} \oplus S_{1^{3},21^{3}}^{\oplus 6} \oplus S_{1^{3},1^{5}}^{\oplus 5}
    """
    return omega(chP(d, m, n))


def chQ_prime(d):
    r"""
    Return the character of `\mathcal{Q}'` in degree `d`.

    EXAMPLES::

        sage: H2 = tensor([h, h])
        sage: for d in range(4): print(d, H2(chQ_prime(d)))
        0 0
        1 h[] # h[1] + h[1] # h[2]
        2 h[] # h[2] + h[1] # h[3]
        3 h[] # h[3] + h[1] # h[4]
    """
    f = S2.zero()
    if d >= 1:
        f += h[d](Y) + h[1](X) * h[d + 1](Y)
    return f


@cached_function
def chP_prime(d):
    r"""
    Return the character of `\mathcal{P}' = S(\mathcal{Q}')` in degree `d`,
    i.e. the degree `d` part of `\sum_{k \geq 1} h_k \circ (ch(\mathcal{Q}'), 0)`.

    EXAMPLES:

    Compare ``Out[50]`` in the Mathematica notebook::

        sage: for d in range(1, 4): print(d, character_latex(chP_prime(d)))
        1 S_{1,2} \oplus S_{\varnothing,1}
        2 S_{2,4} \oplus S_{2,2^{2}} \oplus S_{1^{2},31} \oplus S_{1,3}^{\oplus 2} \oplus S_{1,21} \oplus S_{\varnothing,2}^{\oplus 2}
        3 S_{3,6} \oplus S_{3,42} \oplus S_{3,2^{3}} \oplus S_{21,51} \oplus S_{21,42} \oplus S_{21,321} \oplus S_{1^{3},41^{2}} \oplus S_{1^{3},3^{2}} \oplus S_{2,5}^{\oplus 2} \oplus S_{2,41}^{\oplus 2} \oplus S_{2,32}^{\oplus 2} \oplus S_{2,2^{2}1} \oplus S_{1^{2},5} \oplus S_{1^{2},41}^{\oplus 2} \oplus S_{1^{2},32}^{\oplus 2} \oplus S_{1^{2},31^{2}} \oplus S_{1,4}^{\oplus 4} \oplus S_{1,31}^{\oplus 3} \oplus S_{1,2^{2}}^{\oplus 2} \oplus S_{\varnothing,3}^{\oplus 3} \oplus S_{\varnothing,21}

    TESTS:

    This agrees with the definition used in the Mathematica code, and with
    Sage's lazy plethysm (where `ch(\mathcal{Q}')` is graded by total arity,
    so that degree `d` is spread over total arities at most `3d`)::

        sage: all(chP_prime(d) == degree_part(sum(h[k](sum(chQ_prime(l) for l in range(d + 1)))
        ....:                                     for k in range(1, d + 1)), d)
        ....:     for d in range(1, 4))
        True
        sage: L = LazySymmetricFunctions(S2)
        sage: Q = L(lambda n: h[n](Y) + (h[1](X) * h[n - 1](Y) if n >= 3 else 0), valuation=1)
        sage: H = LazySymmetricFunctions(s)(lambda n: h[n], valuation=1)
        sage: P = H(Q)
        sage: all(chP_prime(d) == sum(degree_part(S2(P[n]), d) for n in range(3 * d + 1)) for d in range(1, 4))
        True
    """
    if d < 1:
        return S2.zero()
    return _saturation(chQ_prime, d)


@cached_function
def chH_prime(d):
    r"""
    Return the character of `\mathcal{H}' = \omega(\mathcal{P}')` in degree `d`.

    EXAMPLES:

    Compare ``Out[52]``--``Out[54]`` and ``Out[58]``--``Out[60]`` in the
    Mathematica notebook::

        sage: for d in range(1, 4): print(d, character_latex(chH_prime(d), 'V'))
        1 V_{1,1^{2}} \oplus V_{\varnothing,1}
        2 V_{2,21^{2}} \oplus V_{1^{2},2^{2}} \oplus V_{1^{2},1^{4}} \oplus V_{1,21} \oplus V_{1,1^{3}}^{\oplus 2} \oplus V_{\varnothing,1^{2}}^{\oplus 2}
        3 V_{3,31^{3}} \oplus V_{3,2^{3}} \oplus V_{21,321} \oplus V_{21,2^{2}1^{2}} \oplus V_{21,21^{4}} \oplus V_{1^{3},3^{2}} \oplus V_{1^{3},2^{2}1^{2}} \oplus V_{1^{3},1^{6}} \oplus V_{2,31^{2}} \oplus V_{2,2^{2}1}^{\oplus 2} \oplus V_{2,21^{3}}^{\oplus 2} \oplus V_{2,1^{5}} \oplus V_{1^{2},32} \oplus V_{1^{2},2^{2}1}^{\oplus 2} \oplus V_{1^{2},21^{3}}^{\oplus 2} \oplus V_{1^{2},1^{5}}^{\oplus 2} \oplus V_{1,2^{2}}^{\oplus 2} \oplus V_{1,21^{2}}^{\oplus 3} \oplus V_{1,1^{4}}^{\oplus 4} \oplus V_{\varnothing,21} \oplus V_{\varnothing,1^{3}}^{\oplus 3}
        sage: [sum(c * la.dimension() * mu.dimension() for (la, mu), c in chH_prime(d)) for d in range(1, 6)]
        [2, 12, 162, 4221, 182106]
        sage: [len(chH_prime(d)) for d in range(1, 6)]
        [2, 6, 21, 69, 219]
        sage: [sum(chH_prime(d).coefficients()) for d in range(1, 6)]
        [2, 8, 34, 152, 720]
    """
    return omega(chP_prime(d))


# Pretty printing

def _partition_latex(la):
    if not la:
        return r"\varnothing"
    sep = r"\," if la[0] >= 10 else ""
    return sep.join(f"{part}" if mult == 1 else f"{part}^{{{mult}}}"
                    for part, mult in ((part, len(list(g))) for part, g in groupby(la)))


def character_latex(f, sym='S'):
    r"""
    Return the character ``f`` as a direct sum of the irreducible
    representations `S_{\lambda,\mu} = S_\lambda \boxtimes S_\mu`, written in
    LaTeX.

    The input is converted to the Schur tensor parent ``S2`` over ``QQ``.
    Direct-sum notation assumes nonnegative integer multiplicities. The
    result is a ``LatexExpr`` for display; this function does not print.

    The terms are sorted by decreasing `(|\lambda|, \lambda, |\mu|, \mu)`.

    EXAMPLES::

        sage: character_latex(2 * h[2](X) * h[1](Y) + 1)
        S_{2,1}^{\oplus 2} \oplus S_{\varnothing,\varnothing}
        sage: character_latex(S2.zero())
        0
    """
    terms = sorted(S2(f), reverse=True,
                   key=lambda t: (t[0][0].size(), list(t[0][0]), t[0][1].size(), list(t[0][1])))
    if not terms:
        return LatexExpr("0")
    return LatexExpr(r" \oplus ".join(
        f"{sym}_{{{_partition_latex(la)},{_partition_latex(mu)}}}" + ("" if c == 1 else rf"^{{\oplus {c}}}")
        for (la, mu), c in terms))


# Storage of the character of H'

def _partition_str(la):
    return ",".join(map(str, la)) or "-"


def _partition_from_str(text):
    return Partition([] if text == "-" else [int(part) for part in text.split(",")])


def _code_provenance():
    """Return the source hash, Git HEAD, and source status when available."""
    from hashlib import sha256
    from pathlib import Path
    from subprocess import CalledProcessError, run

    source = Path(__file__).resolve()
    checksum = sha256(source.read_bytes()).hexdigest()
    git = ["git", "--no-optional-locks", "-C", str(source.parent)]
    try:
        run(git + ["ls-files", "--error-unmatch", "--", source.name],
            check=True, capture_output=True, text=True)
        head = run(git + ["rev-parse", "HEAD"],
                   check=True, capture_output=True, text=True).stdout.strip()
        status = run(git + ["status", "--porcelain", "--", source.name],
                     check=True, capture_output=True, text=True).stdout.strip()
    except (OSError, CalledProcessError):
        return checksum, "unavailable", "unavailable"
    return checksum, head, "modified" if status else "clean"


def save_chH_prime(path, dmax, verbose=False):
    r"""
    Compute ``chH_prime(d)`` for `1 \leq d \leq` ``dmax`` and write it to the
    text file ``path``, one term `c \, s_\lambda(x) s_\mu(y)` per line.

    The header records the SageMath version, coefficient field, basis,
    degree range, SHA-256 of the source file, Git HEAD, and whether that
    source differs from HEAD. Git fields are ``unavailable`` outside a
    checkout or when Git is unavailable; the source hash is still recorded.
    The file is replaced, and the characters are computed by this function.

    TESTS::

        sage: from tempfile import TemporaryDirectory
        sage: from pathlib import Path
        sage: with TemporaryDirectory() as directory:
        ....:     path = Path(directory) / 'characters.txt'
        ....:     save_chH_prime(path, 2)
        ....:     stored = load_chH_prime(path)
        ....:     print(stored == {d: chH_prime(d) for d in (1, 2)})
        True
    """
    import sys
    import time
    from sage.version import version
    checksum, head, status = _code_provenance()
    with open(path, "w") as out:
        out.write(f"# Produced by SageMath {version} with relative_plethysm.py\n"
                  f"# Source SHA-256: {checksum}\n"
                  f"# Git HEAD: {head}\n"
                  f"# Source status: {status}\n"
                  f"# Character of H'_d for 1 <= d <= {dmax}, in the Schur basis over QQ.\n"
                  "# Each line \"d<TAB>lambda<TAB>mu<TAB>c\" is the term c * s_lambda(x) s_mu(y) of ch(H'_d);\n"
                  "# partitions are comma-separated, \"-\" is the empty partition.\n")
        for d in range(1, dmax + 1):
            start = time.time()
            f = chH_prime(d)
            for (la, mu), c in sorted(f, key=lambda t: (list(t[0][0]), list(t[0][1]))):
                out.write(f"{d}\t{_partition_str(la)}\t{_partition_str(mu)}\t{c}\n")
            if verbose:
                print(f"d = {d}: {len(f)} terms, {time.time() - start:.1f}s", file=sys.stderr, flush=True)


def load_chH_prime(path):
    r"""
    Return the dictionary ``{d: chH_prime(d)}`` stored in the text file
    ``path`` by :func:`save_chH_prime`.

    Values belong to ``S2`` over ``QQ``. Comment headers are ignored, so
    tables written before provenance fields were added remain readable.
    """
    terms = {}
    with open(path) as f:
        for line in f:
            if line.startswith("#") or not line.strip():
                continue
            d, la, mu, c = line.rstrip("\n").split("\t")
            terms.setdefault(int(d), []).append(((_partition_from_str(la), _partition_from_str(mu)), QQ(c)))
    return {d: S2.sum_of_terms(t) for d, t in terms.items()}
