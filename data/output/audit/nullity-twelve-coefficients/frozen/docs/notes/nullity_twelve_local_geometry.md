# Nullity-twelve tangent cone at e1+e18

At `x0=e1+e18`, the complete real set of constant-norm velocities admitting
formal second-order rank preservation is `A15 union B17`. The two linear
pieces have dimensions 15 and 17 and intersect in dimension 13. The
[certificate](../../gororoba_quantum/nullity_twelve_locus.py) and
[independent replay](../evidence/nullity_twelve_locus/README.md) reconstruct
all coefficients, exact rank witnesses and sum-of-squares identities.

The statement concerns one selected center on the sphere of norm squared
two. Exact rational computation certifies polynomial identities; the proof
uses those identities for arbitrary real coefficients. The construction below
also realizes every admitted velocity by an actual
smooth curve, proving equality with the Bouligand tangent cone at this center.
Local attachment equations and global topology remain separate obligations.

## Construction and complete equation coverage

The [centered Schur chart](dimension32_skew_schur_charts.md) supplies
fixed complementary frames `U,V`, with `V` spanning `ker L_x0`, and

```text
A0=U^T L_x0 U,  D(h)=V^T L_h V,
B(h)=U^T L_h V, Q(h)=B(h)^T A0^(-1) B(h).
```

The skew-adjoint multiplication rule and the pure-coordinate restriction
follow the primary sources in the
[acceleration proof](schur_acceleration_certificates.md). That proof gives
`D(h)=0`, `<x0,h>=0`, and `D(a)=-2Q(h)` for a twice differentiable
same-nullity curve. Radial correction of `a` enforces
`<x0,a>=-||h||^2` without adding an obstruction.

The 66 strictly upper-triangular entries of `D` form `Dmap`, a `66 x 30`
linear matrix on all doubly-pure coordinates, excluding basis indices 0
and 16. The appended norm row gives `M`, a `67 x 30` matrix. The exact
ranks are 8 and 9. Complete nullspaces give `K: R^21 -> ker M` and
`C: R^58 -> ker Dmap^T`. Their residual, independence and completeness
checks prevent a sparse subset from replacing the full equation system.

Write `h=Kz`. Solvability is equivalent to all 58 entries of
`C^T upper_triangle(Q(Kz))` vanishing. Polarization extracts every square
and every unordered mixed product, giving 231 degree-two monomials. The
resulting coefficient matrix `G` has shape `58 x 231` and rank eight.
The rank measures the linear span of the quadratic polynomials; it
establishes neither geometric codimension nor smoothness.

The independent replay retains a nonzero minor of determinant 2048 at
zero-based rows `[30,31,33,34,35,36,52,53]` and columns
`[6,111,121,122,123,124,125,135]`. The identity `G=T R`, with `R` the
eight reduced generator rows, proves full equation reconstruction. A
second reconstruction uses independent original rows. Every omitted sparse
matrix entry denotes exact zero. These checks prove coverage of all real
coefficients rather than sampling a collection of directions.

## Tangent-coordinate convention

The complete ambient columns of `K` are:

```text
z0=e3       z7=-e2+e17   z14=-e10+e25
z1=e4       z8=e19       z15=e9+e26
z2=e5       z9=e20       z16=e27
z3=e6       z10=e21      z17=e15+e28
z4=e7       z11=e22      z18=-e14+e29
z5=e8       z12=e23      z19=e13+e30
z6=e11      z13=e24      z20=-e12+e31
```

The eight independent generators in that coordinate order are

```text
g0=z6^2-z16^2,
g1=z5*z6-z13*z16,
g2=z13*z6+z16*z5,
g3=z17*z5-z13*z20+z16*z17+z20*z6,
g4=z13*z19+z18*z5+z16*z18-z19*z6,
g5=z19*z5-z13*z18+z16*z19+z18*z6,
g6=z13*z17+z20*z5+z16*z20-z17*z6,
g7=z16*z6.
```

The remaining thirteen coordinates are free at quadratic order. The replay
extracts these polynomials from multiplication matrices; their display
supplies a readable witness, rather than an assumed algebraic model.

## Exact real reduction

The polynomial identity

```text
g0^2+4*g7^2=(z6^2+z16^2)^2
```

forces `z6=z16=0` at every real common zero. Substitution leaves four
nonzero equations:

```text
f1=z5*z17-z13*z20,  f2=z5*z18+z13*z19,
f3=z5*z19-z13*z18,  f4=z5*z20+z13*z17.
```

The second identity is

```text
f1^2+f2^2+f3^2+f4^2
  =(z5^2+z13^2)*(z17^2+z18^2+z19^2+z20^2).
```

Positivity over the reals forces either `z5=z13=0` or
`z17=z18=z19=z20=0`. Each alternative also annihilates every original
generator. Hence

```text
A15={z6=z16=z17=z18=z19=z20=0},
B17={z6=z16=z5=z13=0},
V_R(g0,...,g7)=A15 union B17,
dim(A15 intersect B17)=13.
```

The real vanishing ideal is
`<z6,z16> + <z5,z13>*<z17,z18,z19,z20>`, obtained by intersecting
the two coordinate-plane ideals. The formula describes the real vanishing
ideal of the set; it does not assert that the original eight-generator
ideal is radical. Complex isotropic solutions require a separate argument.

The directions `e8` and `e15+e28` lie in different pieces. Their sum
has `g3=1` and fails quadratic compatibility. The first-order direction
`e11` has `g0=1` and also fails. The admissible set therefore carries
information that its 21-dimensional linear span loses.

## Published curve family for the seventeen-dimensional piece

[Biss, Christensen, Dugger and Isaksen, *Large annihilators II*](math-0702075.md),
Definition 3.1, uses

```text
{a,b}=(a+b, i4*(-a+b))/sqrt(2).
a0=(e1-e10)/sqrt(2), b0=(e1+e10)/sqrt(2),
{a0,b0}=x0.
```

Both factors are unit sedenion zero divisors. Corollary 7.4 places the
pair in the D-locus, and Theorem 6.12 gives nullity `4+4+4=12`.
Theorem 7.5 and Remark 7.6 describe the natural unit-factor D-locus as a
smooth `S5`-bundle over `V2(R7)`, of dimension `5+11=16`.

Independent positive scaling of the factors preserves the D-locus and
their annihilator dimensions. The restriction `r^2+s^2=2`, near `r=s=1`,
adds one smooth length-ratio parameter. The bracket norm identity makes
`{r a,s b}` have norm squared two. Factor norms recover `r,s`, and division
recovers the unit factors, so the construction embeds a smooth
17-dimensional family through the selected center.

The acceleration note proves the quadratic condition for every Bouligand
tangent direction by applying a cokernel functional to the exact Schur
identity along tangent sequences. Its proof requires no second derivative.
The tangent space of the published smooth family therefore lies in
`A15 union B17`. A real linear space contained in a union of two linear
spaces lies in one of them. Dimension 17 excludes containment in `A15`;
its tangent is exactly `B17`. Every `B17` direction consequently has a
smooth constant-norm, nullity-twelve realization.

The dimension and construction inherit the published theorem plus the
explicit length-scaling argument. The particular quadratic decomposition
has an exact computational certificate here; publication priority remains
unassessed.

## An actual curve outside the published slice

The rational curve

```text
x(t)=((4-t^2)e1+4t e8+(4+t^2)e18)/(4+t^2)
```

has norm squared two, passes through `x0`, and has velocity `e8`.
For its numerator and the fixed centered complement, the pivot determinant
is `2^68*(t^2+4)^4`, which is positive for every real finite `t`.
Exact Schur elimination gives a zero `12 x 12` residual. The curve
therefore has rank 20 and nullity 12 throughout its real parameter domain.
The nonzero `e8` coefficient leaves `H5^perp`, the published bracket slice.
The following construction realizes arbitrary combinations in `A15`.

## Four-parameter slice and exact rank proof

Write a dimension-32 element as four octonion blocks `(p,q,r,s)`. For real
parameters `beta,delta,k,f`, with `k!=1,-1`, define

```text
Delta=4(1-k^2), J=[[0,1],[-1,0]],
M=[[beta^2-delta^2,2 beta delta],
   [2 beta delta,delta^2-beta^2]],
N=[[-2 beta delta,beta^2-delta^2],
   [beta^2-delta^2,2 beta delta]],
U=I-M/Delta, V=-k J-k N/Delta,
c=(1-f^2)/(1+f^2), s_phase=2f/(1+f^2),
U_f=c U-s_phase V, V_f=s_phase U+c V.
```

Rows zero and one of `U_f` give the `e1,e2` coefficients of `p,r`.
Rows zero and one of `V_f` give the `e1,e2` coefficients of `q,s`.
The scalar parts of `q,s` are `beta,delta`; every other coefficient
is zero. Denote the resulting vector by `X(beta,delta,k,f)`. The
[implementation](../../gororoba_quantum/nullity_twelve_curves.py) evaluates
exact rational instances and retains the universal polynomial witnesses.

The multiplication matrix splits into invariant 16-dimensional coordinate
blocks. The internal block uses indices
`{0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27}`; the external block uses
indices whose bit of value four is set. XOR closure proves invariance,
and the replay checks every multiplication sign in the internal block
against the standard sedenion convention.

Inside the internal sedenion algebra, the two octonion halves are pure,
nonzero, orthogonal and have equal norm. Exact polynomial identities check
those conditions for the formula above. Positivity follows because a
nonzero scalar pair already makes `X` nonzero, while `beta=delta=0`
leaves `U=I`. The published sedenion zero-divisor characterization gives
internal nullity four; see [Biss-Dugger-Isaksen, Corollary 11.2 and Proposition 12.1](math-0511691.md).
The internal rank is therefore twelve.

For the external block at `f=0`, multiply `X` by `Delta` to obtain a
polynomial numerator. The centered external complement and kernel give
an `8 x 8` pivot and an `8 x 8` Schur residual. Direct symbolic elimination
proves the residual identically zero. The numerator pivot determinant is

```text
(k-1)^4 (k+1)^4
  * (beta^2+delta^2+4(k-1)^2)^4
  * (beta^2+delta^2+4(k+1)^2)^4.
```

Every factor is positive on `k!=1,-1`. The external rank is exactly eight
throughout that domain. Together the blocks give total rank twenty.

The phase parameter preserves the external rank by an explicit orthogonal
similarity. Let `E_j` be the external block for basis coefficient `e_j`,
and let `K_phase=-E9 E1/2`. Exact matrix multiplication verifies
`K_phase^T=-K_phase`, the commutator equations

```text
[K_phase,E1]=E9,   [K_phase,E9]=-E1,
[K_phase,E2]=E10,  [K_phase,E10]=-E2,
[K_phase,E17]=E25, [K_phase,E25]=-E17,
[K_phase,E18]=E26, [K_phase,E26]=-E18,
[K_phase,E8]=[K_phase,E24]=0.
```

Their linear differential equation implies that conjugation by
`exp(phi K_phase)` implements the displayed coefficient rotation, with
`phi=2 arctan(f)`. The internal equal-norm and orthogonality identities
also survive that rotation. Thus `X` has nullity twelve for every real
parameter in the stated domain.

Normalize by `Y=sqrt(2/<X,X>) X`. The positive factor is smooth and
preserves rank. At the parameter origin, `Y=x0`. Its differential has
columns

```text
e8, e24, -e10+e25, 2(e9+e26).
```

The normalization leaves those columns unchanged because they are
orthogonal to `x0`. A line in parameter space realizes every linear
combination of these four velocities by a smooth fixed-norm curve.

## Automorphism directions and tangent-cone equality

The remaining eleven directions come from octonion automorphisms. For
imaginary octonion basis units `a,b`, define

```text
D_(a,b)=[L_a,L_b]+[L_a,R_b]+[R_a,R_b].
```

The retained calculation checks the derivation identity on every ordered
pair of octonion basis vectors, skew symmetry, and `D_(a,b)(1)=0`.
Bilinearity extends the identity to all real inputs. Fourteen independent
matrices span the resulting derivations. Diagonal repetition over the
four octonion blocks gives derivations of dimension-32 multiplication:
conjugation commutes with each derivation, so the Cayley-Dickson product
rule extends the identity through both doublings. Exact coefficient
checks retain that extension as well.

For any such skew derivation `D`, `exp(tD)` is an orthogonal algebra
automorphism. Differentiating the product proves multiplicativity, and
skew symmetry proves norm preservation. Hence these flows preserve rank
and the selected sphere. Their orbit differential at `x0` has rank eleven
and spans exactly `z0,...,z4,z7,...,z12` in the retained tangent basis.
The four slice columns add `z5,z13,z14,2z15`. Their combined rank is
fifteen, and their image is exactly `A15`.

For any `h` in `A15`, choose a real linear combination `D` of the retained
derivations and a real parameter velocity `v` with
`D x0 + dY_0(v)=h`. The curve

```text
x_h(t)=exp(tD) Y(t v)
```

has constant norm squared two, nullity twelve for sufficiently small real
`t`, center `x0`, and velocity `h`. The parameter condition holds near
zero because `k(0)=0`. Thus every `A15` direction is realized. The
published smooth family already realizes every `B17` direction.
Combined with the quadratic necessary condition along arbitrary tangent
sequences, the two inclusions prove

```text
T_Bouligand(X_nullity12 intersect sphere, x0)=A15 union B17.
```

The cone has dimension seventeen and contains a fifteen-dimensional linear
piece outside its seventeen-dimensional piece. The two tangent pieces
intersect in dimension thirteen. The cone is non-linear: the displayed
sum of an `A15`-only direction and a `B17`-only direction lies outside it.
In particular, the complete selected-center locus cannot be a C1 embedded
submanifold there, since such a manifold has a linear tangent cone.

## Scope and remaining geometry

The quadratic certificate and the curve construction prove the complete
selected-center tangent cone. The curve proof uses real smooth
normalization and automorphism flows; the runtime point evaluator retains
exact rational unnormalized coordinates and their rational norm squared.
The executable point API does not approximate a normalized irrational
coordinate vector.

Tangent-cone equality leaves local branch equations, smooth stratification,
kernel-bundle attachments, normal links and global homology or cohomology
separate. The dimensions 15, 17 and 13 describe the tangent pieces and
their intersection. They do not assert an actual two-branch local
attachment model. The global dimension-32 and all-dimensional pair-space
classifications remain open obligations in the
[research roadmap](../RESEARCH_ROADMAP.md).

All retained calculations use exact CPU algebra. The certificate bundle
contains software proof checks and references to published mathematics;
QPU frequencies supply neither these identities nor a global topology proof.
