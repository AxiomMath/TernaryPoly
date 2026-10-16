# TernaryPoly

Lean 4 formalization of *Ternary polynomial relations and periods of cusp forms*
by Vasily Ilin and Ken Ono, developed with AxiomProver at Axiom Math.
[Read the paper](paper/paper.pdf).

## Notation

$F$ is a field with $\mathrm{char}(F) = 0$; $f \in F[x,y,z]$, $q \in F[X,Y]$; a subscript $n$
denotes homogeneous polynomials of degree $n$.

```math
\begin{aligned}
\tau(x,y,z) &= (-y,\ x-y,\ z),\\
Nf &= f + f\circ\tau + f\circ\tau^{2},\\
N_2 q &= q(X,Y) + q(-Y,X-Y) + q(Y-X,-X),\\
\Phi(q) &= q(x,y) + q(y,z) + q(z,x).
\end{aligned}
```

```math
P^{\mathrm{odd}}_n(F) =
\left\{ q \in F[X,Y]_n :
\begin{aligned}
q(Y,X) &= q(X,Y),\\
q(-X,Y) &= q(X,-Y) = -q(X,Y),\\
N_2 q &= 0
\end{aligned}
\right\}.
```

## Main results

**Theorem 1.1** ([`TernaryPeriodPolynomials.bachmann_van_ittersum`](TernaryPeriodPolynomials/MainTheorem.lean)).

```math
\begin{gathered}
f(y,z,x) = f(x,y,z),\qquad Nf = 0\\
\Longrightarrow
\begin{cases}
f \in F[x,y] + F[y,z] + F[z,x],\\
\partial_x\partial_y\partial_z f = 0,\\
f \in F[x,y,z]_n,\quad 2 \nmid n \Longrightarrow f = 0.
\end{cases}
\end{gathered}
```

**Theorem 1.2** ([`TernaryPeriodPolynomials.symmetric_solution_iff_eq_cyclicLift`](TernaryPeriodPolynomials/SymmetricClassification.lean)).

```math
\begin{gathered}
f \in F[x,y,z]_n,\qquad f\circ\sigma=f\quad(\forall\sigma\in S_3)\\
\Longrightarrow\\
Nf = 0 \quad\Longleftrightarrow\quad
\exists!\,q \in P^{\mathrm{odd}}_n(F),\quad f = \Phi(q).
\end{gathered}
```

## Build

Lean 4.35.0-rc3 and Mathlib, pinned in the Lake configuration.

```sh
lake build
```

## Comparator

[`Comparator/Challenge.lean`](Comparator/Challenge.lean) states both theorems with `sorry`
and imports only Mathlib; [`Comparator/Solution.lean`](Comparator/Solution.lean) supplies the
proofs. On Linux, with `bubblewrap` installed:

```sh
lake comparator --config Comparator/comparator.json
```
