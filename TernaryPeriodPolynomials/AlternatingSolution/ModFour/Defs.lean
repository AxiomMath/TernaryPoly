module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.Polynomial.CharTwo.NormGenerators
public import Mathlib.Algebra.MvPolynomial.PDeriv

@[expose] public section


/-!
# Definitions for the mod-four argument (Sections 5.2–5.5 and Appendix D)

Paper:, labels `mf:thm:main`,
`mf:lem:kernel`, `mf:lem:cancellation`, `mf:lem:well-defined`, `mf:lem:beta`, `mf:app:kernel`.

Over `k = 𝔽₂` we reuse the existing literal definitions of `TernaryPoly.CharTwoNorm`:
`a, b, c` (elementary symmetric polynomials in `x, y, z`), `c₊ = ab + c`, the Dickson
invariants `d₄, d₆, d₇` (`mf:eq:invariants`), the reduced norm
`N̄ g = g(x,y,z) + g(y,x+y,z) + g(x+y,x,z)`, the list `B₀, …, B₇` (`mf:eq:Bs`) and the
generators `K_j = a c₊ B_j`. A substitution is a triple of linear forms: the triple
`(λ₁, λ₂, λ₃)` sends `h` to `h(λ₁, λ₂, λ₃) = bind₁ ![λ₁, λ₂, λ₃] h`.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument

open TernaryPoly.CharTwoNorm

/-- Polynomials over `k = 𝔽₂` in `x, y, z`. -/
abbrev Poly2 := MvPolynomial (Fin 3) (ZMod 2)

/-- Reduction of an integral polynomial modulo two. -/
abbrev reduceTwo : MvPolynomial (Fin 3) ℤ →+* Poly2 :=
  MvPolynomial.map (Int.castRingHom (ZMod 2))

/-- The eighteen substitutions `𝒯` of equation `mf:eq:Tlist`, in the printed order. -/
def piSubstitutions : List (Fin 3 → Poly2) :=
  [![X 1, X 2, X 0 + X 1], ![X 2, X 1, X 0 + X 2], ![X 0, X 2, X 0 + X 1],
   ![X 0, X 2, X 1 + X 2], ![X 0 + X 1, X 2, X 0], ![X 0 + X 1, X 2, X 1],
   ![X 2, X 0 + X 1 + X 2, X 0 + X 2], ![X 0 + X 1 + X 2, X 2, X 1 + X 2],
   ![X 0, X 1, X 0 + X 2],
   ![X 0, X 1, X 1 + X 2], ![X 1, X 0 + X 2, X 0], ![X 1, X 0 + X 1 + X 2, X 0 + X 1],
   ![X 0 + X 2, X 1, X 2], ![X 0 + X 1 + X 2, X 1, X 1 + X 2], ![X 0, X 1 + X 2, X 1],
   ![X 0, X 0 + X 1 + X 2, X 0 + X 1], ![X 0, X 1 + X 2, X 2],
   ![X 0, X 0 + X 1 + X 2, X 0 + X 2]]

/-- `Π h = ∑_{λ ∈ 𝒯} h(λ₁, λ₂, λ₃)` (equation `mf:eq:Pi`). -/
def piOperator (h : Poly2) : Poly2 :=
  (piSubstitutions.map fun t => bind₁ t h).sum

/-- The fifteen substitutions `ℋ` of Appendix D, in the printed order. -/
def thetaSubstitutions : List (Fin 3 → Poly2) :=
  [![X 1, X 2, X 0], ![X 1, X 2, X 0 + X 1], ![X 2, X 1, X 0 + X 2],
   ![X 0, X 2, X 1], ![X 0, X 2, X 0 + X 1], ![X 0, X 2, X 1 + X 2],
   ![X 0 + X 1, X 2, X 0], ![X 0 + X 1, X 2, X 1], ![X 0, X 1, X 2],
   ![X 0, X 1, X 0 + X 2], ![X 0, X 1, X 1 + X 2], ![X 1, X 0 + X 2, X 0],
   ![X 0 + X 2, X 1, X 2], ![X 0, X 1 + X 2, X 1], ![X 0, X 1 + X 2, X 2]]

/-- `Θ h = ∑_{λ ∈ ℋ} h(λ)` (Appendix D). -/
def thetaOperator (h : Poly2) : Poly2 :=
  (thetaSubstitutions.map fun t => bind₁ t h).sum

/-- The substitution `𝐱 ↦ U P 𝐱` for the permutation matrix `P` of `σ` and the upper
unitriangular matrix `U` with entries `s, t, u` (Appendix D). -/
def projectorSubstitution (σ : Equiv.Perm (Fin 3)) (s t u : ZMod 2) : Fin 3 → Poly2 :=
  ![X (σ 0) + C s * X (σ 1) + C t * X (σ 2), X (σ 1) + C u * X (σ 2), X (σ 2)]

/-- The projector `π g = ∑_{P ∈ 𝒲} ∑_{U ∈ 𝒰} g(U P 𝐱)`, a sum of `48` substitutions
(Appendix D). -/
def substitutionProjector (g : Poly2) : Poly2 :=
  ∑ σ : Equiv.Perm (Fin 3), ∑ s : ZMod 2, ∑ t : ZMod 2, ∑ u : ZMod 2,
    bind₁ (projectorSubstitution σ s t u) g

/-- The eight projected sources `a²b, ab², b³, b²c, ac², bc², c³, b⁵` of equation
`mf:eq:projected-exps`. -/
def projectedSource : Fin 8 → Poly2 :=
  ![a ^ 2 * b, a * b ^ 2, b ^ 3, b ^ 2 * c, a * c ^ 2, b * c ^ 2, c ^ 3, b ^ 5]

/-- `κ_j = 1` exactly when `deg K_j = (4,5,6,7,7,8,9,10)_j` is even. -/
def kappa : Fin 8 → ℕ := ![1, 0, 1, 0, 0, 1, 0, 1]

/-- The odd-degree generators `L_j = K_j d₇^{κ_j}` (equation `mf:eq:Lbasis`). -/
def oddGenerator (j : Fin 8) : Poly2 := generator j * d7 ^ kappa j

/-- Evaluation of a formal polynomial in `p, q, ρ` (the variables `X 0, X 1, X 2`) at
`p = d₄`, `q = d₆`, `ρ = d₇²`; its range is `R₀ = k[p, q, ρ]`. -/
def evalR0 : MvPolynomial (Fin 3) (ZMod 2) →ₐ[ZMod 2] Poly2 :=
  bind₁ ![d4, d6, d7 ^ 2]

/-- Evaluation at `p² = d₄²`, `q² = d₆²`, `ρ = d₇²`; its range is `R₂ = k[p², q², ρ]`. -/
def evalR2 : MvPolynomial (Fin 3) (ZMod 2) →ₐ[ZMod 2] Poly2 :=
  bind₁ ![d4 ^ 2, d6 ^ 2, d7 ^ 2]

/-- The eight-coefficient expression `v = ∑_j r_j(p, q, ρ) L_j` of equation `mf:eq:eight`. -/
def expandOdd (r : Fin 8 → MvPolynomial (Fin 3) (ZMod 2)) : Poly2 :=
  ∑ j, evalR0 (r j) * oddGenerator j

/-- The operator `U` of equation `mf:eq:U` on coefficient tuples: with subscripts `p, q` the
formal derivatives in the first two variables (`ρ = X 2` fixed),
`U(v) = r_{4,p} L₀ + ρ r_{5,p} L₁ + r_{4,q} L₂ + (r₄ + ρ r_{5,q}) L₃ + ρ (r_{5,q} + r_{7,p}) L₄ +
ρ r_{7,q} L₆`. -/
def uOperator (r : Fin 8 → MvPolynomial (Fin 3) (ZMod 2)) :
    Fin 8 → MvPolynomial (Fin 3) (ZMod 2) :=
  ![pderiv 0 (r 4), X 2 * pderiv 0 (r 5), pderiv 1 (r 4), r 4 + X 2 * pderiv 1 (r 5),
    X 2 * (pderiv 1 (r 5) + pderiv 0 (r 7)), 0, X 2 * pderiv 1 (r 7), 0]

/-! ### Integral lifts used in equation `mf:eq:beta` -/

/-- The integral elementary symmetric polynomial `a = x + y + z`. -/
def liftA : MvPolynomial (Fin 3) ℤ := X 0 + X 1 + X 2
/-- The integral elementary symmetric polynomial `b = xy + xz + yz`. -/
def liftB : MvPolynomial (Fin 3) ℤ := X 0 * X 1 + X 0 * X 2 + X 1 * X 2
/-- The integral elementary symmetric polynomial `c = xyz`. -/
def liftC : MvPolynomial (Fin 3) ℤ := X 0 * X 1 * X 2
/-- The integral polynomial `c₊ = ab + c = (x+y)(x+z)(y+z)`. -/
def liftCplus : MvPolynomial (Fin 3) ℤ := liftA * liftB + liftC
/-- The integral Vandermonde polynomial `Δ = (x-y)(x-z)(y-z)`, whose reduction is `c₊`. -/
def liftDelta : MvPolynomial (Fin 3) ℤ := (X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)
/-- The integral polynomials of equation `mf:eq:invariants`. -/
def liftD4 : MvPolynomial (Fin 3) ℤ := liftA ^ 4 + liftB ^ 2 + liftA * liftC
/-- See `liftD4`. -/
def liftD6 : MvPolynomial (Fin 3) ℤ :=
  liftA ^ 2 * liftB ^ 2 + liftA ^ 3 * liftC + liftA * liftB * liftC + liftC ^ 2
/-- See `liftD4`. -/
def liftD7 : MvPolynomial (Fin 3) ℤ := liftA * liftC * (liftA * liftB + liftC)

/-- Evaluation of an integral formal polynomial at the squared integral invariants
`(D₄², D₆², D₇²)`; these lift `R₂`. -/
def evalSquaredLift : MvPolynomial (Fin 3) ℤ →ₐ[ℤ] MvPolynomial (Fin 3) ℤ :=
  bind₁ ![liftD4 ^ 2, liftD6 ^ 2, liftD7 ^ 2]

end TernaryPeriodPolynomials.Argument
