module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# The closed cusp-form seeds of Appendix C.3 (`ar:sec:series`)

Paper:, equation `ar:eq:seed` and
Lemma C.3 (`ar:lem:seed`). A point of `𝒳` in plane horospherical coordinates is
`p = (u₁, u₂, x, y, t)` with `τ = x + iy` in the upper half-plane and normal height `t > 0`.
The coefficient polynomials are in `(X, Y, Z) = (X 0, X 1, X 2)`.

A two-form is given by its antisymmetric coefficient matrix `ω(eᵢ, eⱼ)`; the seed is
`ω_h = h(τ) 𝓑ⁿ β ∧ dτ` with `𝓑 = τY - X + (u₁ - τu₂)Z`, `β = du₁ - τ du₂`, `dτ = dx + i dy`.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument

/-- `τ = x + iy` for `p = (u₁, u₂, x, y, t)`. -/
def seedTau (p : Fin 5 → ℝ) : ℂ := (p 2 : ℂ) + Complex.I * (p 3 : ℂ)

/-- The linear coefficient polynomial `𝓑 = τY - X + (u₁ - τu₂)Z`. -/
def seedLinear (p : Fin 5 → ℝ) : MvPolynomial (Fin 3) ℂ :=
  C (seedTau p) * X 1 - X 0 + C ((p 0 : ℂ) - seedTau p * (p 1 : ℂ)) * X 2

/-- The coordinate components of `β = du₁ - τ du₂`. -/
def seedBeta (p : Fin 5 → ℝ) : Fin 5 → ℂ := ![1, -seedTau p, 0, 0, 0]

/-- The coordinate components of `dτ = dx + i dy`. -/
def seedDTau : Fin 5 → ℂ := ![0, 0, 1, Complex.I, 0]

/-- The seed `ω_h = h(τ)𝓑ⁿ β ∧ dτ`, as `ω_h(eᵢ, eⱼ) = h(τ)𝓑ⁿ (β(eᵢ)dτ(eⱼ) - β(eⱼ)dτ(eᵢ))`. -/
def seedForm (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) (i j : Fin 5) : MvPolynomial (Fin 3) ℂ :=
  C (h (seedTau p) * (seedBeta p i * seedDTau j - seedBeta p j * seedDTau i)) * seedLinear p ^ n

/-- The partial derivative along the `k`-th coordinate of a complex function on `ℝ⁵`. -/
def coordPartial (f : (Fin 5 → ℝ) → ℂ) (k : Fin 5) (p : Fin 5 → ℝ) : ℂ :=
  deriv (fun s : ℝ => f (Function.update p k s)) (p k)

/-- The action of `g = diag(A, t)` with `det A > 0` on plane coordinates:
`u' = Au/t`, `τ' = (aτ + b)/(cτ + d)`. The normal height is moved to `t·t₀`; the seed is
independent of the normal height and has no `dt` component, so this choice does not affect
pullbacks of seeds. -/
def leviMap (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![(A 0 0 * p 0 + A 0 1 * p 1) / t, (A 1 0 * p 0 + A 1 1 * p 1) / t,
    (((A 0 0 : ℂ) * seedTau p + A 0 1) / ((A 1 0 : ℂ) * seedTau p + A 1 1)).re,
    (((A 0 0 : ℂ) * seedTau p + A 0 1) / ((A 1 0 : ℂ) * seedTau p + A 1 1)).im, t * p 4]

/-- Pullback of a coefficient-matrix two-form: `(Φ*ω)(eᵢ, eⱼ) = ω_{Φ p}(DΦ eᵢ, DΦ eⱼ)`. -/
def formPullback (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ))
    (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ)
    (p : Fin 5 → ℝ) (i j : Fin 5) : MvPolynomial (Fin 3) ℂ :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    C (((fderiv ℝ Φ p (Pi.single i 1) a) * (fderiv ℝ Φ p (Pi.single j 1) b) : ℝ) : ℂ) * ω (Φ p) a b

/-- The coefficient action `ρ(g) q = det(g)⁻¹ q(g⁻¹𝐗)` of `g = diag(A, t)` on polynomials. -/
def leviCoefficientAction (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (q : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial (Fin 3) ℂ :=
  C (((A.det * t)⁻¹ : ℝ) : ℂ) *
    bind₁ ![C ((A 1 1 / A.det : ℝ) : ℂ) * X 0 + C ((-A 0 1 / A.det : ℝ) : ℂ) * X 1,
      C ((-A 1 0 / A.det : ℝ) : ℂ) * X 0 + C ((A 0 0 / A.det : ℝ) : ℂ) * X 1,
      C ((t⁻¹ : ℝ) : ℂ) * X 2] q

/-- `δ^{k/2}(h|_k A)(τ) = δᵏ (cτ + d)^{-k} h(Aτ)` for `δ = det A > 0` and integral weight `k`. -/
def slashTwisted (k : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ) (h : ℂ → ℂ) (τ : ℂ) : ℂ :=
  (A.det : ℂ) ^ k * ((A 1 0 : ℂ) * τ + A 1 1) ^ (-(k : ℤ)) *
    h (((A 0 0 : ℂ) * τ + A 0 1) / ((A 1 0 : ℂ) * τ + A 1 1))

end TernaryPeriodPolynomials.Argument
