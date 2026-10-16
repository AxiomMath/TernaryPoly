module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
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
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Explicit archimedean data of Appendix C.5 (`ar:sec:real`)

Paper:, Section C.5.
For `L = w₀⁻¹ u(s,t)` the Gram matrix `L Lᵀ` has plane coordinates
`u = (s,t)/r²`, `τ = (-st + ir)/(1+s²)` with `r² = 1 + s² + t²`, and the transported linear
coefficient has `Y`-coefficient `b = -(1 + ist/r)/(1+s²)`. With the local holomorphic
lowest-weight vector `h(τ) = (τ + i)^{-k}`, `k = n + 3`, the real entry is
`I_n = -i ∫_{ℝ²} r⁻³ h(τ) bⁿ ds dt` (equation `ar:eq:realintegral`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument

/-- `r = √(1 + s² + t²)`. -/
def entryRadius (st : ℝ × ℝ) : ℝ := Real.sqrt (1 + st.1 ^ 2 + st.2 ^ 2)

/-- `τ = (-st + i r)/(1 + s²)`. -/
def entryTau (st : ℝ × ℝ) : ℂ :=
  (((-(st.1 * st.2) : ℝ) : ℂ) + Complex.I * (entryRadius st : ℂ)) / ((1 + st.1 ^ 2 : ℝ) : ℂ)

/-- `b = -(1 + i s t / r)/(1 + s²)`. -/
def entryCoefficient (st : ℝ × ℝ) : ℂ :=
  -(1 + Complex.I * ((st.1 * st.2 / entryRadius st : ℝ) : ℂ)) / ((1 + st.1 ^ 2 : ℝ) : ℂ)

/-- The integrand `r⁻³ (τ + i)^{-(n+3)} bⁿ` of `I_n`. -/
def entryIntegrand (n : ℕ) (st : ℝ × ℝ) : ℂ :=
  (entryRadius st : ℂ) ^ (-3 : ℤ) * (entryTau st + Complex.I) ^ (-((n : ℤ) + 3)) *
    entryCoefficient st ^ n

/-- `I_n = -i ∫_{ℝ²} r⁻³ h(τ) bⁿ ds dt` (equation `ar:eq:realintegral`). -/
def entryIntegral (n : ℕ) : ℂ :=
  -Complex.I * ∫ st : ℝ × ℝ, entryIntegrand n st

/-- The angular integrand `e^{ikθ}(c - irv)³(c - iv/r)ⁿ`, `c = cos θ`, `v = sin θ`, `k = n + 3`. -/
def angularIntegrand (n : ℕ) (r θ : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((n : ℂ) + 3) * θ) *
    ((Real.cos θ : ℂ) - Complex.I * (r : ℂ) * (Real.sin θ : ℂ)) ^ 3 *
    ((Real.cos θ : ℂ) - Complex.I * (Real.sin θ : ℂ) / (r : ℂ)) ^ n

/-! ### Plane coordinates of a Gram matrix (verification of `ar:eq:tangententry`) -/

/-- The lower-right entry `R = G₃₃` of a Gram matrix. -/
def gramNormal (G : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := G 2 2

/-- The plane coordinates `u = v/R`, `v = G_{{1,2},3}`. -/
def gramPlaneU (G : Matrix (Fin 3) (Fin 3) ℝ) : ℝ × ℝ := (G 0 2 / G 2 2, G 1 2 / G 2 2)

/-- The Schur complement `C = G_{{1,2},{1,2}} - v vᵀ / R`. -/
def gramSchur (G : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![G 0 0 - G 0 2 * G 0 2 / G 2 2, G 0 1 - G 0 2 * G 1 2 / G 2 2;
     G 1 0 - G 1 2 * G 0 2 / G 2 2, G 1 1 - G 1 2 * G 1 2 / G 2 2]

/-- The plane coordinate `τ = C₁₂/C₂₂ + i √(det C)/C₂₂`. -/
def gramPlaneTau (G : Matrix (Fin 3) (Fin 3) ℝ) : ℂ :=
  ((gramSchur G 0 1 / gramSchur G 1 1 : ℝ) : ℂ) +
    Complex.I * ((Real.sqrt (gramSchur G).det / gramSchur G 1 1 : ℝ) : ℂ)

/-- `L = w₀⁻¹ u(s,t)`. -/
def entryFrame (s t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 0, 0, 1; 1, s, t]

/-- The Gram matrix of `L (1 + εV)`, whose derivative at `ε = 0` is `L (V + Vᵀ) Lᵀ`. -/
def entryCurve (s t : ℝ) (V : Matrix (Fin 3) (Fin 3) ℝ) (ε : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  entryFrame s t * (1 + ε • V) * (1 + ε • V).transpose * (entryFrame s t).transpose

/-- The value `β(V) = du₁(V) - τ du₂(V)` at `L Lᵀ`. -/
def entryBeta (s t : ℝ) (V : Matrix (Fin 3) (Fin 3) ℝ) : ℂ :=
  (deriv (fun ε => (gramPlaneU (entryCurve s t V ε)).1) 0 : ℂ) -
    gramPlaneTau (entryCurve s t V 0) * (deriv (fun ε => (gramPlaneU (entryCurve s t V ε)).2) 0 : ℂ)

/-- The value `dτ(V)` at `L Lᵀ`. -/
def entryDTau (s t : ℝ) (V : Matrix (Fin 3) (Fin 3) ℝ) : ℂ :=
  deriv (fun ε => gramPlaneTau (entryCurve s t V ε)) 0

end TernaryPeriodPolynomials.Argument
