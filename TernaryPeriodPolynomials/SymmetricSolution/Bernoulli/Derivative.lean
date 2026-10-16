module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Analysis.Normed.MulAction
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
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.MvPowerSeries.LexOrder
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.MoveAdd
public import Mathlib.Tactic.Ring.NamePowerVars
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# The second Bernoulli cancellation of Lemma 2.3

Formalized by Claude Haiku 5.5. Obligation: the second identity displayed in the proof
of the normal-jet claim of Lemma 2.3,

  `-B(t) + t B'(3t) (1 + eᵗ + e^{2t}) + t e^{2t} B(3t) = -e^{2t} B(3t) B(t)`,

as a literal identity in `ℚ⟦t⟧`, where `B(t) = t/(eᵗ - 1)` (`eq:Bernoulli`) is Mathlib's
`bernoulliPowerSeries ℚ`, `B(3t) = rescale 3 B`, `B'(3t) = rescale 3 (d/dt B)`.

The proof uses only the defining relation `B (eᵗ - 1) = t` (Mathlib's
`bernoulliPowerSeries_mul_exp_sub_one`), its formal derivative, and the rescaling `t ↦ 3t`.
-/

open PowerSeries

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

/-- **Second Bernoulli cancellation**: with `B = bernoulliPowerSeries ℚ`,
`-B + X · B'(3X) · (1 + e^X + e^{2X}) + X · e^{2X} · B(3X) = -e^{2X} · B(3X) · B`
in `ℚ⟦X⟧`, where `B'(3X) = rescale 3 (d⁄dX B)` and `B(3X) = rescale 3 B`. -/
theorem bernoulli_second_cancellation :
    -bernoulliPowerSeries ℚ +
        X * rescale (3 : ℚ) (d⁄dX (bernoulliPowerSeries ℚ)) *
          (1 + exp ℚ + exp ℚ ^ 2) +
        X * exp ℚ ^ 2 * rescale (3 : ℚ) (bernoulliPowerSeries ℚ) =
      -(exp ℚ ^ 2 * rescale (3 : ℚ) (bernoulliPowerSeries ℚ) * bernoulliPowerSeries ℚ) := by
  -- the defining relation `B (eᵗ - 1) = t`
  have hB : bernoulliPowerSeries ℚ * (exp ℚ - 1) = X :=
    bernoulliPowerSeries_mul_exp_sub_one ℚ
  -- its formal derivative `B'(eᵗ - 1) + B eᵗ = 1`, using `d/dt eᵗ = eᵗ`
  have hdE : d⁄dX (exp ℚ) = exp ℚ := derivative_exp ℚ
  have hD0 : d⁄dX (bernoulliPowerSeries ℚ) * (exp ℚ - 1) +
      bernoulliPowerSeries ℚ * exp ℚ = 1 := by
    have h := congrArg (d⁄dX) hB
    simp only [Derivation.leibniz, smul_eq_mul, map_sub, derivative_one,
      derivative_X, hdE] at h
    linear_combination h
  -- rescaling `t ↦ 3t`: `rescale 3` is a ring homomorphism, and `rescale 3 eᵗ = (eᵗ)³`
  have he3 : rescale (3 : ℚ) (exp ℚ) = exp ℚ ^ 3 := by
    have h := exp_pow_eq_rescale_exp (A := ℚ) 3
    have h3 : ((3 : ℕ) : ℚ) = (3 : ℚ) := by norm_num
    rw [h3] at h
    exact h.symm
  have hD : rescale (3 : ℚ) (d⁄dX (bernoulliPowerSeries ℚ)) * (exp ℚ ^ 3 - 1) +
      rescale (3 : ℚ) (bernoulliPowerSeries ℚ) * exp ℚ ^ 3 = 1 := by
    have h := congrArg (rescale (3 : ℚ)) hD0
    simp only [map_add, map_mul, map_sub, map_one] at h
    rw [he3] at h
    linear_combination h
  -- multiply the target by `eᵗ - 1 ≠ 0`; the product vanishes by `hB` and `hD`
  have hne : exp ℚ - 1 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hB
    exact PowerSeries.X_ne_zero hB.symm
  have key : (exp ℚ - 1) *
      (-bernoulliPowerSeries ℚ +
        X * rescale (3 : ℚ) (d⁄dX (bernoulliPowerSeries ℚ)) * (1 + exp ℚ + exp ℚ ^ 2) +
        X * exp ℚ ^ 2 * rescale (3 : ℚ) (bernoulliPowerSeries ℚ) +
        exp ℚ ^ 2 * rescale (3 : ℚ) (bernoulliPowerSeries ℚ) * bernoulliPowerSeries ℚ) = 0 := by
    linear_combination (-1 + exp ℚ ^ 2 * rescale (3 : ℚ) (bernoulliPowerSeries ℚ)) * hB +
      X * hD
  have hG : -bernoulliPowerSeries ℚ +
        X * rescale (3 : ℚ) (d⁄dX (bernoulliPowerSeries ℚ)) * (1 + exp ℚ + exp ℚ ^ 2) +
        X * exp ℚ ^ 2 * rescale (3 : ℚ) (bernoulliPowerSeries ℚ) +
        exp ℚ ^ 2 * rescale (3 : ℚ) (bernoulliPowerSeries ℚ) * bernoulliPowerSeries ℚ = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hne
    · exact h
  linear_combination hG

end TernaryPeriodPolynomials.Argument.Identities

end
