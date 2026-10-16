module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
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
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.ComputeDegree

@[expose] public section


open MvPolynomial

namespace TernaryPoly

/-- Linear substitutions preserve homogeneous degree. -/
theorem isHomogeneous_bind₁_linear {σ τ : Type*} {R : Type*} [CommSemiring R]
    {f : MvPolynomial σ R} {n : ℕ} (hf : f.IsHomogeneous n)
    (g : σ → MvPolynomial τ R) (hg : ∀ i, (g i).IsHomogeneous 1)
    : (bind₁ g f).IsHomogeneous n := by
  simpa only [one_mul, aeval_eq_bind₁] using hf.aeval g hg

/-- Homogeneous projection commutes with substitution by linear forms. -/
theorem homogeneousComponent_bind₁_linear {σ τ : Type*} {R : Type*} [CommSemiring R]
    (g : σ → MvPolynomial τ R) (hg : ∀ i, (g i).IsHomogeneous 1)
    (n : ℕ) (f : MvPolynomial σ R) :
    homogeneousComponent n (bind₁ g f) = bind₁ g (homogeneousComponent n f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    have hm := isHomogeneous_monomial (d := d) r rfl
    have hb := isHomogeneous_bind₁_linear hm g hg
    rw [homogeneousComponent_of_mem hb, homogeneousComponent_of_mem hm]
    split_ifs <;> simp
  | add p q hp hq =>
    simp only [map_add, hp, hq]

private theorem homogeneous_vec3 {R : Type*} [CommSemiring R]
    {a b c : MvPolynomial (Fin 3) R}
    (ha : a.IsHomogeneous 1) (hb : b.IsHomogeneous 1) (hc : c.IsHomogeneous 1) :
    ∀ i : Fin 3, (![a, b, c] i).IsHomogeneous 1 := by
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

/-- Both relations descend to every homogeneous component. -/
theorem homogeneousComponent_relations (f : MvPolynomial (Fin 3) ℚ)
    (hcyclic : bind₁ ![X 1, X 2, X 0] f = f)
    (hnorm : f + bind₁ ![-X 1, X 0 - X 1, X 2] f +
      bind₁ ![X 1 - X 0, -X 0, X 2] f = 0) (n : ℕ) :
    bind₁ ![X 1, X 2, X 0] (homogeneousComponent n f) = homogeneousComponent n f ∧
    homogeneousComponent n f +
      bind₁ ![-X 1, X 0 - X 1, X 2] (homogeneousComponent n f) +
      bind₁ ![X 1 - X 0, -X 0, X 2] (homogeneousComponent n f) = 0 := by
  have h0 := isHomogeneous_X ℚ (0 : Fin 3)
  have h1 := isHomogeneous_X ℚ (1 : Fin 3)
  have h2 := isHomogeneous_X ℚ (2 : Fin 3)
  constructor
  · have h := congrArg (homogeneousComponent n) hcyclic
    rwa [homogeneousComponent_bind₁_linear _ (homogeneous_vec3 h1 h2 h0)] at h
  · have h := congrArg (homogeneousComponent n) hnorm
    simpa only [map_add, map_zero,
      homogeneousComponent_bind₁_linear _ (homogeneous_vec3 h1.neg (h0.sub h1) h2),
      homogeneousComponent_bind₁_linear _ (homogeneous_vec3 (h1.sub h0) h0.neg h2)] using h

end TernaryPoly
