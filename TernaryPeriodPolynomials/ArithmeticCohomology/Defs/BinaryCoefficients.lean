module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Pow
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
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Coefficients for the binary Levi coefficient

`homogeneousAction n (-1)` is `Sym^n((ℂ²)*) ⊗ det⁻¹`: the action is
`p(x) ↦ det(g)⁻¹ p(g⁻¹x)`, not the covariant standard representation.

The coordinate-substitution lemmas are adapted from the verified polynomial
action in AxiomMath/axiom-proofs.
This module imports Mathlib only.
-/


open MvPolynomial Matrix
noncomputable section
namespace GeneralEisenstein.Binary

abbrev Poly := MvPolynomial (Fin 2) ℂ
abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) ℂ

/-- The literal linear coordinate form associated to a matrix row. -/
def linearForm (M : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) : Poly :=
  ∑ j, MvPolynomial.C (M i j)*X j

/-- Right polynomial substitution by the displayed matrix. -/
def substitute (M : Matrix (Fin 2) (Fin 2) ℂ) : Poly →ₐ[ℂ] Poly :=
  bind₁ (linearForm M)

theorem substitute_linearForm (M N : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    substitute M (linearForm N i)=linearForm (N*M) i := by
  simp only [linearForm,substitute,map_sum,map_mul,bind₁_C_right,bind₁_X_right,
    Matrix.mul_apply,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem substitute_X (M : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    substitute M (X i)=linearForm M i := by simp [substitute]

/-- Substitutions compose in the reverse matrix order. -/
theorem substitute_comp (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    (substitute M).comp (substitute N)=substitute (N*M) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply,substitute_X]
  exact substitute_linearForm M N i

theorem substitute_one : substitute (1 : Matrix (Fin 2) (Fin 2) ℂ)=AlgHom.id ℂ Poly := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [substitute,linearForm,Matrix.one_apply]

/-- Inverse substitution is the genuine left action on polynomial coefficients. -/
def untwisted : Representation ℂ GL2 Poly where
  toFun g := (substitute (g⁻¹ : GL2)).toLinearMap
  map_one' := by
    simp only [inv_one,GeneralLinearGroup.coe_one,substitute_one]
    rfl
  map_mul' g h := by
    simp only [_root_.mul_inv_rev,GeneralLinearGroup.coe_mul]
    exact congrArg (fun q : Poly →ₐ[ℂ] Poly => q.toLinearMap)
      (substitute_comp (g⁻¹ : GL2) (h⁻¹ : GL2)).symm

/-- The determinant character; exponent `-1` is the paper's coefficient twist. -/
def determinantCharacter (e : ℤ) : GL2 →* ℂ where
  toFun g := ((GeneralLinearGroup.det g : ℂˣ) : ℂ)^e
  map_one' := by simp
  map_mul' g h := by simp [mul_zpow]

/-- Polynomial coefficients with their actual determinant twist. -/
def action (e : ℤ) : Representation ℂ GL2 Poly where
  toFun g := determinantCharacter e g • untwisted g
  map_one' := by simp
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    change determinantCharacter e (g*h) • untwisted (g*h) f =
      determinantCharacter e g • untwisted g (determinantCharacter e h • untwisted h f)
    rw [map_mul,map_mul,Module.End.mul_apply,map_smul,smul_smul]

theorem action_apply (e : ℤ) (g : GL2) (f : Poly) :
    action e g f=determinantCharacter e g • substitute (g⁻¹ : GL2) f := rfl

theorem linearForm_homogeneous (M : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    (linearForm M i).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _
  exact isHomogeneous_C_mul_X _ _

theorem substitute_homogeneous (M : Matrix (Fin 2) (Fin 2) ℂ)
    {f : Poly} {n : ℕ} (hf : f.IsHomogeneous n) : (substitute M f).IsHomogeneous n :=
  by
  simpa only [substitute, one_mul, aeval_eq_bind₁] using
    hf.aeval (linearForm M) (linearForm_homogeneous M)

theorem action_homogeneous (e : ℤ) (g : GL2) {f : Poly} {n : ℕ}
    (hf : f.IsHomogeneous n) : (action e g f).IsHomogeneous n := by
  rw [action_apply,Algebra.smul_def]
  exact (substitute_homogeneous _ hf).C_mul _

/-- The exact degree-`n` coefficient space, including the zero polynomial. -/
abbrev HomogeneousPoly (n : ℕ) := homogeneousSubmodule (Fin 2) ℂ n

/-- The genuine homogeneous coefficient representation. -/
def homogeneousAction (n : ℕ) (e : ℤ) : Representation ℂ GL2 (HomogeneousPoly n) :=
  (action e).subrepresentation (homogeneousSubmodule (Fin 2) ℂ n)
    (fun g _ hf => action_homogeneous e g hf)

@[simp] theorem homogeneousAction_coe (n : ℕ) (e : ℤ) (g : GL2)
    (f : HomogeneousPoly n) :
    ((homogeneousAction n e g f : HomogeneousPoly n) : Poly) = action e g f := rfl

end GeneralEisenstein.Binary

end
