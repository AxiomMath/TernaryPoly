module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.FiniteSupport.Basic
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
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {index V H : Type} [Fintype index] [AddCommGroup V] [Module ℂ V]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

def finiteTensorOperator (basis : Module.Basis index ℂ V) (operator : Module.End ℂ V) :
    (index → H) →L[ℂ] (index → H) :=
  ContinuousLinearMap.pi (fun position =>
    ∑ source, basis.coord position (operator (basis source)) • ContinuousLinearMap.proj source)

theorem finiteTensorOperator_apply (basis : Module.Basis index ℂ V)
    (operator : Module.End ℂ V) (vectors : index → H) (position : index) :
    finiteTensorOperator basis operator vectors position =
      ∑ source, basis.coord position (operator (basis source)) • vectors source := by
  simp only [finiteTensorOperator, ContinuousLinearMap.pi_apply, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply]

theorem finiteTensorOperator_one (basis : Module.Basis index ℂ V) :
    finiteTensorOperator (H := H) basis 1 = ContinuousLinearMap.id ℂ (index → H) := by
  classical
  apply ContinuousLinearMap.ext
  intro vectors
  funext position
  simp [finiteTensorOperator_apply, Module.Basis.coord_apply]

theorem basis_coord_comp (basis : Module.Basis index ℂ V)
    (first second : Module.End ℂ V) (position source : index) :
    basis.coord position ((first * second) (basis source)) =
      ∑ middle, basis.coord position (first (basis middle)) *
        basis.coord middle (second (basis source)) := by
  have expansion := congrArg (fun vector => basis.coord position (first vector))
    (basis.sum_repr (second (basis source)))
  simpa only [map_sum, map_smul, Module.Basis.coord_apply, smul_eq_mul, mul_comm,
    Module.End.mul_apply] using expansion.symm

theorem finiteTensorOperator_mul (basis : Module.Basis index ℂ V)
    (first second : Module.End ℂ V) :
    finiteTensorOperator (H := H) basis (first * second) =
      (finiteTensorOperator basis first).comp (finiteTensorOperator basis second) := by
  apply ContinuousLinearMap.ext
  intro vectors
  funext position
  simp only [ContinuousLinearMap.comp_apply, finiteTensorOperator_apply,
    basis_coord_comp, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem finiteTensorOperator_commutes (basis : Module.Basis index ℂ V)
    (operator : Module.End ℂ V) (action : H →L[ℂ] H) (vectors : index → H) :
    finiteTensorOperator basis operator (fun position => action (vectors position)) =
      fun position => action (finiteTensorOperator basis operator vectors position) := by
  funext position
  simp only [finiteTensorOperator_apply, map_sum, map_smul]

theorem finiteTensorOperator_add (basis : Module.Basis index ℂ V)
    (first second : Module.End ℂ V) :
    finiteTensorOperator (H := H) basis (first + second) =
      finiteTensorOperator basis first + finiteTensorOperator basis second := by
  ext vectors position
  simp only [finiteTensorOperator_apply, LinearMap.add_apply, map_add, add_smul,
    Finset.sum_add_distrib, _root_.add_apply, Pi.add_apply]

theorem finiteTensorOperator_sub (basis : Module.Basis index ℂ V)
    (first second : Module.End ℂ V) :
    finiteTensorOperator (H := H) basis (first - second) =
      finiteTensorOperator basis first - finiteTensorOperator basis second := by
  ext vectors position
  simp only [finiteTensorOperator_apply, LinearMap.sub_apply, map_sub, sub_smul,
    Finset.sum_sub_distrib, _root_.sub_apply, Pi.sub_apply]

theorem finiteTensorOperator_smul (basis : Module.Basis index ℂ V)
    (scalar : ℂ) (operator : Module.End ℂ V) :
    finiteTensorOperator (H := H) basis (scalar • operator) = scalar • finiteTensorOperator basis operator := by
  ext vectors position
  simp only [finiteTensorOperator_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_smul,
    Finset.smul_sum, _root_.smul_apply, Pi.smul_apply]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
