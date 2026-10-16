module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.RealCoefficients
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory
open scoped TensorProduct

variable {G : Type} [Group G] (A : Rep.{0} ℚ G) [FiniteDimensional ℚ A]

/-- Genuine real scalar extension of finite-dimensional rational coefficients is finite-dimensional. -/
instance realRep_finiteDimensional : FiniteDimensional ℝ (realRep A) := inferInstanceAs
  (FiniteDimensional ℝ (ℝ ⊗[ℚ] A))

/-- A fixed actual linear coordinate system on the real scalar-extended coefficient module. -/
def realCoefficientCoordinates : (realRep A) ≃ₗ[ℝ] (Fin (Module.finrank ℝ (realRep A)) → ℝ) :=
  (Module.finBasis ℝ (realRep A)).equivFun

/-- An actual norm on real scalar-extended coefficients, induced by fixed finite coordinates. -/
abbrev realCoefficientNorm : NormedAddCommGroup (realRep A) :=
  NormedAddCommGroup.induced _ _ (realCoefficientCoordinates A).toAddMonoidHom
    (realCoefficientCoordinates A).injective

/-- The coordinate norm is compatible with the original real scalar multiplication. -/
abbrev realCoefficientNormedSpace : letI := realCoefficientNorm A; NormedSpace ℝ (realRep A) :=
  NormedSpace.induced ℝ _ _ (realCoefficientCoordinates A).toLinearMap

end TernaryPoly.SmoothSingularGlobal
