module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.CommonRootCoinduction
public import Mathlib.RepresentationTheory.FiniteIndex
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryCommonRoot
open ModThreeGoodAction PolynomialGLAction CategoryTheory

/-- The literal mod-three fixer has finite index, since it contains the reduction kernel. -/
instance congruence_finiteIndex : K.FiniteIndex := by
  apply Subgroup.finiteIndex_of_le (H := reduction.ker)
  intro g hg
  change Matrix.vecMul fixedRow (reduction g).val = fixedRow
  rw [show reduction g = 1 from hg, Units.val_one, Matrix.vecMul_one]

/-- The actual homogeneous representation of the subgroup, with arbitrary determinant twist. -/
abbrev subgroupCoefficients (n : ℕ) (e : ℤ) : Rep ℚ K :=
  Rep.of ((integralAction n e).comp K.subtype)

/-- The 26-fiber action is equivariantly isomorphic to actual coinduction. -/
def coinducedIso (n : ℕ) (e : ℤ) : Rep.of (coefficientAction n e) ≅
    Rep.coind K.subtype (subgroupCoefficients n e) :=
  Rep.mkIso (Representation.Equiv.mk (coinducedEquiv n e) (fun g => by
    apply LinearMap.ext
    intro F
    exact toCoinduced_equivariant n e g F))

/-- Finite-index induction is exactly the literal 26-covector homogeneous coefficient system. -/
def inducedIso (n : ℕ) (e : ℤ) :
    Rep.ind K.subtype (subgroupCoefficients n e) ≅ Rep.of (coefficientAction n e) := by
  classical
  exact Rep.indCoindIso (subgroupCoefficients n e) ≪≫ (coinducedIso n e).symm

/-- No finite-dimensional hypothesis on the induced space is assumed: it follows from its 26 fibers. -/
instance induced_finite (n : ℕ) (e : ℤ) :
    FiniteDimensional ℚ (Rep.ind K.subtype (subgroupCoefficients n e)) :=
  FiniteDimensional.of_injective (inducedIso n e).hom.hom.toLinearMap (by
    intro x y h
    have hh := congrArg (fun z => (inducedIso n e).inv.hom z) h
    simpa using hh)

end TernaryPoly.OrdinaryBoundaryCommonRoot
