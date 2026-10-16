module

public import TernaryPeriodPolynomials.Topology.SingularHomology.AlexanderWhitneyChainMap
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Complex
public import TernaryPeriodPolynomials.Topology.SingularLocal.CoefficientComplex

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCap
open CategoryTheory
open scoped Simplicial
open FreeActionLinearization CoveringSingularOrbits
open SphereOddDegree.AlexanderWhitney

/-- The actual continuous map inserting the front vertices of a standard simplex. -/
def frontMap (a b : ℕ) :
    C(Convexity.StdSimplex ℝ (Fin (a+1)), Convexity.StdSimplex ℝ (Fin (a+b+1))) :=
  (SimplexCategory.toTop₀.map (frontFace a b)).hom

/-- The actual continuous map inserting the back vertices of a standard simplex. -/
def backMap (a b : ℕ) :
    C(Convexity.StdSimplex ℝ (Fin (b+1)), Convexity.StdSimplex ℝ (Fin (a+b+1))) :=
  (SimplexCategory.toTop₀.map (backFace a b)).hom

/-- Reparametrizing along the front map is the actual front singular face. -/
theorem pull_front {X : TopCat.{0}} (a b : ℕ) (σ : SingularSimplex X (a+b)) :
    pullSimplex (frontMap a b) σ = frontSimplex X a b σ := rfl

/-- Reparametrizing along the back map is the actual back singular face. -/
theorem pull_back {X : TopCat.{0}} (a b : ℕ) (σ : SingularSimplex X (a+b)) :
    pullSimplex (backMap a b) σ = backSimplex X a b σ := rfl

/-- Front restriction commutes with the actual map on singular simplices. -/
theorem projection_front {X Y : TopCat.{0}} (f : X ⟶ Y) (a b : ℕ)
    (σ : SingularSimplex X (a+b)) :
    projection f a (frontSimplex X a b σ) =
      frontSimplex Y a b (projection f (a+b) σ) :=
  frontSimplex_naturality f a b σ

/-- Back restriction commutes with the actual map on singular simplices. -/
theorem projection_back {X Y : TopCat.{0}} (f : X ⟶ Y) (a b : ℕ)
    (σ : SingularSimplex X (a+b)) :
    projection f b (backSimplex X a b σ) =
      backSimplex Y a b (projection f (a+b) σ) :=
  backSimplex_naturality f a b σ

end TernaryPoly.SingularLocalCap
