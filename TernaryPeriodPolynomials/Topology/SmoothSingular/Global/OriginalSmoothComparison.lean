module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CompactForgetComparison
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Bridge

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory HomologicalComplex
open SmoothCoveringDeRham SymmetricSpaceCovering SingularLocalCoefficient SingularLocalSupport
open CompactInteriorRelativeBoundary

local instance originalSmoothCoverFact : Fact (IsQuotientCoveringMap singularCoveringProjection DeckGroup) :=
  ⟨quotientProjection_quotientCovering⟩

variable (A : Rep.{0} ℚ DeckGroup) [FiniteDimensional ℚ A] (C : CompactConvexCover)
attribute [local instance] realCoefficientNorm realCoefficientNormedSpace

/-- The actual real compact-to-ordinary square in the singular-to-smooth direction. -/
theorem realCompactSmoothComparison_inverse_square :
    realCoverCompactForget A 2 ≫ (realOrdinarySmoothComparison A C).inv =
      (realCompactSmoothComparison A C).inv ≫ homologyMap (compactInclusion (realRep A).ρ isOpen_univ) 2 :=
  isoSquare_inverse (realCompactSmoothComparison A C) (realOrdinarySmoothComparison A C)
    (homologyMap (compactInclusion (realRep A).ρ isOpen_univ) 2) (realCoverCompactForget A 2)
    (realCompactSmoothComparison_forget A C).symm

/-- The original actual rational local-system cohomology maps to genuine real smooth cohomology. -/
def originalSmoothOrdinary :
    (localCochains singularCoveringProjection quotientProjection_quotientCovering A).homology 2 ⟶
      forgetReal.obj ((globalComplex (realRep A).ρ).homology 2) :=
  originalRationalRealOrdinary A 2 ≫ forgetReal.map (realOrdinarySmoothComparison A C).inv

/-- Genuine smooth cohomology detects every original rational local-system class. -/
theorem originalSmoothOrdinary_injective : Function.Injective (originalSmoothOrdinary A C) :=
  (ConcreteCategory.bijective_of_isIso (forgetReal.map (realOrdinarySmoothComparison A C).inv)).1.comp
    (originalRationalRealOrdinary_injective A 2)

/-- The original actual rational compact relative colimit maps to genuine compact smooth cohomology. -/
def originalSmoothCompact : compactCohomology singularCoveringProjection A 2 ⟶
    forgetReal.obj ((globalCompactComplex (realRep A).ρ).homology 2) :=
  originalRationalRealCompact A 2 ≫ forgetReal.map (realCompactSmoothComparison A C).inv

/-- The exact original rational compactForget map commutes with the proved actual smooth comparison. -/
theorem originalSmooth_compact_square :
    compactForget singularCoveringProjection A 2 ≫ originalSmoothOrdinary A C =
      originalSmoothCompact A C ≫ forgetReal.map (homologyMap (compactInclusion (realRep A).ρ isOpen_univ) 2) := by
  have h := congrArg (fun f => forgetReal.map f) (realCompactSmoothComparison_inverse_square A C)
  rw [Functor.map_comp,Functor.map_comp] at h
  exact composeCommutingSquares (compactForget singularCoveringProjection A 2)
    (originalRationalRealOrdinary A 2) (originalRationalRealCompact A 2)
    (forgetReal.map (realCoverCompactForget A 2)) (forgetReal.map (realOrdinarySmoothComparison A C).inv)
    (forgetReal.map (realCompactSmoothComparison A C).inv)
    (forgetReal.map (homologyMap (compactInclusion (realRep A).ρ isOpen_univ) 2))
    (originalRationalReal_compact_square A 2) h

end TernaryPoly.SmoothSingularGlobal
