module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.Ordinary
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.Cap
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence
open SingularBoundaryRestriction SingularLocalCoefficient SingularLocalHomology
open CompactInteriorRelativeBoundary SymmetricSpaceRelativeCapConnecting
open SymmetricSpaceBoundaryManifold SymmetricSpaceBoundaryOrientation SymmetricSpaceBoundaryDuality
open OrdinaryTopBoundaryComparison

variable (W : Rep.{0} ℚ principalSix)

/-- The actual equivariant-to-geometric comparison is a morphism of the genuine relative
cochain short exact sequences. -/
def boundaryCochainSequenceMap :
    RelativeCochainSequence.sequence (boundaryRestriction W) ⟶
      RelativeCochainSequence.sequence (geometricBoundaryRestriction W) where
  τ₁ := (boundaryGeometricIso W).hom
  τ₂ := (cochainIso wholeProjection wholeQuotientCovering W).hom
  τ₃ := (cochainIso boundaryProjection boundaryQuotientCovering W).hom
  comm₁₂ := boundaryGeometricIso_inclusion W
  comm₂₃ := by exact (boundary_cochainIso_square W).symm

/-- Genuine cohomology connecting maps commute with the literal covering-cochain comparison. -/
theorem boundaryConnecting_geometric :
    boundaryConnecting W 1 ≫ homologyMap (boundaryGeometricIso W).hom 2 =
      homologyMap (cochainIso boundaryProjection boundaryQuotientCovering W).hom 1 ≫
        geometricBoundaryConnecting W 1 :=
  HomologySequence.δ_naturality (boundaryCochainSequenceMap W)
    (boundary_shortExact W) (geometricBoundary_shortExact W) 1 2 rfl

/-- The geometric boundary functional equals canonical evaluation of actual equivariant
boundary H1, preserving the actual covering and relative comparisons. -/
theorem boundaryCohomologyOrdinary_equivariant :
    homologyMap (cochainIso boundaryProjection boundaryQuotientCovering W).hom 1 ≫
      boundaryCohomologyOrdinary W = boundaryOrdinaryEvaluation W := by
  have he : homologyMap (boundaryGeometricIso W).hom 2 ≫
      homologyMap (relativeHomGeometricIso W).inv 2 =
        homologyMap (relativeHomKernelIso W).inv 2 := by
    rw [← homologyMap_comp]
    apply congrArg (fun f => homologyMap f 2)
    change (boundaryGeometricIso W).hom ≫
      ((boundaryGeometricIso W).inv ≫ (relativeHomKernelIso W).inv) = _
    rw [Iso.hom_inv_id_assoc]
  unfold boundaryCohomologyOrdinary
  rw [← Category.assoc, ← boundaryConnecting_geometric, Category.assoc,
    ← Category.assoc (homologyMap (boundaryGeometricIso W).hom 2), he,
    boundaryConnecting_ordinary]

/-- Actual cap, the whole-boundary inclusion into arithmetic H3, and the genuine ordinary
comparison return the direct boundary homology evaluator. -/
theorem cappedBoundary_ordinary :
    homologyMap (cochainIso boundaryProjection boundaryQuotientCovering W).hom 1 ≫
      (boundaryH1CapIso W boundaryOrientation).hom ≫ boundaryToGroup W 3 ≫
        (groupOrdinaryIso W).hom = boundaryOrdinaryEvaluation W := by
  rw [boundary_groupOrdinary_square, boundaryCohomologyOrdinary_equivariant]

end TernaryPoly.OrdinaryBoundaryActualEvaluation
