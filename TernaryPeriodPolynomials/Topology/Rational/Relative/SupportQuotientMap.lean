module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportNaturalitySmall

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalRelativeSingular

section General
variable {C : Type*} [Category C] [Abelian C]
variable {S S' T : ShortComplex C} (f : S ⟶ T) (f' : S' ⟶ T) (g : S ⟶ S') (h : g ≫ f' = f)

/-- A commuting diagram over a common ambient row induces the actual map of componentwise cokernels. -/
def quotientRowMap : quotientRow f ⟶ quotientRow f' :=
  (quotientIsCokernel f).desc (CokernelCofork.ofπ (quotientProjection f') (by
    rw [← h, Category.assoc, quotientProjection_condition, comp_zero]))

/-- The quotient-row map preserves all three actual quotient projections. -/
theorem quotientRowMap_projection : quotientProjection f ≫ quotientRowMap f f' g h = quotientProjection f' :=
  (quotientIsCokernel f).fac _ WalkingParallelPair.one

end General
variable {X : Type} [TopologicalSpace X]

/-- The actual chain-level quotient-sequence map associated to increasing both exclusions. -/
def quotientChainMap (U V U' V' : Set X) (hU : U ⊆ U') (hV : V ⊆ V') :
    quotientChainRow U V ⟶ quotientChainRow U' V' :=
  quotientRowMap (smallToDiagonal U V) (smallToDiagonal U' V')
    (smallRowMap U V U' V' hU hV) (smallRowMap_toDiagonal U V U' V' hU hV)

/-- The first component preserves literal quotient projections. -/
theorem quotientChainMap_projection₁ (U V U' V' : Set X) (hU : U ⊆ U') (hV : V ⊆ V') :
    cokernel.π (supportedInclusion (U ∩ V)) ≫ (quotientChainMap U V U' V' hU hV).τ₁ =
      cokernel.π (supportedInclusion (U' ∩ V')) :=
  congrArg ShortComplex.Hom.τ₁ (quotientRowMap_projection (smallToDiagonal U V) (smallToDiagonal U' V')
    (smallRowMap U V U' V' hU hV) (smallRowMap_toDiagonal U V U' V' hU hV))

/-- The middle component preserves literal quotient projections. -/
theorem quotientChainMap_projection₂ (U V U' V' : Set X) (hU : U ⊆ U') (hV : V ⊆ V') :
    cokernel.π (biprod.map (supportedInclusion U) (supportedInclusion V)) ≫
      (quotientChainMap U V U' V' hU hV).τ₂ =
        cokernel.π (biprod.map (supportedInclusion U') (supportedInclusion V')) :=
  congrArg ShortComplex.Hom.τ₂ (quotientRowMap_projection (smallToDiagonal U V) (smallToDiagonal U' V')
    (smallRowMap U V U' V' hU hV) (smallRowMap_toDiagonal U V U' V' hU hV))

/-- The third component preserves literal quotient projections. -/
theorem quotientChainMap_projection₃ (U V U' V' : Set X) (hU : U ⊆ U') (hV : V ⊆ V') :
    cokernel.π (supportedSmallSumInclusion U V) ≫ (quotientChainMap U V U' V' hU hV).τ₃ =
      cokernel.π (supportedSmallSumInclusion U' V') :=
  congrArg ShortComplex.Hom.τ₃ (quotientRowMap_projection (smallToDiagonal U V) (smallToDiagonal U' V')
    (smallRowMap U V U' V' hU hV) (smallRowMap_toDiagonal U V U' V' hU hV))

end TernaryPoly.RationalRelativeSupport
