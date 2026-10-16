module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.ConnectingRepresentative

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence
open EquivariantSingularResolution SingularBoundaryRestriction SymmetricSpaceRationalGluing
open SymmetricSpaceBoundaryIncidenceHomology OrdinaryTopBoundaryComparison

/-- Lift the actual family of relative two-cycles through the actual graded quotient section. -/
def relativeCycleAmbientLift : upstairsRelativeChains.cycles 2 ⟶
    (equivariantChains principalSix (TopCat.of Glued)).X 2 :=
  upstairsRelativeChains.iCycles 2 ≫ relativeProjectionSection boundaryInclusion
    boundaryInclusion_equivariant boundaryInclusion_injective 2

/-- Projection returns exactly the original relative cycle family. -/
theorem relativeCycleAmbientLift_projection :
    relativeCycleAmbientLift ≫ (cokernel.π upstairsBoundaryChainMap).f 2 =
      upstairsRelativeChains.iCycles 2 := by
  unfold relativeCycleAmbientLift
  rw [Category.assoc, relativeProjectionSection_identity, Category.comp_id]

/-- The differential of the actual lifted relative cycle lies in actual boundary chains. -/
theorem relativeCycleAmbientLift_boundary :
    (relativeCycleAmbientLift ≫ (equivariantChains principalSix (TopCat.of Glued)).d 2 1) ≫
      (cokernel.π upstairsBoundaryChainMap).f 1 = 0 := by
  rw [Category.assoc, ← (cokernel.π upstairsBoundaryChainMap).comm 2 1,
    ← Category.assoc, relativeCycleAmbientLift_projection, iCycles_d]

/-- The genuine boundary inclusion is monic after evaluation in every chain degree. -/
instance upstairsBoundaryDegree_mono (n : ℕ) :
    Mono (upstairsRelativeSequence.map
      (eval (Rep ℚ principalSix) (ComplexShape.down ℕ) n)).f := by
  change Mono (upstairsBoundaryChainMap.f n)
  let : Mono upstairsBoundaryChainMap := inclusion_mono boundaryInclusion
    boundaryInclusion_equivariant boundaryInclusion_injective
  infer_instance

/-- The actual degree-one short exact sequence supplies a boundary lift of that differential. -/
def relativeCycleBoundaryLift : upstairsRelativeChains.cycles 2 ⟶ boundaryChains.X 1 :=
  (upstairsRelativeSequence_shortExact.exact.map
    (eval (Rep ℚ principalSix) (ComplexShape.down ℕ) 1)).lift
    (relativeCycleAmbientLift ≫ (equivariantChains principalSix (TopCat.of Glued)).d 2 1)
    relativeCycleAmbientLift_boundary

/-- Inclusion of the boundary lift is precisely the lifted ambient differential. -/
theorem relativeCycleBoundaryLift_inclusion :
    relativeCycleBoundaryLift ≫ upstairsBoundaryChainMap.f 1 =
      relativeCycleAmbientLift ≫ (equivariantChains principalSix (TopCat.of Glued)).d 2 1 :=
  (upstairsRelativeSequence_shortExact.exact.map
    (eval (Rep ℚ principalSix) (ComplexShape.down ℕ) 1)).lift_f _ _

/-- The actual lifted boundary is itself a cycle. -/
theorem relativeCycleBoundaryLift_cycle : relativeCycleBoundaryLift ≫ boundaryChains.d 1 0 = 0 := by
  let : Mono upstairsBoundaryChainMap := inclusion_mono boundaryInclusion
    boundaryInclusion_equivariant boundaryInclusion_injective
  apply (cancel_mono (upstairsBoundaryChainMap.f 0)).mp
  rw [Category.assoc, ← upstairsBoundaryChainMap.comm 1 0, ← Category.assoc,
    relativeCycleBoundaryLift_inclusion, Category.assoc, d_comp_d, comp_zero, zero_comp]

/-- The boundary lift, bundled in the actual boundary cycle object. -/
def relativeCycleBoundaryCycles : upstairsRelativeChains.cycles 2 ⟶ boundaryChains.cycles 1 :=
  boundaryChains.liftCycles relativeCycleBoundaryLift 0 (by simp) relativeCycleBoundaryLift_cycle

/-- The genuine connecting morphism is represented by this actual lifted boundary. -/
theorem relativeCycleBoundaryCycles_connecting :
    upstairsRelativeChains.homologyπ 2 ≫ upstairsRelativeSequence_shortExact.δ 2 1 rfl =
      relativeCycleBoundaryCycles ≫ boundaryChains.homologyπ 1 := by
  have h := upstairsRelativeSequence_shortExact.δ_eq 2 1 rfl
    (upstairsRelativeChains.iCycles 2) (upstairsRelativeChains.iCycles_d 2 1)
    relativeCycleAmbientLift relativeCycleAmbientLift_projection
    relativeCycleBoundaryLift relativeCycleBoundaryLift_inclusion 0 (by simp)
  have hid : upstairsRelativeChains.liftCycles (upstairsRelativeChains.iCycles 2) 1
      ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 2 1 from rfl))
      (upstairsRelativeChains.iCycles_d 2 1) = 𝟙 _ := by
    apply (cancel_mono (upstairsRelativeChains.iCycles 2)).mp
    rw [liftCycles_i, Category.id_comp]
  erw [hid, Category.id_comp] at h
  exact h

end TernaryPoly.OrdinaryBoundaryActualEvaluation
