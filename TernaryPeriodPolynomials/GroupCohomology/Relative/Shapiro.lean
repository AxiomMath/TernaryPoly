module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Shapiro.Bridge

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeShapiro
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open RelativeExtObstructionSequences RelativeOrbitStabilizers
open RelativeShapiroModules RelativeShapiroBridge

/-- The two actual degree-one stabilizer cohomology vanishings kill the relative edge Ext term. -/
theorem relativeEdges_ext (E : Rep.{0} ℚ K)
    (hBB : IsZero (groupCohomology (Rep.res HBB.subtype E) 1))
    (hBG : IsZero (groupCohomology (Rep.res HBG.subtype E) 1)) :
    Subsingleton (Ext.{1} RelativeEdgesRep E 1) := by
  have := coset_ext_subsingleton HBB E 0 hBB
  have := coset_ext_subsingleton HBG E 0 hBG
  exact relativeEdges_ext_subsingleton E

/-- The two actual degree-two stabilizer cohomology vanishings kill the relative vertex Ext term. -/
theorem relativeVertices_ext (E : Rep.{0} ℚ K)
    (hL : IsZero (groupCohomology (Rep.res HL.subtype E) 2))
    (hP : IsZero (groupCohomology (Rep.res HP.subtype E) 2)) :
    Subsingleton (Ext.{1} RelativeVerticesRep E 2) := by
  have := coset_ext_subsingleton HL E 1 hL
  have := coset_ext_subsingleton HP E 1 hP
  exact relativeVertices_ext_subsingleton E

/-- The four explicit arithmetic cohomology vanishings imply extension of every actual
Good-cycle morphism. No stabilizer vanishing is assumed by the Shapiro bridge itself. -/
theorem extend_morphism (E : Rep.{0} ℚ K)
    (hBB : IsZero (groupCohomology (Rep.res HBB.subtype E) 1))
    (hBG : IsZero (groupCohomology (Rep.res HBG.subtype E) 1))
    (hL : IsZero (groupCohomology (Rep.res HL.subtype E) 2))
    (hP : IsZero (groupCohomology (Rep.res HP.subtype E) 2))
    (f : GoodCyclesRep ⟶ E) :
    ∃ F : OrdinaryCyclesRep ⟶ E, goodCycleInclusion ≫ F = f :=
  RelativeExtObstruction.extend_morphism E (relativeEdges_ext E hBB hBG)
    (relativeVertices_ext E hL hP) f

/-- Literal equivariant linear-map extension from the four actual restricted cohomology groups. -/
theorem extends_linear {E : Type} [AddCommGroup E] [Module ℚ E]
    (ρ : Representation ℚ K E)
    (hBB : IsZero (groupCohomology (Rep.res HBB.subtype (Rep.of ρ)) 1))
    (hBG : IsZero (groupCohomology (Rep.res HBG.subtype (Rep.of ρ)) 1))
    (hL : IsZero (groupCohomology (Rep.res HL.subtype (Rep.of ρ)) 2))
    (hP : IsZero (groupCohomology (Rep.res HP.subtype (Rep.of ρ)) 2))
    (f : GoodChainComplex.Cycles →ₗ[ℚ] E)
    (hf : ∀ g c, f (GoodChainComplex.complex.cyclesAction g c) = ρ g (f c)) :
    ∃ F : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] E,
      (∀ g c, F (OrdinaryIncidenceChains.complex.cyclesAction g c) = ρ g (F c)) ∧
      F.comp OrdinaryIncidenceChains.cycleInclusion = f :=
  RelativeExtObstruction.extends_linear ρ (relativeEdges_ext (Rep.of ρ) hBB hBG)
    (relativeVertices_ext (Rep.of ρ) hL hP) f hf

/-- Actual homogeneous polynomial coefficients, with inverse substitution and determinant
convention inherited unchanged from the coefficient representation. -/
theorem homogeneous_extension (n : ℕ)
    (hBB : IsZero (groupCohomology
      (Rep.res HBB.subtype (RelativeExtObstruction.coefficientRep n)) 1))
    (hBG : IsZero (groupCohomology
      (Rep.res HBG.subtype (RelativeExtObstruction.coefficientRep n)) 1))
    (hL : IsZero (groupCohomology
      (Rep.res HL.subtype (RelativeExtObstruction.coefficientRep n)) 2))
    (hP : IsZero (groupCohomology
      (Rep.res HP.subtype (RelativeExtObstruction.coefficientRep n)) 2))
    (f : GoodChainComplex.PolynomialCycleMap n 0) :
    ∃ F : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] PolynomialGLAction.HomogeneousPoly n,
      (∀ g c, F (OrdinaryIncidenceChains.complex.cyclesAction g c) =
        GoodChainComplex.coefficientAction n 0 g (F c)) ∧
      F.comp OrdinaryIncidenceChains.cycleInclusion = f.map :=
  RelativeExtObstruction.homogeneous_extension n
    (relativeEdges_ext _ hBB hBG) (relativeVertices_ext _ hL hP) f

end TernaryPoly.RelativeShapiro
