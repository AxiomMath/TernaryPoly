module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyBB
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyBG
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyConjugacy
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Shapiro

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeEdgeCohomology
open CategoryTheory CategoryTheory.Limits RelativeOrbitStabilizers RelativeExtObstruction

/-- Actual BB edge-stabilizer cohomology vanishes in every even homogeneous degree. -/
theorem hbb_H1_zero (n : ℕ) (hn : Even n) :
    IsZero (groupCohomology (Rep.res HBB.subtype (coefficientRep n)) 1) :=
  RelativeEdgeCohomologyConjugacy.bb_vanishing_transport n
    (RelativeEdgeCohomologyBB.bb_H1_zero n hn)

/-- Actual BG edge-stabilizer cohomology, including the level-three root, vanishes. -/
theorem hbg_H1_zero (n : ℕ) (hn : Even n) :
    IsZero (groupCohomology (Rep.res HBG.subtype (coefficientRep n)) 1) :=
  RelativeEdgeCohomologyConjugacy.bg_vanishing_transport n
    (RelativeEdgeCohomologyBG.bg_H1_zero n hn)

/-- The actual Ext–Shapiro consumer needs only the two vertex H2 vanishings. -/
theorem homogeneous_extension (n : ℕ) (hn : Even n)
    (hL : IsZero (groupCohomology (Rep.res HL.subtype (coefficientRep n)) 2))
    (hP : IsZero (groupCohomology (Rep.res HP.subtype (coefficientRep n)) 2))
    (f : GoodChainComplex.PolynomialCycleMap n 0) :
    ∃ F : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] PolynomialGLAction.HomogeneousPoly n,
      (∀ g c, F (OrdinaryIncidenceChains.complex.cyclesAction g c) =
        GoodChainComplex.coefficientAction n 0 g (F c)) ∧
      F.comp OrdinaryIncidenceChains.cycleInclusion = f.map :=
  RelativeShapiro.homogeneous_extension n (hbb_H1_zero n hn) (hbg_H1_zero n hn) hL hP f

end TernaryPoly.RelativeEdgeCohomology
