module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Vertex.CohomologyCrossSign
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Vertex.CohomologyRadicalFixed
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.LowDegree.Vanishing

@[expose] public section


open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace TernaryPoly.RelativeVertexCohomology
open RelativeStabilizerParameters RelativeStabilizerConsumer RadicalFirstCohomologyLattice
open LowDegreeHochschildSerre

/-- The only premise concerns actual rational cohomology of the actual plane Levi. -/
theorem planePolynomial_H2_zero (n : ℕ) (hn : Even n)
    (hLevi : ∀ A : Rep ℚ GL2, IsZero (groupCohomology A 2)) :
    IsZero (groupCohomology (planePolynomial n) 2) :=
  LowDegreeHochschildSerre.isZero_H2 planeAction (planePolynomial n)
    (hLevi _) (planeCross_H1_zero n hn) (planeRadical_fixed_zero n)

/-- The line statement uses its full actual Levi, not just its diagonal subgroup. -/
theorem linePolynomial_H2_zero (n : ℕ)
    (hLevi : ∀ A : Rep ℚ (ℤˣ × Gamma), IsZero (groupCohomology A 2)) :
    IsZero (groupCohomology (linePolynomial n) 2) :=
  LowDegreeHochschildSerre.isZero_H2 lineAction (linePolynomial n)
    (hLevi _) (lineCross_H1_zero n) (lineRadical_fixed_zero n)

abbrev planeMatrixPolynomial (n : ℕ) : Rep ℚ HPGroup :=
  Rep.of ((PolynomialGLAction.integralAction n 0).comp HPGroup.subtype)
abbrev lineMatrixPolynomial (n : ℕ) : Rep ℚ HLGroup :=
  Rep.of ((PolynomialGLAction.integralAction n 0).comp HLGroup.subtype)

/-- The proved literal matrix isomorphism preserves the actual polynomial action. -/
def planePolynomialIso (n k : ℕ) : groupCohomology (planePolynomial n) k ≅
    groupCohomology (planeMatrixPolynomial n) k :=
  groupCohomology.mapIso planeEquiv
    (LinearEquiv.refl ℚ (PolynomialGLAction.HomogeneousPoly n)) (fun _ => rfl) k

def linePolynomialIso (n k : ℕ) : groupCohomology (linePolynomial n) k ≅
    groupCohomology (lineMatrixPolynomial n) k :=
  groupCohomology.mapIso lineEquiv
    (LinearEquiv.refl ℚ (PolynomialGLAction.HomogeneousPoly n)) (fun _ => rfl) k

theorem planeMatrix_H2_zero (n : ℕ) (hn : Even n)
    (hLevi : ∀ A : Rep ℚ GL2, IsZero (groupCohomology A 2)) :
    IsZero (groupCohomology (planeMatrixPolynomial n) 2) :=
  (planePolynomial_H2_zero n hn hLevi).of_iso (planePolynomialIso n 2).symm

theorem lineMatrix_H2_zero (n : ℕ)
    (hLevi : ∀ A : Rep ℚ (ℤˣ × Gamma), IsZero (groupCohomology A 2)) :
    IsZero (groupCohomology (lineMatrixPolynomial n) 2) :=
  (linePolynomial_H2_zero n hLevi).of_iso (linePolynomialIso n 2).symm

end TernaryPoly.RelativeVertexCohomology
