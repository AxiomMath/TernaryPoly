module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Vertex.CohomologyAssembly
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyConjugacy

@[expose] public section

open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace TernaryPoly.RelativeVertexCohomology
open RelativeStabilizerParameters RelativeStabilizerConsumer RelativeOrbitStabilizers
open RelativeEdgeCohomologyConjugacy RelativeExtObstruction

/-- The actual plane stabilizer in K has zero second cohomology in every even polynomial degree,
conditional only on genuine arbitrary-coefficient H² vanishing for GL₂(ℤ). -/
theorem actualPlane_H2_zero (n : ℕ) (hn : Even n)
    (hLevi : ∀ A : Rep ℚ GL2, IsZero (groupCohomology A 2)) :
    IsZero (groupCohomology (Rep.res HP.subtype (coefficientRep n)) 2) :=
  (planeMatrix_H2_zero n hn hLevi).of_iso
    (cohomologyConjugacy HPGroup inf_le_left n 2).symm

/-- The actual line stabilizer in K has zero second cohomology, conditional only on genuine
arbitrary-coefficient H² vanishing for its full actual sign × congruence Levi. -/
theorem actualLine_H2_zero (n : ℕ)
    (hLevi : ∀ A : Rep ℚ (ℤˣ × Gamma), IsZero (groupCohomology A 2)) :
    IsZero (groupCohomology (Rep.res HL.subtype (coefficientRep n)) 2) :=
  (lineMatrix_H2_zero n hLevi).of_iso
    (cohomologyConjugacy HLGroup inf_le_left n 2).symm

end TernaryPoly.RelativeVertexCohomology
