module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalInducedActions

@[expose] public section


open CategoryTheory
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open RadicalFirstCohomologyLattice LatticeTopCohomology RadicalTopCohomology
open RelativeStabilizerParameters SymmetricLineCohomology OrdinaryBoundaryCommonRoot groupCohomology

/-- Actual inverse plane-Levi conjugation on the full induced radical representation. -/
def inducedPlaneCoefficientHom (n : ℕ) (e : ℤ) (M : GL2) :
    Rep.res (matrixLattice M⁻¹).toMonoidHom (Rep.of (inducedPlaneRepresentation n e)) ⟶
      Rep.of (inducedPlaneRepresentation n e) :=
  Rep.ofHom ⟨coefficientAction n e (planeElement M 0),by
    intro g
    change coefficientAction n e (planeElement M 0)*coefficientAction n e (planeHom (matrixLattice M⁻¹ g))=
      coefficientAction n e (planeHom g)*coefficientAction n e (planeElement M 0)
    rw [←map_mul,←map_mul,plane_inverse_commute]⟩

/-- Actual inverse line-Levi conjugation on the full induced radical representation. -/
def inducedLineCoefficientHom (n : ℕ) (e : ℤ) (t : ℤˣ) (M : GL2) :
    Rep.res (leviLatticeChange t M) (Rep.of (inducedLineRepresentation n e)) ⟶
      Rep.of (inducedLineRepresentation n e) :=
  Rep.ofHom ⟨coefficientAction n e (lineElement t 0 M),by
    intro g
    change coefficientAction n e (lineElement t 0 M)*coefficientAction n e (lineHom (leviLatticeChange t M g))=
      coefficientAction n e (lineHom g)*coefficientAction n e (lineElement t 0 M)
    rw [←map_mul,←map_mul,leviLatticeChange_commute]⟩

def inducedPlaneH1Action (n : ℕ) (e : ℤ) (M : GL2) :
    groupCohomology (Rep.of (inducedPlaneRepresentation n e)) 1 ⟶
      groupCohomology (Rep.of (inducedPlaneRepresentation n e)) 1 :=
  groupCohomology.map (matrixLattice M⁻¹).toMonoidHom (inducedPlaneCoefficientHom n e M) 1

def inducedLineH1Action (n : ℕ) (e : ℤ) (t : ℤˣ) (M : GL2) :
    groupCohomology (Rep.of (inducedLineRepresentation n e)) 1 ⟶
      groupCohomology (Rep.of (inducedLineRepresentation n e)) 1 :=
  groupCohomology.map (leviLatticeChange t M) (inducedLineCoefficientHom n e t M) 1

/-- The literal cohomological restriction to three times the plane radical parameters. -/
def inducedPlaneRestriction (n : ℕ) (e : ℤ) :
    groupCohomology (Rep.of (inducedPlaneRepresentation n e)) 1 ⟶
      groupCohomology (scaledInducedPlaneRep n e) 1 :=
  groupCohomology.map (scaleLattice 3) (𝟙 (scaledInducedPlaneRep n e)) 1

/-- The literal cohomological restriction to three times the line radical parameters. -/
def inducedLineRestriction (n : ℕ) (e : ℤ) :
    groupCohomology (Rep.of (inducedLineRepresentation n e)) 1 ⟶
      groupCohomology (scaledInducedLineRep n e) 1 :=
  groupCohomology.map (scaleLattice 3) (𝟙 (scaledInducedLineRep n e)) 1

theorem inducedPlaneRestriction_natural (n : ℕ) (e : ℤ) (M : GL2)
    (x : groupCohomology (Rep.of (inducedPlaneRepresentation n e)) 1) :
    inducedPlaneRestriction n e (inducedPlaneH1Action n e M x)=
      scaledInducedPlaneH1Action n e M (inducedPlaneRestriction n e x) := by
  refine H1_induction_on x ?_
  intro c
  simp only [inducedPlaneRestriction,inducedPlaneH1Action,scaledInducedPlaneH1Action,H1π_comp_map_apply]
  apply congrArg (H1π (scaledInducedPlaneRep n e))
  apply cocycles₁_ext
  intro g
  change coefficientAction n e (planeElement M 0) (c (matrixLattice M⁻¹ (scaleLattice 3 g)))=
    coefficientAction n e (planeElement M 0) (c (scaleLattice 3 (matrixLattice M⁻¹ g)))
  rw [scaleLattice_matrix]

theorem inducedLineRestriction_natural (n : ℕ) (e : ℤ) (t : ℤˣ) (M : GL2)
    (x : groupCohomology (Rep.of (inducedLineRepresentation n e)) 1) :
    inducedLineRestriction n e (inducedLineH1Action n e t M x)=
      scaledInducedLineH1Action n e t M (inducedLineRestriction n e x) := by
  refine H1_induction_on x ?_
  intro c
  simp only [inducedLineRestriction,inducedLineH1Action,scaledInducedLineH1Action,H1π_comp_map_apply]
  apply congrArg (H1π (scaledInducedLineRep n e))
  apply cocycles₁_ext
  intro g
  change coefficientAction n e (lineElement t 0 M) (c (leviLatticeChange t M (scaleLattice 3 g)))=
    coefficientAction n e (lineElement t 0 M) (c (scaleLattice 3 (leviLatticeChange t M g)))
  rw [scaleLattice_lineLevi]

end TernaryPoly.OrdinaryFaceRadical
