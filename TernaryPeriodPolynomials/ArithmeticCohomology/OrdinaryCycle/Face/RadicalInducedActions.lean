module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalFiberMatrices
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalScalingCohomology

@[expose] public section

open CategoryTheory MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open RadicalCoinvariantAlgebra RadicalFirstCohomologyLattice LatticeTopCohomology
open RelativeStabilizerParameters RelativeStabilizerMatrices PolynomialGLAction
open SymmetricLineCohomology OrdinaryBoundaryCommonRoot OrdinaryCovectors ModThreeGoodAction RadicalTopCohomology

/-- The actual induced twenty-six-fiber coefficient action on the plane radical lattice. -/
def inducedPlaneRepresentation (n : ℕ) (e : ℤ) : Representation ℚ Lattice (Coefficients n) :=
  (coefficientAction n e).comp planeHom

/-- The actual induced twenty-six-fiber coefficient action on the line radical lattice. -/
def inducedLineRepresentation (n : ℕ) (e : ℤ) : Representation ℚ Lattice (Coefficients n) :=
  (coefficientAction n e).comp lineHom

abbrev scaledInducedPlaneRep (n : ℕ) (e : ℤ) : Rep ℚ Lattice :=
  Rep.res (scaleLattice 3) (Rep.of (inducedPlaneRepresentation n e))

abbrev scaledInducedLineRep (n : ℕ) (e : ℤ) : Rep ℚ Lattice :=
  Rep.res (scaleLattice 3) (Rep.of (inducedLineRepresentation n e))

/-- Restriction to three times the plane radical is literally componentwise polynomial action. -/
theorem scaledPlaneFiberAction (n : ℕ) (e : ℤ) (g : Lattice) (F : Coefficients n)
    (r : NonzeroCovector) :
    (scaledInducedPlaneRep n e).ρ g F r=(scaledPlaneRep n).ρ g (F r) := by
  change coefficientAction n e (planeHom (scaleLattice 3 g)) F r=_
  rw [coefficientAction_apply,rowMove_of_reduction_one _ (planeHom_scaled_reduction g),
    planeHom_action_twist]
  rfl

/-- Restriction to three times the line radical is literally componentwise polynomial action. -/
theorem scaledLineFiberAction (n : ℕ) (e : ℤ) (g : Lattice) (F : Coefficients n)
    (r : NonzeroCovector) :
    (scaledInducedLineRep n e).ρ g F r=(scaledLineRep n).ρ g (F r) := by
  change coefficientAction n e (lineHom (scaleLattice 3 g)) F r=_
  rw [coefficientAction_apply,rowMove_of_reduction_one _ (lineHom_scaled_reduction g),
    lineHom_action_twist]
  rfl

/-- The actual induced coefficient morphism for inverse plane-Levi conjugation on the scaled radical. -/
def scaledInducedPlaneCoefficientHom (n : ℕ) (e : ℤ) (M : GL2) :
    Rep.res (matrixLattice M⁻¹).toMonoidHom (scaledInducedPlaneRep n e) ⟶ scaledInducedPlaneRep n e :=
  Rep.ofHom ⟨coefficientAction n e (planeElement M 0),by
    intro g
    change coefficientAction n e (planeElement M 0)*
        coefficientAction n e (planeHom (scaleLattice 3 (matrixLattice M⁻¹ g)))=
      coefficientAction n e (planeHom (scaleLattice 3 g))*coefficientAction n e (planeElement M 0)
    rw [scaleLattice_matrix,←map_mul,←map_mul,plane_inverse_commute]⟩

/-- The actual induced coefficient morphism for inverse line-Levi conjugation on the scaled radical. -/
def scaledInducedLineCoefficientHom (n : ℕ) (e : ℤ) (t : ℤˣ) (M : GL2) :
    Rep.res (leviLatticeChange t M) (scaledInducedLineRep n e) ⟶ scaledInducedLineRep n e :=
  Rep.ofHom ⟨coefficientAction n e (lineElement t 0 M),by
    intro g
    change coefficientAction n e (lineElement t 0 M)*
        coefficientAction n e (lineHom (scaleLattice 3 (leviLatticeChange t M g)))=
      coefficientAction n e (lineHom (scaleLattice 3 g))*coefficientAction n e (lineElement t 0 M)
    rw [scaleLattice_lineLevi,←map_mul,←map_mul,leviLatticeChange_commute]⟩

def scaledInducedPlaneH1Action (n : ℕ) (e : ℤ) (M : GL2) :
    groupCohomology (scaledInducedPlaneRep n e) 1 ⟶ groupCohomology (scaledInducedPlaneRep n e) 1 :=
  groupCohomology.map (matrixLattice M⁻¹).toMonoidHom (scaledInducedPlaneCoefficientHom n e M) 1

def scaledInducedLineH1Action (n : ℕ) (e : ℤ) (t : ℤˣ) (M : GL2) :
    groupCohomology (scaledInducedLineRep n e) 1 ⟶ groupCohomology (scaledInducedLineRep n e) 1 :=
  groupCohomology.map (leviLatticeChange t M) (scaledInducedLineCoefficientHom n e t M) 1

/-- Every residue-trivial determinant-one plane Levi commutes with literal fiber evaluation. -/
theorem scaledInducedPlaneCoefficient_fiber (n : ℕ) (e : ℤ) (M : GL2)
    (hr : reduction (planeElement M 0)=1) (hd : (planeElement M 0).val.det=1)
    (r : NonzeroCovector) (F : Coefficients n) :
    scaledInducedPlaneCoefficientHom n e M F r=scaledPlaneCoefficientHom n M (F r) := by
  change coefficientAction n e (planeElement M 0) F r=integralAction n 0 (planeElement M 0) (F r)
  rw [coefficientAction_apply,rowMove_of_reduction_one _ hr,
    integralAction_twist_eq_of_det_one n e 0 _ hd]

/-- Every residue-trivial determinant-one line Levi commutes with literal fiber evaluation. -/
theorem scaledInducedLineCoefficient_fiber (n : ℕ) (e : ℤ) (t : ℤˣ) (M : GL2)
    (hr : reduction (lineElement t 0 M)=1) (hd : (lineElement t 0 M).val.det=1)
    (r : NonzeroCovector) (F : Coefficients n) :
    scaledInducedLineCoefficientHom n e t M F r=scaledLineCoefficientHom n t M (F r) := by
  change coefficientAction n e (lineElement t 0 M) F r=integralAction n (-1) (lineElement t 0 M) (F r)
  rw [coefficientAction_apply,rowMove_of_reduction_one _ hr,
    integralAction_twist_eq_of_det_one n e (-1) _ hd]

end TernaryPoly.OrdinaryFaceRadical
