module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalInducedRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Parabolic.Groups
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.LowDegree.Actions

@[expose] public section


open CategoryTheory Matrix
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open RadicalFirstCohomologyLattice LatticeTopCohomology RadicalTopCohomology
open RelativeStabilizerParameters RelativeStabilizerMatrices SymmetricLineCohomology
open OrdinaryBoundaryCommonRoot groupCohomology LowDegreeHochschildSerre RadicalCoinvariantAlgebra

abbrev actualPlaneRadicalRep (n : ℕ) (e : ℤ) : Rep ℚ planeRadical :=
  radicalRep OrdinaryParabolicGroups.planeAction (Rep.of (OrdinaryParabolicGroups.planeCoefficients n e))

abbrev actualLineRadicalRep (n : ℕ) (e : ℤ) : Rep ℚ lineRadical :=
  radicalRep OrdinaryParabolicGroups.lineAction (Rep.of (OrdinaryParabolicGroups.lineCoefficients n e))

/-- Actual coefficient-preserving parameterization of the full parabolic's plane radical H¹. -/
def inducedPlaneParameterIso (n : ℕ) (e : ℤ) :
    groupCohomology (Rep.of (inducedPlaneRepresentation n e)) 1 ≅
      groupCohomology (actualPlaneRadicalRep n e) 1 :=
  groupCohomology.mapIso planeParamEquiv (LinearEquiv.refl ℚ (Coefficients n)) (by
    intro g
    change inducedPlaneRepresentation n e g=
      OrdinaryParabolicGroups.planeCoefficients n e (SemidirectProduct.inl (planeParamEquiv g))
    rw [OrdinaryParabolicGroups.planeCoefficients_inl]
    rfl) 1

/-- Actual coefficient-preserving parameterization of the full parabolic's line radical H¹. -/
def inducedLineParameterIso (n : ℕ) (e : ℤ) :
    groupCohomology (Rep.of (inducedLineRepresentation n e)) 1 ≅
      groupCohomology (actualLineRadicalRep n e) 1 :=
  groupCohomology.mapIso lineParamEquiv (LinearEquiv.refl ℚ (Coefficients n)) (by
    intro g
    change inducedLineRepresentation n e g=
      OrdinaryParabolicGroups.lineCoefficients n e (SemidirectProduct.inl (lineParamEquiv g))
    rw [OrdinaryParabolicGroups.lineCoefficients_inl]
    rfl) 1

/-- The full plane Levi with last unit one is exactly the original displayed block matrix. -/
theorem full_planeLevi_unit (M : GL2) :
    OrdinaryParabolicGroups.planeLevi (M,1)=planeElement M 0 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [OrdinaryParabolicGroups.planeLevi,OrdinaryParabolicGroups.planeElement_val,
      OrdinaryParabolicGroups.planeMatrix,planeElement_val,planeMatrix]

theorem planeAction_parameter (M : GL2) (g : Lattice) :
    OrdinaryParabolicGroups.planeAction (M,1)⁻¹ (planeParamEquiv g)=
      planeParamEquiv (matrixLattice M⁻¹ g) := by
  apply Subtype.ext
  rw [OrdinaryParabolicGroups.planeAction_val]
  change OrdinaryParabolicGroups.planeLevi (M⁻¹,1)*planeHom g*
    (OrdinaryParabolicGroups.planeLevi (M⁻¹,1))⁻¹=planeHom (matrixLattice M⁻¹ g)
  rw [full_planeLevi_unit,planeLevi_inv,inv_inv]
  have h := congrArg (fun z => (planeElement M 0)⁻¹*z) (plane_inverse_commute M g)
  simp only [←mul_assoc,inv_mul_cancel,one_mul] at h
  rw [planeLevi_inv] at h
  exact h.symm

theorem lineAction_parameter (M : GL2) (g : Lattice) :
    OrdinaryParabolicGroups.lineAction (1,M)⁻¹ (lineParamEquiv g)=
      lineParamEquiv (leviLatticeChange 1 M g) := by
  apply Subtype.ext
  rw [OrdinaryParabolicGroups.lineAction_val]
  change lineElement 1 0 M⁻¹*lineHom g*(lineElement 1 0 M⁻¹)⁻¹=
    lineHom (leviLatticeChange 1 M g)
  simpa [lineLevi_inv] using (leviLatticeChange_conjugation 1 M g).symm

/-- The actual full-parabolic H¹ action agrees with the displayed plane-lattice action. -/
theorem inducedPlaneParameterIso_natural (n : ℕ) (e : ℤ) (M : GL2)
    (x : groupCohomology (actualPlaneRadicalRep n e) 1) :
    (inducedPlaneParameterIso n e).inv
      ((cohomologyRep OrdinaryParabolicGroups.planeAction
        (Rep.of (OrdinaryParabolicGroups.planeCoefficients n e)) 1).ρ (M,1) x)=
      inducedPlaneH1Action n e M ((inducedPlaneParameterIso n e).inv x) := by
  refine H1_induction_on x ?_
  intro c
  change (inducedPlaneParameterIso n e).inv
      (groupCohomology.map (OrdinaryParabolicGroups.planeAction (M,1)⁻¹).toMonoidHom
        (coefficientHom OrdinaryParabolicGroups.planeAction
          (Rep.of (OrdinaryParabolicGroups.planeCoefficients n e)) (M,1)) 1
        (H1π (actualPlaneRadicalRep n e) c))=_
  simp only [inducedPlaneParameterIso,groupCohomology.mapIso,
    inducedPlaneH1Action,H1π_comp_map_apply]
  apply congrArg (H1π (Rep.of (inducedPlaneRepresentation n e)))
  apply cocycles₁_ext
  intro g
  change OrdinaryParabolicGroups.planeCoefficients n e (SemidirectProduct.inr (M,1))
      (c (OrdinaryParabolicGroups.planeAction (M,1)⁻¹ (planeParamEquiv g)))=
    coefficientAction n e (planeElement M 0) (c (planeParamEquiv (matrixLattice M⁻¹ g)))
  rw [OrdinaryParabolicGroups.planeCoefficients_inr,full_planeLevi_unit,planeAction_parameter]

/-- The actual full-parabolic H¹ action agrees with the displayed line-lattice action. -/
theorem inducedLineParameterIso_natural (n : ℕ) (e : ℤ) (M : GL2)
    (x : groupCohomology (actualLineRadicalRep n e) 1) :
    (inducedLineParameterIso n e).inv
      ((cohomologyRep OrdinaryParabolicGroups.lineAction
        (Rep.of (OrdinaryParabolicGroups.lineCoefficients n e)) 1).ρ (1,M) x)=
      inducedLineH1Action n e 1 M ((inducedLineParameterIso n e).inv x) := by
  refine H1_induction_on x ?_
  intro c
  change (inducedLineParameterIso n e).inv
      (groupCohomology.map (OrdinaryParabolicGroups.lineAction (1,M)⁻¹).toMonoidHom
        (coefficientHom OrdinaryParabolicGroups.lineAction
          (Rep.of (OrdinaryParabolicGroups.lineCoefficients n e)) (1,M)) 1
        (H1π (actualLineRadicalRep n e) c))=_
  simp only [inducedLineParameterIso,groupCohomology.mapIso,
    inducedLineH1Action,H1π_comp_map_apply]
  apply congrArg (H1π (Rep.of (inducedLineRepresentation n e)))
  apply cocycles₁_ext
  intro g
  change OrdinaryParabolicGroups.lineCoefficients n e (SemidirectProduct.inr (1,M))
      (c (OrdinaryParabolicGroups.lineAction (1,M)⁻¹ (lineParamEquiv g)))=
    coefficientAction n e (lineElement 1 0 M) (c (lineParamEquiv (leviLatticeChange 1 M g)))
  rw [OrdinaryParabolicGroups.lineCoefficients_inr,lineAction_parameter]
  rfl

end TernaryPoly.OrdinaryFaceRadical
