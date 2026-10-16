module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.LatticeH1
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneArithmeticEvaluation
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.UpperRadicalEdgeFormula

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix CategoryTheory MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realPlaneLatticeRadical : RadicalLattice →* RealPlaneGroup :=
  SemidirectProduct.inl.comp radicalLatticeReal

theorem realPlaneCuspidalRep_latticeRadical (degree : ℕ) (cusp : CuspidalRepresentation)
    (element : RadicalLattice) (values : cuspidalTensorValues cusp (HomogeneousPoly degree)) (argument : BinaryAdelicGL) :
    ((realPlaneCuspidalRep degree cusp trivialCharacter).ρ (realPlaneLatticeRadical element) values).val argument =
      (upperRadicalLatticeRep degree).ρ element (values.val argument) := by
  change ((realPlaneCuspidalRep degree cusp trivialCharacter).ρ
    (SemidirectProduct.inl (radicalLatticeReal element)) values).val argument = _
  rw [← identityPlaneRealGroup_radical, realPlaneCuspidalRep_apply,
    identityPlaneRealGroup_matrix, identityPlaneRealGroup_right, identityPlaneLeviProjection_radical,
    map_one, atInfinity_one, map_one, normPower_one, one_smul, mul_one]
  rfl

def realPlaneRadicalCoefficientIso (degree : ℕ) (cusp : CuspidalRepresentation) :
    Rep.res realPlaneLatticeRadical (realPlaneCuspidalRep degree cusp trivialCharacter) ≅
      cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree) :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ (cuspidalTensorValues cusp (HomogeneousPoly degree))) (by
    intro element
    apply LinearMap.ext
    intro values
    apply Subtype.ext
    funext argument
    exact realPlaneCuspidalRep_latticeRadical degree cusp element values argument))

def realPlaneRadicalH1Iso (degree : ℕ) (cusp : CuspidalRepresentation) :
    groupCohomology.H1 (Rep.res realPlaneLatticeRadical (realPlaneCuspidalRep degree cusp trivialCharacter)) ≅
      groupCohomology.H1 (cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree)) :=
  (groupCohomology.functor ℂ RadicalLattice 1).mapIso (realPlaneRadicalCoefficientIso degree cusp)

def realPlaneRadicalBinaryCoordinate (degree : ℕ) (cusp : CuspidalRepresentation) :
    groupCohomology.H1 (Rep.res realPlaneLatticeRadical (realPlaneCuspidalRep degree cusp trivialCharacter)) ≃ₗ[ℂ]
      cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1)) := by
  let equivalence := realPlaneRadicalH1Iso degree cusp
  let linear : groupCohomology.H1 (Rep.res realPlaneLatticeRadical (realPlaneCuspidalRep degree cusp trivialCharacter)) ≃ₗ[ℂ]
      groupCohomology.H1 (cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree)) :=
    { equivalence.hom.hom with
      invFun := equivalence.inv
      left_inv := by intro vector; exact ConcreteCategory.congr_hom equivalence.hom_inv_id vector
      right_inv := by intro vector; exact ConcreteCategory.congr_hom equivalence.inv_hom_id vector }
  exact linear.trans (upperRadicalCuspidalH1 degree cusp)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
