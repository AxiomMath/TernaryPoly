module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneProjectedAlternation
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Two.CocycleExtensionMap
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.RealRadicalH1

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realPlaneLevelRadicalForget (degree : ℕ) (cusp : CuspidalRepresentation) :
    Rep.res SemidirectProduct.inl (realPlaneLevelCuspidalRep degree cusp trivialCharacter) →ₗ[ℂ]
      realUpperCuspidalRep degree cusp :=
  (cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)).subtype

theorem realPlaneLevelRadicalForget_intertwines (degree : ℕ) (cusp : CuspidalRepresentation)
    (radical : RealPlaneRadical)
    (values : Rep.res SemidirectProduct.inl (realPlaneLevelCuspidalRep degree cusp trivialCharacter)) :
    realPlaneLevelRadicalForget degree cusp
      ((Rep.res SemidirectProduct.inl (realPlaneLevelCuspidalRep degree cusp trivialCharacter)).ρ radical values) =
    (realUpperCuspidalRep degree cusp).ρ radical (realPlaneLevelRadicalForget degree cusp values) :=
  realPlaneCuspidalRep_radical degree cusp radical values.val

def realPlaneLevelRadicalCycle (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : groupCohomology.cocycles₂ (realPlaneLevelCuspidalRep degree cusp trivialCharacter)) :
    groupCohomology.cocycles₂ (realUpperCuspidalRep degree cusp) :=
  twoCocycleCoefficientMap _ _ (realPlaneLevelRadicalForget degree cusp) (realPlaneLevelRadicalForget_intertwines degree cusp)
    (twoCocycleRestriction SemidirectProduct.inl _ cycle)

theorem realPlaneLevelRadicalCycle_apply (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : groupCohomology.cocycles₂ (realPlaneLevelCuspidalRep degree cusp trivialCharacter)) (first second : RealPlaneRadical) :
    realPlaneLevelRadicalCycle degree cusp cycle (first, second) =
      (cycle (SemidirectProduct.inl first, SemidirectProduct.inl second)).val := rfl

def realPlaneLevelLatticeForget (degree : ℕ) (cusp : CuspidalRepresentation) :
    Rep.res realPlaneLatticeRadical (realPlaneLevelCuspidalRep degree cusp trivialCharacter) →ₗ[ℂ]
      cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree) :=
  (cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)).subtype

theorem realPlaneLevelLatticeForget_intertwines (degree : ℕ) (cusp : CuspidalRepresentation)
    (radical : RadicalLattice)
    (values : Rep.res realPlaneLatticeRadical (realPlaneLevelCuspidalRep degree cusp trivialCharacter)) :
    realPlaneLevelLatticeForget degree cusp
      ((Rep.res realPlaneLatticeRadical (realPlaneLevelCuspidalRep degree cusp trivialCharacter)).ρ radical values) =
    (cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree)).ρ radical (realPlaneLevelLatticeForget degree cusp values) := by
  apply Subtype.ext
  funext argument
  exact realPlaneCuspidalRep_latticeRadical degree cusp radical values.val argument

def realPlaneLevelLatticeCycle (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : groupCohomology.cocycles₂ (realPlaneLevelCuspidalRep degree cusp trivialCharacter)) :
    groupCohomology.cocycles₂ (cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree)) :=
  twoCocycleCoefficientMap _ _ (realPlaneLevelLatticeForget degree cusp) (realPlaneLevelLatticeForget_intertwines degree cusp)
    (twoCocycleRestriction realPlaneLatticeRadical _ cycle)

theorem realPlaneLevelLatticeCycle_apply (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : groupCohomology.cocycles₂ (realPlaneLevelCuspidalRep degree cusp trivialCharacter)) (first second : RadicalLattice) :
    realPlaneLevelLatticeCycle degree cusp cycle (first, second) =
      (cycle (realPlaneLatticeRadical first, realPlaneLatticeRadical second)).val := rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
