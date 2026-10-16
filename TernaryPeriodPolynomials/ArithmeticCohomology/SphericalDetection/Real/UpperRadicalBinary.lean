module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.RealRadicalH1
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.UpperRadicalEdgeFormula
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.CuspidalSmooth

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial CategoryTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realUpperCuspidalBinaryCoordinate (degree : ℕ) (cusp : CuspidalRepresentation) :
    groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp) →ₗ[ℂ]
      cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1)) :=
  (upperRadicalCuspidalH1 degree cusp).toLinearMap.comp
    ((groupCohomology.H1π (cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree))).hom.comp
      (realUpperCuspidalCocycleLattice degree cusp))

theorem realUpperCuspidalBinaryCoordinate_zero_iff {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp))
    (regular : ∀ coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (cycle (realRadicalAxis coordinate parameter))) 0) :
    realUpperCuspidalBinaryCoordinate degree cusp cycle = 0 ↔
      groupCohomology.H1π (realUpperCuspidalRep degree cusp) cycle = 0 := by
  change upperRadicalCuspidalH1 degree cusp
    (groupCohomology.H1π (cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree))
      (realUpperCuspidalCocycleLattice degree cusp cycle)) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  exact (realUpperCuspidalH1_zero_iff_lattice degree cusp basis cycle regular).symm

theorem realUpperCuspidalBinaryCoordinate_apply (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp)) (argument : BinaryAdelicGL) :
    (realUpperCuspidalBinaryCoordinate degree cusp cycle).val argument =
      upperRadicalCocycleCoordinate degree (cuspidalTensorCocycleEvaluation cusp (upperRadicalLatticeRep degree) argument
        (realUpperCuspidalCocycleLattice degree cusp cycle)) :=
  upperRadicalCuspidalH1_apply degree cusp (realUpperCuspidalCocycleLattice degree cusp cycle) argument

theorem realUpperCuspidalBinaryCoordinate_value (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp)) (argument : BinaryAdelicGL) :
    ((realUpperCuspidalBinaryCoordinate degree cusp cycle).val argument).val = (degree + 1 : ℂ)⁻¹ •
      (X 0 * binaryPolynomialRestrict ((cycle (realRadicalAxis 0 1)).val argument).val +
        X 1 * binaryPolynomialRestrict ((cycle (realRadicalAxis 1 1)).val argument).val) := by
  rw [realUpperCuspidalBinaryCoordinate_apply, upperRadicalCocycleCoordinate_value,
    realRadicalAxis_one, realRadicalAxis_one]
  rfl

def realPlaneRadicalCuspidalIso (degree : ℕ) (cusp : CuspidalRepresentation) :
    Rep.res SemidirectProduct.inl (realPlaneCuspidalRep degree cusp trivialCharacter) ≅
      realUpperCuspidalRep degree cusp :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ (cuspidalTensorValues cusp (HomogeneousPoly degree))) (by
    intro element
    apply LinearMap.ext
    intro values
    exact realPlaneCuspidalRep_radical degree cusp element values))

theorem sourcePlaneCuspidalFamily_hilbertSmooth {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source) (base : AdelicGL) :
    Smooth (fun point : Fin 4 → RealGL3 =>
      cuspidalTensorHilbertEmbedding data.cusp basis (sourcePlaneCuspidalFamily data source cocycle base point)) := by
  apply contDiffOn_pi.mpr
  intro position
  exact sourcePlaneCuspidalFunctional_smooth data source cocycle base (basis.coord position)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
