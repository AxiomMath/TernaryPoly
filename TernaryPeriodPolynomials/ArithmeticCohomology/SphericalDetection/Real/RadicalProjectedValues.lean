module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.HilbertFunctionals
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperRadicalBinary

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryHomogeneousRestrict_realUpper (degree : ℕ) (element : RealPlaneRadical)
    (polynomial : HomogeneousPoly degree) :
    binaryHomogeneousRestrict degree ((realUpperRadicalRep degree).ρ element polynomial) =
      binaryHomogeneousRestrict degree polynomial := by
  change binaryHomogeneousRestrict degree (realCoefficientComponent degree trivialCharacter
    (planeUnipotent (element.toAdd 0) (element.toAdd 1)) polynomial) = _
  rw [realCoefficientComponent_trivial, map_planeUnipotent]
  apply Subtype.ext
  exact binaryPolynomialRestrict_planeUnipotent _ _ polynomial.val

theorem realUpperProjectedFunctional_invariant (degree : ℕ) (cusp : CuspidalRepresentation)
    (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ) (element : RealPlaneRadical)
    (values : realUpperCuspidalRep degree cusp) :
    cuspidalTensorFunctional cusp (functional.comp (binaryHomogeneousRestrict degree))
        ((realUpperCuspidalRep degree cusp).ρ element values) =
      cuspidalTensorFunctional cusp (functional.comp (binaryHomogeneousRestrict degree)) values := by
  apply cusp.injective
  funext argument
  calc
    _ = functional (binaryHomogeneousRestrict degree
        ((realUpperRadicalRep degree).ρ element (values.val argument))) :=
      cuspidalTensorFunctional_realize cusp (functional.comp (binaryHomogeneousRestrict degree))
        (cuspidalTensorMap (V := HomogeneousPoly degree) (W := HomogeneousPoly degree) cusp
          ((realUpperRadicalRep degree).ρ element) values) argument
    _ = functional (binaryHomogeneousRestrict degree (values.val argument)) :=
      congrArg functional (binaryHomogeneousRestrict_realUpper degree element (values.val argument))
    _ = _ := (cuspidalTensorFunctional_realize cusp (functional.comp (binaryHomogeneousRestrict degree)) values argument).symm

theorem realUpperProjectedFunctional_mul (degree : ℕ) (cusp : CuspidalRepresentation)
    (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ)
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp)) (first second : RealPlaneRadical) :
    cuspidalTensorFunctional cusp (functional.comp (binaryHomogeneousRestrict degree)) (cycle (first * second)) =
      cuspidalTensorFunctional cusp (functional.comp (binaryHomogeneousRestrict degree)) (cycle first) +
        cuspidalTensorFunctional cusp (functional.comp (binaryHomogeneousRestrict degree)) (cycle second) := by
  let linear : realUpperCuspidalRep degree cusp →ₗ[ℂ] cusp.smooth :=
    cuspidalTensorFunctional cusp (functional.comp (binaryHomogeneousRestrict degree))
  calc
    _ = linear ((realUpperCuspidalRep degree cusp).ρ first (cycle second) + cycle first) :=
      congrArg linear (oneCocycle_mul _ cycle first second)
    _ = linear ((realUpperCuspidalRep degree cusp).ρ first (cycle second)) + linear (cycle first) := map_add linear _ _
    _ = linear (cycle second) + linear (cycle first) :=
      congrArg (fun vector => vector + linear (cycle first))
        (realUpperProjectedFunctional_invariant degree cusp functional first (cycle second))
    _ = _ := add_comm _ _

theorem realUpperProjectedFunctional_axis {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ)
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp)) (coordinate : Fin 2)
    (regular : DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (cycle (realRadicalAxis coordinate parameter))) 0)
    (parameter : ℝ) :
    cuspidalTensorFunctional cusp (functional.comp (binaryHomogeneousRestrict degree)) (cycle (realRadicalAxis coordinate parameter)) =
      (parameter : ℂ) • cuspidalTensorFunctional cusp (functional.comp (binaryHomogeneousRestrict degree))
        (cycle (realRadicalAxis coordinate 1)) := by
  let values (sample : ℝ) :=
    cuspidalTensorFunctional cusp (functional.comp (binaryHomogeneousRestrict degree)) (cycle (realRadicalAxis coordinate sample))
  have additive (first second : ℝ) : (values (first + second)).val = (values first).val + (values second).val := by
    dsimp only [values]
    rw [realRadicalAxis_add, realUpperProjectedFunctional_mul]
    rfl
  have differentiable : DifferentiableAt ℝ (fun sample => (values sample).val) 0 :=
    cuspidalTensorFunctional_differentiableAt cusp basis (functional.comp (binaryHomogeneousRestrict degree))
      (fun sample => cycle (realRadicalAxis coordinate sample)) 0 regular
  apply Subtype.ext
  exact (differentiableAdditive_eq_smul (fun sample => (values sample).val) additive differentiable parameter).trans
    (IsScalarTower.algebraMap_smul ℂ parameter (values 1).val).symm

theorem realUpperProjectedFunctional_value {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ)
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp))
    (regular : ∀ coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (cycle (realRadicalAxis coordinate parameter))) 0)
    (element : RealPlaneRadical) :
    cuspidalTensorFunctional cusp (functional.comp (binaryHomogeneousRestrict degree)) (cycle element) =
      (element.toAdd 0 : ℂ) • cuspidalTensorFunctional cusp (functional.comp (binaryHomogeneousRestrict degree))
        (cycle (realRadicalAxis 0 1)) +
      (element.toAdd 1 : ℂ) • cuspidalTensorFunctional cusp (functional.comp (binaryHomogeneousRestrict degree))
        (cycle (realRadicalAxis 1 1)) := by
  have equality := realUpperProjectedFunctional_mul degree cusp functional cycle
    (realRadicalAxis 0 (element.toAdd 0)) (realRadicalAxis 1 (element.toAdd 1))
  rw [realRadicalAxis_product, realUpperProjectedFunctional_axis degree cusp basis functional cycle 0 (regular 0),
    realUpperProjectedFunctional_axis degree cusp basis functional cycle 1 (regular 1)] at equality
  exact equality

theorem realUpperProjectedCocycle_value {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp))
    (regular : ∀ coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (cycle (realRadicalAxis coordinate parameter))) 0)
    (element : RealPlaneRadical) (argument : BinaryAdelicGL) :
    binaryHomogeneousRestrict degree ((cycle element).val argument) =
      (element.toAdd 0 : ℂ) • binaryHomogeneousRestrict degree ((cycle (realRadicalAxis 0 1)).val argument) +
      (element.toAdd 1 : ℂ) • binaryHomogeneousRestrict degree ((cycle (realRadicalAxis 1 1)).val argument) := by
  apply (Module.Free.chooseBasis ℂ (Binary.HomogeneousPoly degree)).eval_injective
  apply LinearMap.ext
  intro functional
  change functional (binaryHomogeneousRestrict degree ((cycle element).val argument)) =
    functional ((element.toAdd 0 : ℂ) • binaryHomogeneousRestrict degree ((cycle (realRadicalAxis 0 1)).val argument) +
      (element.toAdd 1 : ℂ) • binaryHomogeneousRestrict degree ((cycle (realRadicalAxis 1 1)).val argument))
  have equality := congrArg (fun vector => cusp.realize vector argument)
    (realUpperProjectedFunctional_value degree cusp basis functional cycle regular element)
  have realize (input : RealPlaneRadical) :
      cusp.realize (cuspidalTensorFunctional cusp (functional.comp (binaryHomogeneousRestrict degree)) (cycle input)) argument =
        functional (binaryHomogeneousRestrict degree ((cycle input).val argument)) :=
    cuspidalTensorFunctional_realize cusp (functional.comp (binaryHomogeneousRestrict degree)) (cycle input) argument
  simpa only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, realize] using equality

end TernaryPeriodPolynomials.SphericalDetection.Helpers
