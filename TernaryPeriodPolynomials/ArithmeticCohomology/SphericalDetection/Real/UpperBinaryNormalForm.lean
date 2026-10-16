module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperCuspidalBinarySection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realUpperCuspidalBinarySection_differentiable {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (values : cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1))) (coordinate : Fin 2) :
    Differentiable ℝ (fun parameter => cuspidalTensorHilbertEmbedding cusp basis
      (realUpperCuspidalBinarySection degree cusp values (realRadicalAxis coordinate parameter))) := by
  let : FiniteDimensional ℂ (HomogeneousPoly (degree + 1)) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ (degree + 1))
  let higherBasis := Module.finBasis ℂ (HomogeneousPoly (degree + 1))
  let lifted := cuspidalTensorMap cusp (binaryHomogeneousLift (degree + 1)) values
  let linear := cuspidalTensorHilbertMap cusp higherBasis basis (homogeneousLastDivide degree)
  have regular := realUpperCuspidalBoundary_differentiable (degree + 1) cusp higherBasis lifted coordinate
  have composed := ((linear.restrictScalars ℝ).differentiable.comp regular).neg
  convert composed using 1
  funext parameter
  rw [realUpperCuspidalBinarySection_divided_boundary]
  exact (map_neg (cuspidalTensorHilbertEmbedding cusp basis) _).trans
    (congrArg Neg.neg (cuspidalTensorHilbertMap_embedding cusp higherBasis basis (homogeneousLastDivide degree)
      (oneBoundaryCycle (realUpperCuspidalRep (degree + 1) cusp) lifted (realRadicalAxis coordinate parameter))).symm)

theorem realUpperCuspidalCocycle_exists_binary_normal {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp))
    (regular : ∀ coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (cycle (realRadicalAxis coordinate parameter))) 0) :
    ∃ potential : realUpperCuspidalRep degree cusp,
      cycle = realUpperCuspidalBinarySection degree cusp (realUpperCuspidalBinaryCoordinate degree cusp cycle) +
        oneBoundaryCycle (realUpperCuspidalRep degree cusp) potential := by
  let normalized := realUpperCuspidalBinarySection degree cusp (realUpperCuspidalBinaryCoordinate degree cusp cycle)
  have difference_regular (coordinate : Fin 2) : DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis
        ((cycle - normalized) (realRadicalAxis coordinate parameter))) 0 := by
    have difference := (regular coordinate).sub
      ((realUpperCuspidalBinarySection_differentiable degree cusp basis
        (realUpperCuspidalBinaryCoordinate degree cusp cycle) coordinate) 0)
    convert difference using 1
    funext parameter
    exact map_sub (cuspidalTensorHilbertEmbedding cusp basis) _ _
  have zero : groupCohomology.H1π (realUpperCuspidalRep degree cusp) (cycle - normalized) = 0 := by
    apply (realUpperCuspidalBinaryCoordinate_zero_iff degree cusp basis (cycle - normalized) difference_regular).mp
    rw [map_sub, realUpperCuspidalBinarySection_coordinate, sub_self]
  obtain ⟨potential, equality⟩ := (groupCohomology.H1π_eq_zero_iff (cycle - normalized)).mp zero
  refine ⟨potential, ?_⟩
  apply groupCohomology.cocycles₁_ext
  intro element
  have value := congrFun equality element
  change (realUpperCuspidalRep degree cusp).ρ element potential - potential = cycle element - normalized element at value
  change cycle element = normalized element + ((realUpperCuspidalRep degree cusp).ρ element potential - potential)
  rw [value]
  abel

end TernaryPeriodPolynomials.SphericalDetection.Helpers
