module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SmoothCoordinates
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binarySmoothFunctional_lift {degree matrixSize arity : ℕ}
    (cusp : CuspidalRepresentation)
    (values : (Fin arity → GeneralLinearGroup (Fin matrixSize) ℝ) →
      binaryCuspidalValues cusp degree)
    (coefficient_lifts : ∀ monomial : Fin 2 →₀ ℕ,
      ∃ vectors : (Fin arity → GeneralLinearGroup (Fin matrixSize) ℝ) → cusp.smooth,
        Smooth (fun point => (vectors point).val) ∧ ∀ point argument,
          cusp.realize (vectors point) argument = ((values point).val argument).val.coeff monomial)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) :
    ∃ vectors : (Fin arity → GeneralLinearGroup (Fin matrixSize) ℝ) → cusp.smooth,
      Smooth (fun point => (vectors point).val) ∧ ∀ point argument,
        cusp.realize (vectors point) argument = functional ((values point).val argument) := by
  have spanned := binaryPolynomialDual_mem_span_coefficients functional
  induction spanned using Submodule.span_induction with
  | mem functional membership =>
    rcases membership with ⟨monomial, rfl⟩
    exact coefficient_lifts monomial
  | zero =>
    refine ⟨fun _ => 0, ?_, ?_⟩
    · exact contDiffOn_const
    · intro point argument
      exact congrFun (map_zero cusp.realize) argument
  | add first second _ _ first_lift second_lift =>
    rcases first_lift with ⟨first_vectors, first_smooth, first_realizes⟩
    rcases second_lift with ⟨second_vectors, second_smooth, second_realizes⟩
    refine ⟨fun point => first_vectors point + second_vectors point,
      first_smooth.add second_smooth, ?_⟩
    intro point argument
    simp only [map_add, Pi.add_apply, first_realizes, second_realizes,
      LinearMap.add_apply]
  | smul scalar functional _ lift =>
    rcases lift with ⟨vectors, smooth, realizes⟩
    refine ⟨fun point => scalar • vectors point, smooth.const_smul scalar, ?_⟩
    intro point argument
    simp only [map_smul, Pi.smul_apply, realizes, LinearMap.smul_apply]

theorem binarySmoothCoordinate_smooth {degree matrixSize arity : ℕ}
    (cusp : CuspidalRepresentation)
    (values : (Fin arity → GeneralLinearGroup (Fin matrixSize) ℝ) →
      binaryCuspidalValues cusp degree)
    (coefficient_lifts : ∀ monomial : Fin 2 →₀ ℕ,
      ∃ vectors : (Fin arity → GeneralLinearGroup (Fin matrixSize) ℝ) → cusp.smooth,
        Smooth (fun point => (vectors point).val) ∧ ∀ point argument,
          cusp.realize (vectors point) argument = ((values point).val argument).val.coeff monomial)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) :
    Smooth (fun point => (binarySmoothCoordinate cusp functional (values point)).val) := by
  obtain ⟨vectors, smooth, realizes⟩ :=
    binarySmoothFunctional_lift cusp values coefficient_lifts functional
  have same (point) : binarySmoothCoordinate cusp functional (values point) = vectors point := by
    apply cusp.injective
    funext argument
    rw [binarySmoothCoordinate_realize, realizes]
  simpa only [same] using smooth

theorem binarySmoothCoordinates_smooth {degree matrixSize arity : ℕ}
    {index : Type} [Fintype index]
    (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (values : (Fin arity → GeneralLinearGroup (Fin matrixSize) ℝ) →
      binaryCuspidalValues cusp degree)
    (coefficient_lifts : ∀ monomial : Fin 2 →₀ ℕ,
      ∃ vectors : (Fin arity → GeneralLinearGroup (Fin matrixSize) ℝ) → cusp.smooth,
        Smooth (fun point => (vectors point).val) ∧ ∀ point argument,
          cusp.realize (vectors point) argument = ((values point).val argument).val.coeff monomial) :
    Smooth (fun point position =>
      (binarySmoothCoordinates cusp basis (values point) position).val) := by
  apply contDiffOn_pi.mpr
  intro position
  exact binarySmoothCoordinate_smooth cusp values coefficient_lifts (basis.coord position)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
