module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.CuspidalValues
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.Smooth

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def sourcePlaneCuspidalFamily {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (base : AdelicGL) (point : Fin 4 → RealGL3) :
    cuspidalTensorValues data.cusp (HomogeneousPoly degree) :=
  sourcePlaneCuspidalValues data source cocycle (fun index => point index.castSucc) (base * atInfinity (point (Fin.last 3)))

theorem sourcePlaneCuspidalFamily_coefficient_lift {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (base : AdelicGL) (monomial : Fin 3 →₀ ℕ) :
    ∃ vectors : (Fin 4 → RealGL3) → data.cusp.smooth,
      Smooth (fun point => (vectors point).val) ∧ ∀ point argument,
        data.cusp.realize (vectors point) argument =
          ternaryPolynomialCoefficient degree monomial ((sourcePlaneCuspidalFamily data source cocycle base point).val argument) := by
  obtain ⟨vectors, smooth, realizes⟩ := cocycle.2.1 monomial base
  refine ⟨vectors, smooth, ?_⟩
  intro point argument
  have equality := realizes point argument
  rw [binaryInductionExponent_plane_endpoint] at equality
  change data.cusp.realize (vectors point) argument =
    (normPower (GeneralLinearGroup.det argument) (-(((degree : ℂ) + 3) / 2)) •
      (source (fun index => point index.castSucc) (planeLevi argument 1 * (base * atInfinity (point (Fin.last 3))))).val).coeff monomial
  rw [coeff_smul, smul_eq_mul]
  exact equality

theorem sourcePlaneCuspidalFamily_functional_lift {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (base : AdelicGL) (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    ∃ vectors : (Fin 4 → RealGL3) → data.cusp.smooth,
      Smooth (fun point => (vectors point).val) ∧ ∀ point argument,
        data.cusp.realize (vectors point) argument = functional ((sourcePlaneCuspidalFamily data source cocycle base point).val argument) := by
  have spanned := ternaryPolynomialDual_mem_span_coefficients functional
  induction spanned using Submodule.span_induction with
  | mem functional membership =>
    obtain ⟨monomial, rfl⟩ := membership
    exact sourcePlaneCuspidalFamily_coefficient_lift data source cocycle base monomial
  | zero =>
    refine ⟨fun _ => 0, contDiffOn_const, ?_⟩
    intro point argument
    exact congrFun (map_zero data.cusp.realize) argument
  | add first second _ _ first_lift second_lift =>
    obtain ⟨first_vectors, first_smooth, first_realizes⟩ := first_lift
    obtain ⟨second_vectors, second_smooth, second_realizes⟩ := second_lift
    refine ⟨fun point => first_vectors point + second_vectors point, first_smooth.add second_smooth, ?_⟩
    intro point argument
    simp only [map_add, Pi.add_apply, first_realizes, second_realizes, LinearMap.add_apply]
  | smul scalar functional _ lift =>
    obtain ⟨vectors, smooth, realizes⟩ := lift
    refine ⟨fun point => scalar • vectors point, smooth.const_smul scalar, ?_⟩
    intro point argument
    simp only [map_smul, Pi.smul_apply, realizes, LinearMap.smul_apply]

/-- Every coefficient of the parabolic source family has the supplied Hilbert smoothness. -/
theorem sourcePlaneCuspidalFunctional_smooth {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (base : AdelicGL) (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    Smooth (fun point : Fin 4 → RealGL3 =>
      (cuspidalTensorFunctional data.cusp functional (sourcePlaneCuspidalFamily data source cocycle base point)).val) := by
  obtain ⟨vectors, smooth, realizes⟩ := sourcePlaneCuspidalFamily_functional_lift data source cocycle base functional
  have equality (point : Fin 4 → RealGL3) :
      cuspidalTensorFunctional data.cusp functional (sourcePlaneCuspidalFamily data source cocycle base point) = vectors point := by
    apply data.cusp.injective
    funext argument
    rw [cuspidalTensorFunctional_realize, realizes]
  simpa only [equality] using smooth

end TernaryPeriodPolynomials.SphericalDetection.Helpers
