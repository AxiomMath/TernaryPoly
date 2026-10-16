module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.HilbertCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AdditiveCocycleDifferentiation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {V : Type} [AddCommGroup V] [Module ℂ V] {index : Type} [Fintype index]

theorem cuspidalTensorFunctional_expansion (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (functional : V →ₗ[ℂ] ℂ) (values : cuspidalTensorValues cusp V) :
    cuspidalTensorFunctional cusp functional values =
      ∑ position, functional (basis position) • cuspidalTensorFunctional cusp (basis.coord position) values := by
  classical
  apply cusp.injective
  funext argument
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, cuspidalTensorFunctional_realize]
  have expansion := congrArg functional (basis.sum_repr (values.val argument))
  simpa only [map_sum, map_smul, Module.Basis.coord_apply, smul_eq_mul, mul_comm] using expansion.symm

def basisHilbertFunctional (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (functional : V →ₗ[ℂ] ℂ) : (index → cusp.H) →L[ℂ] cusp.H :=
  ∑ position, functional (basis position) • (ContinuousLinearMap.proj position : (index → cusp.H) →L[ℂ] cusp.H)

theorem basisHilbertFunctional_embedding (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (functional : V →ₗ[ℂ] ℂ) (values : cuspidalTensorValues cusp V) :
    basisHilbertFunctional cusp basis functional (cuspidalTensorHilbertEmbedding cusp basis values) =
      (cuspidalTensorFunctional cusp functional values).val := by
  have expansion := congrArg Subtype.val (cuspidalTensorFunctional_expansion cusp basis functional values)
  simpa only [basisHilbertFunctional, sum_apply, smul_apply, ContinuousLinearMap.proj_apply,
    cuspidalTensorHilbertEmbedding, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    Submodule.coe_sum, Submodule.coe_smul] using expansion.symm

theorem cuspidalTensorFunctional_differentiableAt (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (functional : V →ₗ[ℂ] ℂ) (values : ℝ → cuspidalTensorValues cusp V) (point : ℝ)
    (regular : DifferentiableAt ℝ (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (values parameter)) point) :
    DifferentiableAt ℝ (fun parameter => (cuspidalTensorFunctional cusp functional (values parameter)).val) point := by
  have composite := ((basisHilbertFunctional cusp basis functional).restrictScalars ℝ).differentiableAt.comp point regular
  change DifferentiableAt ℝ (fun parameter => basisHilbertFunctional cusp basis functional
    (cuspidalTensorHilbertEmbedding cusp basis (values parameter))) point at composite
  simpa only [basisHilbertFunctional_embedding] using composite

theorem differentiableAdditive_eq_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : ℝ → E) (additive : ∀ first second, function (first + second) = function first + function second)
    (regular : DifferentiableAt ℝ function 0) (parameter : ℝ) : function parameter = parameter • function 1 := by
  have origin : function 0 = 0 := by
    have equality := additive 0 0
    rw [zero_add] at equality
    exact add_eq_left.mp equality.symm
  have cocycle (first second : ℝ) :
      function (first + second) = (ContinuousLinearMap.id ℝ E) (function second) + function first := by
    rw [additive]
    exact add_comm _ _
  have formula := additiveCocycle_eq_finitePrimitive (fun _ => ContinuousLinearMap.id ℝ E) function cocycle origin
    (deriv function 0) regular.hasDerivAt (fun _ => deriv function 0) 1 (by
      intro sample
      simp [finiteExponentialVector])
  have value : ∀ sample, function sample = sample • deriv function 0 := by
    intro sample
    have equality := congrFun formula sample
    simpa only [finiteExponentialPrimitive, Finset.sum_range_one, zero_add, pow_one,
      Nat.factorial_one, Nat.cast_one, div_one] using equality
  rw [value parameter, value 1, one_smul]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
