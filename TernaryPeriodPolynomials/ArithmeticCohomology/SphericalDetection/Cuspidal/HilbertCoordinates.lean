module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorValues
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.HilbertModel

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {V : Type} [AddCommGroup V] [Module ℂ V] {index : Type} [Fintype index]

def cuspidalTensorHilbertEmbedding (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V) :
    cuspidalTensorValues cusp V →ₗ[ℂ] (index → cusp.H) :=
  LinearMap.pi (fun position => cusp.smooth.subtype.comp (cuspidalTensorFunctional cusp (basis.coord position)))

omit [Fintype index] in
theorem cuspidalTensorHilbertEmbedding_injective (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V) :
    Function.Injective (cuspidalTensorHilbertEmbedding cusp basis) := by
  intro first second equality
  apply Subtype.ext
  funext argument
  apply basis.repr.injective
  ext position
  change basis.coord position (first.val argument) = basis.coord position (second.val argument)
  have vector_eq : cuspidalTensorFunctional cusp (basis.coord position) first =
      cuspidalTensorFunctional cusp (basis.coord position) second := Subtype.ext (congrFun equality position)
  have values := congrArg (fun vector => cusp.realize vector argument) vector_eq
  simpa only [cuspidalTensorFunctional_realize] using values

def basisHilbertCoefficient (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (linear : Module.End ℂ V) : (index → cusp.H) →L[ℂ] (index → cusp.H) :=
  ContinuousLinearMap.pi (fun position =>
    ∑ source, basis.coord position (linear (basis source)) • (ContinuousLinearMap.proj source : (index → cusp.H) →L[ℂ] cusp.H))

theorem basisHilbertCoefficient_apply (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (linear : Module.End ℂ V) (vectors : index → cusp.H) (position : index) :
    basisHilbertCoefficient cusp basis linear vectors position =
      ∑ source, basis.coord position (linear (basis source)) • vectors source := by
  simp only [basisHilbertCoefficient, ContinuousLinearMap.pi_apply, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply]

theorem basisHilbertCoefficient_one (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V) :
    basisHilbertCoefficient cusp basis 1 = 1 := by
  classical
  apply ContinuousLinearMap.ext
  intro vectors
  funext position
  simp [basisHilbertCoefficient_apply, Module.Basis.coord_apply]

theorem basisHilbertCoefficient_mul (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (first second : Module.End ℂ V) :
    basisHilbertCoefficient cusp basis (first * second) =
      basisHilbertCoefficient cusp basis first * basisHilbertCoefficient cusp basis second := by
  classical
  have coefficients (position source : index) :
      basis.coord position (first (second (basis source))) =
        ∑ middle, basis.coord position (first (basis middle)) * basis.coord middle (second (basis source)) := by
    have expanded := congrArg (fun vector => basis.coord position (first vector)) (basis.sum_repr (second (basis source)))
    simpa only [map_sum, map_smul, Module.Basis.coord_apply, smul_eq_mul, mul_comm] using expanded.symm
  apply ContinuousLinearMap.ext
  intro vectors
  funext position
  change basisHilbertCoefficient cusp basis (first * second) vectors position =
    basisHilbertCoefficient cusp basis first (basisHilbertCoefficient cusp basis second vectors) position
  simp only [basisHilbertCoefficient_apply, Module.End.mul_apply, coefficients, Finset.sum_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

def basisHilbertCoefficientHom (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V) :
    Module.End ℂ V →ₐ[ℂ] Module.End ℂ (index → cusp.H) where
  toFun linear := (basisHilbertCoefficient cusp basis linear).toLinearMap
  map_one' := by
    rw [basisHilbertCoefficient_one]
    rfl
  map_mul' first second := by
    rw [basisHilbertCoefficient_mul]
    rfl
  map_zero' := by
    apply LinearMap.ext
    intro vectors
    funext position
    simp [basisHilbertCoefficient_apply]
  map_add' first second := by
    apply LinearMap.ext
    intro vectors
    funext position
    simp [basisHilbertCoefficient_apply, add_smul, Finset.sum_add_distrib]
  commutes' scalar := by
    classical
    apply LinearMap.ext
    intro vectors
    funext position
    simp [basisHilbertCoefficient_apply, Algebra.algebraMap_eq_smul_one, Module.Basis.coord_apply,
      Finsupp.single_apply, mul_ite, ite_smul]

theorem cuspidalTensorHilbertEmbedding_map (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (linear : Module.End ℂ V) (values : cuspidalTensorValues cusp V) :
    cuspidalTensorHilbertEmbedding cusp basis (cuspidalTensorMap cusp linear values) =
      basisHilbertCoefficient cusp basis linear (cuspidalTensorHilbertEmbedding cusp basis values) := by
  classical
  funext position
  have coordinate : cuspidalTensorFunctional cusp (basis.coord position) (cuspidalTensorMap cusp linear values) =
      ∑ source, basis.coord position (linear (basis source)) • cuspidalTensorFunctional cusp (basis.coord source) values := by
    apply cusp.injective
    funext argument
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, cuspidalTensorFunctional_realize]
    change basis.coord position (linear (values.val argument)) = _
    have expansion := congrArg (fun vector => basis.coord position (linear vector)) (basis.sum_repr (values.val argument))
    simpa only [map_sum, map_smul, Module.Basis.coord_apply, smul_eq_mul, mul_comm] using expansion.symm
  have hilbert := congrArg Subtype.val coordinate
  simpa only [Submodule.coe_sum, Submodule.coe_smul, cuspidalTensorHilbertEmbedding, LinearMap.pi_apply,
    LinearMap.comp_apply, Submodule.subtype_apply, basisHilbertCoefficient_apply] using hilbert

end TernaryPeriodPolynomials.SphericalDetection.Helpers
